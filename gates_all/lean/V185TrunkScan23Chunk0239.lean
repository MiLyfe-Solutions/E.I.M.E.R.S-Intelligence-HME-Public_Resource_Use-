import V185TrunkScan23Chunk0238

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1414129 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_1414129 : Nat := 118140960795 + 1414129 * 2 ^ 59
def prefixEnd_1414129 : Nat := 4983230072969 + 3 ^ 40 * 1414129 * 2
def baseEnd_1414129 : Nat := 726127884462002947484045

theorem tailTrace_1414129 : CollatzResearch.WordTrace tailWord_1414129 prefixEnd_1414129 726127884462002947484045 := by
  unfold tailWord_1414129
  simp only [CollatzResearch.WordTrace]
  refine ⟨51577521893859621850397441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34385014595906414566931627 51577521893859621850397441)
  ·
    refine ⟨38683141420394716387798081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51577521893859621850397441 38683141420394716387798081)
    ·
      refine ⟨29012356065296037290848561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38683141420394716387798081 29012356065296037290848561)
      ·
        refine ⟨21759267048972027968136421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29012356065296037290848561 21759267048972027968136421)
        ·
          refine ⟨4079862571682255244025579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21759267048972027968136421 4079862571682255244025579)
          ·
            refine ⟨6119793857523382866038369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4079862571682255244025579 6119793857523382866038369)
            ·
              refine ⟨4589845393142537149528777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6119793857523382866038369 4589845393142537149528777)
              ·
                refine ⟨3442384044856902862146583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4589845393142537149528777 3442384044856902862146583)
                ·
                  refine ⟨5163576067285354293219875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442384044856902862146583 5163576067285354293219875)
                  ·
                    refine ⟨7745364100928031439829813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5163576067285354293219875 7745364100928031439829813)
                    ·
                      refine ⟨726127884462002947484045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7745364100928031439829813 726127884462002947484045)
                      ·
                        rfl

theorem cell23_1414129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_1414129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414129 prefixEnd_1414129 := by exact prefixLift 1414129
  have htrace : WordTrace (prefixWord ++ tailWord_1414129) baseStart_1414129 baseEnd_1414129 := by
    simpa [prefixWord, tailWord_1414129, baseEnd_1414129] using wordTrace_append hprefix tailTrace_1414129
  have hstable : (prefixWord ++ tailWord_1414129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414129).length < 2 ^ (prefixWord ++ tailWord_1414129).sum := by decide
  have hdescent : baseEnd_1414129 < baseStart_1414129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414177 : List Nat := [1, 2, 3, 2, 3, 1, 4, 2, 1, 2, 2]
def baseStart_1414177 : Nat := 118140960795 + 1414177 * 2 ^ 59
def prefixEnd_1414177 : Nat := 4983230072969 + 3 ^ 40 * 1414177 * 2
def baseEnd_1414177 : Nat := 726152531533418759683825

theorem tailTrace_1414177 : CollatzResearch.WordTrace tailWord_1414177 prefixEnd_1414177 726152531533418759683825 := by
  unfold tailWord_1414177
  simp only [CollatzResearch.WordTrace]
  refine ⟨51579272597685726048144785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34386181731790484032096523 51579272597685726048144785)
  ·
    refine ⟨38684454448264294536108589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51579272597685726048144785 38684454448264294536108589)
    ·
      refine ⟨14506670418099110451040721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38684454448264294536108589 14506670418099110451040721)
      ·
        refine ⟨10880002813574332838280541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14506670418099110451040721 10880002813574332838280541)
        ·
          refine ⟨4080001055090374814355203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10880002813574332838280541 4080001055090374814355203)
          ·
            refine ⟨6120001582635562221532805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080001055090374814355203 6120001582635562221532805)
            ·
              refine ⟨1147500296744167916537401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6120001582635562221532805 1147500296744167916537401)
              ·
                refine ⟨860625222558125937403051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147500296744167916537401 860625222558125937403051)
                ·
                  refine ⟨1290937833837188906104577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860625222558125937403051 1290937833837188906104577)
                  ·
                    refine ⟨968203375377891679578433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1290937833837188906104577 968203375377891679578433)
                    ·
                      refine ⟨726152531533418759683825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968203375377891679578433 726152531533418759683825)
                      ·
                        rfl

theorem cell23_1414177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_1414177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414177 prefixEnd_1414177 := by exact prefixLift 1414177
  have htrace : WordTrace (prefixWord ++ tailWord_1414177) baseStart_1414177 baseEnd_1414177 := by
    simpa [prefixWord, tailWord_1414177, baseEnd_1414177] using wordTrace_append hprefix tailTrace_1414177
  have hstable : (prefixWord ++ tailWord_1414177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414177).length < 2 ^ (prefixWord ++ tailWord_1414177).sum := by decide
  have hdescent : baseEnd_1414177 < baseStart_1414177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414216 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 1, 4, 2]
def baseStart_1414216 : Nat := 118140960795 + 1414216 * 2 ^ 59
def prefixEnd_1414216 : Nat := 4983230072969 + 3 ^ 40 * 1414216 * 2
def baseEnd_1414216 : Nat := 726172557278944107096145

theorem tailTrace_1414216 : CollatzResearch.WordTrace tailWord_1414216 prefixEnd_1414216 726172557278944107096145 := by
  unfold tailWord_1414216
  simp only [CollatzResearch.WordTrace]
  refine ⟨25790347522272217854407251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34387130029696290472543001 25790347522272217854407251)
  ·
    refine ⟨38685521283408326781610877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25790347522272217854407251 38685521283408326781610877)
    ·
      refine ⟨14507070481278122543104079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38685521283408326781610877 14507070481278122543104079)
      ·
        refine ⟨21760605721917183814656119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14507070481278122543104079 21760605721917183814656119)
        ·
          refine ⟨32640908582875775721984179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21760605721917183814656119 32640908582875775721984179)
          ·
            refine ⟨48961362874313663582976269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32640908582875775721984179 48961362874313663582976269)
            ·
              refine ⟨18360511077867623843616101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48961362874313663582976269 18360511077867623843616101)
              ·
                refine ⟨3442595827100179470678019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18360511077867623843616101 3442595827100179470678019)
                ·
                  refine ⟨5163893740650269206017029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442595827100179470678019 5163893740650269206017029)
                  ·
                    refine ⟨968230076371925476128193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5163893740650269206017029 968230076371925476128193)
                    ·
                      refine ⟨726172557278944107096145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968230076371925476128193 726172557278944107096145)
                      ·
                        rfl

theorem cell23_1414216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_1414216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414216 prefixEnd_1414216 := by exact prefixLift 1414216
  have htrace : WordTrace (prefixWord ++ tailWord_1414216) baseStart_1414216 baseEnd_1414216 := by
    simpa [prefixWord, tailWord_1414216, baseEnd_1414216] using wordTrace_append hprefix tailTrace_1414216
  have hstable : (prefixWord ++ tailWord_1414216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414216).length < 2 ^ (prefixWord ++ tailWord_1414216).sum := by decide
  have hdescent : baseEnd_1414216 < baseStart_1414216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414229 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1414229 : Nat := 118140960795 + 1414229 * 2 ^ 59
def prefixEnd_1414229 : Nat := 4983230072969 + 3 ^ 40 * 1414229 * 2
def baseEnd_1414229 : Nat := 726179232527452556233585

theorem tailTrace_1414229 : CollatzResearch.WordTrace tailWord_1414229 prefixEnd_1414229 726179232527452556233585 := by
  unfold tailWord_1414229
  simp only [CollatzResearch.WordTrace]
  refine ⟨51581169193497338929037741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34387446128998225952691827 51581169193497338929037741)
  ·
    refine ⟨19342938447561502098389153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51581169193497338929037741 19342938447561502098389153)
    ·
      refine ⟨14507203835671126573791865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19342938447561502098389153 14507203835671126573791865)
      ·
        refine ⟨10880402876753344930343899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14507203835671126573791865 10880402876753344930343899)
        ·
          refine ⟨16320604315130017395515849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10880402876753344930343899 16320604315130017395515849)
          ·
            refine ⟨12240453236347513046636887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16320604315130017395515849 12240453236347513046636887)
            ·
              refine ⟨18360679854521269569955331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12240453236347513046636887 18360679854521269569955331)
              ·
                refine ⟨27541019781781904354932997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18360679854521269569955331 27541019781781904354932997)
                ·
                  refine ⟨5163941209084107066549937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27541019781781904354932997 5163941209084107066549937)
                  ·
                    refine ⟨3872955906813080299912453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5163941209084107066549937 3872955906813080299912453)
                    ·
                      refine ⟨726179232527452556233585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3872955906813080299912453 726179232527452556233585)
                      ·
                        rfl

theorem cell23_1414229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1414229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414229 prefixEnd_1414229 := by exact prefixLift 1414229
  have htrace : WordTrace (prefixWord ++ tailWord_1414229) baseStart_1414229 baseEnd_1414229 := by
    simpa [prefixWord, tailWord_1414229, baseEnd_1414229] using wordTrace_append hprefix tailTrace_1414229
  have hstable : (prefixWord ++ tailWord_1414229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414229).length < 2 ^ (prefixWord ++ tailWord_1414229).sum := by decide
  have hdescent : baseEnd_1414229 < baseStart_1414229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414233 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 2, 2, 2]
def baseStart_1414233 : Nat := 118140960795 + 1414233 * 2 ^ 59
def prefixEnd_1414233 : Nat := 4983230072969 + 3 ^ 40 * 1414233 * 2
def baseEnd_1414233 : Nat := 726181286450070540583567

theorem tailTrace_1414233 : CollatzResearch.WordTrace tailWord_1414233 prefixEnd_1414233 726181286450070540583567 := by
  unfold tailWord_1414233
  simp only [CollatzResearch.WordTrace]
  refine ⟨51581315085482847612183353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34387543390321898408122235 51581315085482847612183353)
  ·
    refine ⟨38685986314112135709137515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51581315085482847612183353 38685986314112135709137515)
    ·
      refine ⟨58028979471168203563706273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38685986314112135709137515 58028979471168203563706273)
      ·
        refine ⟨43521734603376152672779705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58028979471168203563706273 43521734603376152672779705)
        ·
          refine ⟨32641300952532114504584779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43521734603376152672779705 32641300952532114504584779)
          ·
            refine ⟨48961951428798171756877169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32641300952532114504584779 48961951428798171756877169)
            ·
              refine ⟨36721463571598628817657877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48961951428798171756877169 36721463571598628817657877)
              ·
                refine ⟨1721318604918685725827713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36721463571598628817657877 1721318604918685725827713)
                ·
                  refine ⟨1290988953689014294370785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1721318604918685725827713 1290988953689014294370785)
                  ·
                    refine ⟨968241715266760720778089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1290988953689014294370785 968241715266760720778089)
                    ·
                      refine ⟨726181286450070540583567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968241715266760720778089 726181286450070540583567)
                      ·
                        rfl

theorem cell23_1414233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 2, 2].length) (baseStart_1414233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414233 prefixEnd_1414233 := by exact prefixLift 1414233
  have htrace : WordTrace (prefixWord ++ tailWord_1414233) baseStart_1414233 baseEnd_1414233 := by
    simpa [prefixWord, tailWord_1414233, baseEnd_1414233] using wordTrace_append hprefix tailTrace_1414233
  have hstable : (prefixWord ++ tailWord_1414233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414233).length < 2 ^ (prefixWord ++ tailWord_1414233).sum := by decide
  have hdescent : baseEnd_1414233 < baseStart_1414233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414239 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 7]
def baseStart_1414239 : Nat := 118140960795 + 1414239 * 2 ^ 59
def prefixEnd_1414239 : Nat := 4983230072969 + 3 ^ 40 * 1414239 * 2
def baseEnd_1414239 : Nat := 80687151925999724123171

theorem tailTrace_1414239 : CollatzResearch.WordTrace tailWord_1414239 prefixEnd_1414239 80687151925999724123171 := by
  unfold tailWord_1414239
  simp only [CollatzResearch.WordTrace]
  refine ⟨51581533923461110636901771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34387689282307407091267847 51581533923461110636901771)
  ·
    refine ⟨77372300885191665955352657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51581533923461110636901771 77372300885191665955352657)
    ·
      refine ⟨58029225663893749466514493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77372300885191665955352657 58029225663893749466514493)
      ·
        refine ⟨21760959623960156049942935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58029225663893749466514493 21760959623960156049942935)
        ·
          refine ⟨32641439435940234074914403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21760959623960156049942935 32641439435940234074914403)
          ·
            refine ⟨48962159153910351112371605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32641439435940234074914403 48962159153910351112371605)
            ·
              refine ⟨2295101210339547708392419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48962159153910351112371605 2295101210339547708392419)
              ·
                refine ⟨3442651815509321562588629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295101210339547708392419 3442651815509321562588629)
                ·
                  refine ⟨80687151925999724123171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3442651815509321562588629 80687151925999724123171)
                  ·
                    rfl

theorem cell23_1414239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 7].length) (baseStart_1414239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414239 prefixEnd_1414239 := by exact prefixLift 1414239
  have htrace : WordTrace (prefixWord ++ tailWord_1414239) baseStart_1414239 baseEnd_1414239 := by
    simpa [prefixWord, tailWord_1414239, baseEnd_1414239] using wordTrace_append hprefix tailTrace_1414239
  have hstable : (prefixWord ++ tailWord_1414239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414239).length < 2 ^ (prefixWord ++ tailWord_1414239).sum := by decide
  have hdescent : baseEnd_1414239 < baseStart_1414239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414250 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_1414250 : Nat := 118140960795 + 1414250 * 2 ^ 59
def prefixEnd_1414250 : Nat := 4983230072969 + 3 ^ 40 * 1414250 * 2
def baseEnd_1414250 : Nat := 726190015621196974070989

theorem tailTrace_1414250 : CollatzResearch.WordTrace tailWord_1414250 prefixEnd_1414250 726190015621196974070989 := by
  unfold tailWord_1414250
  simp only [CollatzResearch.WordTrace]
  refine ⟨12895483781605314878888051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34387956750947506343701469 12895483781605314878888051)
  ·
    refine ⟨19343225672407972318332077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12895483781605314878888051 19343225672407972318332077)
    ·
      refine ⟨7253709627152989619374529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19343225672407972318332077 7253709627152989619374529)
      ·
        refine ⟨5440282220364742214530897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7253709627152989619374529 5440282220364742214530897)
        ·
          refine ⟨4080211665273556660898173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5440282220364742214530897 4080211665273556660898173)
          ·
            refine ⟨1530079374477583747836815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4080211665273556660898173 1530079374477583747836815)
            ·
              refine ⟨2295119061716375621755223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1530079374477583747836815 2295119061716375621755223)
              ·
                refine ⟨3442678592574563432632835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295119061716375621755223 3442678592574563432632835)
                ·
                  refine ⟨5164017888861845148949253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3442678592574563432632835 5164017888861845148949253)
                  ·
                    refine ⟨968253354161595965427985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5164017888861845148949253 968253354161595965427985)
                    ·
                      refine ⟨726190015621196974070989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968253354161595965427985 726190015621196974070989)
                      ·
                        rfl

theorem cell23_1414250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_1414250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414250 prefixEnd_1414250 := by exact prefixLift 1414250
  have htrace : WordTrace (prefixWord ++ tailWord_1414250) baseStart_1414250 baseEnd_1414250 := by
    simpa [prefixWord, tailWord_1414250, baseEnd_1414250] using wordTrace_append hprefix tailTrace_1414250
  have hstable : (prefixWord ++ tailWord_1414250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414250).length < 2 ^ (prefixWord ++ tailWord_1414250).sum := by decide
  have hdescent : baseEnd_1414250 < baseStart_1414250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414269 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_1414269 : Nat := 118140960795 + 1414269 * 2 ^ 59
def prefixEnd_1414269 : Nat := 4983230072969 + 3 ^ 40 * 1414269 * 2
def baseEnd_1414269 : Nat := 242066590584544133244467

theorem tailTrace_1414269 : CollatzResearch.WordTrace tailWord_1414269 prefixEnd_1414269 242066590584544133244467 := by
  unfold tailWord_1414269
  simp only [CollatzResearch.WordTrace]
  refine ⟨51582628113352425760493861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34388418742234950506995907 51582628113352425760493861)
  ·
    refine ⟨9671742771253579830092599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51582628113352425760493861 9671742771253579830092599)
    ·
      refine ⟨14507614156880369745138899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9671742771253579830092599 14507614156880369745138899)
      ·
        refine ⟨21761421235320554617708349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14507614156880369745138899 21761421235320554617708349)
        ·
          refine ⟨8160532963245207981640631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21761421235320554617708349 8160532963245207981640631)
          ·
            refine ⟨12240799444867811972460947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8160532963245207981640631 12240799444867811972460947)
            ·
              refine ⟨18361199167301717958691421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12240799444867811972460947 18361199167301717958691421)
              ·
                refine ⟨6885449687738144234509283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18361199167301717958691421 6885449687738144234509283)
                ·
                  refine ⟨10328174531607216351763925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6885449687738144234509283 10328174531607216351763925)
                  ·
                    refine ⟨242066590584544133244467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10328174531607216351763925 242066590584544133244467)
                    ·
                      rfl

theorem cell23_1414269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_1414269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414269 prefixEnd_1414269 := by exact prefixLift 1414269
  have htrace : WordTrace (prefixWord ++ tailWord_1414269) baseStart_1414269 baseEnd_1414269 := by
    simpa [prefixWord, tailWord_1414269, baseEnd_1414269] using wordTrace_append hprefix tailTrace_1414269
  have hstable : (prefixWord ++ tailWord_1414269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414269).length < 2 ^ (prefixWord ++ tailWord_1414269).sum := by decide
  have hdescent : baseEnd_1414269 < baseStart_1414269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414273 : List Nat := [1, 2, 4, 2, 2, 1, 3, 3, 5]
def baseStart_1414273 : Nat := 118140960795 + 1414273 * 2 ^ 59
def prefixEnd_1414273 : Nat := 4983230072969 + 3 ^ 40 * 1414273 * 2
def baseEnd_1414273 : Nat := 80689091741805598231487

theorem tailTrace_1414273 : CollatzResearch.WordTrace tailWord_1414273 prefixEnd_1414273 80689091741805598231487 := by
  unfold tailWord_1414273
  simp only [CollatzResearch.WordTrace]
  refine ⟨51582774005337934443639473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34388516003558622962426315 51582774005337934443639473)
  ·
    refine ⟨38687080504003450832729605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51582774005337934443639473 38687080504003450832729605)
    ·
      refine ⟨7253827594500647031136801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38687080504003450832729605 7253827594500647031136801)
      ·
        refine ⟨5440370695875485273352601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7253827594500647031136801 5440370695875485273352601)
        ·
          refine ⟨4080278021906613955014451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5440370695875485273352601 4080278021906613955014451)
          ·
            refine ⟨6120417032859920932521677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080278021906613955014451 6120417032859920932521677)
            ·
              refine ⟨2295156387322470349695629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6120417032859920932521677 2295156387322470349695629)
              ·
                refine ⟨860683645245926381135861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2295156387322470349695629 860683645245926381135861)
                ·
                  refine ⟨80689091741805598231487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 860683645245926381135861 80689091741805598231487)
                  ·
                    rfl

theorem cell23_1414273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 5].length) (baseStart_1414273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414273 prefixEnd_1414273 := by exact prefixLift 1414273
  have htrace : WordTrace (prefixWord ++ tailWord_1414273) baseStart_1414273 baseEnd_1414273 := by
    simpa [prefixWord, tailWord_1414273, baseEnd_1414273] using wordTrace_append hprefix tailTrace_1414273
  have hstable : (prefixWord ++ tailWord_1414273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414273).length < 2 ^ (prefixWord ++ tailWord_1414273).sum := by decide
  have hdescent : baseEnd_1414273 < baseStart_1414273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414279 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1414279 : Nat := 118140960795 + 1414279 * 2 ^ 59
def prefixEnd_1414279 : Nat := 4983230072969 + 3 ^ 40 * 1414279 * 2
def baseEnd_1414279 : Nat := 726204906560177360608355

theorem tailTrace_1414279 : CollatzResearch.WordTrace tailWord_1414279 prefixEnd_1414279 726204906560177360608355 := by
  unfold tailWord_1414279
  simp only [CollatzResearch.WordTrace]
  refine ⟨51582992843316197468357891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34388661895544131645571927 51582992843316197468357891)
  ·
    refine ⟨77374489264974296202536837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51582992843316197468357891 77374489264974296202536837)
    ·
      refine ⟨14507716737182680537975657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77374489264974296202536837 14507716737182680537975657)
      ·
        refine ⟨10880787552887010403481743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14507716737182680537975657 10880787552887010403481743)
        ·
          refine ⟨16321181329330515605222615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10880787552887010403481743 16321181329330515605222615)
          ·
            refine ⟨24481771993995773407833923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16321181329330515605222615 24481771993995773407833923)
            ·
              refine ⟨36722657990993660111750885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24481771993995773407833923 36722657990993660111750885)
              ·
                refine ⟨6885498373311311270953291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36722657990993660111750885 6885498373311311270953291)
                ·
                  refine ⟨10328247559966966906429937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6885498373311311270953291 10328247559966966906429937)
                  ·
                    refine ⟨7746185669975225179822453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10328247559966966906429937 7746185669975225179822453)
                    ·
                      refine ⟨726204906560177360608355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7746185669975225179822453 726204906560177360608355)
                      ·
                        rfl

theorem cell23_1414279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1414279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414279 prefixEnd_1414279 := by exact prefixLift 1414279
  have htrace : WordTrace (prefixWord ++ tailWord_1414279) baseStart_1414279 baseEnd_1414279 := by
    simpa [prefixWord, tailWord_1414279, baseEnd_1414279] using wordTrace_append hprefix tailTrace_1414279
  have hstable : (prefixWord ++ tailWord_1414279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414279).length < 2 ^ (prefixWord ++ tailWord_1414279).sum := by decide
  have hdescent : baseEnd_1414279 < baseStart_1414279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414286 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_1414286 : Nat := 118140960795 + 1414286 * 2 ^ 59
def prefixEnd_1414286 : Nat := 4983230072969 + 3 ^ 40 * 1414286 * 2
def baseEnd_1414286 : Nat := 242069500308252944406941

theorem tailTrace_1414286 : CollatzResearch.WordTrace tailWord_1414286 prefixEnd_1414286 242069500308252944406941 := by
  unfold tailWord_1414286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6447906019286354707982839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34388832102860558442575141 6447906019286354707982839)
  ·
    refine ⟨9671859028929532061974259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6447906019286354707982839 9671859028929532061974259)
    ·
      refine ⟨14507788543394298092961389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9671859028929532061974259 14507788543394298092961389)
      ·
        refine ⟨5440420703772861784860521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14507788543394298092961389 5440420703772861784860521)
        ·
          refine ⟨4080315527829646338645391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5440420703772861784860521 4080315527829646338645391)
          ·
            refine ⟨6120473291744469507968087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080315527829646338645391 6120473291744469507968087)
            ·
              refine ⟨9180709937616704261952131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6120473291744469507968087 9180709937616704261952131)
              ·
                refine ⟨13771064906425056392928197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9180709937616704261952131 13771064906425056392928197)
                ·
                  refine ⟨2582074669954698073674037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13771064906425056392928197 2582074669954698073674037)
                  ·
                    refine ⟨242069500308252944406941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2582074669954698073674037 242069500308252944406941)
                    ·
                      rfl

theorem cell23_1414286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_1414286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414286 prefixEnd_1414286 := by exact prefixLift 1414286
  have htrace : WordTrace (prefixWord ++ tailWord_1414286) baseStart_1414286 baseEnd_1414286 := by
    simpa [prefixWord, tailWord_1414286, baseEnd_1414286] using wordTrace_append hprefix tailTrace_1414286
  have hstable : (prefixWord ++ tailWord_1414286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414286).length < 2 ^ (prefixWord ++ tailWord_1414286).sum := by decide
  have hdescent : baseEnd_1414286 < baseStart_1414286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414290 : List Nat := [3, 2, 3, 1, 1, 3, 3, 2, 5]
def baseStart_1414290 : Nat := 118140960795 + 1414290 * 2 ^ 59
def prefixEnd_1414290 : Nat := 4983230072969 + 3 ^ 40 * 1414290 * 2
def baseEnd_1414290 : Nat := 80690061649708535285645

theorem tailTrace_1414290 : CollatzResearch.WordTrace tailWord_1414290 prefixEnd_1414290 80690061649708535285645 := by
  unfold tailWord_1414290
  simp only [CollatzResearch.WordTrace]
  refine ⟨12895848511569086586752081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34388929364184230898005549 12895848511569086586752081)
  ·
    refine ⟨9671886383676814940064061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12895848511569086586752081 9671886383676814940064061)
    ·
      refine ⟨3626957393878805602524023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9671886383676814940064061 3626957393878805602524023)
      ·
        refine ⟨5440436090818208403786035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626957393878805602524023 5440436090818208403786035)
        ·
          refine ⟨8160654136227312605679053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5440436090818208403786035 8160654136227312605679053)
          ·
            refine ⟨3060245301085242227129645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8160654136227312605679053 3060245301085242227129645)
            ·
              refine ⟨1147591987906965835173617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3060245301085242227129645 1147591987906965835173617)
              ·
                refine ⟨860693990930224376380213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147591987906965835173617 860693990930224376380213)
                ·
                  refine ⟨80690061649708535285645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 860693990930224376380213 80690061649708535285645)
                  ·
                    rfl

theorem cell23_1414290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_1414290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414290 prefixEnd_1414290 := by exact prefixLift 1414290
  have htrace : WordTrace (prefixWord ++ tailWord_1414290) baseStart_1414290 baseEnd_1414290 := by
    simpa [prefixWord, tailWord_1414290, baseEnd_1414290] using wordTrace_append hprefix tailTrace_1414290
  have hstable : (prefixWord ++ tailWord_1414290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414290).length < 2 ^ (prefixWord ++ tailWord_1414290).sum := by decide
  have hdescent : baseEnd_1414290 < baseStart_1414290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414296 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1414296 : Nat := 118140960795 + 1414296 * 2 ^ 59
def prefixEnd_1414296 : Nat := 4983230072969 + 3 ^ 40 * 1414296 * 2
def baseEnd_1414296 : Nat := 726213635731303794095777

theorem tailTrace_1414296 : CollatzResearch.WordTrace tailWord_1414296 prefixEnd_1414296 726213635731303794095777 := by
  unfold tailWord_1414296
  simp only [CollatzResearch.WordTrace]
  refine ⟨25791806442127304685863371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34389075256169739581151161 25791806442127304685863371)
  ·
    refine ⟨38687709663190957028795057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25791806442127304685863371 38687709663190957028795057)
    ·
      refine ⟨29015782247393217771596293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38687709663190957028795057 29015782247393217771596293)
      ·
        refine ⟨5440459171386228332174305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29015782247393217771596293 5440459171386228332174305)
        ·
          refine ⟨4080344378539671249130729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5440459171386228332174305 4080344378539671249130729)
          ·
            refine ⟨3060258283904753436848047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4080344378539671249130729 3060258283904753436848047)
            ·
              refine ⟨4590387425857130155272071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060258283904753436848047 4590387425857130155272071)
              ·
                refine ⟨6885581138785695232908107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590387425857130155272071 6885581138785695232908107)
                ·
                  refine ⟨10328371708178542849362161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6885581138785695232908107 10328371708178542849362161)
                  ·
                    refine ⟨7746278781133907137021621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10328371708178542849362161 7746278781133907137021621)
                    ·
                      refine ⟨726213635731303794095777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7746278781133907137021621 726213635731303794095777)
                      ·
                        rfl

theorem cell23_1414296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1414296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414296 prefixEnd_1414296 := by exact prefixLift 1414296
  have htrace : WordTrace (prefixWord ++ tailWord_1414296) baseStart_1414296 baseEnd_1414296 := by
    simpa [prefixWord, tailWord_1414296, baseEnd_1414296] using wordTrace_append hprefix tailTrace_1414296
  have hstable : (prefixWord ++ tailWord_1414296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414296).length < 2 ^ (prefixWord ++ tailWord_1414296).sum := by decide
  have hdescent : baseEnd_1414296 < baseStart_1414296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414319 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 4]
def baseStart_1414319 : Nat := 118140960795 + 1414319 * 2 ^ 59
def prefixEnd_1414319 : Nat := 4983230072969 + 3 ^ 40 * 1414319 * 2
def baseEnd_1414319 : Nat := 726225445786357204108171

theorem tailTrace_1414319 : CollatzResearch.WordTrace tailWord_1414319 prefixEnd_1414319 726225445786357204108171 := by
  unfold tailWord_1414319
  simp only [CollatzResearch.WordTrace]
  refine ⟨51584451763171284299814011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34389634508780856199876007 51584451763171284299814011)
  ·
    refine ⟨77376677644756926449721017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51584451763171284299814011 77376677644756926449721017)
    ·
      refine ⟨58032508233567694837290763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77376677644756926449721017 58032508233567694837290763)
      ·
        refine ⟨87048762350351542255936145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58032508233567694837290763 87048762350351542255936145)
        ·
          refine ⟨65286571762763656691952109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87048762350351542255936145 65286571762763656691952109)
          ·
            refine ⟨24482464411036371259482041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65286571762763656691952109 24482464411036371259482041)
            ·
              refine ⟨18361848308277278444611531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24482464411036371259482041 18361848308277278444611531)
              ·
                refine ⟨27542772462415917666917297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18361848308277278444611531 27542772462415917666917297)
                ·
                  refine ⟨20657079346811938250187973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27542772462415917666917297 20657079346811938250187973)
                  ·
                    refine ⟨3873202377527238421910245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20657079346811938250187973 3873202377527238421910245)
                    ·
                      refine ⟨726225445786357204108171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3873202377527238421910245 726225445786357204108171)
                      ·
                        rfl

theorem cell23_1414319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_1414319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414319 prefixEnd_1414319 := by exact prefixLift 1414319
  have htrace : WordTrace (prefixWord ++ tailWord_1414319) baseStart_1414319 baseEnd_1414319 := by
    simpa [prefixWord, tailWord_1414319, baseEnd_1414319] using wordTrace_append hprefix tailTrace_1414319
  have hstable : (prefixWord ++ tailWord_1414319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414319).length < 2 ^ (prefixWord ++ tailWord_1414319).sum := by decide
  have hdescent : baseEnd_1414319 < baseStart_1414319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414346 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 6]
def baseStart_1414346 : Nat := 118140960795 + 1414346 * 2 ^ 59
def prefixEnd_1414346 : Nat := 4983230072969 + 3 ^ 40 * 1414346 * 2
def baseEnd_1414346 : Nat := 80693256640447622052283

theorem tailTrace_1414346 : CollatzResearch.WordTrace tailWord_1414346 prefixEnd_1414346 80693256640447622052283 := by
  unfold tailWord_1414346
  simp only [CollatzResearch.WordTrace]
  refine ⟨12896359133518366977761723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34390291022715645274031261 12896359133518366977761723)
  ·
    refine ⟨19344538700277550466642585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12896359133518366977761723 19344538700277550466642585)
    ·
      refine ⟨14508404025208162849981939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19344538700277550466642585 14508404025208162849981939)
      ·
        refine ⟨21762606037812244274972909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14508404025208162849981939 21762606037812244274972909)
        ·
          refine ⟨8160977264179591603114841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21762606037812244274972909 8160977264179591603114841)
          ·
            refine ⟨6120732948134693702336131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8160977264179591603114841 6120732948134693702336131)
            ·
              refine ⟨9181099422202040553504197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6120732948134693702336131 9181099422202040553504197)
              ·
                refine ⟨1721456141662882603782037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9181099422202040553504197 1721456141662882603782037)
                ·
                  refine ⟨80693256640447622052283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1721456141662882603782037 80693256640447622052283)
                  ·
                    rfl

theorem cell23_1414346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_1414346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414346 prefixEnd_1414346 := by exact prefixLift 1414346
  have htrace : WordTrace (prefixWord ++ tailWord_1414346) baseStart_1414346 baseEnd_1414346 := by
    simpa [prefixWord, tailWord_1414346, baseEnd_1414346] using wordTrace_append hprefix tailTrace_1414346
  have hstable : (prefixWord ++ tailWord_1414346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414346).length < 2 ^ (prefixWord ++ tailWord_1414346).sum := by decide
  have hdescent : baseEnd_1414346 < baseStart_1414346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414376 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 3, 5]
def baseStart_1414376 : Nat := 118140960795 + 1414376 * 2 ^ 59
def prefixEnd_1414376 : Nat := 4983230072969 + 3 ^ 40 * 1414376 * 2
def baseEnd_1414376 : Nat := 242084904727887827031803

theorem tailTrace_1414376 : CollatzResearch.WordTrace tailWord_1414376 prefixEnd_1414376 242084904727887827031803 := by
  unfold tailWord_1414376
  simp only [CollatzResearch.WordTrace]
  refine ⟨25793265361982391517319491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34391020482643188689759321 25793265361982391517319491)
  ·
    refine ⟨38689898042973587275979237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25793265361982391517319491 38689898042973587275979237)
    ·
      refine ⟨7254355883057547614246107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38689898042973587275979237 7254355883057547614246107)
      ·
        refine ⟨10881533824586321421369161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7254355883057547614246107 10881533824586321421369161)
        ·
          refine ⟨8161150368439741066026871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10881533824586321421369161 8161150368439741066026871)
          ·
            refine ⟨12241725552659611599040307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8161150368439741066026871 12241725552659611599040307)
            ·
              refine ⟨18362588328989417398560461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12241725552659611599040307 18362588328989417398560461)
              ·
                refine ⟨6885970623371031524460173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18362588328989417398560461 6885970623371031524460173)
                ·
                  refine ⟨2582238983764136821672565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6885970623371031524460173 2582238983764136821672565)
                  ·
                    refine ⟨242084904727887827031803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2582238983764136821672565 242084904727887827031803)
                    ·
                      rfl

theorem cell23_1414376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_1414376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414376 prefixEnd_1414376 := by exact prefixLift 1414376
  have htrace : WordTrace (prefixWord ++ tailWord_1414376) baseStart_1414376 baseEnd_1414376 := by
    simpa [prefixWord, tailWord_1414376, baseEnd_1414376] using wordTrace_append hprefix tailTrace_1414376
  have hstable : (prefixWord ++ tailWord_1414376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414376).length < 2 ^ (prefixWord ++ tailWord_1414376).sum := by decide
  have hdescent : baseEnd_1414376 < baseStart_1414376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414436 : List Nat := [2, 3, 1, 3, 1, 1, 3, 9]
def baseStart_1414436 : Nat := 118140960795 + 1414436 * 2 ^ 59
def prefixEnd_1414436 : Nat := 4983230072969 + 3 ^ 40 * 1414436 * 2
def baseEnd_1414436 : Nat := 26899463815664194309079

theorem tailTrace_1414436 : CollatzResearch.WordTrace tailWord_1414436 prefixEnd_1414436 26899463815664194309079 := by
  unfold tailWord_1414436
  simp only [CollatzResearch.WordTrace]
  refine ⟨25794359551873706640911581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34392479402498275521215441 25794359551873706640911581)
  ·
    refine ⟨9672884831952639990341843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25794359551873706640911581 9672884831952639990341843)
    ·
      refine ⟨14509327247928959985512765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9672884831952639990341843 14509327247928959985512765)
      ·
        refine ⟨5440997717973359994567287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14509327247928959985512765 5440997717973359994567287)
        ·
          refine ⟨8161496576960039991850931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5440997717973359994567287 8161496576960039991850931)
          ·
            refine ⟨12242244865440059987776397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8161496576960039991850931 12242244865440059987776397)
            ·
              refine ⟨4590841824540022495416149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12242244865440059987776397 4590841824540022495416149)
              ·
                refine ⟨26899463815664194309079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4590841824540022495416149 26899463815664194309079)
                ·
                  rfl

theorem cell23_1414436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 9].length) (baseStart_1414436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414436 prefixEnd_1414436 := by exact prefixLift 1414436
  have htrace : WordTrace (prefixWord ++ tailWord_1414436) baseStart_1414436 baseEnd_1414436 := by
    simpa [prefixWord, tailWord_1414436, baseEnd_1414436] using wordTrace_append hprefix tailTrace_1414436
  have hstable : (prefixWord ++ tailWord_1414436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414436).length < 2 ^ (prefixWord ++ tailWord_1414436).sum := by decide
  have hdescent : baseEnd_1414436 < baseStart_1414436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414450 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_1414450 : Nat := 118140960795 + 1414450 * 2 ^ 59
def prefixEnd_1414450 : Nat := 4983230072969 + 3 ^ 40 * 1414450 * 2
def baseEnd_1414450 : Nat := 726292711752096191570069

theorem tailTrace_1414450 : CollatzResearch.WordTrace tailWord_1414450 prefixEnd_1414450 726292711752096191570069 := by
  unfold tailWord_1414450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12897307431424173418208201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34392819817131129115221869 12897307431424173418208201)
  ·
    refine ⟨9672980573568130063656151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12897307431424173418208201 9672980573568130063656151)
    ·
      refine ⟨14509470860352195095484227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9672980573568130063656151 14509470860352195095484227)
      ·
        refine ⟨21764206290528292643226341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14509470860352195095484227 21764206290528292643226341)
        ·
          refine ⟨4080788679474054870604939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21764206290528292643226341 4080788679474054870604939)
          ·
            refine ⟨6121183019211082305907409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080788679474054870604939 6121183019211082305907409)
            ·
              refine ⟨4590887264408311729430557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6121183019211082305907409 4590887264408311729430557)
              ·
                refine ⟨1721582724153116898536459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4590887264408311729430557 1721582724153116898536459)
                ·
                  refine ⟨2582374086229675347804689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721582724153116898536459 2582374086229675347804689)
                  ·
                    refine ⟨1936780564672256510853517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2582374086229675347804689 1936780564672256510853517)
                    ·
                      refine ⟨726292711752096191570069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1936780564672256510853517 726292711752096191570069)
                      ·
                        rfl

theorem cell23_1414450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_1414450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414450 prefixEnd_1414450 := by exact prefixLift 1414450
  have htrace : WordTrace (prefixWord ++ tailWord_1414450) baseStart_1414450 baseEnd_1414450 := by
    simpa [prefixWord, tailWord_1414450, baseEnd_1414450] using wordTrace_append hprefix tailTrace_1414450
  have hstable : (prefixWord ++ tailWord_1414450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414450).length < 2 ^ (prefixWord ++ tailWord_1414450).sum := by decide
  have hdescent : baseEnd_1414450 < baseStart_1414450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414464 : List Nat := [2, 1, 1, 2, 2, 1, 7, 2, 1, 2, 2]
def baseStart_1414464 : Nat := 118140960795 + 1414464 * 2 ^ 59
def prefixEnd_1414464 : Nat := 4983230072969 + 3 ^ 40 * 1414464 * 2
def baseEnd_1414464 : Nat := 726299900481259136795005

theorem tailTrace_1414464 : CollatzResearch.WordTrace tailWord_1414464 prefixEnd_1414464 726299900481259136795005 := by
  unfold tailWord_1414464
  simp only [CollatzResearch.WordTrace]
  refine ⟨25794870173822987031921223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34393160231763982709228297 25794870173822987031921223)
  ·
    refine ⟨38692305260734480547881835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25794870173822987031921223 38692305260734480547881835)
    ·
      refine ⟨58038457891101720821822753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38692305260734480547881835 58038457891101720821822753)
      ·
        refine ⟨43528843418326290616367065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58038457891101720821822753 43528843418326290616367065)
        ·
          refine ⟨32646632563744717962275299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43528843418326290616367065 32646632563744717962275299)
          ·
            refine ⟨48969948845617076943412949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32646632563744717962275299 48969948845617076943412949)
            ·
              refine ⟨1147733176069150240861241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 48969948845617076943412949 1147733176069150240861241)
              ·
                refine ⟨860799882051862680645931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147733176069150240861241 860799882051862680645931)
                ·
                  refine ⟨1291199823077794020968897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 860799882051862680645931 1291199823077794020968897)
                  ·
                    refine ⟨968399867308345515726673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1291199823077794020968897 968399867308345515726673)
                    ·
                      refine ⟨726299900481259136795005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968399867308345515726673 726299900481259136795005)
                      ·
                        rfl

theorem cell23_1414464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 1, 2, 2].length) (baseStart_1414464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414464 prefixEnd_1414464 := by exact prefixLift 1414464
  have htrace : WordTrace (prefixWord ++ tailWord_1414464) baseStart_1414464 baseEnd_1414464 := by
    simpa [prefixWord, tailWord_1414464, baseEnd_1414464] using wordTrace_append hprefix tailTrace_1414464
  have hstable : (prefixWord ++ tailWord_1414464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414464).length < 2 ^ (prefixWord ++ tailWord_1414464).sum := by decide
  have hdescent : baseEnd_1414464 < baseStart_1414464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414480 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 2, 1, 3]
def baseStart_1414480 : Nat := 118140960795 + 1414480 * 2 ^ 59
def prefixEnd_1414480 : Nat := 4983230072969 + 3 ^ 40 * 1414480 * 2
def baseEnd_1414480 : Nat := 726308116171731074194931

theorem tailTrace_1414480 : CollatzResearch.WordTrace tailWord_1414480 prefixEnd_1414480 726308116171731074194931 := by
  unfold tailWord_1414480
  simp only [CollatzResearch.WordTrace]
  refine ⟨25795161957794004398212447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34393549277058672530949929 25795161957794004398212447)
  ·
    refine ⟨38692742936691006597318671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25795161957794004398212447 38692742936691006597318671)
    ·
      refine ⟨58039114405036509895978007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38692742936691006597318671 58039114405036509895978007)
      ·
        refine ⟨87058671607554764843967011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58039114405036509895978007 87058671607554764843967011)
        ·
          refine ⟨130588007411332147265950517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87058671607554764843967011 130588007411332147265950517)
          ·
            refine ⟨12242625694812388806182861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130588007411332147265950517 12242625694812388806182861)
            ·
              refine ⟨4590984635554645802318573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12242625694812388806182861 4590984635554645802318573)
              ·
                refine ⟨1721619238332992175869465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4590984635554645802318573 1721619238332992175869465)
                ·
                  refine ⟨1291214428749744131902099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1721619238332992175869465 1291214428749744131902099)
                  ·
                    refine ⟨1936821643124616197853149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1291214428749744131902099 1936821643124616197853149)
                    ·
                      refine ⟨726308116171731074194931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1936821643124616197853149 726308116171731074194931)
                      ·
                        rfl

theorem cell23_1414480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2, 1, 3].length) (baseStart_1414480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414480 prefixEnd_1414480 := by exact prefixLift 1414480
  have htrace : WordTrace (prefixWord ++ tailWord_1414480) baseStart_1414480 baseEnd_1414480 := by
    simpa [prefixWord, tailWord_1414480, baseEnd_1414480] using wordTrace_append hprefix tailTrace_1414480
  have hstable : (prefixWord ++ tailWord_1414480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414480).length < 2 ^ (prefixWord ++ tailWord_1414480).sum := by decide
  have hdescent : baseEnd_1414480 < baseStart_1414480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414530 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1414530 : Nat := 118140960795 + 1414530 * 2 ^ 59
def prefixEnd_1414530 : Nat := 4983230072969 + 3 ^ 40 * 1414530 * 2
def baseEnd_1414530 : Nat := 242111263401485292856567

theorem tailTrace_1414530 : CollatzResearch.WordTrace tailWord_1414530 prefixEnd_1414530 242111263401485292856567 := by
  unfold tailWord_1414530
  simp only [CollatzResearch.WordTrace]
  refine ⟨12898036891351716833936261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34394765043604578223830029 12898036891351716833936261)
  ·
    refine ⟨2418381917128446906363049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12898036891351716833936261 2418381917128446906363049)
    ·
      refine ⟨1813786437846335179772287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2418381917128446906363049 1813786437846335179772287)
      ·
        refine ⟨2720679656769502769658431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1813786437846335179772287 2720679656769502769658431)
        ·
          refine ⟨4081019485154254154487647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2720679656769502769658431 4081019485154254154487647)
          ·
            refine ⟨6121529227731381231731471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4081019485154254154487647 6121529227731381231731471)
            ·
              refine ⟨9182293841597071847597207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6121529227731381231731471 9182293841597071847597207)
              ·
                refine ⟨13773440762395607771395811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9182293841597071847597207 13773440762395607771395811)
                ·
                  refine ⟨20660161143593411657093717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13773440762395607771395811 20660161143593411657093717)
                  ·
                    refine ⟨242111263401485292856567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20660161143593411657093717 242111263401485292856567)
                    ·
                      rfl

theorem cell23_1414530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1414530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414530 prefixEnd_1414530 := by exact prefixLift 1414530
  have htrace : WordTrace (prefixWord ++ tailWord_1414530) baseStart_1414530 baseEnd_1414530 := by
    simpa [prefixWord, tailWord_1414530, baseEnd_1414530] using wordTrace_append hprefix tailTrace_1414530
  have hstable : (prefixWord ++ tailWord_1414530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414530).length < 2 ^ (prefixWord ++ tailWord_1414530).sum := by decide
  have hdescent : baseEnd_1414530 < baseStart_1414530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414537 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 1, 4, 2]
def baseStart_1414537 : Nat := 118140960795 + 1414537 * 2 ^ 59
def prefixEnd_1414537 : Nat := 4983230072969 + 3 ^ 40 * 1414537 * 2
def baseEnd_1414537 : Nat := 726337384569037351182169

theorem tailTrace_1414537 : CollatzResearch.WordTrace tailWord_1414537 prefixEnd_1414537 726337384569037351182169 := by
  unfold tailWord_1414537
  simp only [CollatzResearch.WordTrace]
  refine ⟨51592402876381507531249865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34394935250921005020833243 51592402876381507531249865)
  ·
    refine ⟨38694302157286130648437399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51592402876381507531249865 38694302157286130648437399)
    ·
      refine ⟨58041453235929195972656099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38694302157286130648437399 58041453235929195972656099)
      ·
        refine ⟨87062179853893793958984149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58041453235929195972656099 87062179853893793958984149)
        ·
          refine ⟨2040519840325635795913691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 87062179853893793958984149 2040519840325635795913691)
          ·
            refine ⟨3060779760488453693870537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040519840325635795913691 3060779760488453693870537)
            ·
              refine ⟨2295584820366340270402903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3060779760488453693870537 2295584820366340270402903)
              ·
                refine ⟨3443377230549510405604355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295584820366340270402903 3443377230549510405604355)
                ·
                  refine ⟨5165065845824265608406533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3443377230549510405604355 5165065845824265608406533)
                  ·
                    refine ⟨968449846092049801576225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5165065845824265608406533 968449846092049801576225)
                    ·
                      refine ⟨726337384569037351182169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968449846092049801576225 726337384569037351182169)
                      ·
                        rfl

theorem cell23_1414537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 4, 2].length) (baseStart_1414537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414537 prefixEnd_1414537 := by exact prefixLift 1414537
  have htrace : WordTrace (prefixWord ++ tailWord_1414537) baseStart_1414537 baseEnd_1414537 := by
    simpa [prefixWord, tailWord_1414537, baseEnd_1414537] using wordTrace_append hprefix tailTrace_1414537
  have hstable : (prefixWord ++ tailWord_1414537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414537).length < 2 ^ (prefixWord ++ tailWord_1414537).sum := by decide
  have hdescent : baseEnd_1414537 < baseStart_1414537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414558 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_1414558 : Nat := 118140960795 + 1414558 * 2 ^ 59
def prefixEnd_1414558 : Nat := 4983230072969 + 3 ^ 40 * 1414558 * 2
def baseEnd_1414558 : Nat := 726348167662781769019573

theorem tailTrace_1414558 : CollatzResearch.WordTrace tailWord_1414558 prefixEnd_1414558 726348167662781769019573 := by
  unfold tailWord_1414558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6449146101163178514720541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34395445872870285411842885 6449146101163178514720541)
  ·
    refine ⟨2418429787936191943020203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6449146101163178514720541 2418429787936191943020203)
    ·
      refine ⟨3627644681904287914530305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2418429787936191943020203 3627644681904287914530305)
      ·
        refine ⟨2720733511428215935897729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3627644681904287914530305 2720733511428215935897729)
        ·
          refine ⟨2040550133571161951923297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2720733511428215935897729 2040550133571161951923297)
          ·
            refine ⟨1530412600178371463942473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2040550133571161951923297 1530412600178371463942473)
            ·
              refine ⟨1147809450133778597956855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530412600178371463942473 1147809450133778597956855)
              ·
                refine ⟨1721714175200667896935283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147809450133778597956855 1721714175200667896935283)
                ·
                  refine ⟨2582571262801001845402925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721714175200667896935283 2582571262801001845402925)
                  ·
                    refine ⟨968464223550375692026097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2582571262801001845402925 968464223550375692026097)
                    ·
                      refine ⟨726348167662781769019573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968464223550375692026097 726348167662781769019573)
                      ·
                        rfl

theorem cell23_1414558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_1414558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414558 prefixEnd_1414558 := by exact prefixLift 1414558
  have htrace : WordTrace (prefixWord ++ tailWord_1414558) baseStart_1414558 baseEnd_1414558 := by
    simpa [prefixWord, tailWord_1414558, baseEnd_1414558] using wordTrace_append hprefix tailTrace_1414558
  have hstable : (prefixWord ++ tailWord_1414558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414558).length < 2 ^ (prefixWord ++ tailWord_1414558).sum := by decide
  have hdescent : baseEnd_1414558 < baseStart_1414558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414560 : List Nat := [2, 1, 1, 4, 1, 2, 4, 3, 5]
def baseStart_1414560 : Nat := 118140960795 + 1414560 * 2 ^ 59
def prefixEnd_1414560 : Nat := 4983230072969 + 3 ^ 40 * 1414560 * 2
def baseEnd_1414560 : Nat := 80705466069343417910507

theorem tailTrace_1414560 : CollatzResearch.WordTrace tailWord_1414560 prefixEnd_1414560 80705466069343417910507 := by
  unfold tailWord_1414560
  simp only [CollatzResearch.WordTrace]
  refine ⟨25796620877649091229668567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34395494503532121639558089 25796620877649091229668567)
  ·
    refine ⟨38694931316473636844502851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25796620877649091229668567 38694931316473636844502851)
    ·
      refine ⟨58042396974710455266754277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38694931316473636844502851 58042396974710455266754277)
      ·
        refine ⟨10882949432758210362516427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58042396974710455266754277 10882949432758210362516427)
        ·
          refine ⟨16324424149137315543774641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10882949432758210362516427 16324424149137315543774641)
          ·
            refine ⟨12243318111852986657830981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16324424149137315543774641 12243318111852986657830981)
            ·
              refine ⟨2295622145972434998343309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12243318111852986657830981 2295622145972434998343309)
              ·
                refine ⟨860858304739663124378741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2295622145972434998343309 860858304739663124378741)
                ·
                  refine ⟨80705466069343417910507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 860858304739663124378741 80705466069343417910507)
                  ·
                    rfl

theorem cell23_1414560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 5].length) (baseStart_1414560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414560 prefixEnd_1414560 := by exact prefixLift 1414560
  have htrace : WordTrace (prefixWord ++ tailWord_1414560) baseStart_1414560 baseEnd_1414560 := by
    simpa [prefixWord, tailWord_1414560, baseEnd_1414560] using wordTrace_append hprefix tailTrace_1414560
  have hstable : (prefixWord ++ tailWord_1414560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414560).length < 2 ^ (prefixWord ++ tailWord_1414560).sum := by decide
  have hdescent : baseEnd_1414560 < baseStart_1414560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414643 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 3]
def baseStart_1414643 : Nat := 118140960795 + 1414643 * 2 ^ 59
def prefixEnd_1414643 : Nat := 4983230072969 + 3 ^ 40 * 1414643 * 2
def baseEnd_1414643 : Nat := 726391813518413936456681

theorem tailTrace_1414643 : CollatzResearch.WordTrace tailWord_1414643 prefixEnd_1414643 726391813518413936456681 := by
  unfold tailWord_1414643
  simp only [CollatzResearch.WordTrace]
  refine ⟨51596269013997487634608583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34397512675998325089739055 51596269013997487634608583)
  ·
    refine ⟨77394403520996231451912875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51596269013997487634608583 77394403520996231451912875)
    ·
      refine ⟨116091605281494347177869313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77394403520996231451912875 116091605281494347177869313)
      ·
        refine ⟨87068703961120760383401985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116091605281494347177869313 87068703961120760383401985)
        ·
          refine ⟨65301527970840570287551489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87068703961120760383401985 65301527970840570287551489)
          ·
            refine ⟨48976145978130427715663617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65301527970840570287551489 48976145978130427715663617)
            ·
              refine ⟨36732109483597820786747713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48976145978130427715663617 36732109483597820786747713)
              ·
                refine ⟨27549082112698365590060785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36732109483597820786747713 27549082112698365590060785)
                ·
                  refine ⟨20661811584523774192545589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27549082112698365590060785 20661811584523774192545589)
                  ·
                    refine ⟨1937044836049103830551149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20661811584523774192545589 1937044836049103830551149)
                    ·
                      refine ⟨726391813518413936456681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1937044836049103830551149 726391813518413936456681)
                      ·
                        rfl

theorem cell23_1414643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 3].length) (baseStart_1414643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414643 prefixEnd_1414643 := by exact prefixLift 1414643
  have htrace : WordTrace (prefixWord ++ tailWord_1414643) baseStart_1414643 baseEnd_1414643 := by
    simpa [prefixWord, tailWord_1414643, baseEnd_1414643] using wordTrace_append hprefix tailTrace_1414643
  have hstable : (prefixWord ++ tailWord_1414643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414643).length < 2 ^ (prefixWord ++ tailWord_1414643).sum := by decide
  have hdescent : baseEnd_1414643 < baseStart_1414643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414687 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 2, 3, 2]
def baseStart_1414687 : Nat := 118140960795 + 1414687 * 2 ^ 59
def prefixEnd_1414687 : Nat := 4983230072969 + 3 ^ 40 * 1414687 * 2
def baseEnd_1414687 : Nat := 726414406667211764306479

theorem tailTrace_1414687 : CollatzResearch.WordTrace tailWord_1414687 prefixEnd_1414687 726414406667211764306479 := by
  unfold tailWord_1414687
  simp only [CollatzResearch.WordTrace]
  refine ⟨51597873825838083149210315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34398582550558722099473543 51597873825838083149210315)
  ·
    refine ⟨77396810738757124723815473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51597873825838083149210315 77396810738757124723815473)
    ·
      refine ⟨58047608054067843542861605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77396810738757124723815473 58047608054067843542861605)
      ·
        refine ⟨10883926510137720664286551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58047608054067843542861605 10883926510137720664286551)
        ·
          refine ⟨16325889765206580996429827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10883926510137720664286551 16325889765206580996429827)
          ·
            refine ⟨24488834647809871494644741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16325889765206580996429827 24488834647809871494644741)
            ·
              refine ⟨4591656496464350905245889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24488834647809871494644741 4591656496464350905245889)
              ·
                refine ⟨3443742372348263178934417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4591656496464350905245889 3443742372348263178934417)
                ·
                  refine ⟨2582806779261197384200813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3443742372348263178934417 2582806779261197384200813)
                  ·
                    refine ⟨968552542222949019075305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2582806779261197384200813 968552542222949019075305)
                    ·
                      refine ⟨726414406667211764306479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968552542222949019075305 726414406667211764306479)
                      ·
                        rfl

theorem cell23_1414687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_1414687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414687 prefixEnd_1414687 := by exact prefixLift 1414687
  have htrace : WordTrace (prefixWord ++ tailWord_1414687) baseStart_1414687 baseEnd_1414687 := by
    simpa [prefixWord, tailWord_1414687, baseEnd_1414687] using wordTrace_append hprefix tailTrace_1414687
  have hstable : (prefixWord ++ tailWord_1414687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414687).length < 2 ^ (prefixWord ++ tailWord_1414687).sum := by decide
  have hdescent : baseEnd_1414687 < baseStart_1414687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414693 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 5, 6]
def baseStart_1414693 : Nat := 118140960795 + 1414693 * 2 ^ 59
def prefixEnd_1414693 : Nat := 4983230072969 + 3 ^ 40 * 1414693 * 2
def baseEnd_1414693 : Nat := 242139162517046246943817

theorem tailTrace_1414693 : CollatzResearch.WordTrace tailWord_1414693 prefixEnd_1414693 242139162517046246943817 := by
  unfold tailWord_1414693
  simp only [CollatzResearch.WordTrace]
  refine ⟨51598092663816346173928733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34398728442544230782619155 51598092663816346173928733)
  ·
    refine ⟨19349284748931129815223275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51598092663816346173928733 19349284748931129815223275)
    ·
      refine ⟨29023927123396694722834913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19349284748931129815223275 29023927123396694722834913)
      ·
        refine ⟨21767945342547521042126185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29023927123396694722834913 21767945342547521042126185)
        ·
          refine ⟨16325959006910640781594639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21767945342547521042126185 16325959006910640781594639)
          ·
            refine ⟨24488938510365961172391959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16325959006910640781594639 24488938510365961172391959)
            ·
              refine ⟨36733407765548941758587939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24488938510365961172391959 36733407765548941758587939)
              ·
                refine ⟨55100111648323412637881909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36733407765548941758587939 55100111648323412637881909)
                ·
                  refine ⟨5165635467030319934801429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55100111648323412637881909 5165635467030319934801429)
                  ·
                    refine ⟨242139162517046246943817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5165635467030319934801429 242139162517046246943817)
                    ·
                      rfl

theorem cell23_1414693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 5, 6].length) (baseStart_1414693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414693 prefixEnd_1414693 := by exact prefixLift 1414693
  have htrace : WordTrace (prefixWord ++ tailWord_1414693) baseStart_1414693 baseEnd_1414693 := by
    simpa [prefixWord, tailWord_1414693, baseEnd_1414693] using wordTrace_append hprefix tailTrace_1414693
  have hstable : (prefixWord ++ tailWord_1414693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414693).length < 2 ^ (prefixWord ++ tailWord_1414693).sum := by decide
  have hdescent : baseEnd_1414693 < baseStart_1414693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414700 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 4, 6, 2]
def baseStart_1414700 : Nat := 118140960795 + 1414700 * 2 ^ 59
def prefixEnd_1414700 : Nat := 4983230072969 + 3 ^ 40 * 1414700 * 2
def baseEnd_1414700 : Nat := 726421081915720213443919

theorem tailTrace_1414700 : CollatzResearch.WordTrace tailWord_1414700 prefixEnd_1414700 726421081915720213443919 := by
  unfold tailWord_1414700
  simp only [CollatzResearch.WordTrace]
  refine ⟨25799173987395493184716777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34398898649860657579622369 25799173987395493184716777)
  ·
    refine ⟨19349380490546619888537583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25799173987395493184716777 19349380490546619888537583)
    ·
      refine ⟨29024070735819929832806375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19349380490546619888537583 29024070735819929832806375)
      ·
        refine ⟨43536106103729894749209563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29024070735819929832806375 43536106103729894749209563)
        ·
          refine ⟨65304159155594842123814345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43536106103729894749209563 65304159155594842123814345)
          ·
            refine ⟨48978119366696131592860759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65304159155594842123814345 48978119366696131592860759)
            ·
              refine ⟨73467179050044197389291139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48978119366696131592860759 73467179050044197389291139)
              ·
                refine ⟨110200768575066296083936709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73467179050044197389291139 110200768575066296083936709)
                ·
                  refine ⟨20662644107824930515738133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110200768575066296083936709 20662644107824930515738133)
                  ·
                    refine ⟨968561442554293617925225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20662644107824930515738133 968561442554293617925225)
                    ·
                      refine ⟨726421081915720213443919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968561442554293617925225 726421081915720213443919)
                      ·
                        rfl

theorem cell23_1414700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 6, 2].length) (baseStart_1414700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414700 prefixEnd_1414700 := by exact prefixLift 1414700
  have htrace : WordTrace (prefixWord ++ tailWord_1414700) baseStart_1414700 baseEnd_1414700 := by
    simpa [prefixWord, tailWord_1414700, baseEnd_1414700] using wordTrace_append hprefix tailTrace_1414700
  have hstable : (prefixWord ++ tailWord_1414700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414700).length < 2 ^ (prefixWord ++ tailWord_1414700).sum := by decide
  have hdescent : baseEnd_1414700 < baseStart_1414700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414730 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1414730 : Nat := 118140960795 + 1414730 * 2 ^ 59
def prefixEnd_1414730 : Nat := 4983230072969 + 3 ^ 40 * 1414730 * 2
def baseEnd_1414730 : Nat := 726436486335355096068781

theorem tailTrace_1414730 : CollatzResearch.WordTrace tailWord_1414730 prefixEnd_1414730 726436486335355096068781 := by
  unfold tailWord_1414730
  simp only [CollatzResearch.WordTrace]
  refine ⟨12899860541170575373256411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34399628109788200995350429 12899860541170575373256411)
  ·
    refine ⟨19349790811755863059884617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12899860541170575373256411 19349790811755863059884617)
    ·
      refine ⟨14512343108816897294913463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19349790811755863059884617 14512343108816897294913463)
      ·
        refine ⟨21768514663225345942370195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14512343108816897294913463 21768514663225345942370195)
        ·
          refine ⟨32652771994838018913555293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21768514663225345942370195 32652771994838018913555293)
          ·
            refine ⟨12244789498064257092583235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32652771994838018913555293 12244789498064257092583235)
            ·
              refine ⟨18367184247096385638874853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12244789498064257092583235 18367184247096385638874853)
              ·
                refine ⟨3443847046330572307289035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18367184247096385638874853 3443847046330572307289035)
                ·
                  refine ⟨5165770569495858460933553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3443847046330572307289035 5165770569495858460933553)
                  ·
                    refine ⟨3874327927121893845700165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5165770569495858460933553 3874327927121893845700165)
                    ·
                      refine ⟨726436486335355096068781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3874327927121893845700165 726436486335355096068781)
                      ·
                        rfl

theorem cell23_1414730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1414730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414730 prefixEnd_1414730 := by exact prefixLift 1414730
  have htrace : WordTrace (prefixWord ++ tailWord_1414730) baseStart_1414730 baseEnd_1414730 := by
    simpa [prefixWord, tailWord_1414730, baseEnd_1414730] using wordTrace_append hprefix tailTrace_1414730
  have hstable : (prefixWord ++ tailWord_1414730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414730).length < 2 ^ (prefixWord ++ tailWord_1414730).sum := by decide
  have hdescent : baseEnd_1414730 < baseStart_1414730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414737 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 1, 2, 3]
def baseStart_1414737 : Nat := 118140960795 + 1414737 * 2 ^ 59
def prefixEnd_1414737 : Nat := 4983230072969 + 3 ^ 40 * 1414737 * 2
def baseEnd_1414737 : Nat := 726440080699936568681249

theorem tailTrace_1414737 : CollatzResearch.WordTrace tailWord_1414737 prefixEnd_1414737 726440080699936568681249 := by
  unfold tailWord_1414737
  simp only [CollatzResearch.WordTrace]
  refine ⟨51599697475656941688530465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34399798317104627792353643 51599697475656941688530465)
  ·
    refine ⟨38699773106742706266397849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51599697475656941688530465 38699773106742706266397849)
    ·
      refine ⟨29024829830057029699798387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38699773106742706266397849 29024829830057029699798387)
      ·
        refine ⟨43537244745085544549697581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29024829830057029699798387 43537244745085544549697581)
        ·
          refine ⟨16326466779407079206136593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43537244745085544549697581 16326466779407079206136593)
          ·
            refine ⟨12244850084555309404602445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16326466779407079206136593 12244850084555309404602445)
            ·
              refine ⟨4591818781708241026725917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12244850084555309404602445 4591818781708241026725917)
              ·
                refine ⟨1721932043140590385022219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4591818781708241026725917 1721932043140590385022219)
                ·
                  refine ⟨2582898064710885577533329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1721932043140590385022219 2582898064710885577533329)
                  ·
                    refine ⟨1937173548533164183149997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2582898064710885577533329 1937173548533164183149997)
                    ·
                      refine ⟨726440080699936568681249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1937173548533164183149997 726440080699936568681249)
                      ·
                        rfl

theorem cell23_1414737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_1414737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414737 prefixEnd_1414737 := by exact prefixLift 1414737
  have htrace : WordTrace (prefixWord ++ tailWord_1414737) baseStart_1414737 baseEnd_1414737 := by
    simpa [prefixWord, tailWord_1414737, baseEnd_1414737] using wordTrace_append hprefix tailTrace_1414737
  have hstable : (prefixWord ++ tailWord_1414737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414737).length < 2 ^ (prefixWord ++ tailWord_1414737).sum := by decide
  have hdescent : baseEnd_1414737 < baseStart_1414737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414774 : List Nat := [5, 1, 1, 2, 2, 3, 2, 7]
def baseStart_1414774 : Nat := 118140960795 + 1414774 * 2 ^ 59
def prefixEnd_1414774 : Nat := 4983230072969 + 3 ^ 40 * 1414774 * 2
def baseEnd_1414774 : Nat := 26905891832746404589577

theorem tailTrace_1414774 : CollatzResearch.WordTrace tailWord_1414774 prefixEnd_1414774 26905891832746404589577 := by
  unfold tailWord_1414774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225065436032681062976711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34400697984348598005084917 3225065436032681062976711)
  ·
    refine ⟨4837598154049021594465067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3225065436032681062976711 4837598154049021594465067)
    ·
      refine ⟨7256397231073532391697601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4837598154049021594465067 7256397231073532391697601)
      ·
        refine ⟨5442297923305149293773201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7256397231073532391697601 5442297923305149293773201)
        ·
          refine ⟨4081723442478861970329901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5442297923305149293773201 4081723442478861970329901)
          ·
            refine ⟨1530646290929573238873713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4081723442478861970329901 1530646290929573238873713)
            ·
              refine ⟨1147984718197179929155285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530646290929573238873713 1147984718197179929155285)
              ·
                refine ⟨26905891832746404589577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1147984718197179929155285 26905891832746404589577)
                ·
                  rfl

theorem cell23_1414774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_1414774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414774 prefixEnd_1414774 := by exact prefixLift 1414774
  have htrace : WordTrace (prefixWord ++ tailWord_1414774) baseStart_1414774 baseEnd_1414774 := by
    simpa [prefixWord, tailWord_1414774, baseEnd_1414774] using wordTrace_append hprefix tailTrace_1414774
  have hstable : (prefixWord ++ tailWord_1414774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414774).length < 2 ^ (prefixWord ++ tailWord_1414774).sum := by decide
  have hdescent : baseEnd_1414774 < baseStart_1414774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414818 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1414818 : Nat := 118140960795 + 1414818 * 2 ^ 59
def prefixEnd_1414818 : Nat := 4983230072969 + 3 ^ 40 * 1414818 * 2
def baseEnd_1414818 : Nat := 726481672632950751768377

theorem tailTrace_1414818 : CollatzResearch.WordTrace tailWord_1414818 prefixEnd_1414818 726481672632950751768377 := by
  unfold tailWord_1414818
  simp only [CollatzResearch.WordTrace]
  refine ⟨12900662947090873130557277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34401767858908995014819405 12900662947090873130557277)
  ·
    refine ⟨4837748605159077423958979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12900662947090873130557277 4837748605159077423958979)
    ·
      refine ⟨7256622907738616135938469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4837748605159077423958979 7256622907738616135938469)
      ·
        refine ⟨1360616795200990525488463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7256622907738616135938469 1360616795200990525488463)
        ·
          refine ⟨2040925192801485788232695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360616795200990525488463 2040925192801485788232695)
          ·
            refine ⟨3061387789202228682349043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040925192801485788232695 3061387789202228682349043)
            ·
              refine ⟨4592081683803343023523565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061387789202228682349043 4592081683803343023523565)
              ·
                refine ⟨1722030631426253633821337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4592081683803343023523565 1722030631426253633821337)
                ·
                  refine ⟨1291522973569690225366003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1722030631426253633821337 1291522973569690225366003)
                  ·
                    refine ⟨1937284460354535338049005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1291522973569690225366003 1937284460354535338049005)
                    ·
                      refine ⟨726481672632950751768377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1937284460354535338049005 726481672632950751768377)
                      ·
                        rfl

theorem cell23_1414818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1414818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414818 prefixEnd_1414818 := by exact prefixLift 1414818
  have htrace : WordTrace (prefixWord ++ tailWord_1414818) baseStart_1414818 baseEnd_1414818 := by
    simpa [prefixWord, tailWord_1414818, baseEnd_1414818] using wordTrace_append hprefix tailTrace_1414818
  have hstable : (prefixWord ++ tailWord_1414818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414818).length < 2 ^ (prefixWord ++ tailWord_1414818).sum := by decide
  have hdescent : baseEnd_1414818 < baseStart_1414818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414847 : List Nat := [1, 1, 2, 2, 2, 3, 2, 5, 5]
def baseStart_1414847 : Nat := 118140960795 + 1414847 * 2 ^ 59
def prefixEnd_1414847 : Nat := 4983230072969 + 3 ^ 40 * 1414847 * 2
def baseEnd_1414847 : Nat := 80721840396881237589527

theorem tailTrace_1414847 : CollatzResearch.WordTrace tailWord_1414847 prefixEnd_1414847 80721840396881237589527 := by
  unfold tailWord_1414847
  simp only [CollatzResearch.WordTrace]
  refine ⟨51603709505258430475034795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34402473003505620316689863 51603709505258430475034795)
  ·
    refine ⟨77405564257887645712552193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51603709505258430475034795 77405564257887645712552193)
    ·
      refine ⟨58054173193415734284414145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77405564257887645712552193 58054173193415734284414145)
      ·
        refine ⟨43540629895061800713310609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58054173193415734284414145 43540629895061800713310609)
        ·
          refine ⟨32655472421296350534982957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43540629895061800713310609 32655472421296350534982957)
          ·
            refine ⟨12245802157986131450618609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32655472421296350534982957 12245802157986131450618609)
            ·
              refine ⟨9184351618489598587963957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12245802157986131450618609 9184351618489598587963957)
              ·
                refine ⟨861032964233399867621621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9184351618489598587963957 861032964233399867621621)
                ·
                  refine ⟨80721840396881237589527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 861032964233399867621621 80721840396881237589527)
                  ·
                    rfl

theorem cell23_1414847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 5].length) (baseStart_1414847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414847 prefixEnd_1414847 := by exact prefixLift 1414847
  have htrace : WordTrace (prefixWord ++ tailWord_1414847) baseStart_1414847 baseEnd_1414847 := by
    simpa [prefixWord, tailWord_1414847, baseEnd_1414847] using wordTrace_append hprefix tailTrace_1414847
  have hstable : (prefixWord ++ tailWord_1414847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414847).length < 2 ^ (prefixWord ++ tailWord_1414847).sum := by decide
  have hdescent : baseEnd_1414847 < baseStart_1414847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414858 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2]
def baseStart_1414858 : Nat := 118140960795 + 1414858 * 2 ^ 59
def prefixEnd_1414858 : Nat := 4983230072969 + 3 ^ 40 * 1414858 * 2
def baseEnd_1414858 : Nat := 726502211859130595268193

theorem tailTrace_1414858 : CollatzResearch.WordTrace tailWord_1414858 prefixEnd_1414858 726502211859130595268193 := by
  unfold tailWord_1414858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12901027677054644838421307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34402740472145719569123485 12901027677054644838421307)
  ·
    refine ⟨19351541515581967257631961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12901027677054644838421307 19351541515581967257631961)
    ·
      refine ⟨14513656136686475443223971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19351541515581967257631961 14513656136686475443223971)
      ·
        refine ⟨21770484205029713164835957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14513656136686475443223971 21770484205029713164835957)
        ·
          refine ⟨2040982894221535609203371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21770484205029713164835957 2040982894221535609203371)
          ·
            refine ⟨3061474341332303413805057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040982894221535609203371 3061474341332303413805057)
            ·
              refine ⟨2296105755999227560353793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3061474341332303413805057 2296105755999227560353793)
              ·
                refine ⟨1722079316999420670265345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296105755999227560353793 1722079316999420670265345)
                ·
                  refine ⟨1291559487749565502699009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1722079316999420670265345 1291559487749565502699009)
                  ·
                    refine ⟨968669615812174127024257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1291559487749565502699009 968669615812174127024257)
                    ·
                      refine ⟨726502211859130595268193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968669615812174127024257 726502211859130595268193)
                      ·
                        rfl

theorem cell23_1414858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_1414858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414858 prefixEnd_1414858 := by exact prefixLift 1414858
  have htrace : WordTrace (prefixWord ++ tailWord_1414858) baseStart_1414858 baseEnd_1414858 := by
    simpa [prefixWord, tailWord_1414858, baseEnd_1414858] using wordTrace_append hprefix tailTrace_1414858
  have hstable : (prefixWord ++ tailWord_1414858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414858).length < 2 ^ (prefixWord ++ tailWord_1414858).sum := by decide
  have hdescent : baseEnd_1414858 < baseStart_1414858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414897 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_1414897 : Nat := 118140960795 + 1414897 * 2 ^ 59
def prefixEnd_1414897 : Nat := 4983230072969 + 3 ^ 40 * 1414897 * 2
def baseEnd_1414897 : Nat := 726522237604655942680513

theorem tailTrace_1414897 : CollatzResearch.WordTrace tailWord_1414897 prefixEnd_1414897 726522237604655942680513 := by
  unfold tailWord_1414897
  simp only [CollatzResearch.WordTrace]
  refine ⟨51605533155077289014354945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34403688770051526009569963 51605533155077289014354945)
  ·
    refine ⟨38704149866307966760766209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51605533155077289014354945 38704149866307966760766209)
    ·
      refine ⟨29028112399730975070574657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38704149866307966760766209 29028112399730975070574657)
      ·
        refine ⟨21771084299798231302930993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29028112399730975070574657 21771084299798231302930993)
        ·
          refine ⟨16328313224848673477198245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21771084299798231302930993 16328313224848673477198245)
          ·
            refine ⟨3061558729659126276974671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16328313224848673477198245 3061558729659126276974671)
            ·
              refine ⟨4592338094488689415462007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061558729659126276974671 4592338094488689415462007)
              ·
                refine ⟨6888507141733034123193011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4592338094488689415462007 6888507141733034123193011)
                ·
                  refine ⟨10332760712599551184789517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6888507141733034123193011 10332760712599551184789517)
                  ·
                    refine ⟨3874785267224831694296069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10332760712599551184789517 3874785267224831694296069)
                    ·
                      refine ⟨726522237604655942680513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3874785267224831694296069 726522237604655942680513)
                      ·
                        rfl

theorem cell23_1414897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_1414897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414897 prefixEnd_1414897 := by exact prefixLift 1414897
  have htrace : WordTrace (prefixWord ++ tailWord_1414897) baseStart_1414897 baseEnd_1414897 := by
    simpa [prefixWord, tailWord_1414897, baseEnd_1414897] using wordTrace_append hprefix tailTrace_1414897
  have hstable : (prefixWord ++ tailWord_1414897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414897).length < 2 ^ (prefixWord ++ tailWord_1414897).sum := by decide
  have hdescent : baseEnd_1414897 < baseStart_1414897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414914 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1414914 : Nat := 118140960795 + 1414914 * 2 ^ 59
def prefixEnd_1414914 : Nat := 4983230072969 + 3 ^ 40 * 1414914 * 2
def baseEnd_1414914 : Nat := 726530966775782376167935

theorem tailTrace_1414914 : CollatzResearch.WordTrace tailWord_1414914 prefixEnd_1414914 726530966775782376167935 := by
  unfold tailWord_1414914
  simp only [CollatzResearch.WordTrace]
  refine ⟨12901538299003925229430949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34404102130677133945149197 12901538299003925229430949)
  ·
    refine ⟨2419038431063235980518303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12901538299003925229430949 2419038431063235980518303)
    ·
      refine ⟨3628557646594853970777455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419038431063235980518303 3628557646594853970777455)
      ·
        refine ⟨5442836469892280956166183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3628557646594853970777455 5442836469892280956166183)
        ·
          refine ⟨8164254704838421434249275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5442836469892280956166183 8164254704838421434249275)
          ·
            refine ⟨12246382057257632151373913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8164254704838421434249275 12246382057257632151373913)
            ·
              refine ⟨9184786542943224113530435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12246382057257632151373913 9184786542943224113530435)
              ·
                refine ⟨13777179814414836170295653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9184786542943224113530435 13777179814414836170295653)
                ·
                  refine ⟨2583221215202781781930435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13777179814414836170295653 2583221215202781781930435)
                  ·
                    refine ⟨3874831822804172672895653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2583221215202781781930435 3874831822804172672895653)
                    ·
                      refine ⟨726530966775782376167935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3874831822804172672895653 726530966775782376167935)
                      ·
                        rfl

theorem cell23_1414914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1414914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414914 prefixEnd_1414914 := by exact prefixLift 1414914
  have htrace : WordTrace (prefixWord ++ tailWord_1414914) baseStart_1414914 baseEnd_1414914 := by
    simpa [prefixWord, tailWord_1414914, baseEnd_1414914] using wordTrace_append hprefix tailTrace_1414914
  have hstable : (prefixWord ++ tailWord_1414914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414914).length < 2 ^ (prefixWord ++ tailWord_1414914).sum := by decide
  have hdescent : baseEnd_1414914 < baseStart_1414914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1414988 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 6]
def baseStart_1414988 : Nat := 118140960795 + 1414988 * 2 ^ 59
def prefixEnd_1414988 : Nat := 4983230072969 + 3 ^ 40 * 1414988 * 2
def baseEnd_1414988 : Nat := 80729884927135009626955

theorem tailTrace_1414988 : CollatzResearch.WordTrace tailWord_1414988 prefixEnd_1414988 80729884927135009626955 := by
  unfold tailWord_1414988
  simp only [CollatzResearch.WordTrace]
  refine ⟨25804426098873805777958809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34405901465165074370611745 25804426098873805777958809)
  ·
    refine ⟨19353319574155354333469107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25804426098873805777958809 19353319574155354333469107)
    ·
      refine ⟨29029979361233031500203661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19353319574155354333469107 29029979361233031500203661)
      ·
        refine ⟨10886242260462386812576373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29029979361233031500203661 10886242260462386812576373)
        ·
          refine ⟨1020585211918348763679035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10886242260462386812576373 1020585211918348763679035)
          ·
            refine ⟨1530877817877523145518553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020585211918348763679035 1530877817877523145518553)
            ·
              refine ⟨1148158363408142359138915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530877817877523145518553 1148158363408142359138915)
              ·
                refine ⟨1722237545112213538708373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148158363408142359138915 1722237545112213538708373)
                ·
                  refine ⟨80729884927135009626955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1722237545112213538708373 80729884927135009626955)
                  ·
                    rfl

theorem cell23_1414988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_1414988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1414988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1414988 prefixEnd_1414988 := by exact prefixLift 1414988
  have htrace : WordTrace (prefixWord ++ tailWord_1414988) baseStart_1414988 baseEnd_1414988 := by
    simpa [prefixWord, tailWord_1414988, baseEnd_1414988] using wordTrace_append hprefix tailTrace_1414988
  have hstable : (prefixWord ++ tailWord_1414988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1414988).length < 2 ^ (prefixWord ++ tailWord_1414988).sum := by decide
  have hdescent : baseEnd_1414988 < baseStart_1414988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1414988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415087 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 4, 6]
def baseStart_1415087 : Nat := 118140960795 + 1415087 * 2 ^ 59
def prefixEnd_1415087 : Nat := 4983230072969 + 3 ^ 40 * 1415087 * 2
def baseEnd_1415087 : Nat := 242206599643003399768213

theorem tailTrace_1415087 : CollatzResearch.WordTrace tailWord_1415087 prefixEnd_1415087 242206599643003399768213 := by
  unfold tailWord_1415087
  simp only [CollatzResearch.WordTrace]
  refine ⟨51612463024388951463771515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34408308682925967642514343 51612463024388951463771515)
  ·
    refine ⟨77418694536583427195657273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51612463024388951463771515 77418694536583427195657273)
    ·
      refine ⟨58064020902437570396742955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77418694536583427195657273 58064020902437570396742955)
      ·
        refine ⟨87096031353656355595114433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58064020902437570396742955 87096031353656355595114433)
        ·
          refine ⟨65322023515242266696335825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87096031353656355595114433 65322023515242266696335825)
          ·
            refine ⟨48991517636431700022251869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65322023515242266696335825 48991517636431700022251869)
            ·
              refine ⟨18371819113661887508344451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48991517636431700022251869 18371819113661887508344451)
              ·
                refine ⟨27557728670492831262516677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18371819113661887508344451 27557728670492831262516677)
                ·
                  refine ⟨5167074125717405861721877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27557728670492831262516677 5167074125717405861721877)
                  ·
                    refine ⟨242206599643003399768213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5167074125717405861721877 242206599643003399768213)
                    ·
                      rfl

theorem cell23_1415087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 6].length) (baseStart_1415087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415087 prefixEnd_1415087 := by exact prefixLift 1415087
  have htrace : WordTrace (prefixWord ++ tailWord_1415087) baseStart_1415087 baseEnd_1415087 := by
    simpa [prefixWord, tailWord_1415087, baseEnd_1415087] using wordTrace_append hprefix tailTrace_1415087
  have hstable : (prefixWord ++ tailWord_1415087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415087).length < 2 ^ (prefixWord ++ tailWord_1415087).sum := by decide
  have hdescent : baseEnd_1415087 < baseStart_1415087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415114 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_1415114 : Nat := 118140960795 + 1415114 * 2 ^ 59
def prefixEnd_1415114 : Nat := 4983230072969 + 3 ^ 40 * 1415114 * 2
def baseEnd_1415114 : Nat := 726633662906681593667015

theorem tailTrace_1415114 : CollatzResearch.WordTrace tailWord_1415114 prefixEnd_1415114 726633662906681593667015 := by
  unfold tailWord_1415114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12903361948822783768751099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34408965196860756716669597 12903361948822783768751099)
  ·
    refine ⟨19355042923234175653126649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12903361948822783768751099 19355042923234175653126649)
    ·
      refine ⟨14516282192425631739844987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19355042923234175653126649 14516282192425631739844987)
      ·
        refine ⟨21774423288638447609767481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14516282192425631739844987 21774423288638447609767481)
        ·
          refine ⟨16330817466478835707325611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21774423288638447609767481 16330817466478835707325611)
          ·
            refine ⟨24496226199718253560988417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16330817466478835707325611 24496226199718253560988417)
            ·
              refine ⟨18372169649788690170741313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24496226199718253560988417 18372169649788690170741313)
              ·
                refine ⟨13779127237341517628055985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18372169649788690170741313 13779127237341517628055985)
                ·
                  refine ⟨10334345428006138221041989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13779127237341517628055985 10334345428006138221041989)
                  ·
                    refine ⟨1937689767751150916445373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10334345428006138221041989 1937689767751150916445373)
                    ·
                      refine ⟨726633662906681593667015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1937689767751150916445373 726633662906681593667015)
                      ·
                        rfl

theorem cell23_1415114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_1415114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415114 prefixEnd_1415114 := by exact prefixLift 1415114
  have htrace : WordTrace (prefixWord ++ tailWord_1415114) baseStart_1415114 baseEnd_1415114 := by
    simpa [prefixWord, tailWord_1415114, baseEnd_1415114] using wordTrace_append hprefix tailTrace_1415114
  have hstable : (prefixWord ++ tailWord_1415114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415114).length < 2 ^ (prefixWord ++ tailWord_1415114).sum := by decide
  have hdescent : baseEnd_1415114 < baseStart_1415114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415164 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 4, 5]
def baseStart_1415164 : Nat := 118140960795 + 1415164 * 2 ^ 59
def prefixEnd_1415164 : Nat := 4983230072969 + 3 ^ 40 * 1415164 * 2
def baseEnd_1415164 : Nat := 242219778979802132680595

theorem tailTrace_1415164 : CollatzResearch.WordTrace tailWord_1415164 prefixEnd_1415164 242219778979802132680595 := by
  unfold tailWord_1415164
  simp only [CollatzResearch.WordTrace]
  refine ⟨25807635722554996807162273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34410180963406662409549697 25807635722554996807162273)
  ·
    refine ⟨19355726791916247605371705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25807635722554996807162273 19355726791916247605371705)
    ·
      refine ⟨14516795093937185704028779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19355726791916247605371705 14516795093937185704028779)
      ·
        refine ⟨21775192640905778556043169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14516795093937185704028779 21775192640905778556043169)
        ·
          refine ⟨16331394480679333917032377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21775192640905778556043169 16331394480679333917032377)
          ·
            refine ⟨12248545860509500437774283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16331394480679333917032377 12248545860509500437774283)
            ·
              refine ⟨18372818790764250656661425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12248545860509500437774283 18372818790764250656661425)
              ·
                refine ⟨13779614093073187992496069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18372818790764250656661425 13779614093073187992496069)
                ·
                  refine ⟨2583677642451222748593013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13779614093073187992496069 2583677642451222748593013)
                  ·
                    refine ⟨242219778979802132680595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2583677642451222748593013 242219778979802132680595)
                    ·
                      rfl

theorem cell23_1415164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_1415164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415164 prefixEnd_1415164 := by exact prefixLift 1415164
  have htrace : WordTrace (prefixWord ++ tailWord_1415164) baseStart_1415164 baseEnd_1415164 := by
    simpa [prefixWord, tailWord_1415164, baseEnd_1415164] using wordTrace_append hprefix tailTrace_1415164
  have hstable : (prefixWord ++ tailWord_1415164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415164).length < 2 ^ (prefixWord ++ tailWord_1415164).sum := by decide
  have hdescent : baseEnd_1415164 < baseStart_1415164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415184 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 4]
def baseStart_1415184 : Nat := 118140960795 + 1415184 * 2 ^ 59
def prefixEnd_1415184 : Nat := 4983230072969 + 3 ^ 40 * 1415184 * 2
def baseEnd_1415184 : Nat := 726669606552496319791693

theorem tailTrace_1415184 : CollatzResearch.WordTrace tailWord_1415184 prefixEnd_1415184 726669606552496319791693 := by
  unfold tailWord_1415184
  simp only [CollatzResearch.WordTrace]
  refine ⟨25808000452518768515026303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34410667270025024686701737 25808000452518768515026303)
  ·
    refine ⟨38712000678778152772539455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25808000452518768515026303 38712000678778152772539455)
    ·
      refine ⟨58068001018167229158809183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38712000678778152772539455 58068001018167229158809183)
      ·
        refine ⟨87102001527250843738213775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58068001018167229158809183 87102001527250843738213775)
        ·
          refine ⟨130653002290876265607320663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87102001527250843738213775 130653002290876265607320663)
          ·
            refine ⟨195979503436314398410980995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130653002290876265607320663 195979503436314398410980995)
            ·
              refine ⟨293969255154471597616471493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 195979503436314398410980995 293969255154471597616471493)
              ·
                refine ⟨55119235341463424553088405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 293969255154471597616471493 55119235341463424553088405)
                ·
                  refine ⟨2583714156631098025926019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55119235341463424553088405 2583714156631098025926019)
                  ·
                    refine ⟨3875571234946647038889029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2583714156631098025926019 3875571234946647038889029)
                    ·
                      refine ⟨726669606552496319791693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3875571234946647038889029 726669606552496319791693)
                      ·
                        rfl

theorem cell23_1415184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 4].length) (baseStart_1415184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415184 prefixEnd_1415184 := by exact prefixLift 1415184
  have htrace : WordTrace (prefixWord ++ tailWord_1415184) baseStart_1415184 baseEnd_1415184 := by
    simpa [prefixWord, tailWord_1415184, baseEnd_1415184] using wordTrace_append hprefix tailTrace_1415184
  have hstable : (prefixWord ++ tailWord_1415184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415184).length < 2 ^ (prefixWord ++ tailWord_1415184).sum := by decide
  have hdescent : baseEnd_1415184 < baseStart_1415184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415218 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2]
def baseStart_1415218 : Nat := 118140960795 + 1415218 * 2 ^ 59
def prefixEnd_1415218 : Nat := 4983230072969 + 3 ^ 40 * 1415218 * 2
def baseEnd_1415218 : Nat := 726687064894749186766537

theorem tailTrace_1415218 : CollatzResearch.WordTrace tailWord_1415218 prefixEnd_1415218 726687064894749186766537 := by
  unfold tailWord_1415218
  simp only [CollatzResearch.WordTrace]
  refine ⟨12904310246728590209197577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34411493991276240557860205 12904310246728590209197577)
  ·
    refine ⟨9678232685046442656898183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12904310246728590209197577 9678232685046442656898183)
    ·
      refine ⟨14517349027569663985347275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9678232685046442656898183 14517349027569663985347275)
      ·
        refine ⟨21776023541354495978020913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14517349027569663985347275 21776023541354495978020913)
        ·
          refine ⟨16332017656015871983515685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21776023541354495978020913 16332017656015871983515685)
          ·
            refine ⟨3062253310502975996909191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16332017656015871983515685 3062253310502975996909191)
            ·
              refine ⟨4593379965754463995363787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062253310502975996909191 4593379965754463995363787)
              ·
                refine ⟨6890069948631695993045681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593379965754463995363787 6890069948631695993045681)
                ·
                  refine ⟨5167552461473771994784261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6890069948631695993045681 5167552461473771994784261)
                  ·
                    refine ⟨968916086526332249022049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5167552461473771994784261 968916086526332249022049)
                    ·
                      refine ⟨726687064894749186766537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968916086526332249022049 726687064894749186766537)
                      ·
                        rfl

theorem cell23_1415218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_1415218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415218 prefixEnd_1415218 := by exact prefixLift 1415218
  have htrace : WordTrace (prefixWord ++ tailWord_1415218) baseStart_1415218 baseEnd_1415218 := by
    simpa [prefixWord, tailWord_1415218, baseEnd_1415218] using wordTrace_append hprefix tailTrace_1415218
  have hstable : (prefixWord ++ tailWord_1415218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415218).length < 2 ^ (prefixWord ++ tailWord_1415218).sum := by decide
  have hdescent : baseEnd_1415218 < baseStart_1415218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415221 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_1415221 : Nat := 118140960795 + 1415221 * 2 ^ 59
def prefixEnd_1415221 : Nat := 4983230072969 + 3 ^ 40 * 1415221 * 2
def baseEnd_1415221 : Nat := 726688605336712675029023

theorem tailTrace_1415221 : CollatzResearch.WordTrace tailWord_1415221 prefixEnd_1415221 726688605336712675029023 := by
  unfold tailWord_1415221
  simp only [CollatzResearch.WordTrace]
  refine ⟨51617350405903492349149517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34411566937268994899433011 51617350405903492349149517)
  ·
    refine ⟨19356506402213809630931069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51617350405903492349149517 19356506402213809630931069)
    ·
      refine ⟨7258689900830178611599151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19356506402213809630931069 7258689900830178611599151)
      ·
        refine ⟨10888034851245267917398727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7258689900830178611599151 10888034851245267917398727)
        ·
          refine ⟨16332052276867901876098091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10888034851245267917398727 16332052276867901876098091)
          ·
            refine ⟨24498078415301852814147137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16332052276867901876098091 24498078415301852814147137)
            ·
              refine ⟨18373558811476389610610353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24498078415301852814147137 18373558811476389610610353)
              ·
                refine ⟨13780169108607292207957765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18373558811476389610610353 13780169108607292207957765)
                ·
                  refine ⟨2583781707863867288992081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13780169108607292207957765 2583781707863867288992081)
                  ·
                    refine ⟨1937836280897900466744061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2583781707863867288992081 1937836280897900466744061)
                    ·
                      refine ⟨726688605336712675029023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1937836280897900466744061 726688605336712675029023)
                      ·
                        rfl

theorem cell23_1415221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_1415221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415221 prefixEnd_1415221 := by exact prefixLift 1415221
  have htrace : WordTrace (prefixWord ++ tailWord_1415221) baseStart_1415221 baseEnd_1415221 := by
    simpa [prefixWord, tailWord_1415221, baseEnd_1415221] using wordTrace_append hprefix tailTrace_1415221
  have hstable : (prefixWord ++ tailWord_1415221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415221).length < 2 ^ (prefixWord ++ tailWord_1415221).sum := by decide
  have hdescent : baseEnd_1415221 < baseStart_1415221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415268 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_1415268 : Nat := 118140960795 + 1415268 * 2 ^ 59
def prefixEnd_1415268 : Nat := 4983230072969 + 3 ^ 40 * 1415268 * 2
def baseEnd_1415268 : Nat := 726712738927473991141307

theorem tailTrace_1415268 : CollatzResearch.WordTrace tailWord_1415268 prefixEnd_1415268 726712738927473991141307 := by
  unfold tailWord_1415268
  simp only [CollatzResearch.WordTrace]
  refine ⟨25809532318366609688055229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34412709757822146250740305 25809532318366609688055229)
  ·
    refine ⟨9678574619387478633020711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25809532318366609688055229 9678574619387478633020711)
    ·
      refine ⟨14517861929081217949531067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9678574619387478633020711 14517861929081217949531067)
      ·
        refine ⟨21776792893621826924296601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14517861929081217949531067 21776792893621826924296601)
        ·
          refine ⟨16332594670216370193222451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21776792893621826924296601 16332594670216370193222451)
          ·
            refine ⟨24498892005324555289833677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16332594670216370193222451 24498892005324555289833677)
            ·
              refine ⟨9187084501996708233687629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24498892005324555289833677 9187084501996708233687629)
              ·
                refine ⟨3445156688248765587632861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9187084501996708233687629 3445156688248765587632861)
                ·
                  refine ⟨1291933758093287095362323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3445156688248765587632861 1291933758093287095362323)
                  ·
                    refine ⟨1937900637139930643043485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1291933758093287095362323 1937900637139930643043485)
                    ·
                      refine ⟨726712738927473991141307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1937900637139930643043485 726712738927473991141307)
                      ·
                        rfl

theorem cell23_1415268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_1415268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415268 prefixEnd_1415268 := by exact prefixLift 1415268
  have htrace : WordTrace (prefixWord ++ tailWord_1415268) baseStart_1415268 baseEnd_1415268 := by
    simpa [prefixWord, tailWord_1415268, baseEnd_1415268] using wordTrace_append hprefix tailTrace_1415268
  have hstable : (prefixWord ++ tailWord_1415268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415268).length < 2 ^ (prefixWord ++ tailWord_1415268).sum := by decide
  have hdescent : baseEnd_1415268 < baseStart_1415268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415278 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_1415278 : Nat := 118140960795 + 1415278 * 2 ^ 59
def prefixEnd_1415278 : Nat := 4983230072969 + 3 ^ 40 * 1415278 * 2
def baseEnd_1415278 : Nat := 726717873734018952016261

theorem tailTrace_1415278 : CollatzResearch.WordTrace tailWord_1415278 prefixEnd_1415278 726717873734018952016261 := by
  unfold tailWord_1415278
  simp only [CollatzResearch.WordTrace]
  refine ⟨6452428670837123885496811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34412952911131327389316325 6452428670837123885496811)
  ·
    refine ⟨9678643006255685828245217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6452428670837123885496811 9678643006255685828245217)
    ·
      refine ⟨7258982254691764371183913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9678643006255685828245217 7258982254691764371183913)
      ·
        refine ⟨5444236691018823278387935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7258982254691764371183913 5444236691018823278387935)
        ·
          refine ⟨8166355036528234917581903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5444236691018823278387935 8166355036528234917581903)
          ·
            refine ⟨12249532554792352376372855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8166355036528234917581903 12249532554792352376372855)
            ·
              refine ⟨18374298832188528564559283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12249532554792352376372855 18374298832188528564559283)
              ·
                refine ⟨27561448248282792846838925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18374298832188528564559283 27561448248282792846838925)
                ·
                  refine ⟨10335543093106047317564597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27561448248282792846838925 10335543093106047317564597)
                  ·
                    refine ⟨968957164978691936021681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10335543093106047317564597 968957164978691936021681)
                    ·
                      refine ⟨726717873734018952016261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 968957164978691936021681 726717873734018952016261)
                      ·
                        rfl

theorem cell23_1415278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_1415278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415278 prefixEnd_1415278 := by exact prefixLift 1415278
  have htrace : WordTrace (prefixWord ++ tailWord_1415278) baseStart_1415278 baseEnd_1415278 := by
    simpa [prefixWord, tailWord_1415278, baseEnd_1415278] using wordTrace_append hprefix tailTrace_1415278
  have hstable : (prefixWord ++ tailWord_1415278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415278).length < 2 ^ (prefixWord ++ tailWord_1415278).sum := by decide
  have hdescent : baseEnd_1415278 < baseStart_1415278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415319 : List Nat := [1, 1, 3, 3, 4, 1, 3, 2, 1, 1, 3]
def baseStart_1415319 : Nat := 118140960795 + 1415319 * 2 ^ 59
def prefixEnd_1415319 : Nat := 4983230072969 + 3 ^ 40 * 1415319 * 2
def baseEnd_1415319 : Nat := 726738926440853291603573

theorem tailTrace_1415319 : CollatzResearch.WordTrace tailWord_1415319 prefixEnd_1415319 726738926440853291603573 := by
  unfold tailWord_1415319
  simp only [CollatzResearch.WordTrace]
  refine ⟨51620924759548455086217011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34413949839698970057478007 51620924759548455086217011)
  ·
    refine ⟨77431387139322682629325517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51620924759548455086217011 77431387139322682629325517)
    ·
      refine ⟨29036770177246005985997069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77431387139322682629325517 29036770177246005985997069)
      ·
        refine ⟨10888788816467252244748901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29036770177246005985997069 10888788816467252244748901)
        ·
          refine ⟨2041647903087609795890419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10888788816467252244748901 2041647903087609795890419)
          ·
            refine ⟨3062471854631414693835629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041647903087609795890419 3062471854631414693835629)
            ·
              refine ⟨1148426945486780510188361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3062471854631414693835629 1148426945486780510188361)
              ·
                refine ⟨861320209115085382641271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148426945486780510188361 861320209115085382641271)
                ·
                  refine ⟨1291980313672628073961907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861320209115085382641271 1291980313672628073961907)
                  ·
                    refine ⟨1937970470508942110942861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1291980313672628073961907 1937970470508942110942861)
                    ·
                      refine ⟨726738926440853291603573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1937970470508942110942861 726738926440853291603573)
                      ·
                        rfl

theorem cell23_1415319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_1415319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415319 prefixEnd_1415319 := by exact prefixLift 1415319
  have htrace : WordTrace (prefixWord ++ tailWord_1415319) baseStart_1415319 baseEnd_1415319 := by
    simpa [prefixWord, tailWord_1415319, baseEnd_1415319] using wordTrace_append hprefix tailTrace_1415319
  have hstable : (prefixWord ++ tailWord_1415319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415319).length < 2 ^ (prefixWord ++ tailWord_1415319).sum := by decide
  have hdescent : baseEnd_1415319 < baseStart_1415319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415342 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1415342 : Nat := 118140960795 + 1415342 * 2 ^ 59
def prefixEnd_1415342 : Nat := 4983230072969 + 3 ^ 40 * 1415342 * 2
def baseEnd_1415342 : Nat := 726750736495906701615967

theorem tailTrace_1415342 : CollatzResearch.WordTrace tailWord_1415342 prefixEnd_1415342 726750736495906701615967 := by
  unfold tailWord_1415342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6452720454808141251788035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34414509092310086676202853 6452720454808141251788035)
  ·
    refine ⟨9679080682212211877682053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6452720454808141251788035 9679080682212211877682053)
    ·
      refine ⟨1814827627914789727065385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9679080682212211877682053 1814827627914789727065385)
      ·
        refine ⟨1361120720936092295299039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1814827627914789727065385 1361120720936092295299039)
        ·
          refine ⟨2041681081404138442948559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361120720936092295299039 2041681081404138442948559)
          ·
            refine ⟨3062521622106207664422839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041681081404138442948559 3062521622106207664422839)
            ·
              refine ⟨4593782433159311496634259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062521622106207664422839 4593782433159311496634259)
              ·
                refine ⟨6890673649738967244951389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593782433159311496634259 6890673649738967244951389)
                ·
                  refine ⟨2584002618652112716856771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6890673649738967244951389 2584002618652112716856771)
                  ·
                    refine ⟨3876003927978169075285157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2584002618652112716856771 3876003927978169075285157)
                    ·
                      refine ⟨726750736495906701615967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3876003927978169075285157 726750736495906701615967)
                      ·
                        rfl

theorem cell23_1415342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1415342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415342 prefixEnd_1415342 := by exact prefixLift 1415342
  have htrace : WordTrace (prefixWord ++ tailWord_1415342) baseStart_1415342 baseEnd_1415342 := by
    simpa [prefixWord, tailWord_1415342, baseEnd_1415342] using wordTrace_append hprefix tailTrace_1415342
  have hstable : (prefixWord ++ tailWord_1415342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415342).length < 2 ^ (prefixWord ++ tailWord_1415342).sum := by decide
  have hdescent : baseEnd_1415342 < baseStart_1415342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415345 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1415345 : Nat := 118140960795 + 1415345 * 2 ^ 59
def prefixEnd_1415345 : Nat := 4983230072969 + 3 ^ 40 * 1415345 * 2
def baseEnd_1415345 : Nat := 726752276937870189878453

theorem tailTrace_1415345 : CollatzResearch.WordTrace tailWord_1415345 prefixEnd_1415345 726752276937870189878453 := by
  unfold tailWord_1415345
  simp only [CollatzResearch.WordTrace]
  refine ⟨51621873057454261526663489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34414582038302841017775659 51621873057454261526663489)
  ·
    refine ⟨38716404793090696144997617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51621873057454261526663489 38716404793090696144997617)
    ·
      refine ⟨29037303594818022108748213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38716404793090696144997617 29037303594818022108748213)
      ·
        refine ⟨2722247212014189572695145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29037303594818022108748213 2722247212014189572695145)
        ·
          refine ⟨2041685409010642179521359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2722247212014189572695145 2041685409010642179521359)
          ·
            refine ⟨3062528113515963269282039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041685409010642179521359 3062528113515963269282039)
            ·
              refine ⟨4593792170273944903923059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062528113515963269282039 4593792170273944903923059)
              ·
                refine ⟨6890688255410917355884589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4593792170273944903923059 6890688255410917355884589)
                ·
                  refine ⟨2584008095779094008456721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6890688255410917355884589 2584008095779094008456721)
                  ·
                    refine ⟨1938006071834320506342541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2584008095779094008456721 1938006071834320506342541)
                    ·
                      refine ⟨726752276937870189878453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1938006071834320506342541 726752276937870189878453)
                      ·
                        rfl

theorem cell23_1415345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1415345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415345 prefixEnd_1415345 := by exact prefixLift 1415345
  have htrace : WordTrace (prefixWord ++ tailWord_1415345) baseStart_1415345 baseEnd_1415345 := by
    simpa [prefixWord, tailWord_1415345, baseEnd_1415345] using wordTrace_append hprefix tailTrace_1415345
  have hstable : (prefixWord ++ tailWord_1415345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415345).length < 2 ^ (prefixWord ++ tailWord_1415345).sum := by decide
  have hdescent : baseEnd_1415345 < baseStart_1415345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415362 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1415362 : Nat := 118140960795 + 1415362 * 2 ^ 59
def prefixEnd_1415362 : Nat := 4983230072969 + 3 ^ 40 * 1415362 * 2
def baseEnd_1415362 : Nat := 726761006108996623365875

theorem tailTrace_1415362 : CollatzResearch.WordTrace tailWord_1415362 prefixEnd_1415362 726761006108996623365875 := by
  unfold tailWord_1415362
  simp only [CollatzResearch.WordTrace]
  refine ⟨12905623274598168357508085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34414995398928448953354893 12905623274598168357508085)
  ·
    refine ⟨1209902181993578283516383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12905623274598168357508085 1209902181993578283516383)
    ·
      refine ⟨1814853272990367425274575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1209902181993578283516383 1814853272990367425274575)
      ·
        refine ⟨2722279909485551137911863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814853272990367425274575 2722279909485551137911863)
        ·
          refine ⟨4083419864228326706867795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722279909485551137911863 4083419864228326706867795)
          ·
            refine ⟨6125129796342490060301693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4083419864228326706867795 6125129796342490060301693)
            ·
              refine ⟨2296923673628433772613135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6125129796342490060301693 2296923673628433772613135)
              ·
                refine ⟨3445385510442650658919703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2296923673628433772613135 3445385510442650658919703)
                ·
                  refine ⟨5168078265663975988379555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3445385510442650658919703 5168078265663975988379555)
                  ·
                    refine ⟨7752117398495963982569333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5168078265663975988379555 7752117398495963982569333)
                    ·
                      refine ⟨726761006108996623365875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7752117398495963982569333 726761006108996623365875)
                      ·
                        rfl

theorem cell23_1415362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1415362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415362 prefixEnd_1415362 := by exact prefixLift 1415362
  have htrace : WordTrace (prefixWord ++ tailWord_1415362) baseStart_1415362 baseEnd_1415362 := by
    simpa [prefixWord, tailWord_1415362, baseEnd_1415362] using wordTrace_append hprefix tailTrace_1415362
  have hstable : (prefixWord ++ tailWord_1415362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415362).length < 2 ^ (prefixWord ++ tailWord_1415362).sum := by decide
  have hdescent : baseEnd_1415362 < baseStart_1415362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415375 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 2, 1, 3]
def baseStart_1415375 : Nat := 118140960795 + 1415375 * 2 ^ 59
def prefixEnd_1415375 : Nat := 4983230072969 + 3 ^ 40 * 1415375 * 2
def baseEnd_1415375 : Nat := 726767681357505072503315

theorem tailTrace_1415375 : CollatzResearch.WordTrace tailWord_1415375 prefixEnd_1415375 726767681357505072503315 := by
  unfold tailWord_1415375
  simp only [CollatzResearch.WordTrace]
  refine ⟨51622967247345576650255579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34415311498230384433503719 51622967247345576650255579)
  ·
    refine ⟨77434450871018364975383369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51622967247345576650255579 77434450871018364975383369)
    ·
      refine ⟨58075838153263773731537527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77434450871018364975383369 58075838153263773731537527)
      ·
        refine ⟨87113757229895660597306291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58075838153263773731537527 87113757229895660597306291)
        ·
          refine ⟨130670635844843490895959437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87113757229895660597306291 130670635844843490895959437)
          ·
            refine ⟨49001488441816309085984789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130670635844843490895959437 49001488441816309085984789)
            ·
              refine ⟨2296944770710139488405537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49001488441816309085984789 2296944770710139488405537)
              ·
                refine ⟨1722708578032604616304153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2296944770710139488405537 1722708578032604616304153)
                ·
                  refine ⟨1292031433524453462228115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1722708578032604616304153 1292031433524453462228115)
                  ·
                    refine ⟨1938047150286680193342173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1292031433524453462228115 1938047150286680193342173)
                    ·
                      refine ⟨726767681357505072503315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1938047150286680193342173 726767681357505072503315)
                      ·
                        rfl

theorem cell23_1415375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 1, 3].length) (baseStart_1415375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415375 prefixEnd_1415375 := by exact prefixLift 1415375
  have htrace : WordTrace (prefixWord ++ tailWord_1415375) baseStart_1415375 baseEnd_1415375 := by
    simpa [prefixWord, tailWord_1415375, baseEnd_1415375] using wordTrace_append hprefix tailTrace_1415375
  have hstable : (prefixWord ++ tailWord_1415375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415375).length < 2 ^ (prefixWord ++ tailWord_1415375).sum := by decide
  have hdescent : baseEnd_1415375 < baseStart_1415375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415411 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 4]
def baseStart_1415411 : Nat := 118140960795 + 1415411 * 2 ^ 59
def prefixEnd_1415411 : Nat := 4983230072969 + 3 ^ 40 * 1415411 * 2
def baseEnd_1415411 : Nat := 726786166661066931653149

theorem tailTrace_1415411 : CollatzResearch.WordTrace tailWord_1415411 prefixEnd_1415411 726786166661066931653149 := by
  unfold tailWord_1415411
  simp only [CollatzResearch.WordTrace]
  refine ⟨51624280275215154798566087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34416186850143436532377391 51624280275215154798566087)
  ·
    refine ⟨77436420412822732197849131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51624280275215154798566087 77436420412822732197849131)
    ·
      refine ⟨116154630619234098296773697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77436420412822732197849131 116154630619234098296773697)
      ·
        refine ⟨87115972964425573722580273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116154630619234098296773697 87115972964425573722580273)
        ·
          refine ⟨65336979723319180291935205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87115972964425573722580273 65336979723319180291935205)
          ·
            refine ⟨12250683698122346304737851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65336979723319180291935205 12250683698122346304737851)
            ·
              refine ⟨18376025547183519457106777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12250683698122346304737851 18376025547183519457106777)
              ·
                refine ⟨13782019160387639592830083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18376025547183519457106777 13782019160387639592830083)
                ·
                  refine ⟨20673028740581459389245125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13782019160387639592830083 20673028740581459389245125)
                  ·
                    refine ⟨3876192888859023635483461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20673028740581459389245125 3876192888859023635483461)
                    ·
                      refine ⟨726786166661066931653149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3876192888859023635483461 726786166661066931653149)
                      ·
                        rfl

theorem cell23_1415411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 4].length) (baseStart_1415411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415411 prefixEnd_1415411 := by exact prefixLift 1415411
  have htrace : WordTrace (prefixWord ++ tailWord_1415411) baseStart_1415411 baseEnd_1415411 := by
    simpa [prefixWord, tailWord_1415411, baseEnd_1415411] using wordTrace_append hprefix tailTrace_1415411
  have hstable : (prefixWord ++ tailWord_1415411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415411).length < 2 ^ (prefixWord ++ tailWord_1415411).sum := by decide
  have hdescent : baseEnd_1415411 < baseStart_1415411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415432 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 4, 2, 2]
def baseStart_1415432 : Nat := 118140960795 + 1415432 * 2 ^ 59
def prefixEnd_1415432 : Nat := 4983230072969 + 3 ^ 40 * 1415432 * 2
def baseEnd_1415432 : Nat := 726796949754811349490553

theorem tailTrace_1415432 : CollatzResearch.WordTrace tailWord_1415432 prefixEnd_1415432 726796949754811349490553 := by
  unfold tailWord_1415432
  simp only [CollatzResearch.WordTrace]
  refine ⟨25812523104069537692540275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34416697472092716923387033 25812523104069537692540275)
  ·
    refine ⟨38718784656104306538810413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25812523104069537692540275 38718784656104306538810413)
    ·
      refine ⟨14519544246039114952053905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38718784656104306538810413 14519544246039114952053905)
      ·
        refine ⟨10889658184529336214040429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14519544246039114952053905 10889658184529336214040429)
        ·
          refine ⟨4083621819198501080265161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10889658184529336214040429 4083621819198501080265161)
          ·
            refine ⟨3062716364398875810198871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4083621819198501080265161 3062716364398875810198871)
            ·
              refine ⟨4594074546598313715298307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062716364398875810198871 4594074546598313715298307)
              ·
                refine ⟨6891111819897470572947461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4594074546598313715298307 6891111819897470572947461)
                ·
                  refine ⟨1292083466230775732427649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6891111819897470572947461 1292083466230775732427649)
                  ·
                    refine ⟨969062599673081799320737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1292083466230775732427649 969062599673081799320737)
                    ·
                      refine ⟨726796949754811349490553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 969062599673081799320737 726796949754811349490553)
                      ·
                        rfl

theorem cell23_1415432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_1415432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415432 prefixEnd_1415432 := by exact prefixLift 1415432
  have htrace : WordTrace (prefixWord ++ tailWord_1415432) baseStart_1415432 baseEnd_1415432 := by
    simpa [prefixWord, tailWord_1415432, baseEnd_1415432] using wordTrace_append hprefix tailTrace_1415432
  have hstable : (prefixWord ++ tailWord_1415432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415432).length < 2 ^ (prefixWord ++ tailWord_1415432).sum := by decide
  have hdescent : baseEnd_1415432 < baseStart_1415432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415438 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_1415438 : Nat := 118140960795 + 1415438 * 2 ^ 59
def prefixEnd_1415438 : Nat := 4983230072969 + 3 ^ 40 * 1415438 * 2
def baseEnd_1415438 : Nat := 80755558959859814001725

theorem tailTrace_1415438 : CollatzResearch.WordTrace tailWord_1415438 prefixEnd_1415438 80755558959859814001725 := by
  unfold tailWord_1415438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6453158130764667301224871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34416843364078225606532645 6453158130764667301224871)
  ·
    refine ⟨9679737196147000951837307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6453158130764667301224871 9679737196147000951837307)
    ·
      refine ⟨14519605794220501427755961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9679737196147000951837307 14519605794220501427755961)
      ·
        refine ⟨10889704345665376070816971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14519605794220501427755961 10889704345665376070816971)
        ·
          refine ⟨16334556518498064106225457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10889704345665376070816971 16334556518498064106225457)
          ·
            refine ⟨12250917388873548079669093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16334556518498064106225457 12250917388873548079669093)
            ·
              refine ⟨2297047010413790264937955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12250917388873548079669093 2297047010413790264937955)
              ·
                refine ⟨3445570515620685397406933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297047010413790264937955 3445570515620685397406933)
                ·
                  refine ⟨80755558959859814001725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3445570515620685397406933 80755558959859814001725)
                  ·
                    rfl

theorem cell23_1415438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_1415438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415438 prefixEnd_1415438 := by exact prefixLift 1415438
  have htrace : WordTrace (prefixWord ++ tailWord_1415438) baseStart_1415438 baseEnd_1415438 := by
    simpa [prefixWord, tailWord_1415438, baseEnd_1415438] using wordTrace_append hprefix tailTrace_1415438
  have hstable : (prefixWord ++ tailWord_1415438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415438).length < 2 ^ (prefixWord ++ tailWord_1415438).sum := by decide
  have hdescent : baseEnd_1415438 < baseStart_1415438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415448 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 2, 3, 3]
def baseStart_1415448 : Nat := 118140960795 + 1415448 * 2 ^ 59
def prefixEnd_1415448 : Nat := 4983230072969 + 3 ^ 40 * 1415448 * 2
def baseEnd_1415448 : Nat := 726805165445283286890479

theorem tailTrace_1415448 : CollatzResearch.WordTrace tailWord_1415448 prefixEnd_1415448 726805165445283286890479 := by
  unfold tailWord_1415448
  simp only [CollatzResearch.WordTrace]
  refine ⟨25812814888040555058831499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34417086517387406745108665 25812814888040555058831499)
  ·
    refine ⟨38719222332060832588247249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25812814888040555058831499 38719222332060832588247249)
    ·
      refine ⟨29039416749045624441185437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38719222332060832588247249 29039416749045624441185437)
      ·
        refine ⟨10889781280892109165444539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29039416749045624441185437 10889781280892109165444539)
        ·
          refine ⟨16334671921338163748166809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10889781280892109165444539 16334671921338163748166809)
          ·
            refine ⟨12251003941003622811125107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16334671921338163748166809 12251003941003622811125107)
            ·
              refine ⟨18376505911505434216687661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12251003941003622811125107 18376505911505434216687661)
              ·
                refine ⟨6891189716814537831257873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18376505911505434216687661 6891189716814537831257873)
                ·
                  refine ⟨5168392287610903373443405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6891189716814537831257873 5168392287610903373443405)
                  ·
                    refine ⟨1938147107854088765041277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5168392287610903373443405 1938147107854088765041277)
                    ·
                      refine ⟨726805165445283286890479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1938147107854088765041277 726805165445283286890479)
                      ·
                        rfl

theorem cell23_1415448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_1415448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415448 prefixEnd_1415448 := by exact prefixLift 1415448
  have htrace : WordTrace (prefixWord ++ tailWord_1415448) baseStart_1415448 baseEnd_1415448 := by
    simpa [prefixWord, tailWord_1415448, baseEnd_1415448] using wordTrace_append hprefix tailTrace_1415448
  have hstable : (prefixWord ++ tailWord_1415448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415448).length < 2 ^ (prefixWord ++ tailWord_1415448).sum := by decide
  have hdescent : baseEnd_1415448 < baseStart_1415448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415451 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 1, 7]
def baseStart_1415451 : Nat := 118140960795 + 1415451 * 2 ^ 59
def prefixEnd_1415451 : Nat := 4983230072969 + 3 ^ 40 * 1415451 * 2
def baseEnd_1415451 : Nat := 242268901962415591717655

theorem tailTrace_1415451 : CollatzResearch.WordTrace tailWord_1415451 prefixEnd_1415451 242268901962415591717655 := by
  unfold tailWord_1415451
  simp only [CollatzResearch.WordTrace]
  refine ⟨51625739195070241630022207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34417159463380161086681471 51625739195070241630022207)
  ·
    refine ⟨77438608792605362445033311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51625739195070241630022207 77438608792605362445033311)
    ·
      refine ⟨116157913188908043667549967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77438608792605362445033311 116157913188908043667549967)
      ·
        refine ⟨174236869783362065501324951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116157913188908043667549967 174236869783362065501324951)
        ·
          refine ⟨261355304675043098251987427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174236869783362065501324951 261355304675043098251987427)
          ·
            refine ⟨392032957012564647377981141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261355304675043098251987427 392032957012564647377981141)
            ·
              refine ⟨9188272429981983922921433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 392032957012564647377981141 9188272429981983922921433)
              ·
                refine ⟨6891204322486487942191075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9188272429981983922921433 6891204322486487942191075)
                ·
                  refine ⟨10336806483729731913286613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6891204322486487942191075 10336806483729731913286613)
                  ·
                    refine ⟨242268901962415591717655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10336806483729731913286613 242268901962415591717655)
                    ·
                      rfl

theorem cell23_1415451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 7].length) (baseStart_1415451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415451 prefixEnd_1415451 := by exact prefixLift 1415451
  have htrace : WordTrace (prefixWord ++ tailWord_1415451) baseStart_1415451 baseEnd_1415451 := by
    simpa [prefixWord, tailWord_1415451, baseEnd_1415451] using wordTrace_append hprefix tailTrace_1415451
  have hstable : (prefixWord ++ tailWord_1415451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415451).length < 2 ^ (prefixWord ++ tailWord_1415451).sum := by decide
  have hdescent : baseEnd_1415451 < baseStart_1415451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415489 : List Nat := [1, 2, 5, 2, 2, 1, 3, 2, 5]
def baseStart_1415489 : Nat := 118140960795 + 1415489 * 2 ^ 59
def prefixEnd_1415489 : Nat := 4983230072969 + 3 ^ 40 * 1415489 * 2
def baseEnd_1415489 : Nat := 80758468683568625164199

theorem tailTrace_1415489 : CollatzResearch.WordTrace tailWord_1415489 prefixEnd_1415489 80758468683568625164199 := by
  unfold tailWord_1415489
  simp only [CollatzResearch.WordTrace]
  refine ⟨51627125168932574119905521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34418083445955049413270347 51627125168932574119905521)
  ·
    refine ⟨38720343876699430589929141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51627125168932574119905521 38720343876699430589929141)
    ·
      refine ⟨3630032238440571617805857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38720343876699430589929141 3630032238440571617805857)
      ·
        refine ⟨2722524178830428713354393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3630032238440571617805857 2722524178830428713354393)
        ·
          refine ⟨2041893134122821535015795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2722524178830428713354393 2041893134122821535015795)
          ·
            refine ⟨3062839701184232302523693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041893134122821535015795 3062839701184232302523693)
            ·
              refine ⟨1148564887944087113446385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3062839701184232302523693 1148564887944087113446385)
              ·
                refine ⟨861423665958065335084789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148564887944087113446385 861423665958065335084789)
                ·
                  refine ⟨80758468683568625164199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 861423665958065335084789 80758468683568625164199)
                  ·
                    rfl

theorem cell23_1415489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 5].length) (baseStart_1415489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415489 prefixEnd_1415489 := by exact prefixLift 1415489
  have htrace : WordTrace (prefixWord ++ tailWord_1415489) baseStart_1415489 baseEnd_1415489 := by
    simpa [prefixWord, tailWord_1415489, baseEnd_1415489] using wordTrace_append hprefix tailTrace_1415489
  have hstable : (prefixWord ++ tailWord_1415489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415489).length < 2 ^ (prefixWord ++ tailWord_1415489).sum := by decide
  have hdescent : baseEnd_1415489 < baseStart_1415489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415522 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1415522 : Nat := 118140960795 + 1415522 * 2 ^ 59
def prefixEnd_1415522 : Nat := 4983230072969 + 3 ^ 40 * 1415522 * 2
def baseEnd_1415522 : Nat := 726843163013715997365139

theorem tailTrace_1415522 : CollatzResearch.WordTrace tailWord_1415522 prefixEnd_1415522 726843163013715997365139 := by
  unfold tailWord_1415522
  simp only [CollatzResearch.WordTrace]
  refine ⟨12907082194453255188964205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34418885851875347170571213 12907082194453255188964205)
  ·
    refine ⟨4840155822919970695861577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12907082194453255188964205 4840155822919970695861577)
    ·
      refine ⟨3630116867189978021896183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4840155822919970695861577 3630116867189978021896183)
      ·
        refine ⟨5445175300784967032844275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3630116867189978021896183 5445175300784967032844275)
        ·
          refine ⟨8167762951177450549266413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5445175300784967032844275 8167762951177450549266413)
          ·
            refine ⟨3062911106691543955974905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8167762951177450549266413 3062911106691543955974905)
            ·
              refine ⟨2297183330018657966981179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3062911106691543955974905 2297183330018657966981179)
              ·
                refine ⟨3445774995027986950471769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297183330018657966981179 3445774995027986950471769)
                ·
                  refine ⟨2584331246270990212853827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3445774995027986950471769 2584331246270990212853827)
                  ·
                    refine ⟨3876496869406485319280741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2584331246270990212853827 3876496869406485319280741)
                    ·
                      refine ⟨726843163013715997365139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3876496869406485319280741 726843163013715997365139)
                      ·
                        rfl

theorem cell23_1415522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1415522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415522 prefixEnd_1415522 := by exact prefixLift 1415522
  have htrace : WordTrace (prefixWord ++ tailWord_1415522) baseStart_1415522 baseEnd_1415522 := by
    simpa [prefixWord, tailWord_1415522, baseEnd_1415522] using wordTrace_append hprefix tailTrace_1415522
  have hstable : (prefixWord ++ tailWord_1415522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415522).length < 2 ^ (prefixWord ++ tailWord_1415522).sum := by decide
  have hdescent : baseEnd_1415522 < baseStart_1415522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415525 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 2, 2, 3]
def baseStart_1415525 : Nat := 118140960795 + 1415525 * 2 ^ 59
def prefixEnd_1415525 : Nat := 4983230072969 + 3 ^ 40 * 1415525 * 2
def baseEnd_1415525 : Nat := 726844703455679485627625

theorem tailTrace_1415525 : CollatzResearch.WordTrace tailWord_1415525 prefixEnd_1415525 726844703455679485627625 := by
  unfold tailWord_1415525
  simp only [CollatzResearch.WordTrace]
  refine ⟨51628438196802152268216029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34418958797868101512144019 51628438196802152268216029)
  ·
    refine ⟨19360664323800807100581011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51628438196802152268216029 19360664323800807100581011)
    ·
      refine ⟨29040996485701210650871517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19360664323800807100581011 29040996485701210650871517)
      ·
        refine ⟨10890373682137953994076819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29040996485701210650871517 10890373682137953994076819)
        ·
          refine ⟨16335560523206930991115229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10890373682137953994076819 16335560523206930991115229)
          ·
            refine ⟨6125835196202599121668211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16335560523206930991115229 6125835196202599121668211)
            ·
              refine ⟨9188752794303898682502317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6125835196202599121668211 9188752794303898682502317)
              ·
                refine ⟨3445782297863962005938369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9188752794303898682502317 3445782297863962005938369)
                ·
                  refine ⟨2584336723397971504453777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3445782297863962005938369 2584336723397971504453777)
                  ·
                    refine ⟨1938252542548478628340333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2584336723397971504453777 1938252542548478628340333)
                    ·
                      refine ⟨726844703455679485627625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1938252542548478628340333 726844703455679485627625)
                      ·
                        rfl

theorem cell23_1415525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_1415525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415525 prefixEnd_1415525 := by exact prefixLift 1415525
  have htrace : WordTrace (prefixWord ++ tailWord_1415525) baseStart_1415525 baseEnd_1415525 := by
    simpa [prefixWord, tailWord_1415525, baseEnd_1415525] using wordTrace_append hprefix tailTrace_1415525
  have hstable : (prefixWord ++ tailWord_1415525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415525).length < 2 ^ (prefixWord ++ tailWord_1415525).sum := by decide
  have hdescent : baseEnd_1415525 < baseStart_1415525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415549 : List Nat := [1, 4, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_1415549 : Nat := 118140960795 + 1415549 * 2 ^ 59
def prefixEnd_1415549 : Nat := 4983230072969 + 3 ^ 40 * 1415549 * 2
def baseEnd_1415549 : Nat := 242285675663795797242505

theorem tailTrace_1415549 : CollatzResearch.WordTrace tailWord_1415549 prefixEnd_1415549 242285675663795797242505 := by
  unfold tailWord_1415549
  simp only [CollatzResearch.WordTrace]
  refine ⟨51629313548715204367089701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34419542365810136244726467 51629313548715204367089701)
  ·
    refine ⟨9680496290384100818829319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51629313548715204367089701 9680496290384100818829319)
    ·
      refine ⟨14520744435576151228243979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9680496290384100818829319 14520744435576151228243979)
      ·
        refine ⟨21781116653364226842365969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14520744435576151228243979 21781116653364226842365969)
        ·
          refine ⟨16335837490023170131774477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21781116653364226842365969 16335837490023170131774477)
          ·
            refine ⟨6125939058758688799415429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16335837490023170131774477 6125939058758688799415429)
            ·
              refine ⟨1148613573517254149890393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6125939058758688799415429 1148613573517254149890393)
              ·
                refine ⟨861460180137940612417795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148613573517254149890393 861460180137940612417795)
                ·
                  refine ⟨1292190270206910918626693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861460180137940612417795 1292190270206910918626693)
                  ·
                    refine ⟨242285675663795797242505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1292190270206910918626693 242285675663795797242505)
                    ·
                      rfl

theorem cell23_1415549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_1415549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415549 prefixEnd_1415549 := by exact prefixLift 1415549
  have htrace : WordTrace (prefixWord ++ tailWord_1415549) baseStart_1415549 baseEnd_1415549 := by
    simpa [prefixWord, tailWord_1415549, baseEnd_1415549] using wordTrace_append hprefix tailTrace_1415549
  have hstable : (prefixWord ++ tailWord_1415549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415549).length < 2 ^ (prefixWord ++ tailWord_1415549).sum := by decide
  have hdescent : baseEnd_1415549 < baseStart_1415549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415589 : List Nat := [1, 3, 1, 2, 1, 1, 6, 3, 1, 1, 3]
def baseStart_1415589 : Nat := 118140960795 + 1415589 * 2 ^ 59
def prefixEnd_1415589 : Nat := 4983230072969 + 3 ^ 40 * 1415589 * 2
def baseEnd_1415589 : Nat := 726877566217567235227331

theorem tailTrace_1415589 : CollatzResearch.WordTrace tailWord_1415589 prefixEnd_1415589 726877566217567235227331 := by
  unfold tailWord_1415589
  simp only [CollatzResearch.WordTrace]
  refine ⟨51630772468570291198545821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34420514979046860799030547 51630772468570291198545821)
  ·
    refine ⟨19361539675713859199454683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51630772468570291198545821 19361539675713859199454683)
    ·
      refine ⟨29042309513570788799182025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19361539675713859199454683 29042309513570788799182025)
      ·
        refine ⟨21781732135178091599386519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29042309513570788799182025 21781732135178091599386519)
        ·
          refine ⟨32672598202767137399079779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21781732135178091599386519 32672598202767137399079779)
          ·
            refine ⟨49008897304150706098619669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32672598202767137399079779 49008897304150706098619669)
            ·
              refine ⟨2297292061132064348372797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49008897304150706098619669 2297292061132064348372797)
              ·
                refine ⟨861484522924524130639799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2297292061132064348372797 861484522924524130639799)
                ·
                  refine ⟨1292226784386786195959699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861484522924524130639799 1292226784386786195959699)
                  ·
                    refine ⟨1938340176580179293939549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1292226784386786195959699 1938340176580179293939549)
                    ·
                      refine ⟨726877566217567235227331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1938340176580179293939549 726877566217567235227331)
                      ·
                        rfl

theorem cell23_1415589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 3, 1, 1, 3].length) (baseStart_1415589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415589 prefixEnd_1415589 := by exact prefixLift 1415589
  have htrace : WordTrace (prefixWord ++ tailWord_1415589) baseStart_1415589 baseEnd_1415589 := by
    simpa [prefixWord, tailWord_1415589, baseEnd_1415589] using wordTrace_append hprefix tailTrace_1415589
  have hstable : (prefixWord ++ tailWord_1415589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415589).length < 2 ^ (prefixWord ++ tailWord_1415589).sum := by decide
  have hdescent : baseEnd_1415589 < baseStart_1415589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415608 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 1, 1, 6]
def baseStart_1415608 : Nat := 118140960795 + 1415608 * 2 ^ 59
def prefixEnd_1415608 : Nat := 4983230072969 + 3 ^ 40 * 1415608 * 2
def baseEnd_1415608 : Nat := 726887322350002660889743

theorem tailTrace_1415608 : CollatzResearch.WordTrace tailWord_1415608 prefixEnd_1415608 726887322350002660889743 := by
  unfold tailWord_1415608
  simp only [CollatzResearch.WordTrace]
  refine ⟨25815732727750728721743739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34420976970334304962324985 25815732727750728721743739)
  ·
    refine ⟨38723599091626093082615609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25815732727750728721743739 38723599091626093082615609)
    ·
      refine ⟨29042699318719569811961707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38723599091626093082615609 29042699318719569811961707)
      ·
        refine ⟨43564048978079354717942561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29042699318719569811961707 43564048978079354717942561)
        ·
          refine ⟨32673036733559516038456921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43564048978079354717942561 32673036733559516038456921)
          ·
            refine ⟨24504777550169637028842691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32673036733559516038456921 24504777550169637028842691)
            ·
              refine ⟨36757166325254455543264037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24504777550169637028842691 36757166325254455543264037)
              ·
                refine ⟨6891968685985210414362007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36757166325254455543264037 6891968685985210414362007)
                ·
                  refine ⟨10337953028977815621543011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6891968685985210414362007 10337953028977815621543011)
                  ·
                    refine ⟨15506929543466723432314517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10337953028977815621543011 15506929543466723432314517)
                    ·
                      refine ⟨726887322350002660889743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15506929543466723432314517 726887322350002660889743)
                      ·
                        rfl

theorem cell23_1415608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_1415608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415608 prefixEnd_1415608 := by exact prefixLift 1415608
  have htrace : WordTrace (prefixWord ++ tailWord_1415608) baseStart_1415608 baseEnd_1415608 := by
    simpa [prefixWord, tailWord_1415608, baseEnd_1415608] using wordTrace_append hprefix tailTrace_1415608
  have hstable : (prefixWord ++ tailWord_1415608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415608).length < 2 ^ (prefixWord ++ tailWord_1415608).sum := by decide
  have hdescent : baseEnd_1415608 < baseStart_1415608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415625 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 4]
def baseStart_1415625 : Nat := 118140960795 + 1415625 * 2 ^ 59
def prefixEnd_1415625 : Nat := 4983230072969 + 3 ^ 40 * 1415625 * 2
def baseEnd_1415625 : Nat := 726896051521129094377165

theorem tailTrace_1415625 : CollatzResearch.WordTrace tailWord_1415625 prefixEnd_1415625 726896051521129094377165 := by
  unfold tailWord_1415625
  simp only [CollatzResearch.WordTrace]
  refine ⟨51632085496439869346856329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34421390330959912897904219 51632085496439869346856329)
  ·
    refine ⟨38724064122329902010142247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51632085496439869346856329 38724064122329902010142247)
    ·
      refine ⟨58086096183494853015213371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38724064122329902010142247 58086096183494853015213371)
      ·
        refine ⟨87129144275242279522820057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58086096183494853015213371 87129144275242279522820057)
        ·
          refine ⟨65346858206431709642115043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87129144275242279522820057 65346858206431709642115043)
          ·
            refine ⟨98020287309647564463172565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65346858206431709642115043 98020287309647564463172565)
            ·
              refine ⟨2297350483819864792105607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 98020287309647564463172565 2297350483819864792105607)
              ·
                refine ⟨3446025725729797188158411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297350483819864792105607 3446025725729797188158411)
                ·
                  refine ⟨5169038588594695782237617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3446025725729797188158411 5169038588594695782237617)
                  ·
                    refine ⟨3876778941446021836678213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5169038588594695782237617 3876778941446021836678213)
                    ·
                      refine ⟨726896051521129094377165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3876778941446021836678213 726896051521129094377165)
                      ·
                        rfl

theorem cell23_1415625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 2, 4].length) (baseStart_1415625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415625 prefixEnd_1415625 := by exact prefixLift 1415625
  have htrace : WordTrace (prefixWord ++ tailWord_1415625) baseStart_1415625 baseEnd_1415625 := by
    simpa [prefixWord, tailWord_1415625, baseEnd_1415625] using wordTrace_append hprefix tailTrace_1415625
  have hstable : (prefixWord ++ tailWord_1415625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415625).length < 2 ^ (prefixWord ++ tailWord_1415625).sum := by decide
  have hdescent : baseEnd_1415625 < baseStart_1415625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415672 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 3, 3, 2]
def baseStart_1415672 : Nat := 118140960795 + 1415672 * 2 ^ 59
def prefixEnd_1415672 : Nat := 4983230072969 + 3 ^ 40 * 1415672 * 2
def baseEnd_1415672 : Nat := 726920185111890410489449

theorem tailTrace_1415672 : CollatzResearch.WordTrace tailWord_1415672 prefixEnd_1415672 726920185111890410489449 := by
  unfold tailWord_1415672
  simp only [CollatzResearch.WordTrace]
  refine ⟨25816899863634798186908635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34422533151513064249211513 25816899863634798186908635)
  ·
    refine ⟨38725349795452197280362953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25816899863634798186908635 38725349795452197280362953)
    ·
      refine ⟨29044012346589147960272215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38725349795452197280362953 29044012346589147960272215)
      ·
        refine ⟨43566018519883721940408323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29044012346589147960272215 43566018519883721940408323)
        ·
          refine ⟨65349027779825582910612485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43566018519883721940408323 65349027779825582910612485)
          ·
            refine ⟨12252942708717296795739841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65349027779825582910612485 12252942708717296795739841)
            ·
              refine ⟨9189707031537972596804881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12252942708717296795739841 9189707031537972596804881)
              ·
                refine ⟨6892280273653479447603661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9189707031537972596804881 6892280273653479447603661)
                ·
                  refine ⟨2584605102620054792851373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6892280273653479447603661 2584605102620054792851373)
                  ·
                    refine ⟨969226913482520547319265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2584605102620054792851373 969226913482520547319265)
                    ·
                      refine ⟨726920185111890410489449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 969226913482520547319265 726920185111890410489449)
                      ·
                        rfl

theorem cell23_1415672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 3, 3, 2].length) (baseStart_1415672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415672 prefixEnd_1415672 := by exact prefixLift 1415672
  have htrace : WordTrace (prefixWord ++ tailWord_1415672) baseStart_1415672 baseEnd_1415672 := by
    simpa [prefixWord, tailWord_1415672, baseEnd_1415672] using wordTrace_append hprefix tailTrace_1415672
  have hstable : (prefixWord ++ tailWord_1415672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415672).length < 2 ^ (prefixWord ++ tailWord_1415672).sum := by decide
  have hdescent : baseEnd_1415672 < baseStart_1415672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415722 : List Nat := [3, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_1415722 : Nat := 118140960795 + 1415722 * 2 ^ 59
def prefixEnd_1415722 : Nat := 4983230072969 + 3 ^ 40 * 1415722 * 2
def baseEnd_1415722 : Nat := 726945859144615214864219

theorem tailTrace_1415722 : CollatzResearch.WordTrace tailWord_1415722 prefixEnd_1415722 726945859144615214864219 := by
  unfold tailWord_1415722
  simp only [CollatzResearch.WordTrace]
  refine ⟨12908905844272113728284355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34423748918058969942091613 12908905844272113728284355)
  ·
    refine ⟨19363358766408170592426533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12908905844272113728284355 19363358766408170592426533)
    ·
      refine ⟨3630629768701531986079975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19363358766408170592426533 3630629768701531986079975)
      ·
        refine ⟨5445944653052297979119963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3630629768701531986079975 5445944653052297979119963)
        ·
          refine ⟨8168916979578446968679945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5445944653052297979119963 8168916979578446968679945)
          ·
            refine ⟨6126687734683835226509959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8168916979578446968679945 6126687734683835226509959)
            ·
              refine ⟨9190031602025752839764939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6126687734683835226509959 9190031602025752839764939)
              ·
                refine ⟨13785047403038629259647409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9190031602025752839764939 13785047403038629259647409)
                ·
                  refine ⟨10338785552278971944735557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13785047403038629259647409 10338785552278971944735557)
                  ·
                    refine ⟨1938522291052307239637917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10338785552278971944735557 1938522291052307239637917)
                    ·
                      refine ⟨726945859144615214864219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1938522291052307239637917 726945859144615214864219)
                      ·
                        rfl

theorem cell23_1415722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_1415722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415722 prefixEnd_1415722 := by exact prefixLift 1415722
  have htrace : WordTrace (prefixWord ++ tailWord_1415722) baseStart_1415722 baseEnd_1415722 := by
    simpa [prefixWord, tailWord_1415722, baseEnd_1415722] using wordTrace_append hprefix tailTrace_1415722
  have hstable : (prefixWord ++ tailWord_1415722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415722).length < 2 ^ (prefixWord ++ tailWord_1415722).sum := by decide
  have hdescent : baseEnd_1415722 < baseStart_1415722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415765 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1415765 : Nat := 118140960795 + 1415765 * 2 ^ 59
def prefixEnd_1415765 : Nat := 4983230072969 + 3 ^ 40 * 1415765 * 2
def baseEnd_1415765 : Nat := 726967938812758546626521

theorem tailTrace_1415765 : CollatzResearch.WordTrace tailWord_1415765 prefixEnd_1415765 726967938812758546626521 := by
  unfold tailWord_1415765
  simp only [CollatzResearch.WordTrace]
  refine ⟨51637191715932673256952749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34424794477288448837968499 51637191715932673256952749)
  ·
    refine ⟨19363946893474752471357281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51637191715932673256952749 19363946893474752471357281)
    ·
      refine ⟨14522960170106064353517961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19363946893474752471357281 14522960170106064353517961)
      ·
        refine ⟨10892220127579548265138471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14522960170106064353517961 10892220127579548265138471)
        ·
          refine ⟨16338330191369322397707707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10892220127579548265138471 16338330191369322397707707)
          ·
            refine ⟨24507495287053983596561561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16338330191369322397707707 24507495287053983596561561)
            ·
              refine ⟨18380621465290487697421171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24507495287053983596561561 18380621465290487697421171)
              ·
                refine ⟨27570932197935731546131757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18380621465290487697421171 27570932197935731546131757)
                ·
                  refine ⟨10339099574225899329799409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27570932197935731546131757 10339099574225899329799409)
                  ·
                    refine ⟨7754324680669424497349557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10339099574225899329799409 7754324680669424497349557)
                    ·
                      refine ⟨726967938812758546626521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7754324680669424497349557 726967938812758546626521)
                      ·
                        rfl

theorem cell23_1415765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1415765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415765 prefixEnd_1415765 := by exact prefixLift 1415765
  have htrace : WordTrace (prefixWord ++ tailWord_1415765) baseStart_1415765 baseEnd_1415765 := by
    simpa [prefixWord, tailWord_1415765, baseEnd_1415765] using wordTrace_append hprefix tailTrace_1415765
  have hstable : (prefixWord ++ tailWord_1415765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415765).length < 2 ^ (prefixWord ++ tailWord_1415765).sum := by decide
  have hdescent : baseEnd_1415765 < baseStart_1415765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415815 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 10]
def baseStart_1415815 : Nat := 118140960795 + 1415815 * 2 ^ 59
def prefixEnd_1415815 : Nat := 4983230072969 + 3 ^ 40 * 1415815 * 2
def baseEnd_1415815 : Nat := 80777068093942594555699

theorem tailTrace_1415815 : CollatzResearch.WordTrace tailWord_1415815 prefixEnd_1415815 80777068093942594555699 := by
  unfold tailWord_1415815
  simp only [CollatzResearch.WordTrace]
  refine ⟨51639015365751531796272899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34426010243834354530848599 51639015365751531796272899)
  ·
    refine ⟨77458523048627297694409349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51639015365751531796272899 77458523048627297694409349)
    ·
      refine ⟨14523473071617618317701753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77458523048627297694409349 14523473071617618317701753)
      ·
        refine ⟨10892604803713213738276315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14523473071617618317701753 10892604803713213738276315)
        ·
          refine ⟨16338907205569820607414473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10892604803713213738276315 16338907205569820607414473)
          ·
            refine ⟨12254180404177365455560855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16338907205569820607414473 12254180404177365455560855)
            ·
              refine ⟨18381270606266048183341283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12254180404177365455560855 18381270606266048183341283)
              ·
                refine ⟨27571905909399072275011925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18381270606266048183341283 27571905909399072275011925)
                ·
                  refine ⟨80777068093942594555699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 27571905909399072275011925 80777068093942594555699)
                  ·
                    rfl

theorem cell23_1415815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 10].length) (baseStart_1415815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415815 prefixEnd_1415815 := by exact prefixLift 1415815
  have htrace : WordTrace (prefixWord ++ tailWord_1415815) baseStart_1415815 baseEnd_1415815 := by
    simpa [prefixWord, tailWord_1415815, baseEnd_1415815] using wordTrace_append hprefix tailTrace_1415815
  have hstable : (prefixWord ++ tailWord_1415815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415815).length < 2 ^ (prefixWord ++ tailWord_1415815).sum := by decide
  have hdescent : baseEnd_1415815 < baseStart_1415815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415819 : List Nat := [1, 1, 1, 1, 4, 1, 2, 7, 1, 4]
def baseStart_1415819 : Nat := 118140960795 + 1415819 * 2 ^ 59
def prefixEnd_1415819 : Nat := 4983230072969 + 3 ^ 40 * 1415819 * 2
def baseEnd_1415819 : Nat := 242331888922700445117091

theorem tailTrace_1415819 : CollatzResearch.WordTrace tailWord_1415819 prefixEnd_1415819 242331888922700445117091 := by
  unfold tailWord_1415819
  simp only [CollatzResearch.WordTrace]
  refine ⟨51639161257737040479418511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34426107505158026986279007 51639161257737040479418511)
  ·
    refine ⟨77458741886605560719127767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51639161257737040479418511 77458741886605560719127767)
    ·
      refine ⟨116188112829908341078691651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77458741886605560719127767 116188112829908341078691651)
      ·
        refine ⟨174282169244862511618037477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116188112829908341078691651 174282169244862511618037477)
        ·
          refine ⟨32677906733411720928382027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174282169244862511618037477 32677906733411720928382027)
          ·
            refine ⟨49016860100117581392573041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32677906733411720928382027 49016860100117581392573041)
            ·
              refine ⟨36762645075088186044429781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49016860100117581392573041 36762645075088186044429781)
              ·
                refine ⟨861624493947379360416323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36762645075088186044429781 861624493947379360416323)
                ·
                  refine ⟨1292436740921069040624485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861624493947379360416323 1292436740921069040624485)
                  ·
                    refine ⟨242331888922700445117091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1292436740921069040624485 242331888922700445117091)
                    ·
                      rfl

theorem cell23_1415819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 1, 4].length) (baseStart_1415819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415819 prefixEnd_1415819 := by exact prefixLift 1415819
  have htrace : WordTrace (prefixWord ++ tailWord_1415819) baseStart_1415819 baseEnd_1415819 := by
    simpa [prefixWord, tailWord_1415819, baseEnd_1415819] using wordTrace_append hprefix tailTrace_1415819
  have hstable : (prefixWord ++ tailWord_1415819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415819).length < 2 ^ (prefixWord ++ tailWord_1415819).sum := by decide
  have hdescent : baseEnd_1415819 < baseStart_1415819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415832 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 6]
def baseStart_1415832 : Nat := 118140960795 + 1415832 * 2 ^ 59
def prefixEnd_1415832 : Nat := 4983230072969 + 3 ^ 40 * 1415832 * 2
def baseEnd_1415832 : Nat := 80778038001845531609857

theorem tailTrace_1415832 : CollatzResearch.WordTrace tailWord_1415832 prefixEnd_1415832 80778038001845531609857 := by
  unfold tailWord_1415832
  simp only [CollatzResearch.WordTrace]
  refine ⟨25819817703344971849820875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34426423604459962466427833 25819817703344971849820875)
  ·
    refine ⟨38729726555017457774731313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25819817703344971849820875 38729726555017457774731313)
    ·
      refine ⟨29047294916263093331048485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38729726555017457774731313 29047294916263093331048485)
      ·
        refine ⟨5446367796799329999571591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29047294916263093331048485 5446367796799329999571591)
        ·
          refine ⟨8169551695198994999357387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5446367796799329999571591 8169551695198994999357387)
          ·
            refine ⟨12254327542798492499036081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8169551695198994999357387 12254327542798492499036081)
            ·
              refine ⟨9190745657098869374277061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12254327542798492499036081 9190745657098869374277061)
              ·
                refine ⟨1723264810706038007676949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9190745657098869374277061 1723264810706038007676949)
                ·
                  refine ⟨80778038001845531609857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1723264810706038007676949 80778038001845531609857)
                  ·
                    rfl

theorem cell23_1415832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 6].length) (baseStart_1415832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415832 prefixEnd_1415832 := by exact prefixLift 1415832
  have htrace : WordTrace (prefixWord ++ tailWord_1415832) baseStart_1415832 baseEnd_1415832 := by
    simpa [prefixWord, tailWord_1415832, baseEnd_1415832] using wordTrace_append hprefix tailTrace_1415832
  have hstable : (prefixWord ++ tailWord_1415832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415832).length < 2 ^ (prefixWord ++ tailWord_1415832).sum := by decide
  have hdescent : baseEnd_1415832 < baseStart_1415832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415836 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 3, 4]
def baseStart_1415836 : Nat := 118140960795 + 1415836 * 2 ^ 59
def prefixEnd_1415836 : Nat := 4983230072969 + 3 ^ 40 * 1415836 * 2
def baseEnd_1415836 : Nat := 242334798646409256279565

theorem tailTrace_1415836 : CollatzResearch.WordTrace tailWord_1415836 prefixEnd_1415836 242334798646409256279565 := by
  unfold tailWord_1415836
  simp only [CollatzResearch.WordTrace]
  refine ⟨25819890649337726191393681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34426520865783634921858241 25819890649337726191393681)
  ·
    refine ⟨19364917987003294643545261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25819890649337726191393681 19364917987003294643545261)
    ·
      refine ⟨7261844245126235491329473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19364917987003294643545261 7261844245126235491329473)
      ·
        refine ⟨5446383183844676618497105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7261844245126235491329473 5446383183844676618497105)
        ·
          refine ⟨4084787387883507463872829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5446383183844676618497105 4084787387883507463872829)
          ·
            refine ⟨1531795270456315298952311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4084787387883507463872829 1531795270456315298952311)
            ·
              refine ⟨2297692905684472948428467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531795270456315298952311 2297692905684472948428467)
              ·
                refine ⟨3446539358526709422642701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297692905684472948428467 3446539358526709422642701)
                ·
                  refine ⟨1292452259447516033491013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3446539358526709422642701 1292452259447516033491013)
                  ·
                    refine ⟨242334798646409256279565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1292452259447516033491013 242334798646409256279565)
                    ·
                      rfl

theorem cell23_1415836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_1415836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415836 prefixEnd_1415836 := by exact prefixLift 1415836
  have htrace : WordTrace (prefixWord ++ tailWord_1415836) baseStart_1415836 baseEnd_1415836 := by
    simpa [prefixWord, tailWord_1415836, baseEnd_1415836] using wordTrace_append hprefix tailTrace_1415836
  have hstable : (prefixWord ++ tailWord_1415836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415836).length < 2 ^ (prefixWord ++ tailWord_1415836).sum := by decide
  have hdescent : baseEnd_1415836 < baseStart_1415836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415845 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 2, 9]
def baseStart_1415845 : Nat := 118140960795 + 1415845 * 2 ^ 59
def prefixEnd_1415845 : Nat := 4983230072969 + 3 ^ 40 * 1415845 * 2
def baseEnd_1415845 : Nat := 242336339088372744542051

theorem tailTrace_1415845 : CollatzResearch.WordTrace tailWord_1415845 prefixEnd_1415845 242336339088372744542051 := by
  unfold tailWord_1415845
  simp only [CollatzResearch.WordTrace]
  refine ⟨51640109555642846919864989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34426739703761897946576659 51640109555642846919864989)
  ·
    refine ⟨19365041083366067594949371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51640109555642846919864989 19365041083366067594949371)
    ·
      refine ⟨29047561625049101392424057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19365041083366067594949371 29047561625049101392424057)
      ·
        refine ⟨21785671218786826044318043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29047561625049101392424057 21785671218786826044318043)
        ·
          refine ⟨32678506828180239066477065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21785671218786826044318043 32678506828180239066477065)
          ·
            refine ⟨24508880121135179299857799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32678506828180239066477065 24508880121135179299857799)
            ·
              refine ⟨36763320181702768949786699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24508880121135179299857799 36763320181702768949786699)
              ·
                refine ⟨55144980272554153424680049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36763320181702768949786699 55144980272554153424680049)
                ·
                  refine ⟨41358735204415615068510037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55144980272554153424680049 41358735204415615068510037)
                  ·
                    refine ⟨242336339088372744542051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 41358735204415615068510037 242336339088372744542051)
                    ·
                      rfl

theorem cell23_1415845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_1415845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415845 prefixEnd_1415845 := by exact prefixLift 1415845
  have htrace : WordTrace (prefixWord ++ tailWord_1415845) baseStart_1415845 baseEnd_1415845 := by
    simpa [prefixWord, tailWord_1415845, baseEnd_1415845] using wordTrace_append hprefix tailTrace_1415845
  have hstable : (prefixWord ++ tailWord_1415845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415845).length < 2 ^ (prefixWord ++ tailWord_1415845).sum := by decide
  have hdescent : baseEnd_1415845 < baseStart_1415845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415886 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2]
def baseStart_1415886 : Nat := 118140960795 + 1415886 * 2 ^ 59
def prefixEnd_1415886 : Nat := 4983230072969 + 3 ^ 40 * 1415886 * 2
def baseEnd_1415886 : Nat := 727030069971952573213465

theorem tailTrace_1415886 : CollatzResearch.WordTrace tailWord_1415886 prefixEnd_1415886 727030069971952573213465 := by
  unfold tailWord_1415886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6455200618561788865263439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34427736632329540614738341 6455200618561788865263439)
  ·
    refine ⟨9682800927842683297895159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6455200618561788865263439 9682800927842683297895159)
    ·
      refine ⟨14524201391764024946842739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9682800927842683297895159 14524201391764024946842739)
      ·
        refine ⟨21786302087646037420264109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14524201391764024946842739 21786302087646037420264109)
        ·
          refine ⟨8169863282867264032599041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21786302087646037420264109 8169863282867264032599041)
          ·
            refine ⟨6127397462150448024449281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8169863282867264032599041 6127397462150448024449281)
            ·
              refine ⟨4595548096612836018336961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6127397462150448024449281 4595548096612836018336961)
              ·
                refine ⟨3446661072459627013752721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4595548096612836018336961 3446661072459627013752721)
                ·
                  refine ⟨2584995804344720260314541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3446661072459627013752721 2584995804344720260314541)
                  ·
                    refine ⟨969373426629270097617953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2584995804344720260314541 969373426629270097617953)
                    ·
                      refine ⟨727030069971952573213465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 969373426629270097617953 727030069971952573213465)
                      ·
                        rfl

theorem cell23_1415886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_1415886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415886 prefixEnd_1415886 := by exact prefixLift 1415886
  have htrace : WordTrace (prefixWord ++ tailWord_1415886) baseStart_1415886 baseEnd_1415886 := by
    simpa [prefixWord, tailWord_1415886, baseEnd_1415886] using wordTrace_append hprefix tailTrace_1415886
  have hstable : (prefixWord ++ tailWord_1415886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415886).length < 2 ^ (prefixWord ++ tailWord_1415886).sum := by decide
  have hdescent : baseEnd_1415886 < baseStart_1415886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415909 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 1, 6]
def baseStart_1415909 : Nat := 118140960795 + 1415909 * 2 ^ 59
def prefixEnd_1415909 : Nat := 4983230072969 + 3 ^ 40 * 1415909 * 2
def baseEnd_1415909 : Nat := 242347293342335327741953

theorem tailTrace_1415909 : CollatzResearch.WordTrace tailWord_1415909 prefixEnd_1415909 242347293342335327741953 := by
  unfold tailWord_1415909
  simp only [CollatzResearch.WordTrace]
  refine ⟨51642443827410985850194781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34428295884940657233463187 51642443827410985850194781)
  ·
    refine ⟨19365916435279119693823043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51642443827410985850194781 19365916435279119693823043)
    ·
      refine ⟨29048874652918679540734565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19365916435279119693823043 29048874652918679540734565)
      ·
        refine ⟨5446663997422252413887731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29048874652918679540734565 5446663997422252413887731)
        ·
          refine ⟨8169995996133378620831597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5446663997422252413887731 8169995996133378620831597)
          ·
            refine ⟨3063748498550016982811849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8169995996133378620831597 3063748498550016982811849)
            ·
              refine ⟨2297811373912512737108887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3063748498550016982811849 2297811373912512737108887)
              ·
                refine ⟨3446717060868769105663331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297811373912512737108887 3446717060868769105663331)
                ·
                  refine ⟨5170075591303153658494997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3446717060868769105663331 5170075591303153658494997)
                  ·
                    refine ⟨242347293342335327741953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5170075591303153658494997 242347293342335327741953)
                    ·
                      rfl

theorem cell23_1415909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_1415909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415909 prefixEnd_1415909 := by exact prefixLift 1415909
  have htrace : WordTrace (prefixWord ++ tailWord_1415909) baseStart_1415909 baseEnd_1415909 := by
    simpa [prefixWord, tailWord_1415909, baseEnd_1415909] using wordTrace_append hprefix tailTrace_1415909
  have hstable : (prefixWord ++ tailWord_1415909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415909).length < 2 ^ (prefixWord ++ tailWord_1415909).sum := by decide
  have hdescent : baseEnd_1415909 < baseStart_1415909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415919 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 3]
def baseStart_1415919 : Nat := 118140960795 + 1415919 * 2 ^ 59
def prefixEnd_1415919 : Nat := 4983230072969 + 3 ^ 40 * 1415919 * 2
def baseEnd_1415919 : Nat := 727047014833550944100813

theorem tailTrace_1415919 : CollatzResearch.WordTrace tailWord_1415919 prefixEnd_1415919 727047014833550944100813 := by
  unfold tailWord_1415919
  simp only [CollatzResearch.WordTrace]
  refine ⟨51642808557374757558058811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34428539038249838372039207 51642808557374757558058811)
  ·
    refine ⟨77464212836062136337088217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51642808557374757558058811 77464212836062136337088217)
    ·
      refine ⟨58098159627046602252816163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77464212836062136337088217 58098159627046602252816163)
      ·
        refine ⟨87147239440569903379224245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58098159627046602252816163 87147239440569903379224245)
        ·
          refine ⟨8170053697553428441802273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87147239440569903379224245 8170053697553428441802273)
          ·
            refine ⟨6127540273165071331351705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8170053697553428441802273 6127540273165071331351705)
            ·
              refine ⟨4595655204873803498513779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6127540273165071331351705 4595655204873803498513779)
              ·
                refine ⟨6893482807310705247770669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4595655204873803498513779 6893482807310705247770669)
                ·
                  refine ⟨2585056052741514467914001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6893482807310705247770669 2585056052741514467914001)
                  ·
                    refine ⟨1938792039556135850935501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2585056052741514467914001 1938792039556135850935501)
                    ·
                      refine ⟨727047014833550944100813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1938792039556135850935501 727047014833550944100813)
                      ·
                        rfl

theorem cell23_1415919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 3].length) (baseStart_1415919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415919 prefixEnd_1415919 := by exact prefixLift 1415919
  have htrace : WordTrace (prefixWord ++ tailWord_1415919) baseStart_1415919 baseEnd_1415919 := by
    simpa [prefixWord, tailWord_1415919, baseEnd_1415919] using wordTrace_append hprefix tailTrace_1415919
  have hstable : (prefixWord ++ tailWord_1415919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415919).length < 2 ^ (prefixWord ++ tailWord_1415919).sum := by decide
  have hdescent : baseEnd_1415919 < baseStart_1415919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1415943 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 2, 4]
def baseStart_1415943 : Nat := 118140960795 + 1415943 * 2 ^ 59
def prefixEnd_1415943 : Nat := 4983230072969 + 3 ^ 40 * 1415943 * 2
def baseEnd_1415943 : Nat := 242353112789752950066901

theorem tailTrace_1415943 : CollatzResearch.WordTrace tailWord_1415943 prefixEnd_1415943 242353112789752950066901 := by
  unfold tailWord_1415943
  simp only [CollatzResearch.WordTrace]
  refine ⟨51643683909287809656932483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34429122606191873104621655 51643683909287809656932483)
  ·
    refine ⟨77465525863931714485398725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51643683909287809656932483 77465525863931714485398725)
    ·
      refine ⟨14524786099487196466012261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77465525863931714485398725 14524786099487196466012261)
      ·
        refine ⟨2723397393653849337377299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14524786099487196466012261 2723397393653849337377299)
        ·
          refine ⟨4085096090480774006065949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2723397393653849337377299 4085096090480774006065949)
          ·
            refine ⟨1531911033930290252274731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4085096090480774006065949 1531911033930290252274731)
            ·
              refine ⟨2297866550895435378412097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531911033930290252274731 2297866550895435378412097)
              ·
                refine ⟨1723399913171576533809073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2297866550895435378412097 1723399913171576533809073)
                ·
                  refine ⟨1292549934878682400356805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1723399913171576533809073 1292549934878682400356805)
                  ·
                    refine ⟨242353112789752950066901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1292549934878682400356805 242353112789752950066901)
                    ·
                      rfl

theorem cell23_1415943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_1415943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1415943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1415943 prefixEnd_1415943 := by exact prefixLift 1415943
  have htrace : WordTrace (prefixWord ++ tailWord_1415943) baseStart_1415943 baseEnd_1415943 := by
    simpa [prefixWord, tailWord_1415943, baseEnd_1415943] using wordTrace_append hprefix tailTrace_1415943
  have hstable : (prefixWord ++ tailWord_1415943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1415943).length < 2 ^ (prefixWord ++ tailWord_1415943).sum := by decide
  have hdescent : baseEnd_1415943 < baseStart_1415943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1415943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416017 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 2, 1, 3]
def baseStart_1416017 : Nat := 118140960795 + 1416017 * 2 ^ 59
def prefixEnd_1416017 : Nat := 4983230072969 + 3 ^ 40 * 1416017 * 2
def baseEnd_1416017 : Nat := 727097335937691560675363

theorem tailTrace_1416017 : CollatzResearch.WordTrace tailWord_1416017 prefixEnd_1416017 727097335937691560675363 := by
  unfold tailWord_1416017
  simp only [CollatzResearch.WordTrace]
  refine ⟨51646382911019720295126305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34430921940679813530084203 51646382911019720295126305)
  ·
    refine ⟨38734787183264790221344729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51646382911019720295126305 38734787183264790221344729)
    ·
      refine ⟨29051090387448592666008547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38734787183264790221344729 29051090387448592666008547)
      ·
        refine ⟨43576635581172888999012821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29051090387448592666008547 43576635581172888999012821)
        ·
          refine ⟨1021327396433739585914363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 43576635581172888999012821 1021327396433739585914363)
          ·
            refine ⟨1531991094650609378871545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021327396433739585914363 1531991094650609378871545)
            ·
              refine ⟨1148993320987957034153659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1531991094650609378871545 1148993320987957034153659)
              ·
                refine ⟨1723489981481935551230489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148993320987957034153659 1723489981481935551230489)
                ·
                  refine ⟨1292617486111451663422867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1723489981481935551230489 1292617486111451663422867)
                  ·
                    refine ⟨1938926229167177495134301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1292617486111451663422867 1938926229167177495134301)
                    ·
                      refine ⟨727097335937691560675363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1938926229167177495134301 727097335937691560675363)
                      ·
                        rfl

theorem cell23_1416017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 2, 1, 3].length) (baseStart_1416017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416017 prefixEnd_1416017 := by exact prefixLift 1416017
  have htrace : WordTrace (prefixWord ++ tailWord_1416017) baseStart_1416017 baseEnd_1416017 := by
    simpa [prefixWord, tailWord_1416017, baseEnd_1416017] using wordTrace_append hprefix tailTrace_1416017
  have hstable : (prefixWord ++ tailWord_1416017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416017).length < 2 ^ (prefixWord ++ tailWord_1416017).sum := by decide
  have hdescent : baseEnd_1416017 < baseStart_1416017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416059 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 2, 5]
def baseStart_1416059 : Nat := 118140960795 + 1416059 * 2 ^ 59
def prefixEnd_1416059 : Nat := 4983230072969 + 3 ^ 40 * 1416059 * 2
def baseEnd_1416059 : Nat := 242372967375060132116723

theorem tailTrace_1416059 : CollatzResearch.WordTrace tailWord_1416059 prefixEnd_1416059 242372967375060132116723 := by
  unfold tailWord_1416059
  simp only [CollatzResearch.WordTrace]
  refine ⟨51647914776867561468155231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34431943184578374312103487 51647914776867561468155231)
  ·
    refine ⟨77471872165301342202232847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51647914776867561468155231 77471872165301342202232847)
    ·
      refine ⟨116207808247952013303349271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77471872165301342202232847 116207808247952013303349271)
      ·
        refine ⟨174311712371928019955023907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116207808247952013303349271 174311712371928019955023907)
        ·
          refine ⟨261467568557892029932535861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174311712371928019955023907 261467568557892029932535861)
          ·
            refine ⟨24512584552302377806175237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 261467568557892029932535861 24512584552302377806175237)
            ·
              refine ⟨4596109603556695838657857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24512584552302377806175237 4596109603556695838657857)
              ·
                refine ⟨3447082202667521878993393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4596109603556695838657857 3447082202667521878993393)
                ·
                  refine ⟨2585311652000641409245045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3447082202667521878993393 2585311652000641409245045)
                  ·
                    refine ⟨242372967375060132116723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2585311652000641409245045 242372967375060132116723)
                    ·
                      rfl

theorem cell23_1416059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 5].length) (baseStart_1416059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416059 prefixEnd_1416059 := by exact prefixLift 1416059
  have htrace : WordTrace (prefixWord ++ tailWord_1416059) baseStart_1416059 baseEnd_1416059 := by
    simpa [prefixWord, tailWord_1416059, baseEnd_1416059] using wordTrace_append hprefix tailTrace_1416059
  have hstable : (prefixWord ++ tailWord_1416059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416059).length < 2 ^ (prefixWord ++ tailWord_1416059).sum := by decide
  have hdescent : baseEnd_1416059 < baseStart_1416059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416069 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_1416069 : Nat := 118140960795 + 1416069 * 2 ^ 59
def prefixEnd_1416069 : Nat := 4983230072969 + 3 ^ 40 * 1416069 * 2
def baseEnd_1416069 : Nat := 727124036931725357225123

theorem tailTrace_1416069 : CollatzResearch.WordTrace tailWord_1416069 prefixEnd_1416069 727124036931725357225123 := by
  unfold tailWord_1416069
  simp only [CollatzResearch.WordTrace]
  refine ⟨51648279506831333176019261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34432186337887555450679507 51648279506831333176019261)
  ·
    refine ⟨19368104815061749941007223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51648279506831333176019261 19368104815061749941007223)
    ·
      refine ⟨29052157222592624911510835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19368104815061749941007223 29052157222592624911510835)
      ·
        refine ⟨43578235833888937367266253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29052157222592624911510835 43578235833888937367266253)
        ·
          refine ⟨16341838437708351512724845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43578235833888937367266253 16341838437708351512724845)
          ·
            refine ⟨6128189414140631817271817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16341838437708351512724845 6128189414140631817271817)
            ·
              refine ⟨4596142060605473862953863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6128189414140631817271817 4596142060605473862953863)
              ·
                refine ⟨6894213090908210794430795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4596142060605473862953863 6894213090908210794430795)
                ·
                  refine ⟨10341319636362316191646193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6894213090908210794430795 10341319636362316191646193)
                  ·
                    refine ⟨7755989727271737143734645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10341319636362316191646193 7755989727271737143734645)
                    ·
                      refine ⟨727124036931725357225123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7755989727271737143734645 727124036931725357225123)
                      ·
                        rfl

theorem cell23_1416069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_1416069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416069 prefixEnd_1416069 := by exact prefixLift 1416069
  have htrace : WordTrace (prefixWord ++ tailWord_1416069) baseStart_1416069 baseEnd_1416069 := by
    simpa [prefixWord, tailWord_1416069, baseEnd_1416069] using wordTrace_append hprefix tailTrace_1416069
  have hstable : (prefixWord ++ tailWord_1416069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416069).length < 2 ^ (prefixWord ++ tailWord_1416069).sum := by decide
  have hdescent : baseEnd_1416069 < baseStart_1416069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416096 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 4]
def baseStart_1416096 : Nat := 118140960795 + 1416096 * 2 ^ 59
def prefixEnd_1416096 : Nat := 4983230072969 + 3 ^ 40 * 1416096 * 2
def baseEnd_1416096 : Nat := 727137900909396751587499

theorem tailTrace_1416096 : CollatzResearch.WordTrace tailWord_1416096 prefixEnd_1416096 727137900909396751587499 := by
  unfold tailWord_1416096
  simp only [CollatzResearch.WordTrace]
  refine ⟨25824632138866758393626071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34432842851822344524834761 25824632138866758393626071)
  ·
    refine ⟨38736948208300137590439107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25824632138866758393626071 38736948208300137590439107)
    ·
      refine ⟨58105422312450206385658661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38736948208300137590439107 58105422312450206385658661)
      ·
        refine ⟨10894766683584413697310999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58105422312450206385658661 10894766683584413697310999)
        ·
          refine ⟨16342150025376620545966499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10894766683584413697310999 16342150025376620545966499)
          ·
            refine ⟨24513225038064930818949749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16342150025376620545966499 24513225038064930818949749)
            ·
              refine ⟨2298114847318587264276539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24513225038064930818949749 2298114847318587264276539)
              ·
                refine ⟨3447172270977880896414809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298114847318587264276539 3447172270977880896414809)
                ·
                  refine ⟨2585379203233410672311107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3447172270977880896414809 2585379203233410672311107)
                  ·
                    refine ⟨3878068804850116008466661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2585379203233410672311107 3878068804850116008466661)
                    ·
                      refine ⟨727137900909396751587499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3878068804850116008466661 727137900909396751587499)
                      ·
                        rfl

theorem cell23_1416096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_1416096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416096 prefixEnd_1416096 := by exact prefixLift 1416096
  have htrace : WordTrace (prefixWord ++ tailWord_1416096) baseStart_1416096 baseEnd_1416096 := by
    simpa [prefixWord, tailWord_1416096, baseEnd_1416096] using wordTrace_append hprefix tailTrace_1416096
  have hstable : (prefixWord ++ tailWord_1416096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416096).length < 2 ^ (prefixWord ++ tailWord_1416096).sum := by decide
  have hdescent : baseEnd_1416096 < baseStart_1416096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416157 : List Nat := [1, 4, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_1416157 : Nat := 118140960795 + 1416157 * 2 ^ 59
def prefixEnd_1416157 : Nat := 4983230072969 + 3 ^ 40 * 1416157 * 2
def baseEnd_1416157 : Nat := 242389741076440337641573

theorem tailTrace_1416157 : CollatzResearch.WordTrace tailWord_1416157 prefixEnd_1416157 242389741076440337641573 := by
  unfold tailWord_1416157
  simp only [CollatzResearch.WordTrace]
  refine ⟨51651489130512524205222725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34434326087008349470148483 51651489130512524205222725)
  ·
    refine ⟨9684654211971098288479261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51651489130512524205222725 9684654211971098288479261)
    ·
      refine ⟨3631745329489161858179723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9684654211971098288479261 3631745329489161858179723)
      ·
        refine ⟨5447617994233742787269585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3631745329489161858179723 5447617994233742787269585)
        ·
          refine ⟨4085713495675307090452189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5447617994233742787269585 4085713495675307090452189)
          ·
            refine ⟨1532142560878240158919571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4085713495675307090452189 1532142560878240158919571)
            ·
              refine ⟨2298213841317360238379357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532142560878240158919571 2298213841317360238379357)
              ·
                refine ⟨861830190494010089392259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2298213841317360238379357 861830190494010089392259)
                ·
                  refine ⟨1292745285741015134088389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861830190494010089392259 1292745285741015134088389)
                  ·
                    refine ⟨242389741076440337641573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1292745285741015134088389 242389741076440337641573)
                    ·
                      rfl

theorem cell23_1416157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_1416157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416157 prefixEnd_1416157 := by exact prefixLift 1416157
  have htrace : WordTrace (prefixWord ++ tailWord_1416157) baseStart_1416157 baseEnd_1416157 := by
    simpa [prefixWord, tailWord_1416157, baseEnd_1416157] using wordTrace_append hprefix tailTrace_1416157
  have hstable : (prefixWord ++ tailWord_1416157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416157).length < 2 ^ (prefixWord ++ tailWord_1416157).sum := by decide
  have hdescent : baseEnd_1416157 < baseStart_1416157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416203 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 4]
def baseStart_1416203 : Nat := 118140960795 + 1416203 * 2 ^ 59
def prefixEnd_1416203 : Nat := 4983230072969 + 3 ^ 40 * 1416203 * 2
def baseEnd_1416203 : Nat := 727192843339427832949507

theorem tailTrace_1416203 : CollatzResearch.WordTrace tailWord_1416203 prefixEnd_1416203 727192843339427832949507 := by
  unfold tailWord_1416203
  simp only [CollatzResearch.WordTrace]
  refine ⟨51653166888345874061397263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34435444592230582707598175 51653166888345874061397263)
  ·
    refine ⟨77479750332518811092095895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51653166888345874061397263 77479750332518811092095895)
    ·
      refine ⟨116219625498778216638143843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77479750332518811092095895 116219625498778216638143843)
      ·
        refine ⟨174329438248167324957215765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116219625498778216638143843 174329438248167324957215765)
        ·
          refine ⟨8171692417882843357369489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 174329438248167324957215765 8171692417882843357369489)
          ·
            refine ⟨6128769313412132518027117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8171692417882843357369489 6128769313412132518027117)
            ·
              refine ⟨2298288492529549694260169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6128769313412132518027117 2298288492529549694260169)
              ·
                refine ⟨1723716369397162270695127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2298288492529549694260169 1723716369397162270695127)
                ·
                  refine ⟨2585574554095743406042691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1723716369397162270695127 2585574554095743406042691)
                  ·
                    refine ⟨3878361831143615109064037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2585574554095743406042691 3878361831143615109064037)
                    ·
                      refine ⟨727192843339427832949507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3878361831143615109064037 727192843339427832949507)
                      ·
                        rfl

theorem cell23_1416203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 4].length) (baseStart_1416203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416203 prefixEnd_1416203 := by exact prefixLift 1416203
  have htrace : WordTrace (prefixWord ++ tailWord_1416203) baseStart_1416203 baseEnd_1416203 := by
    simpa [prefixWord, tailWord_1416203, baseEnd_1416203] using wordTrace_append hprefix tailTrace_1416203
  have hstable : (prefixWord ++ tailWord_1416203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416203).length < 2 ^ (prefixWord ++ tailWord_1416203).sum := by decide
  have hdescent : baseEnd_1416203 < baseStart_1416203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416216 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1416216 : Nat := 118140960795 + 1416216 * 2 ^ 59
def prefixEnd_1416216 : Nat := 4983230072969 + 3 ^ 40 * 1416216 * 2
def baseEnd_1416216 : Nat := 727199518587936282086947

theorem tailTrace_1416216 : CollatzResearch.WordTrace tailWord_1416216 prefixEnd_1416216 727199518587936282086947 := by
  unfold tailWord_1416216
  simp only [CollatzResearch.WordTrace]
  refine ⟨25826820518649388640810251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34435760691532518187747001 25826820518649388640810251)
  ·
    refine ⟨38740230777974082961215377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25826820518649388640810251 38740230777974082961215377)
    ·
      refine ⟨29055173083480562220911533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38740230777974082961215377 29055173083480562220911533)
      ·
        refine ⟨10895689906305210832841825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29055173083480562220911533 10895689906305210832841825)
        ·
          refine ⟨8171767429728908124631369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10895689906305210832841825 8171767429728908124631369)
          ·
            refine ⟨6128825572296681093473527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8171767429728908124631369 6128825572296681093473527)
            ·
              refine ⟨9193238358445021640210291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6128825572296681093473527 9193238358445021640210291)
              ·
                refine ⟨13789857537667532460315437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9193238358445021640210291 13789857537667532460315437)
                ·
                  refine ⟨5171196576625324672618289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13789857537667532460315437 5171196576625324672618289)
                  ·
                    refine ⟨3878397432468993504463717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5171196576625324672618289 3878397432468993504463717)
                    ·
                      refine ⟨727199518587936282086947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3878397432468993504463717 727199518587936282086947)
                      ·
                        rfl

theorem cell23_1416216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1416216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416216 prefixEnd_1416216 := by exact prefixLift 1416216
  have htrace : WordTrace (prefixWord ++ tailWord_1416216) baseStart_1416216 baseEnd_1416216 := by
    simpa [prefixWord, tailWord_1416216, baseEnd_1416216] using wordTrace_append hprefix tailTrace_1416216
  have hstable : (prefixWord ++ tailWord_1416216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416216).length < 2 ^ (prefixWord ++ tailWord_1416216).sum := by decide
  have hdescent : baseEnd_1416216 < baseStart_1416216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416223 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 5]
def baseStart_1416223 : Nat := 118140960795 + 1416223 * 2 ^ 59
def prefixEnd_1416223 : Nat := 4983230072969 + 3 ^ 40 * 1416223 * 2
def baseEnd_1416223 : Nat := 727203112952517754699415

theorem tailTrace_1416223 : CollatzResearch.WordTrace tailWord_1416223 prefixEnd_1416223 727203112952517754699415 := by
  unfold tailWord_1416223
  simp only [CollatzResearch.WordTrace]
  refine ⟨51653896348273417477125323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34435930898848944984750215 51653896348273417477125323)
  ·
    refine ⟨77480844522410126215687985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51653896348273417477125323 77480844522410126215687985)
    ·
      refine ⟨58110633391807594661765989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77480844522410126215687985 58110633391807594661765989)
      ·
        refine ⟨10895743760963923999081123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58110633391807594661765989 10895743760963923999081123)
        ·
          refine ⟨16343615641445885998621685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10895743760963923999081123 16343615641445885998621685)
          ·
            refine ⟨1532213966385551812370783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16343615641445885998621685 1532213966385551812370783)
            ·
              refine ⟨2298320949578327718556175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532213966385551812370783 2298320949578327718556175)
              ·
                refine ⟨3447481424367491577834263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298320949578327718556175 3447481424367491577834263)
                ·
                  refine ⟨5171222136551237366751395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3447481424367491577834263 5171222136551237366751395)
                  ·
                    refine ⟨7756833204826856050127093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5171222136551237366751395 7756833204826856050127093)
                    ·
                      refine ⟨727203112952517754699415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7756833204826856050127093 727203112952517754699415)
                      ·
                        rfl

theorem cell23_1416223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_1416223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416223 prefixEnd_1416223 := by exact prefixLift 1416223
  have htrace : WordTrace (prefixWord ++ tailWord_1416223) baseStart_1416223 baseEnd_1416223 := by
    simpa [prefixWord, tailWord_1416223, baseEnd_1416223] using wordTrace_append hprefix tailTrace_1416223
  have hstable : (prefixWord ++ tailWord_1416223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416223).length < 2 ^ (prefixWord ++ tailWord_1416223).sum := by decide
  have hdescent : baseEnd_1416223 < baseStart_1416223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416231 : List Nat := [1, 1, 7, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_1416231 : Nat := 118140960795 + 1416231 * 2 ^ 59
def prefixEnd_1416231 : Nat := 4983230072969 + 3 ^ 40 * 1416231 * 2
def baseEnd_1416231 : Nat := 727207220797753723399379

theorem tailTrace_1416231 : CollatzResearch.WordTrace tailWord_1416231 prefixEnd_1416231 727207220797753723399379 := by
  unfold tailWord_1416231
  simp only [CollatzResearch.WordTrace]
  refine ⟨51654188132244434843416547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34436125421496289895611031 51654188132244434843416547)
  ·
    refine ⟨77481282198366652265124821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51654188132244434843416547 77481282198366652265124821)
    ·
      refine ⟨1815967551524218412463863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 77481282198366652265124821 1815967551524218412463863)
      ·
        refine ⟨2723951327286327618695795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1815967551524218412463863 2723951327286327618695795)
        ·
          refine ⟨4085926990929491428043693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2723951327286327618695795 4085926990929491428043693)
          ·
            refine ⟨1532222621598559285516385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4085926990929491428043693 1532222621598559285516385)
            ·
              refine ⟨1149166966198919464137289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532222621598559285516385 1149166966198919464137289)
              ·
                refine ⟨861875224649189598102967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149166966198919464137289 861875224649189598102967)
                ·
                  refine ⟨1292812836973784397154451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861875224649189598102967 1292812836973784397154451)
                  ·
                    refine ⟨1939219255460676595731677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1292812836973784397154451 1939219255460676595731677)
                    ·
                      refine ⟨727207220797753723399379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1939219255460676595731677 727207220797753723399379)
                      ·
                        rfl

theorem cell23_1416231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_1416231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416231 prefixEnd_1416231 := by exact prefixLift 1416231
  have htrace : WordTrace (prefixWord ++ tailWord_1416231) baseStart_1416231 baseEnd_1416231 := by
    simpa [prefixWord, tailWord_1416231, baseEnd_1416231] using wordTrace_append hprefix tailTrace_1416231
  have hstable : (prefixWord ++ tailWord_1416231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416231).length < 2 ^ (prefixWord ++ tailWord_1416231).sum := by decide
  have hdescent : baseEnd_1416231 < baseStart_1416231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416236 : List Nat := [2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 3]
def baseStart_1416236 : Nat := 118140960795 + 1416236 * 2 ^ 59
def prefixEnd_1416236 : Nat := 4983230072969 + 3 ^ 40 * 1416236 * 2
def baseEnd_1416236 : Nat := 727209788201026203836855

theorem tailTrace_1416236 : CollatzResearch.WordTrace tailWord_1416236 prefixEnd_1416236 727209788201026203836855 := by
  unfold tailWord_1416236
  simp only [CollatzResearch.WordTrace]
  refine ⟨25827185248613160348674281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34436246998150880464899041 25827185248613160348674281)
  ·
    refine ⟨19370388936459870261505711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25827185248613160348674281 19370388936459870261505711)
    ·
      refine ⟨29055583404689805392258567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19370388936459870261505711 29055583404689805392258567)
      ·
        refine ⟨43583375107034708088387851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29055583404689805392258567 43583375107034708088387851)
        ·
          refine ⟨65375062660552062132581777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43583375107034708088387851 65375062660552062132581777)
          ·
            refine ⟨49031296995414046599436333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65375062660552062132581777 49031296995414046599436333)
            ·
              refine ⟨18386736373280267474788625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49031296995414046599436333 18386736373280267474788625)
              ·
                refine ⟨13790052279960200606091469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18386736373280267474788625 13790052279960200606091469)
                ·
                  refine ⟨5171269604985075227284301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13790052279960200606091469 5171269604985075227284301)
                  ·
                    refine ⟨1939226101869403210231613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5171269604985075227284301 1939226101869403210231613)
                    ·
                      refine ⟨727209788201026203836855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1939226101869403210231613 727209788201026203836855)
                      ·
                        rfl

theorem cell23_1416236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_1416236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416236 prefixEnd_1416236 := by exact prefixLift 1416236
  have htrace : WordTrace (prefixWord ++ tailWord_1416236) baseStart_1416236 baseEnd_1416236 := by
    simpa [prefixWord, tailWord_1416236, baseEnd_1416236] using wordTrace_append hprefix tailTrace_1416236
  have hstable : (prefixWord ++ tailWord_1416236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416236).length < 2 ^ (prefixWord ++ tailWord_1416236).sum := by decide
  have hdescent : baseEnd_1416236 < baseStart_1416236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416253 : List Nat := [1, 4, 1, 3, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1416253 : Nat := 118140960795 + 1416253 * 2 ^ 59
def prefixEnd_1416253 : Nat := 4983230072969 + 3 ^ 40 * 1416253 * 2
def baseEnd_1416253 : Nat := 727218517372152637324277

theorem tailTrace_1416253 : CollatzResearch.WordTrace tailWord_1416253 prefixEnd_1416253 727218517372152637324277 := by
  unfold tailWord_1416253
  simp only [CollatzResearch.WordTrace]
  refine ⟨51654990538164732600717413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34436660358776488400478275 51654990538164732600717413)
  ·
    refine ⟨9685310725905887362634515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51654990538164732600717413 9685310725905887362634515)
    ·
      refine ⟨14527966088858831043951773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9685310725905887362634515 14527966088858831043951773)
      ·
        refine ⟨5447987283322061641481915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14527966088858831043951773 5447987283322061641481915)
        ·
          refine ⟨8171980924983092462222873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5447987283322061641481915 8171980924983092462222873)
          ·
            refine ⟨6128985693737319346667155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8171980924983092462222873 6128985693737319346667155)
            ·
              refine ⟨9193478540605979020000733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6128985693737319346667155 9193478540605979020000733)
              ·
                refine ⟨3447554452727242132500275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9193478540605979020000733 3447554452727242132500275)
                ·
                  refine ⟨5171331679090863198750413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3447554452727242132500275 5171331679090863198750413)
                  ·
                    refine ⟨1939249379659073699531405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5171331679090863198750413 1939249379659073699531405)
                    ·
                      refine ⟨727218517372152637324277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1939249379659073699531405 727218517372152637324277)
                      ·
                        rfl

theorem cell23_1416253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1416253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416253 prefixEnd_1416253 := by exact prefixLift 1416253
  have htrace : WordTrace (prefixWord ++ tailWord_1416253) baseStart_1416253 baseEnd_1416253 := by
    simpa [prefixWord, tailWord_1416253, baseEnd_1416253] using wordTrace_append hprefix tailTrace_1416253
  have hstable : (prefixWord ++ tailWord_1416253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416253).length < 2 ^ (prefixWord ++ tailWord_1416253).sum := by decide
  have hdescent : baseEnd_1416253 < baseStart_1416253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416280 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 1, 3, 2]
def baseStart_1416280 : Nat := 118140960795 + 1416280 * 2 ^ 59
def prefixEnd_1416280 : Nat := 4983230072969 + 3 ^ 40 * 1416280 * 2
def baseEnd_1416280 : Nat := 727232381349824031686653

theorem tailTrace_1416280 : CollatzResearch.WordTrace tailWord_1416280 prefixEnd_1416280 727232381349824031686653 := by
  unfold tailWord_1416280
  simp only [CollatzResearch.WordTrace]
  refine ⟨25827987654533458105975147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34437316872711277474633529 25827987654533458105975147)
  ·
    refine ⟨38741981481800187158962721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25827987654533458105975147 38741981481800187158962721)
    ·
      refine ⟨29056486111350140369222041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38741981481800187158962721 29056486111350140369222041)
      ·
        refine ⟨21792364583512605276916531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29056486111350140369222041 21792364583512605276916531)
        ·
          refine ⟨32688546875268907915374797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21792364583512605276916531 32688546875268907915374797)
          ·
            refine ⟨12258205078225840468265549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32688546875268907915374797 12258205078225840468265549)
            ·
              refine ⟨4596826904334690175599581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12258205078225840468265549 4596826904334690175599581)
              ·
                refine ⟨1723810089125508815849843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4596826904334690175599581 1723810089125508815849843)
                ·
                  refine ⟨2585715133688263223774765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1723810089125508815849843 2585715133688263223774765)
                  ·
                    refine ⟨969643175133098708915537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2585715133688263223774765 969643175133098708915537)
                    ·
                      refine ⟨727232381349824031686653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 969643175133098708915537 727232381349824031686653)
                      ·
                        rfl

theorem cell23_1416280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_1416280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416280 prefixEnd_1416280 := by exact prefixLift 1416280
  have htrace : WordTrace (prefixWord ++ tailWord_1416280) baseStart_1416280 baseEnd_1416280 := by
    simpa [prefixWord, tailWord_1416280, baseEnd_1416280] using wordTrace_append hprefix tailTrace_1416280
  have hstable : (prefixWord ++ tailWord_1416280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416280).length < 2 ^ (prefixWord ++ tailWord_1416280).sum := by decide
  have hdescent : baseEnd_1416280 < baseStart_1416280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416316 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 7]
def baseStart_1416316 : Nat := 118140960795 + 1416316 * 2 ^ 59
def prefixEnd_1416316 : Nat := 4983230072969 + 3 ^ 40 * 1416316 * 2
def baseEnd_1416316 : Nat := 80805651850376210092943

theorem tailTrace_1416316 : CollatzResearch.WordTrace tailWord_1416316 prefixEnd_1416316 80805651850376210092943 := by
  unfold tailWord_1416316
  simp only [CollatzResearch.WordTrace]
  refine ⟨25828644168468247180130401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34438192224624329573507201 25828644168468247180130401)
  ·
    refine ⟨19371483126351185385097801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25828644168468247180130401 19371483126351185385097801)
    ·
      refine ⟨14528612344763389038823351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19371483126351185385097801 14528612344763389038823351)
      ·
        refine ⟨21792918517145083558235027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14528612344763389038823351 21792918517145083558235027)
        ·
          refine ⟨32689377775717625337352541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21792918517145083558235027 32689377775717625337352541)
          ·
            refine ⟨12258516665894109501507203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32689377775717625337352541 12258516665894109501507203)
            ·
              refine ⟨18387774998841164252260805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12258516665894109501507203 18387774998841164252260805)
              ·
                refine ⟨3447707812282718297298901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18387774998841164252260805 3447707812282718297298901)
                ·
                  refine ⟨80805651850376210092943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3447707812282718297298901 80805651850376210092943)
                  ·
                    rfl

theorem cell23_1416316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 7].length) (baseStart_1416316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416316 prefixEnd_1416316 := by exact prefixLift 1416316
  have htrace : WordTrace (prefixWord ++ tailWord_1416316) baseStart_1416316 baseEnd_1416316 := by
    simpa [prefixWord, tailWord_1416316, baseEnd_1416316] using wordTrace_append hprefix tailTrace_1416316
  have hstable : (prefixWord ++ tailWord_1416316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416316).length < 2 ^ (prefixWord ++ tailWord_1416316).sum := by decide
  have hdescent : baseEnd_1416316 < baseStart_1416316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416350 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_1416350 : Nat := 118140960795 + 1416350 * 2 ^ 59
def prefixEnd_1416350 : Nat := 4983230072969 + 3 ^ 40 * 1416350 * 2
def baseEnd_1416350 : Nat := 80807591666182084201259

theorem tailTrace_1416350 : CollatzResearch.WordTrace tailWord_1416350 prefixEnd_1416350 80807591666182084201259 := by
  unfold tailWord_1416350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6457316052351664770874813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34439018945875545444665669 6457316052351664770874813)
  ·
    refine ⟨2421493519631874289078055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6457316052351664770874813 2421493519631874289078055)
    ·
      refine ⟨3632240279447811433617083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2421493519631874289078055 3632240279447811433617083)
      ·
        refine ⟨5448360419171717150425625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3632240279447811433617083 5448360419171717150425625)
        ·
          refine ⟨4086270314378787862819219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5448360419171717150425625 4086270314378787862819219)
          ·
            refine ⟨6129405471568181794228829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086270314378787862819219 6129405471568181794228829)
            ·
              refine ⟨2298527051838068172835811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6129405471568181794228829 2298527051838068172835811)
              ·
                refine ⟨3447790577757102259253717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298527051838068172835811 3447790577757102259253717)
                ·
                  refine ⟨80807591666182084201259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3447790577757102259253717 80807591666182084201259)
                  ·
                    rfl

theorem cell23_1416350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_1416350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416350 prefixEnd_1416350 := by exact prefixLift 1416350
  have htrace : WordTrace (prefixWord ++ tailWord_1416350) baseStart_1416350 baseEnd_1416350 := by
    simpa [prefixWord, tailWord_1416350, baseEnd_1416350] using wordTrace_append hprefix tailTrace_1416350
  have hstable : (prefixWord ++ tailWord_1416350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416350).length < 2 ^ (prefixWord ++ tailWord_1416350).sum := by decide
  have hdescent : baseEnd_1416350 < baseStart_1416350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416380 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 2, 5]
def baseStart_1416380 : Nat := 118140960795 + 1416380 * 2 ^ 59
def prefixEnd_1416380 : Nat := 4983230072969 + 3 ^ 40 * 1416380 * 2
def baseEnd_1416380 : Nat := 242427909805091213478731

theorem tailTrace_1416380 : CollatzResearch.WordTrace tailWord_1416380 prefixEnd_1416380 242427909805091213478731 := by
  unfold tailWord_1416380
  simp only [CollatzResearch.WordTrace]
  refine ⟨25829811304352316645295297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34439748405803088860393729 25829811304352316645295297)
  ·
    refine ⟨19372358478264237483971473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25829811304352316645295297 19372358478264237483971473)
    ·
      refine ⟨14529268858698178112978605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19372358478264237483971473 14529268858698178112978605)
      ·
        refine ⟨5448475822011816792366977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14529268858698178112978605 5448475822011816792366977)
        ·
          refine ⟨4086356866508862594275233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5448475822011816792366977 4086356866508862594275233)
          ·
            refine ⟨3064767649881646945706425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4086356866508862594275233 3064767649881646945706425)
            ·
              refine ⟨2298575737411235209279819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3064767649881646945706425 2298575737411235209279819)
              ·
                refine ⟨3447863606116852813919729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298575737411235209279819 3447863606116852813919729)
                ·
                  refine ⟨2585897704587639610439797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3447863606116852813919729 2585897704587639610439797)
                  ·
                    refine ⟨242427909805091213478731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2585897704587639610439797 242427909805091213478731)
                    ·
                      rfl

theorem cell23_1416380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_1416380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416380 prefixEnd_1416380 := by exact prefixLift 1416380
  have htrace : WordTrace (prefixWord ++ tailWord_1416380) baseStart_1416380 baseEnd_1416380 := by
    simpa [prefixWord, tailWord_1416380, baseEnd_1416380] using wordTrace_append hprefix tailTrace_1416380
  have hstable : (prefixWord ++ tailWord_1416380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416380).length < 2 ^ (prefixWord ++ tailWord_1416380).sum := by decide
  have hdescent : baseEnd_1416380 < baseStart_1416380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416383 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 4]
def baseStart_1416383 : Nat := 118140960795 + 1416383 * 2 ^ 59
def prefixEnd_1416383 : Nat := 4983230072969 + 3 ^ 40 * 1416383 * 2
def baseEnd_1416383 : Nat := 727285269857237128698679

theorem tailTrace_1416383 : CollatzResearch.WordTrace tailWord_1416383 prefixEnd_1416383 727285269857237128698679 := by
  unfold tailWord_1416383
  simp only [CollatzResearch.WordTrace]
  refine ⟨51659732027693764802949803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34439821351795843201966535 51659732027693764802949803)
  ·
    refine ⟨77489598041540647204424705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51659732027693764802949803 77489598041540647204424705)
    ·
      refine ⟨58117198531155485403318529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77489598041540647204424705 58117198531155485403318529)
      ·
        refine ⟨43587898898366614052488897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58117198531155485403318529 43587898898366614052488897)
        ·
          refine ⟨32690924173774960539366673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43587898898366614052488897 32690924173774960539366673)
          ·
            refine ⟨24518193130331220404525005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32690924173774960539366673 24518193130331220404525005)
            ·
              refine ⟨9194322423874207651696877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24518193130331220404525005 9194322423874207651696877)
              ·
                refine ⟨3447870908952827869386329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9194322423874207651696877 3447870908952827869386329)
                ·
                  refine ⟨2585903181714620902039747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3447870908952827869386329 2585903181714620902039747)
                  ·
                    refine ⟨3878854772571931353059621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2585903181714620902039747 3878854772571931353059621)
                    ·
                      refine ⟨727285269857237128698679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3878854772571931353059621 727285269857237128698679)
                      ·
                        rfl

theorem cell23_1416383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_1416383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416383 prefixEnd_1416383 := by exact prefixLift 1416383
  have htrace : WordTrace (prefixWord ++ tailWord_1416383) baseStart_1416383 baseEnd_1416383 := by
    simpa [prefixWord, tailWord_1416383, baseEnd_1416383] using wordTrace_append hprefix tailTrace_1416383
  have hstable : (prefixWord ++ tailWord_1416383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416383).length < 2 ^ (prefixWord ++ tailWord_1416383).sum := by decide
  have hdescent : baseEnd_1416383 < baseStart_1416383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416434 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 2, 1, 4]
def baseStart_1416434 : Nat := 118140960795 + 1416434 * 2 ^ 59
def prefixEnd_1416434 : Nat := 4983230072969 + 3 ^ 40 * 1416434 * 2
def baseEnd_1416434 : Nat := 727311457370616429160945

theorem tailTrace_1416434 : CollatzResearch.WordTrace tailWord_1416434 prefixEnd_1416434 727311457370616429160945 := by
  unfold tailWord_1416434
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915398037627250128264089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34441061433672667008704237 12915398037627250128264089)
  ·
    refine ⟨9686548528220437596198067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12915398037627250128264089 9686548528220437596198067)
    ·
      refine ⟨14529822792330656394297101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9686548528220437596198067 14529822792330656394297101)
      ·
        refine ⟨5448683547123996147861413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14529822792330656394297101 5448683547123996147861413)
        ·
          refine ⟨1021628165085749277724015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5448683547123996147861413 1021628165085749277724015)
          ·
            refine ⟨1532442247628623916586023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021628165085749277724015 1532442247628623916586023)
            ·
              refine ⟨2298663371442935874879035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532442247628623916586023 2298663371442935874879035)
              ·
                refine ⟨3447995057164403812318553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298663371442935874879035 3447995057164403812318553)
                ·
                  refine ⟨2585996292873302859238915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3447995057164403812318553 2585996292873302859238915)
                  ·
                    refine ⟨3878994439309954288858373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2585996292873302859238915 3878994439309954288858373)
                    ·
                      refine ⟨727311457370616429160945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3878994439309954288858373 727311457370616429160945)
                      ·
                        rfl

theorem cell23_1416434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_1416434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416434 prefixEnd_1416434 := by exact prefixLift 1416434
  have htrace : WordTrace (prefixWord ++ tailWord_1416434) baseStart_1416434 baseEnd_1416434 := by
    simpa [prefixWord, tailWord_1416434, baseEnd_1416434] using wordTrace_append hprefix tailTrace_1416434
  have hstable : (prefixWord ++ tailWord_1416434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416434).length < 2 ^ (prefixWord ++ tailWord_1416434).sum := by decide
  have hdescent : baseEnd_1416434 < baseStart_1416434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416444 : List Nat := [2, 2, 2, 1, 5, 1, 2, 3, 1, 4]
def baseStart_1416444 : Nat := 118140960795 + 1416444 * 2 ^ 59
def prefixEnd_1416444 : Nat := 4983230072969 + 3 ^ 40 * 1416444 * 2
def baseEnd_1416444 : Nat := 242438864059053796678633

theorem tailTrace_1416444 : CollatzResearch.WordTrace tailWord_1416444 prefixEnd_1416444 242438864059053796678633 := by
  unfold tailWord_1416444
  simp only [CollatzResearch.WordTrace]
  refine ⟨25830978440236386110460193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34441304586981848147280257 25830978440236386110460193)
  ·
    refine ⟨19373233830177289582845145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25830978440236386110460193 19373233830177289582845145)
    ·
      refine ⟨14529925372632967187133859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19373233830177289582845145 14529925372632967187133859)
      ·
        refine ⟨21794888058949450780700789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14529925372632967187133859 21794888058949450780700789)
        ·
          refine ⟨2043270755526511010690699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21794888058949450780700789 2043270755526511010690699)
          ·
            refine ⟨3064906133289766516036049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043270755526511010690699 3064906133289766516036049)
            ·
              refine ⟨2298679599967324887027037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3064906133289766516036049 2298679599967324887027037)
              ·
                refine ⟨862004849987746832635139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2298679599967324887027037 862004849987746832635139)
                ·
                  refine ⟨1293007274981620248952709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862004849987746832635139 1293007274981620248952709)
                  ·
                    refine ⟨242438864059053796678633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1293007274981620248952709 242438864059053796678633)
                    ·
                      rfl

theorem cell23_1416444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_1416444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416444 prefixEnd_1416444 := by exact prefixLift 1416444
  have htrace : WordTrace (prefixWord ++ tailWord_1416444) baseStart_1416444 baseEnd_1416444 := by
    simpa [prefixWord, tailWord_1416444, baseEnd_1416444] using wordTrace_append hprefix tailTrace_1416444
  have hstable : (prefixWord ++ tailWord_1416444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416444).length < 2 ^ (prefixWord ++ tailWord_1416444).sum := by decide
  have hdescent : baseEnd_1416444 < baseStart_1416444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416477 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_1416477 : Nat := 118140960795 + 1416477 * 2 ^ 59
def prefixEnd_1416477 : Nat := 4983230072969 + 3 ^ 40 * 1416477 * 2
def baseEnd_1416477 : Nat := 727333537038759760923247

theorem tailTrace_1416477 : CollatzResearch.WordTrace tailWord_1416477 prefixEnd_1416477 727333537038759760923247 := by
  unfold tailWord_1416477
  simp only [CollatzResearch.WordTrace]
  refine ⟨51663160489353218856871685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34442106992902145904581123 51663160489353218856871685)
  ·
    refine ⟨9686842591753728535663441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51663160489353218856871685 9686842591753728535663441)
    ·
      refine ⟨7265131943815296401747581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9686842591753728535663441 7265131943815296401747581)
      ·
        refine ⟨2724424478930736150655343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7265131943815296401747581 2724424478930736150655343)
        ·
          refine ⟨4086636718396104225983015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2724424478930736150655343 4086636718396104225983015)
          ·
            refine ⟨6129955077594156338974523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4086636718396104225983015 6129955077594156338974523)
            ·
              refine ⟨9194932616391234508461785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6129955077594156338974523 9194932616391234508461785)
              ·
                refine ⟨6896199462293425881346339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9194932616391234508461785 6896199462293425881346339)
                ·
                  refine ⟨10344299193440138822019509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6896199462293425881346339 10344299193440138822019509)
                  ·
                    refine ⟨969778049385013014564329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10344299193440138822019509 969778049385013014564329)
                    ·
                      refine ⟨727333537038759760923247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 969778049385013014564329 727333537038759760923247)
                      ·
                        rfl

theorem cell23_1416477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_1416477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416477 prefixEnd_1416477 := by exact prefixLift 1416477
  have htrace : WordTrace (prefixWord ++ tailWord_1416477) baseStart_1416477 baseEnd_1416477 := by
    simpa [prefixWord, tailWord_1416477, baseEnd_1416477] using wordTrace_append hprefix tailTrace_1416477
  have hstable : (prefixWord ++ tailWord_1416477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416477).length < 2 ^ (prefixWord ++ tailWord_1416477).sum := by decide
  have hdescent : baseEnd_1416477 < baseStart_1416477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416500 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_1416500 : Nat := 118140960795 + 1416500 * 2 ^ 59
def prefixEnd_1416500 : Nat := 4983230072969 + 3 ^ 40 * 1416500 * 2
def baseEnd_1416500 : Nat := 242448449031271056978547

theorem tailTrace_1416500 : CollatzResearch.WordTrace tailWord_1416500 prefixEnd_1416500 242448449031271056978547 := by
  unfold tailWord_1416500
  simp only [CollatzResearch.WordTrace]
  refine ⟨25831999684134946892479477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34442666245513262523305969 25831999684134946892479477)
  ·
    refine ⟨2421749970387651271169951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25831999684134946892479477 2421749970387651271169951)
    ·
      refine ⟨3632624955581476906754927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2421749970387651271169951 3632624955581476906754927)
      ·
        refine ⟨5448937433372215360132391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3632624955581476906754927 5448937433372215360132391)
        ·
          refine ⟨8173406150058323040198587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5448937433372215360132391 8173406150058323040198587)
          ·
            refine ⟨12260109225087484560297881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8173406150058323040198587 12260109225087484560297881)
            ·
              refine ⟨9195081918815613420223411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12260109225087484560297881 9195081918815613420223411)
              ·
                refine ⟨13792622878223420130335117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9195081918815613420223411 13792622878223420130335117)
                ·
                  refine ⟨5172233579333782548875669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13792622878223420130335117 5172233579333782548875669)
                  ·
                    refine ⟨242448449031271056978547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5172233579333782548875669 242448449031271056978547)
                    ·
                      rfl

theorem cell23_1416500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_1416500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416500 prefixEnd_1416500 := by exact prefixLift 1416500
  have htrace : WordTrace (prefixWord ++ tailWord_1416500) baseStart_1416500 baseEnd_1416500 := by
    simpa [prefixWord, tailWord_1416500, baseEnd_1416500] using wordTrace_append hprefix tailTrace_1416500
  have hstable : (prefixWord ++ tailWord_1416500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416500).length < 2 ^ (prefixWord ++ tailWord_1416500).sum := by decide
  have hdescent : baseEnd_1416500 < baseStart_1416500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416501 : List Nat := [1, 3, 3, 1, 2, 4, 1, 3, 1, 1, 3]
def baseStart_1416501 : Nat := 118140960795 + 1416501 * 2 ^ 59
def prefixEnd_1416501 : Nat := 4983230072969 + 3 ^ 40 * 1416501 * 2
def baseEnd_1416501 : Nat := 727345860574467667023137

theorem tailTrace_1416501 : CollatzResearch.WordTrace tailWord_1416501 prefixEnd_1416501 727345860574467667023137 := by
  unfold tailWord_1416501
  simp only [CollatzResearch.WordTrace]
  refine ⟨51664035841266270955745357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34442690560844180637163571 51664035841266270955745357)
  ·
    refine ⟨19374013440474851608404509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51664035841266270955745357 19374013440474851608404509)
    ·
      refine ⟨7265255040178069353151691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19374013440474851608404509 7265255040178069353151691)
      ·
        refine ⟨10897882560267104029727537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7265255040178069353151691 10897882560267104029727537)
        ·
          refine ⟨8173411920200328022295653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10897882560267104029727537 8173411920200328022295653)
          ·
            refine ⟨1532514735037561504180435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8173411920200328022295653 1532514735037561504180435)
            ·
              refine ⟨2298772102556342256270653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532514735037561504180435 2298772102556342256270653)
              ·
                refine ⟨862039538458628346101495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2298772102556342256270653 862039538458628346101495)
                ·
                  refine ⟨1293059307687942519152243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862039538458628346101495 1293059307687942519152243)
                  ·
                    refine ⟨1939588961531913778728365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1293059307687942519152243 1939588961531913778728365)
                    ·
                      refine ⟨727345860574467667023137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1939588961531913778728365 727345860574467667023137)
                      ·
                        rfl

theorem cell23_1416501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_1416501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416501 prefixEnd_1416501 := by exact prefixLift 1416501
  have htrace : WordTrace (prefixWord ++ tailWord_1416501) baseStart_1416501 baseEnd_1416501 := by
    simpa [prefixWord, tailWord_1416501, baseEnd_1416501] using wordTrace_append hprefix tailTrace_1416501
  have hstable : (prefixWord ++ tailWord_1416501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416501).length < 2 ^ (prefixWord ++ tailWord_1416501).sum := by decide
  have hdescent : baseEnd_1416501 < baseStart_1416501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416524 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 3, 2, 2]
def baseStart_1416524 : Nat := 118140960795 + 1416524 * 2 ^ 59
def prefixEnd_1416524 : Nat := 4983230072969 + 3 ^ 40 * 1416524 * 2
def baseEnd_1416524 : Nat := 727357670629521077035531

theorem tailTrace_1416524 : CollatzResearch.WordTrace tailWord_1416524 prefixEnd_1416524 727357670629521077035531 := by
  unfold tailWord_1416524
  simp only [CollatzResearch.WordTrace]
  refine ⟨25832437360091472941916313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34443249813455297255888417 25832437360091472941916313)
  ·
    refine ⟨19374328020068604706437235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25832437360091472941916313 19374328020068604706437235)
    ·
      refine ⟨29061492030102907059655853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19374328020068604706437235 29061492030102907059655853)
      ·
        refine ⟨10898059511288590147370945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29061492030102907059655853 10898059511288590147370945)
        ·
          refine ⟨8173544633466442610528209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10898059511288590147370945 8173544633466442610528209)
          ·
            refine ⟨6130158475099831957896157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8173544633466442610528209 6130158475099831957896157)
            ·
              refine ⟨2298809428162436984211059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6130158475099831957896157 2298809428162436984211059)
              ·
                refine ⟨3448214142243655476316589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298809428162436984211059 3448214142243655476316589)
                ·
                  refine ⟨1293080303341370803618721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3448214142243655476316589 1293080303341370803618721)
                  ·
                    refine ⟨969810227506028102714041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1293080303341370803618721 969810227506028102714041)
                    ·
                      refine ⟨727357670629521077035531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 969810227506028102714041 727357670629521077035531)
                      ·
                        rfl

theorem cell23_1416524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_1416524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416524 prefixEnd_1416524 := by exact prefixLift 1416524
  have htrace : WordTrace (prefixWord ++ tailWord_1416524) baseStart_1416524 baseEnd_1416524 := by
    simpa [prefixWord, tailWord_1416524, baseEnd_1416524] using wordTrace_append hprefix tailTrace_1416524
  have hstable : (prefixWord ++ tailWord_1416524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416524).length < 2 ^ (prefixWord ++ tailWord_1416524).sum := by decide
  have hdescent : baseEnd_1416524 < baseStart_1416524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416541 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1416541 : Nat := 118140960795 + 1416541 * 2 ^ 59
def prefixEnd_1416541 : Nat := 4983230072969 + 3 ^ 40 * 1416541 * 2
def baseEnd_1416541 : Nat := 727366399800647510522953

theorem tailTrace_1416541 : CollatzResearch.WordTrace tailWord_1416541 prefixEnd_1416541 727366399800647510522953 := by
  unfold tailWord_1416541
  simp only [CollatzResearch.WordTrace]
  refine ⟨51665494761121357787201477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34443663174080905191467651 51665494761121357787201477)
  ·
    refine ⟨9687280267710254585100277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51665494761121357787201477 9687280267710254585100277)
    ·
      refine ⟨908182525097836367353151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9687280267710254585100277 908182525097836367353151)
      ·
        refine ⟨1362273787646754551029727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908182525097836367353151 1362273787646754551029727)
        ·
          refine ⟨2043410681470131826544591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362273787646754551029727 2043410681470131826544591)
          ·
            refine ⟨3065116022205197739816887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043410681470131826544591 3065116022205197739816887)
            ·
              refine ⟨4597674033307796609725331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3065116022205197739816887 4597674033307796609725331)
              ·
                refine ⟨6896511049961694914587997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4597674033307796609725331 6896511049961694914587997)
                ·
                  refine ⟨2586191643735635592970499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6896511049961694914587997 2586191643735635592970499)
                  ·
                    refine ⟨3879287465603453389455749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2586191643735635592970499 3879287465603453389455749)
                    ·
                      refine ⟨727366399800647510522953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3879287465603453389455749 727366399800647510522953)
                      ·
                        rfl

theorem cell23_1416541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1416541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416541 prefixEnd_1416541 := by exact prefixLift 1416541
  have htrace : WordTrace (prefixWord ++ tailWord_1416541) baseStart_1416541 baseEnd_1416541 := by
    simpa [prefixWord, tailWord_1416541, baseEnd_1416541] using wordTrace_append hprefix tailTrace_1416541
  have hstable : (prefixWord ++ tailWord_1416541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416541).length < 2 ^ (prefixWord ++ tailWord_1416541).sum := by decide
  have hdescent : baseEnd_1416541 < baseStart_1416541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416544 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 3]
def baseStart_1416544 : Nat := 118140960795 + 1416544 * 2 ^ 59
def prefixEnd_1416544 : Nat := 4983230072969 + 3 ^ 40 * 1416544 * 2
def baseEnd_1416544 : Nat := 727367940242610998785439

theorem tailTrace_1416544 : CollatzResearch.WordTrace tailWord_1416544 prefixEnd_1416544 727367940242610998785439 := by
  unfold tailWord_1416544
  simp only [CollatzResearch.WordTrace]
  refine ⟨25832802090055244649780343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34443736120073659533040457 25832802090055244649780343)
  ·
    refine ⟨38749203135082866974670515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25832802090055244649780343 38749203135082866974670515)
    ·
      refine ⟨58123804702624300462005773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38749203135082866974670515 58123804702624300462005773)
      ·
        refine ⟨21796426763484112673252165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58123804702624300462005773 21796426763484112673252165)
        ·
          refine ⟨4086830018153271126234781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21796426763484112673252165 4086830018153271126234781)
          ·
            refine ⟨1532561256807476672338043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4086830018153271126234781 1532561256807476672338043)
            ·
              refine ⟨2298841885211215008507065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532561256807476672338043 2298841885211215008507065)
              ·
                refine ⟨1724131413908411256380299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2298841885211215008507065 1724131413908411256380299)
                ·
                  refine ⟨2586197120862616884570449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724131413908411256380299 2586197120862616884570449)
                  ·
                    refine ⟨1939647840646962663427837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2586197120862616884570449 1939647840646962663427837)
                    ·
                      refine ⟨727367940242610998785439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1939647840646962663427837 727367940242610998785439)
                      ·
                        rfl

theorem cell23_1416544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_1416544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416544 prefixEnd_1416544 := by exact prefixLift 1416544
  have htrace : WordTrace (prefixWord ++ tailWord_1416544) baseStart_1416544 baseEnd_1416544 := by
    simpa [prefixWord, tailWord_1416544, baseEnd_1416544] using wordTrace_append hprefix tailTrace_1416544
  have hstable : (prefixWord ++ tailWord_1416544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416544).length < 2 ^ (prefixWord ++ tailWord_1416544).sum := by decide
  have hdescent : baseEnd_1416544 < baseStart_1416544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416553 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_1416553 : Nat := 118140960795 + 1416553 * 2 ^ 59
def prefixEnd_1416553 : Nat := 4983230072969 + 3 ^ 40 * 1416553 * 2
def baseEnd_1416553 : Nat := 727372561568501463572897

theorem tailTrace_1416553 : CollatzResearch.WordTrace tailWord_1416553 prefixEnd_1416553 727372561568501463572897 := by
  unfold tailWord_1416553
  simp only [CollatzResearch.WordTrace]
  refine ⟨51665932437077883836638313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34443954958051922557758875 51665932437077883836638313)
  ·
    refine ⟨38749449327808412877478735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51665932437077883836638313 38749449327808412877478735)
    ·
      refine ⟨58124173991712619316218103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38749449327808412877478735 58124173991712619316218103)
      ·
        refine ⟨87186260987568928974327155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58124173991712619316218103 87186260987568928974327155)
        ·
          refine ⟨130779391481353393461490733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87186260987568928974327155 130779391481353393461490733)
          ·
            refine ⟨49042271805507522548059025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130779391481353393461490733 49042271805507522548059025)
            ·
              refine ⟨36781703854130641911044269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49042271805507522548059025 36781703854130641911044269)
              ·
                refine ⟨13793138945298990716641601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36781703854130641911044269 13793138945298990716641601)
                ·
                  refine ⟨10344854208974243037481201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13793138945298990716641601 10344854208974243037481201)
                  ·
                    refine ⟨7758640656730682278110901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10344854208974243037481201 7758640656730682278110901)
                    ·
                      refine ⟨727372561568501463572897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7758640656730682278110901 727372561568501463572897)
                      ·
                        rfl

theorem cell23_1416553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_1416553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416553 prefixEnd_1416553 := by exact prefixLift 1416553
  have htrace : WordTrace (prefixWord ++ tailWord_1416553) baseStart_1416553 baseEnd_1416553 := by
    simpa [prefixWord, tailWord_1416553, baseEnd_1416553] using wordTrace_append hprefix tailTrace_1416553
  have hstable : (prefixWord ++ tailWord_1416553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416553).length < 2 ^ (prefixWord ++ tailWord_1416553).sum := by decide
  have hdescent : baseEnd_1416553 < baseStart_1416553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416557 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_1416557 : Nat := 118140960795 + 1416557 * 2 ^ 59
def prefixEnd_1416557 : Nat := 4983230072969 + 3 ^ 40 * 1416557 * 2
def baseEnd_1416557 : Nat := 727374615491119447922879

theorem tailTrace_1416557 : CollatzResearch.WordTrace tailWord_1416557 prefixEnd_1416557 727374615491119447922879 := by
  unfold tailWord_1416557
  simp only [CollatzResearch.WordTrace]
  refine ⟨51666078329063392519783925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34444052219375595013189283 51666078329063392519783925)
  ·
    refine ⟨4843694843349693048729743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51666078329063392519783925 4843694843349693048729743)
    ·
      refine ⟨7265542265024539573094615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4843694843349693048729743 7265542265024539573094615)
      ·
        refine ⟨10898313397536809359641923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7265542265024539573094615 10898313397536809359641923)
        ·
          refine ⟨16347470096305214039462885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10898313397536809359641923 16347470096305214039462885)
          ·
            refine ⟨3065150643057227632399291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16347470096305214039462885 3065150643057227632399291)
            ·
              refine ⟨4597725964585841448598937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3065150643057227632399291 4597725964585841448598937)
              ·
                refine ⟨3448294473439381086449203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4597725964585841448598937 3448294473439381086449203)
                ·
                  refine ⟨5172441710159071629673805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448294473439381086449203 5172441710159071629673805)
                  ·
                    refine ⟨1939665641309651861127677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5172441710159071629673805 1939665641309651861127677)
                    ·
                      refine ⟨727374615491119447922879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1939665641309651861127677 727374615491119447922879)
                      ·
                        rfl

theorem cell23_1416557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_1416557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416557 prefixEnd_1416557 := by exact prefixLift 1416557
  have htrace : WordTrace (prefixWord ++ tailWord_1416557) baseStart_1416557 baseEnd_1416557 := by
    simpa [prefixWord, tailWord_1416557, baseEnd_1416557] using wordTrace_append hprefix tailTrace_1416557
  have hstable : (prefixWord ++ tailWord_1416557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416557).length < 2 ^ (prefixWord ++ tailWord_1416557).sum := by decide
  have hdescent : baseEnd_1416557 < baseStart_1416557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416563 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 4]
def baseStart_1416563 : Nat := 118140960795 + 1416563 * 2 ^ 59
def prefixEnd_1416563 : Nat := 4983230072969 + 3 ^ 40 * 1416563 * 2
def baseEnd_1416563 : Nat := 727377696375046424447851

theorem tailTrace_1416563 : CollatzResearch.WordTrace tailWord_1416563 prefixEnd_1416563 727377696375046424447851 := by
  unfold tailWord_1416563
  simp only [CollatzResearch.WordTrace]
  refine ⟨51666297167041655544502343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34444198111361103696334895 51666297167041655544502343)
  ·
    refine ⟨77499445750562483316753515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51666297167041655544502343 77499445750562483316753515)
    ·
      refine ⟨116249168625843724975130273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77499445750562483316753515 116249168625843724975130273)
      ·
        refine ⟨87186876469382793731347705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116249168625843724975130273 87186876469382793731347705)
        ·
          refine ⟨65390157352037095298510779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87186876469382793731347705 65390157352037095298510779)
          ·
            refine ⟨98085236028055642947766169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65390157352037095298510779 98085236028055642947766169)
            ·
              refine ⟨73563927021041732210824627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98085236028055642947766169 73563927021041732210824627)
              ·
                refine ⟨110345890531562598316236941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73563927021041732210824627 110345890531562598316236941)
                ·
                  refine ⟨41379708949335974368588853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110345890531562598316236941 41379708949335974368588853)
                  ·
                    refine ⟨3879347714000247597055205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41379708949335974368588853 3879347714000247597055205)
                    ·
                      refine ⟨727377696375046424447851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3879347714000247597055205 727377696375046424447851)
                      ·
                        rfl

theorem cell23_1416563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_1416563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416563 prefixEnd_1416563 := by exact prefixLift 1416563
  have htrace : WordTrace (prefixWord ++ tailWord_1416563) baseStart_1416563 baseEnd_1416563 := by
    simpa [prefixWord, tailWord_1416563, baseEnd_1416563] using wordTrace_append hprefix tailTrace_1416563
  have hstable : (prefixWord ++ tailWord_1416563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416563).length < 2 ^ (prefixWord ++ tailWord_1416563).sum := by decide
  have hdescent : baseEnd_1416563 < baseStart_1416563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416580 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1416580 : Nat := 118140960795 + 1416580 * 2 ^ 59
def prefixEnd_1416580 : Nat := 4983230072969 + 3 ^ 40 * 1416580 * 2
def baseEnd_1416580 : Nat := 727386425546172857935273

theorem tailTrace_1416580 : CollatzResearch.WordTrace tailWord_1416580 prefixEnd_1416580 727386425546172857935273 := by
  unfold tailWord_1416580
  simp only [CollatzResearch.WordTrace]
  refine ⟨25833458603990033723935597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34444611471986711631914129 25833458603990033723935597)
  ·
    refine ⟨9687546976496262646475849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25833458603990033723935597 9687546976496262646475849)
    ·
      refine ⟨7265660232372196984856887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9687546976496262646475849 7265660232372196984856887)
      ·
        refine ⟨10898490348558295477285331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7265660232372196984856887 10898490348558295477285331)
        ·
          refine ⟨16347735522837443215927997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10898490348558295477285331 16347735522837443215927997)
          ·
            refine ⟨6130400821064041205972999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16347735522837443215927997 6130400821064041205972999)
            ·
              refine ⟨9195601231596061808959499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6130400821064041205972999 9195601231596061808959499)
              ·
                refine ⟨13793401847394092713439249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9195601231596061808959499 13793401847394092713439249)
                ·
                  refine ⟨10345051385545569535079437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13793401847394092713439249 10345051385545569535079437)
                  ·
                    refine ⟨3879394269579588575654789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10345051385545569535079437 3879394269579588575654789)
                    ·
                      refine ⟨727386425546172857935273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3879394269579588575654789 727386425546172857935273)
                      ·
                        rfl

theorem cell23_1416580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1416580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416580 prefixEnd_1416580 := by exact prefixLift 1416580
  have htrace : WordTrace (prefixWord ++ tailWord_1416580) baseStart_1416580 baseEnd_1416580 := by
    simpa [prefixWord, tailWord_1416580, baseEnd_1416580] using wordTrace_append hprefix tailTrace_1416580
  have hstable : (prefixWord ++ tailWord_1416580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416580).length < 2 ^ (prefixWord ++ tailWord_1416580).sum := by decide
  have hdescent : baseEnd_1416580 < baseStart_1416580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416593 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_1416593 : Nat := 118140960795 + 1416593 * 2 ^ 59
def prefixEnd_1416593 : Nat := 4983230072969 + 3 ^ 40 * 1416593 * 2
def baseEnd_1416593 : Nat := 727393100794681307072713

theorem tailTrace_1416593 : CollatzResearch.WordTrace tailWord_1416593 prefixEnd_1416593 727393100794681307072713 := by
  unfold tailWord_1416593
  simp only [CollatzResearch.WordTrace]
  refine ⟨51667391356932970668094433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34444927571288647112062955 51667391356932970668094433)
  ·
    refine ⟨38750543517699728001070825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51667391356932970668094433 38750543517699728001070825)
    ·
      refine ⟨29062907638274796000803119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38750543517699728001070825 29062907638274796000803119)
      ·
        refine ⟨43594361457412194001204679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29062907638274796000803119 43594361457412194001204679)
        ·
          refine ⟨65391542186118291001807019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43594361457412194001204679 65391542186118291001807019)
          ·
            refine ⟨98087313279177436502710529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65391542186118291001807019 98087313279177436502710529)
            ·
              refine ⟨73565484959383077377032897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98087313279177436502710529 73565484959383077377032897)
              ·
                refine ⟨55174113719537308032774673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73565484959383077377032897 55174113719537308032774673)
                ·
                  refine ⟨41380585289652981024581005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55174113719537308032774673 41380585289652981024581005)
                  ·
                    refine ⟨15517719483619867884217877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41380585289652981024581005 15517719483619867884217877)
                    ·
                      refine ⟨727393100794681307072713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15517719483619867884217877 727393100794681307072713)
                      ·
                        rfl

theorem cell23_1416593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_1416593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416593 prefixEnd_1416593 := by exact prefixLift 1416593
  have htrace : WordTrace (prefixWord ++ tailWord_1416593) baseStart_1416593 baseEnd_1416593 := by
    simpa [prefixWord, tailWord_1416593, baseEnd_1416593] using wordTrace_append hprefix tailTrace_1416593
  have hstable : (prefixWord ++ tailWord_1416593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416593).length < 2 ^ (prefixWord ++ tailWord_1416593).sum := by decide
  have hdescent : baseEnd_1416593 < baseStart_1416593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416597 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 1, 4, 2]
def baseStart_1416597 : Nat := 118140960795 + 1416597 * 2 ^ 59
def prefixEnd_1416597 : Nat := 4983230072969 + 3 ^ 40 * 1416597 * 2
def baseEnd_1416597 : Nat := 727395154717299291422695

theorem tailTrace_1416597 : CollatzResearch.WordTrace tailWord_1416597 prefixEnd_1416597 727395154717299291422695 := by
  unfold tailWord_1416597
  simp only [CollatzResearch.WordTrace]
  refine ⟨51667537248918479351240045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34445024832612319567493363 51667537248918479351240045)
  ·
    refine ⟨19375326468344429756715017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51667537248918479351240045 19375326468344429756715017)
    ·
      refine ⟨14531494851258322317536263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19375326468344429756715017 14531494851258322317536263)
      ·
        refine ⟨21797242276887483476304395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14531494851258322317536263 21797242276887483476304395)
        ·
          refine ⟨32695863415331225214456593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21797242276887483476304395 32695863415331225214456593)
          ·
            refine ⟨24521897561498418910842445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32695863415331225214456593 24521897561498418910842445)
            ·
              refine ⟨9195711585561907091565917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24521897561498418910842445 9195711585561907091565917)
              ·
                refine ⟨3448391844585715159337219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9195711585561907091565917 3448391844585715159337219)
                ·
                  refine ⟨5172587766878572739005829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448391844585715159337219 5172587766878572739005829)
                  ·
                    refine ⟨969860206289732388563593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5172587766878572739005829 969860206289732388563593)
                    ·
                      refine ⟨727395154717299291422695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 969860206289732388563593 727395154717299291422695)
                      ·
                        rfl

theorem cell23_1416597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_1416597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416597 prefixEnd_1416597 := by exact prefixLift 1416597
  have htrace : WordTrace (prefixWord ++ tailWord_1416597) baseStart_1416597 baseEnd_1416597 := by
    simpa [prefixWord, tailWord_1416597, baseEnd_1416597] using wordTrace_append hprefix tailTrace_1416597
  have hstable : (prefixWord ++ tailWord_1416597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416597).length < 2 ^ (prefixWord ++ tailWord_1416597).sum := by decide
  have hdescent : baseEnd_1416597 < baseStart_1416597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416637 : List Nat := [1, 4, 1, 2, 2, 1, 1, 6, 5]
def baseStart_1416637 : Nat := 118140960795 + 1416637 * 2 ^ 59
def prefixEnd_1416637 : Nat := 4983230072969 + 3 ^ 40 * 1416637 * 2
def baseEnd_1416637 : Nat := 80823965993719903880279

theorem tailTrace_1416637 : CollatzResearch.WordTrace tailWord_1416637 prefixEnd_1416637 80823965993719903880279 := by
  unfold tailWord_1416637
  simp only [CollatzResearch.WordTrace]
  refine ⟨51668996168773566182696165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34445997445849044121797443 51668996168773566182696165)
  ·
    refine ⟨9687936781645043659255531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51668996168773566182696165 9687936781645043659255531)
    ·
      refine ⟨14531905172467565488883297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9687936781645043659255531 14531905172467565488883297)
      ·
        refine ⟨10898928879350674116662473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14531905172467565488883297 10898928879350674116662473)
        ·
          refine ⟨8174196659513005587496855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10898928879350674116662473 8174196659513005587496855)
          ·
            refine ⟨12261294989269508381245283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8174196659513005587496855 12261294989269508381245283)
            ·
              refine ⟨18391942483904262571867925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12261294989269508381245283 18391942483904262571867925)
              ·
                refine ⟨862122303933012308056309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18391942483904262571867925 862122303933012308056309)
                ·
                  refine ⟨80823965993719903880279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 862122303933012308056309 80823965993719903880279)
                  ·
                    rfl

theorem cell23_1416637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_1416637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416637 prefixEnd_1416637 := by exact prefixLift 1416637
  have htrace : WordTrace (prefixWord ++ tailWord_1416637) baseStart_1416637 baseEnd_1416637 := by
    simpa [prefixWord, tailWord_1416637, baseEnd_1416637] using wordTrace_append hprefix tailTrace_1416637
  have hstable : (prefixWord ++ tailWord_1416637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416637).length < 2 ^ (prefixWord ++ tailWord_1416637).sum := by decide
  have hdescent : baseEnd_1416637 < baseStart_1416637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416642 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_1416642 : Nat := 118140960795 + 1416642 * 2 ^ 59
def prefixEnd_1416642 : Nat := 4983230072969 + 3 ^ 40 * 1416642 * 2
def baseEnd_1416642 : Nat := 727418261346751615359989

theorem tailTrace_1416642 : CollatzResearch.WordTrace tailWord_1416642 prefixEnd_1416642 727418261346751615359989 := by
  unfold tailWord_1416642
  simp only [CollatzResearch.WordTrace]
  refine ⟨12917294633438863009157045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34446119022503634691085453 12917294633438863009157045)
  ·
    refine ⟨1210996371884893407108473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12917294633438863009157045 1210996371884893407108473)
    ·
      refine ⟨908247278913670055331355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1210996371884893407108473 908247278913670055331355)
      ·
        refine ⟨1362370918370505082997033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908247278913670055331355 1362370918370505082997033)
        ·
          refine ⟨1021778188777878812247775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1362370918370505082997033 1021778188777878812247775)
          ·
            refine ⟨1532667283166818218371663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021778188777878812247775 1532667283166818218371663)
            ·
              refine ⟨2299000924750227327557495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532667283166818218371663 2299000924750227327557495)
              ·
                refine ⟨3448501387125340991336243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299000924750227327557495 3448501387125340991336243)
                ·
                  refine ⟨5172752080688011487004365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448501387125340991336243 5172752080688011487004365)
                  ·
                    refine ⟨1939782030258004307626637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5172752080688011487004365 1939782030258004307626637)
                    ·
                      refine ⟨727418261346751615359989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1939782030258004307626637 727418261346751615359989)
                      ·
                        rfl

theorem cell23_1416642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_1416642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416642 prefixEnd_1416642 := by exact prefixLift 1416642
  have htrace : WordTrace (prefixWord ++ tailWord_1416642) baseStart_1416642 baseEnd_1416642 := by
    simpa [prefixWord, tailWord_1416642, baseEnd_1416642] using wordTrace_append hprefix tailTrace_1416642
  have hstable : (prefixWord ++ tailWord_1416642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416642).length < 2 ^ (prefixWord ++ tailWord_1416642).sum := by decide
  have hdescent : baseEnd_1416642 < baseStart_1416642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416650 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_1416650 : Nat := 118140960795 + 1416650 * 2 ^ 59
def prefixEnd_1416650 : Nat := 4983230072969 + 3 ^ 40 * 1416650 * 2
def baseEnd_1416650 : Nat := 242474123063995861353317

theorem tailTrace_1416650 : CollatzResearch.WordTrace tailWord_1416650 prefixEnd_1416650 242474123063995861353317 := by
  unfold tailWord_1416650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12917367579431617350729851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34446313545150979601946269 12917367579431617350729851)
  ·
    refine ⟨19376051369147426026094777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12917367579431617350729851 19376051369147426026094777)
    ·
      refine ⟨14532038526860569519571083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19376051369147426026094777 14532038526860569519571083)
      ·
        refine ⟨21798057790290854279356625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14532038526860569519571083 21798057790290854279356625)
        ·
          refine ⟨16348543342718140709517469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21798057790290854279356625 16348543342718140709517469)
          ·
            refine ⟨6130703753519302766069051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16348543342718140709517469 6130703753519302766069051)
            ·
              refine ⟨9196055630278954149103577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6130703753519302766069051 9196055630278954149103577)
              ·
                refine ⟨6897041722709215611827683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9196055630278954149103577 6897041722709215611827683)
                ·
                  refine ⟨10345562584063823417741525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6897041722709215611827683 10345562584063823417741525)
                  ·
                    refine ⟨242474123063995861353317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10345562584063823417741525 242474123063995861353317)
                    ·
                      rfl

theorem cell23_1416650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_1416650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416650 prefixEnd_1416650 := by exact prefixLift 1416650
  have htrace : WordTrace (prefixWord ++ tailWord_1416650) baseStart_1416650 baseEnd_1416650 := by
    simpa [prefixWord, tailWord_1416650, baseEnd_1416650] using wordTrace_append hprefix tailTrace_1416650
  have hstable : (prefixWord ++ tailWord_1416650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416650).length < 2 ^ (prefixWord ++ tailWord_1416650).sum := by decide
  have hdescent : baseEnd_1416650 < baseStart_1416650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416687 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 4, 4, 2]
def baseStart_1416687 : Nat := 118140960795 + 1416687 * 2 ^ 59
def prefixEnd_1416687 : Nat := 4983230072969 + 3 ^ 40 * 1416687 * 2
def baseEnd_1416687 : Nat := 727441367976203939297281

theorem tailTrace_1416687 : CollatzResearch.WordTrace tailWord_1416687 prefixEnd_1416687 727441367976203939297281 := by
  unfold tailWord_1416687
  simp only [CollatzResearch.WordTrace]
  refine ⟨51670819818592424722016315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34447213212394949814677543 51670819818592424722016315)
  ·
    refine ⟨77506229727888637083024473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51670819818592424722016315 77506229727888637083024473)
    ·
      refine ⟨58129672295916477812268355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77506229727888637083024473 58129672295916477812268355)
      ·
        refine ⟨87194508443874716718402533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58129672295916477812268355 87194508443874716718402533)
        ·
          refine ⟨16348970333226509384700475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87194508443874716718402533 16348970333226509384700475)
          ·
            refine ⟨24523455499839764077050713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16348970333226509384700475 24523455499839764077050713)
            ·
              refine ⟨18392591624879823057788035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24523455499839764077050713 18392591624879823057788035)
              ·
                refine ⟨27588887437319734586682053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18392591624879823057788035 27588887437319734586682053)
                ·
                  refine ⟨5172916394497450235002885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27588887437319734586682053 5172916394497450235002885)
                  ·
                    refine ⟨969921823968271919063041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5172916394497450235002885 969921823968271919063041)
                    ·
                      refine ⟨727441367976203939297281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 969921823968271919063041 727441367976203939297281)
                      ·
                        rfl

theorem cell23_1416687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 4, 2].length) (baseStart_1416687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416687 prefixEnd_1416687 := by exact prefixLift 1416687
  have htrace : WordTrace (prefixWord ++ tailWord_1416687) baseStart_1416687 baseEnd_1416687 := by
    simpa [prefixWord, tailWord_1416687, baseEnd_1416687] using wordTrace_append hprefix tailTrace_1416687
  have hstable : (prefixWord ++ tailWord_1416687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416687).length < 2 ^ (prefixWord ++ tailWord_1416687).sum := by decide
  have hdescent : baseEnd_1416687 < baseStart_1416687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416700 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_1416700 : Nat := 118140960795 + 1416700 * 2 ^ 59
def prefixEnd_1416700 : Nat := 4983230072969 + 3 ^ 40 * 1416700 * 2
def baseEnd_1416700 : Nat := 727448043224712388434721

theorem tailTrace_1416700 : CollatzResearch.WordTrace tailWord_1416700 prefixEnd_1416700 727448043224712388434721 := by
  unfold tailWord_1416700
  simp only [CollatzResearch.WordTrace]
  refine ⟨25835646983772663971119777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34447529311696885294826369 25835646983772663971119777)
  ·
    refine ⟨19376735237829497978339833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25835646983772663971119777 19376735237829497978339833)
    ·
      refine ⟨14532551428372123483754875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19376735237829497978339833 14532551428372123483754875)
      ·
        refine ⟨21798827142558185225632313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14532551428372123483754875 21798827142558185225632313)
        ·
          refine ⟨16349120356918638919224235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21798827142558185225632313 16349120356918638919224235)
          ·
            refine ⟨24523680535377958378836353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16349120356918638919224235 24523680535377958378836353)
            ·
              refine ⟨18392760401533468784127265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24523680535377958378836353 18392760401533468784127265)
              ·
                refine ⟨13794570301150101588095449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18392760401533468784127265 13794570301150101588095449)
                ·
                  refine ⟨10345927725862576191071587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13794570301150101588095449 10345927725862576191071587)
                  ·
                    refine ⟨15518891588793864286607381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10345927725862576191071587 15518891588793864286607381)
                    ·
                      refine ⟨727448043224712388434721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15518891588793864286607381 727448043224712388434721)
                      ·
                        rfl

theorem cell23_1416700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_1416700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416700 prefixEnd_1416700 := by exact prefixLift 1416700
  have htrace : WordTrace (prefixWord ++ tailWord_1416700) baseStart_1416700 baseEnd_1416700 := by
    simpa [prefixWord, tailWord_1416700, baseEnd_1416700] using wordTrace_append hprefix tailTrace_1416700
  have hstable : (prefixWord ++ tailWord_1416700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416700).length < 2 ^ (prefixWord ++ tailWord_1416700).sum := by decide
  have hdescent : baseEnd_1416700 < baseStart_1416700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416730 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_1416730 : Nat := 118140960795 + 1416730 * 2 ^ 59
def prefixEnd_1416730 : Nat := 4983230072969 + 3 ^ 40 * 1416730 * 2
def baseEnd_1416730 : Nat := 727463447644347271059583

theorem tailTrace_1416730 : CollatzResearch.WordTrace tailWord_1416730 prefixEnd_1416730 727463447644347271059583 := by
  unfold tailWord_1416730
  simp only [CollatzResearch.WordTrace]
  refine ⟨12918097039359160766457911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34448258771624428710554429 12918097039359160766457911)
  ·
    refine ⟨19377145559038741149686867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12918097039359160766457911 19377145559038741149686867)
    ·
      refine ⟨29065718338558111724530301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19377145559038741149686867 29065718338558111724530301)
      ·
        refine ⟨10899644376959291896698863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29065718338558111724530301 10899644376959291896698863)
        ·
          refine ⟨16349466565438937845048295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10899644376959291896698863 16349466565438937845048295)
          ·
            refine ⟨24524199848158406767572443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16349466565438937845048295 24524199848158406767572443)
            ·
              refine ⟨36786299772237610151358665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24524199848158406767572443 36786299772237610151358665)
              ·
                refine ⟨27589724829178207613518999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36786299772237610151358665 27589724829178207613518999)
                ·
                  refine ⟨41384587243767311420278499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27589724829178207613518999 41384587243767311420278499)
                  ·
                    refine ⟨62076880865650967130417749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41384587243767311420278499 62076880865650967130417749)
                    ·
                      refine ⟨727463447644347271059583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 62076880865650967130417749 727463447644347271059583)
                      ·
                        rfl

theorem cell23_1416730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_1416730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416730 prefixEnd_1416730 := by exact prefixLift 1416730
  have htrace : WordTrace (prefixWord ++ tailWord_1416730) baseStart_1416730 baseEnd_1416730 := by
    simpa [prefixWord, tailWord_1416730, baseEnd_1416730] using wordTrace_append hprefix tailTrace_1416730
  have hstable : (prefixWord ++ tailWord_1416730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416730).length < 2 ^ (prefixWord ++ tailWord_1416730).sum := by decide
  have hdescent : baseEnd_1416730 < baseStart_1416730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416747 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 5, 5, 2]
def baseStart_1416747 : Nat := 118140960795 + 1416747 * 2 ^ 59
def prefixEnd_1416747 : Nat := 4983230072969 + 3 ^ 40 * 1416747 * 2
def baseEnd_1416747 : Nat := 727472176815473704547005

theorem tailTrace_1416747 : CollatzResearch.WordTrace tailWord_1416747 prefixEnd_1416747 727472176815473704547005 := by
  unfold tailWord_1416747
  simp only [CollatzResearch.WordTrace]
  refine ⟨51673008198375054969200495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34448672132250036646133663 51673008198375054969200495)
  ·
    refine ⟨77509512297562582453800743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51673008198375054969200495 77509512297562582453800743)
    ·
      refine ⟨116264268446343873680701115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77509512297562582453800743 116264268446343873680701115)
      ·
        refine ⟨174396402669515810521051673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116264268446343873680701115 174396402669515810521051673)
        ·
          refine ⟨130797302002136857890788755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174396402669515810521051673 130797302002136857890788755)
          ·
            refine ⟨196195953003205286836183133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130797302002136857890788755 196195953003205286836183133)
            ·
              refine ⟨73573482376201982563568675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196195953003205286836183133 73573482376201982563568675)
              ·
                refine ⟨110360223564302973845353013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73573482376201982563568675 110360223564302973845353013)
                ·
                  refine ⟨10346270959153403798001845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110360223564302973845353013 10346270959153403798001845)
                  ·
                    refine ⟨969962902420631606062673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10346270959153403798001845 969962902420631606062673)
                    ·
                      refine ⟨727472176815473704547005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 969962902420631606062673 727472176815473704547005)
                      ·
                        rfl

theorem cell23_1416747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 5, 2].length) (baseStart_1416747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416747 prefixEnd_1416747 := by exact prefixLift 1416747
  have htrace : WordTrace (prefixWord ++ tailWord_1416747) baseStart_1416747 baseEnd_1416747 := by
    simpa [prefixWord, tailWord_1416747, baseEnd_1416747] using wordTrace_append hprefix tailTrace_1416747
  have hstable : (prefixWord ++ tailWord_1416747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416747).length < 2 ^ (prefixWord ++ tailWord_1416747).sum := by decide
  have hdescent : baseEnd_1416747 < baseStart_1416747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416754 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_1416754 : Nat := 118140960795 + 1416754 * 2 ^ 59
def prefixEnd_1416754 : Nat := 4983230072969 + 3 ^ 40 * 1416754 * 2
def baseEnd_1416754 : Nat := 727475771180055177159473

theorem tailTrace_1416754 : CollatzResearch.WordTrace tailWord_1416754 prefixEnd_1416754 727475771180055177159473 := by
  unfold tailWord_1416754
  simp only [CollatzResearch.WordTrace]
  refine ⟨12918315877337423791176329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34448842339566463443136877 12918315877337423791176329)
  ·
    refine ⟨9688736908003067843382247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12918315877337423791176329 9688736908003067843382247)
    ·
      refine ⟨14533105362004601765073371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9688736908003067843382247 14533105362004601765073371)
      ·
        refine ⟨21799658043006902647610057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14533105362004601765073371 21799658043006902647610057)
        ·
          refine ⟨16349743532255176985707543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21799658043006902647610057 16349743532255176985707543)
          ·
            refine ⟨24524615298382765478561315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16349743532255176985707543 24524615298382765478561315)
            ·
              refine ⟨36786922947574148217841973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24524615298382765478561315 36786922947574148217841973)
              ·
                refine ⟨3448774026335076395422685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36786922947574148217841973 3448774026335076395422685)
                ·
                  refine ⟨1293290259875653648283507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3448774026335076395422685 1293290259875653648283507)
                  ·
                    refine ⟨1939935389813480472425261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1293290259875653648283507 1939935389813480472425261)
                    ·
                      refine ⟨727475771180055177159473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1939935389813480472425261 727475771180055177159473)
                      ·
                        rfl

theorem cell23_1416754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_1416754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416754 prefixEnd_1416754 := by exact prefixLift 1416754
  have htrace : WordTrace (prefixWord ++ tailWord_1416754) baseStart_1416754 baseEnd_1416754 := by
    simpa [prefixWord, tailWord_1416754, baseEnd_1416754] using wordTrace_append hprefix tailTrace_1416754
  have hstable : (prefixWord ++ tailWord_1416754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416754).length < 2 ^ (prefixWord ++ tailWord_1416754).sum := by decide
  have hdescent : baseEnd_1416754 < baseStart_1416754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416757 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_1416757 : Nat := 118140960795 + 1416757 * 2 ^ 59
def prefixEnd_1416757 : Nat := 4983230072969 + 3 ^ 40 * 1416757 * 2
def baseEnd_1416757 : Nat := 242492437207339555140653

theorem tailTrace_1416757 : CollatzResearch.WordTrace tailWord_1416757 prefixEnd_1416757 242492437207339555140653 := by
  unfold tailWord_1416757
  simp only [CollatzResearch.WordTrace]
  refine ⟨51673372928338826677064525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34448915285559217784709683 51673372928338826677064525)
  ·
    refine ⟨19377514848127060003899197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51673372928338826677064525 19377514848127060003899197)
    ·
      refine ⟨7266568068047647501462199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19377514848127060003899197 7266568068047647501462199)
      ·
        refine ⟨10899852102071471252193299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7266568068047647501462199 10899852102071471252193299)
        ·
          refine ⟨16349778153107206878289949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10899852102071471252193299 16349778153107206878289949)
          ·
            refine ⟨6131166807415202579358731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16349778153107206878289949 6131166807415202579358731)
            ·
              refine ⟨9196750211122803869038097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131166807415202579358731 9196750211122803869038097)
              ·
                refine ⟨6897562658342102901778573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9196750211122803869038097 6897562658342102901778573)
                ·
                  refine ⟨2586585996878288588166965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6897562658342102901778573 2586585996878288588166965)
                  ·
                    refine ⟨242492437207339555140653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2586585996878288588166965 242492437207339555140653)
                    ·
                      rfl

theorem cell23_1416757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_1416757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416757 prefixEnd_1416757 := by exact prefixLift 1416757
  have htrace : WordTrace (prefixWord ++ tailWord_1416757) baseStart_1416757 baseEnd_1416757 := by
    simpa [prefixWord, tailWord_1416757, baseEnd_1416757] using wordTrace_append hprefix tailTrace_1416757
  have hstable : (prefixWord ++ tailWord_1416757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416757).length < 2 ^ (prefixWord ++ tailWord_1416757).sum := by decide
  have hdescent : baseEnd_1416757 < baseStart_1416757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416788 : List Nat := [2, 4, 1, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_1416788 : Nat := 118140960795 + 1416788 * 2 ^ 59
def prefixEnd_1416788 : Nat := 4983230072969 + 3 ^ 40 * 1416788 * 2
def baseEnd_1416788 : Nat := 727493229522308044134317

theorem tailTrace_1416788 : CollatzResearch.WordTrace tailWord_1416788 prefixEnd_1416788 727493229522308044134317 := by
  unfold tailWord_1416788
  simp only [CollatzResearch.WordTrace]
  refine ⟨25837251795613259485721509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34449669060817679314295345 25837251795613259485721509)
  ·
    refine ⟨4844484711677486153572783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25837251795613259485721509 4844484711677486153572783)
    ·
      refine ⟨7266727067516229230359175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4844484711677486153572783 7266727067516229230359175)
      ·
        refine ⟨10900090601274343845538763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7266727067516229230359175 10900090601274343845538763)
        ·
          refine ⟨16350135901911515768308145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10900090601274343845538763 16350135901911515768308145)
          ·
            refine ⟨12262601926433636826231109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16350135901911515768308145 12262601926433636826231109)
            ·
              refine ⟨2299237861206306904918333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12262601926433636826231109 2299237861206306904918333)
              ·
                refine ⟨862214197952365089344375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2299237861206306904918333 862214197952365089344375)
                ·
                  refine ⟨1293321296928547634016563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862214197952365089344375 1293321296928547634016563)
                  ·
                    refine ⟨1939981945392821451024845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1293321296928547634016563 1939981945392821451024845)
                    ·
                      refine ⟨727493229522308044134317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1939981945392821451024845 727493229522308044134317)
                      ·
                        rfl

theorem cell23_1416788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_1416788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416788 prefixEnd_1416788 := by exact prefixLift 1416788
  have htrace : WordTrace (prefixWord ++ tailWord_1416788) baseStart_1416788 baseEnd_1416788 := by
    simpa [prefixWord, tailWord_1416788, baseEnd_1416788] using wordTrace_append hprefix tailTrace_1416788
  have hstable : (prefixWord ++ tailWord_1416788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416788).length < 2 ^ (prefixWord ++ tailWord_1416788).sum := by decide
  have hdescent : baseEnd_1416788 < baseStart_1416788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416791 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 1, 5]
def baseStart_1416791 : Nat := 118140960795 + 1416791 * 2 ^ 59
def prefixEnd_1416791 : Nat := 4983230072969 + 3 ^ 40 * 1416791 * 2
def baseEnd_1416791 : Nat := 242498256654757177465601

theorem tailTrace_1416791 : CollatzResearch.WordTrace tailWord_1416791 prefixEnd_1416791 242498256654757177465601 := by
  unfold tailWord_1416791
  simp only [CollatzResearch.WordTrace]
  refine ⟨51674613010215650483802227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34449742006810433655868151 51674613010215650483802227)
  ·
    refine ⟨77511919515323475725703341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51674613010215650483802227 77511919515323475725703341)
    ·
      refine ⟨29066969818246303397138753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77511919515323475725703341 29066969818246303397138753)
      ·
        refine ⟨21800227363684727547854065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29066969818246303397138753 21800227363684727547854065)
        ·
          refine ⟨16350170522763545660890549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21800227363684727547854065 16350170522763545660890549)
          ·
            refine ⟨1532828486509082405708489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16350170522763545660890549 1532828486509082405708489)
            ·
              refine ⟨1149621364881811804281367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532828486509082405708489 1149621364881811804281367)
              ·
                refine ⟨1724432047322717706422051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149621364881811804281367 1724432047322717706422051)
                ·
                  refine ⟨2586648070984076559633077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724432047322717706422051 2586648070984076559633077)
                  ·
                    refine ⟨242498256654757177465601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2586648070984076559633077 242498256654757177465601)
                    ·
                      rfl

theorem cell23_1416791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_1416791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416791 prefixEnd_1416791 := by exact prefixLift 1416791
  have htrace : WordTrace (prefixWord ++ tailWord_1416791) baseStart_1416791 baseEnd_1416791 := by
    simpa [prefixWord, tailWord_1416791, baseEnd_1416791] using wordTrace_append hprefix tailTrace_1416791
  have hstable : (prefixWord ++ tailWord_1416791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416791).length < 2 ^ (prefixWord ++ tailWord_1416791).sum := by decide
  have hdescent : baseEnd_1416791 < baseStart_1416791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416804 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_1416804 : Nat := 118140960795 + 1416804 * 2 ^ 59
def prefixEnd_1416804 : Nat := 4983230072969 + 3 ^ 40 * 1416804 * 2
def baseEnd_1416804 : Nat := 242500481737593327178081

theorem tailTrace_1416804 : CollatzResearch.WordTrace tailWord_1416804 prefixEnd_1416804 242500481737593327178081 := by
  unfold tailWord_1416804
  simp only [CollatzResearch.WordTrace]
  refine ⟨25837543579584276852012733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34450058106112369136016977 25837543579584276852012733)
  ·
    refine ⟨9689078842344103819504775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25837543579584276852012733 9689078842344103819504775)
    ·
      refine ⟨14533618263516155729257163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9689078842344103819504775 14533618263516155729257163)
      ·
        refine ⟨21800427395274233593885745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14533618263516155729257163 21800427395274233593885745)
        ·
          refine ⟨16350320546455675195414309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21800427395274233593885745 16350320546455675195414309)
          ·
            refine ⟨3065685102460439099140183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16350320546455675195414309 3065685102460439099140183)
            ·
              refine ⟨4598527653690658648710275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3065685102460439099140183 4598527653690658648710275)
              ·
                refine ⟨6897791480535987973065413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4598527653690658648710275 6897791480535987973065413)
                ·
                  refine ⟨1293335902600497744949765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6897791480535987973065413 1293335902600497744949765)
                  ·
                    refine ⟨242500481737593327178081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1293335902600497744949765 242500481737593327178081)
                    ·
                      rfl

theorem cell23_1416804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_1416804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416804 prefixEnd_1416804 := by exact prefixLift 1416804
  have htrace : WordTrace (prefixWord ++ tailWord_1416804) baseStart_1416804 baseEnd_1416804 := by
    simpa [prefixWord, tailWord_1416804, baseEnd_1416804] using wordTrace_append hprefix tailTrace_1416804
  have hstable : (prefixWord ++ tailWord_1416804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416804).length < 2 ^ (prefixWord ++ tailWord_1416804).sum := by decide
  have hdescent : baseEnd_1416804 < baseStart_1416804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416807 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1416807 : Nat := 118140960795 + 1416807 * 2 ^ 59
def prefixEnd_1416807 : Nat := 4983230072969 + 3 ^ 40 * 1416807 * 2
def baseEnd_1416807 : Nat := 727502985654743469796729

theorem tailTrace_1416807 : CollatzResearch.WordTrace tailWord_1416807 prefixEnd_1416807 727502985654743469796729 := by
  unfold tailWord_1416807
  simp only [CollatzResearch.WordTrace]
  refine ⟨51675196578157685216384675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34450131052105123477589783 51675196578157685216384675)
  ·
    refine ⟨77512794867236527824577013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51675196578157685216384675 77512794867236527824577013)
    ·
      refine ⟨7266824518803424483554095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77512794867236527824577013 7266824518803424483554095)
      ·
        refine ⟨10900236778205136725331143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7266824518803424483554095 10900236778205136725331143)
        ·
          refine ⟨16350355167307705087996715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10900236778205136725331143 16350355167307705087996715)
          ·
            refine ⟨24525532750961557631995073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16350355167307705087996715 24525532750961557631995073)
            ·
              refine ⟨18394149563221168223996305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24525532750961557631995073 18394149563221168223996305)
              ·
                refine ⟨13795612172415876167997229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18394149563221168223996305 13795612172415876167997229)
                ·
                  refine ⟨5173354564655953562998961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13795612172415876167997229 5173354564655953562998961)
                  ·
                    refine ⟨3880015923491965172249221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5173354564655953562998961 3880015923491965172249221)
                    ·
                      refine ⟨727502985654743469796729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3880015923491965172249221 727502985654743469796729)
                      ·
                        rfl

theorem cell23_1416807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1416807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416807 prefixEnd_1416807 := by exact prefixLift 1416807
  have htrace : WordTrace (prefixWord ++ tailWord_1416807) baseStart_1416807 baseEnd_1416807 := by
    simpa [prefixWord, tailWord_1416807, baseEnd_1416807] using wordTrace_append hprefix tailTrace_1416807
  have hstable : (prefixWord ++ tailWord_1416807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416807).length < 2 ^ (prefixWord ++ tailWord_1416807).sum := by decide
  have hdescent : baseEnd_1416807 < baseStart_1416807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416821 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1416821 : Nat := 118140960795 + 1416821 * 2 ^ 59
def prefixEnd_1416821 : Nat := 4983230072969 + 3 ^ 40 * 1416821 * 2
def baseEnd_1416821 : Nat := 242503391461302138340555

theorem tailTrace_1416821 : CollatzResearch.WordTrace tailWord_1416821 prefixEnd_1416821 242503391461302138340555 := by
  unfold tailWord_1416821
  simp only [CollatzResearch.WordTrace]
  refine ⟨51675707200106965607394317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34450471466737977071596211 51675707200106965607394317)
  ·
    refine ⟨19378390200040112102772869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51675707200106965607394317 19378390200040112102772869)
    ·
      refine ⟨3633448162507521019269913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19378390200040112102772869 3633448162507521019269913)
      ·
        refine ⟨2725086121880640764452435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3633448162507521019269913 2725086121880640764452435)
        ·
          refine ⟨4087629182820961146678653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2725086121880640764452435 4087629182820961146678653)
          ·
            refine ⟨1532860943557860430004495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4087629182820961146678653 1532860943557860430004495)
            ·
              refine ⟨2299291415336790645006743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532860943557860430004495 2299291415336790645006743)
              ·
                refine ⟨3448937123005185967510115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299291415336790645006743 3448937123005185967510115)
                ·
                  refine ⟨5173405684507778951265173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448937123005185967510115 5173405684507778951265173)
                  ·
                    refine ⟨242503391461302138340555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5173405684507778951265173 242503391461302138340555)
                    ·
                      rfl

theorem cell23_1416821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1416821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416821 prefixEnd_1416821 := by exact prefixLift 1416821
  have htrace : WordTrace (prefixWord ++ tailWord_1416821) baseStart_1416821 baseEnd_1416821 := by
    simpa [prefixWord, tailWord_1416821, baseEnd_1416821] using wordTrace_append hprefix tailTrace_1416821
  have hstable : (prefixWord ++ tailWord_1416821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416821).length < 2 ^ (prefixWord ++ tailWord_1416821).sum := by decide
  have hdescent : baseEnd_1416821 < baseStart_1416821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416844 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 6, 1, 3]
def baseStart_1416844 : Nat := 118140960795 + 1416844 * 2 ^ 59
def prefixEnd_1416844 : Nat := 4983230072969 + 3 ^ 40 * 1416844 * 2
def baseEnd_1416844 : Nat := 727521984438959825034059

theorem tailTrace_1416844 : CollatzResearch.WordTrace tailWord_1416844 prefixEnd_1416844 727521984438959825034059 := by
  unfold tailWord_1416844
  simp only [CollatzResearch.WordTrace]
  refine ⟨25838273039511820267740793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34451030719349093690321057 25838273039511820267740793)
  ·
    refine ⟨19378704779633865200805595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25838273039511820267740793 19378704779633865200805595)
    ·
      refine ⟨29068057169450797801208393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19378704779633865200805595 29068057169450797801208393)
      ·
        refine ⟨21801042877088098350906295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29068057169450797801208393 21801042877088098350906295)
        ·
          refine ⟨32701564315632147526359443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21801042877088098350906295 32701564315632147526359443)
          ·
            refine ⟨49052346473448221289539165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32701564315632147526359443 49052346473448221289539165)
            ·
              refine ⟨18394629927543082983577187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49052346473448221289539165 18394629927543082983577187)
              ·
                refine ⟨27591944891314624475365781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18394629927543082983577187 27591944891314624475365781)
                ·
                  refine ⟨1293372416780373022282771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27591944891314624475365781 1293372416780373022282771)
                  ·
                    refine ⟨1940058625170559533424157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1293372416780373022282771 1940058625170559533424157)
                    ·
                      refine ⟨727521984438959825034059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1940058625170559533424157 727521984438959825034059)
                      ·
                        rfl

theorem cell23_1416844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_1416844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416844 prefixEnd_1416844 := by exact prefixLift 1416844
  have htrace : WordTrace (prefixWord ++ tailWord_1416844) baseStart_1416844 baseEnd_1416844 := by
    simpa [prefixWord, tailWord_1416844, baseEnd_1416844] using wordTrace_append hprefix tailTrace_1416844
  have hstable : (prefixWord ++ tailWord_1416844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416844).length < 2 ^ (prefixWord ++ tailWord_1416844).sum := by decide
  have hdescent : baseEnd_1416844 < baseStart_1416844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416861 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_1416861 : Nat := 118140960795 + 1416861 * 2 ^ 59
def prefixEnd_1416861 : Nat := 4983230072969 + 3 ^ 40 * 1416861 * 2
def baseEnd_1416861 : Nat := 727530713610086258521481

theorem tailTrace_1416861 : CollatzResearch.WordTrace tailWord_1416861 prefixEnd_1416861 727530713610086258521481 := by
  unfold tailWord_1416861
  simp only [CollatzResearch.WordTrace]
  refine ⟨51677166119962052438850437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34451444079974701625900291 51677166119962052438850437)
  ·
    refine ⟨9689468647492884832284457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51677166119962052438850437 9689468647492884832284457)
    ·
      refine ⟨7267101485619663624213343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9689468647492884832284457 7267101485619663624213343)
      ·
        refine ⟨10900652228429495436320015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7267101485619663624213343 10900652228429495436320015)
        ·
          refine ⟨16350978342644243154480023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10900652228429495436320015 16350978342644243154480023)
          ·
            refine ⟨24526467513966364731720035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16350978342644243154480023 24526467513966364731720035)
            ·
              refine ⟨36789701270949547097580053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24526467513966364731720035 36789701270949547097580053)
              ·
                refine ⟨1724517247075760020199065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36789701270949547097580053 1724517247075760020199065)
                ·
                  refine ⟨1293387935306820015149299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1724517247075760020199065 1293387935306820015149299)
                  ·
                    refine ⟨1940081902960230022723949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1293387935306820015149299 1940081902960230022723949)
                    ·
                      refine ⟨727530713610086258521481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1940081902960230022723949 727530713610086258521481)
                      ·
                        rfl

theorem cell23_1416861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_1416861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416861 prefixEnd_1416861 := by exact prefixLift 1416861
  have htrace : WordTrace (prefixWord ++ tailWord_1416861) baseStart_1416861 baseEnd_1416861 := by
    simpa [prefixWord, tailWord_1416861, baseEnd_1416861] using wordTrace_append hprefix tailTrace_1416861
  have hstable : (prefixWord ++ tailWord_1416861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416861).length < 2 ^ (prefixWord ++ tailWord_1416861).sum := by decide
  have hdescent : baseEnd_1416861 < baseStart_1416861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416867 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1416867 : Nat := 118140960795 + 1416867 * 2 ^ 59
def prefixEnd_1416867 : Nat := 4983230072969 + 3 ^ 40 * 1416867 * 2
def baseEnd_1416867 : Nat := 727533794494013235046453

theorem tailTrace_1416867 : CollatzResearch.WordTrace tailWord_1416867 prefixEnd_1416867 727533794494013235046453 := by
  unfold tailWord_1416867
  simp only [CollatzResearch.WordTrace]
  refine ⟨51677384957940315463568855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34451589971960210309045903 51677384957940315463568855)
  ·
    refine ⟨77516077436910473195353283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51677384957940315463568855 77516077436910473195353283)
    ·
      refine ⟨116274116155365709793029925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77516077436910473195353283 116274116155365709793029925)
      ·
        refine ⟨21801396779131070586193111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116274116155365709793029925 21801396779131070586193111)
        ·
          refine ⟨32702095168696605879289667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21801396779131070586193111 32702095168696605879289667)
          ·
            refine ⟨49053142753044908818934501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32702095168696605879289667 49053142753044908818934501)
            ·
              refine ⟨9197464266195920403550219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49053142753044908818934501 9197464266195920403550219)
              ·
                refine ⟨13796196399293880605325329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9197464266195920403550219 13796196399293880605325329)
                ·
                  refine ⟨10347147299470410453993997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13796196399293880605325329 10347147299470410453993997)
                  ·
                    refine ⟨3880180237301403920247749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10347147299470410453993997 3880180237301403920247749)
                    ·
                      refine ⟨727533794494013235046453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3880180237301403920247749 727533794494013235046453)
                      ·
                        rfl

theorem cell23_1416867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1416867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416867 prefixEnd_1416867 := by exact prefixLift 1416867
  have htrace : WordTrace (prefixWord ++ tailWord_1416867) baseStart_1416867 baseEnd_1416867 := by
    simpa [prefixWord, tailWord_1416867, baseEnd_1416867] using wordTrace_append hprefix tailTrace_1416867
  have hstable : (prefixWord ++ tailWord_1416867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416867).length < 2 ^ (prefixWord ++ tailWord_1416867).sum := by decide
  have hdescent : baseEnd_1416867 < baseStart_1416867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416931 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1416931 : Nat := 118140960795 + 1416931 * 2 ^ 59
def prefixEnd_1416931 : Nat := 4983230072969 + 3 ^ 40 * 1416931 * 2
def baseEnd_1416931 : Nat := 727566657255900984646159

theorem tailTrace_1416931 : CollatzResearch.WordTrace tailWord_1416931 prefixEnd_1416931 727566657255900984646159 := by
  unfold tailWord_1416931
  simp only [CollatzResearch.WordTrace]
  refine ⟨51679719229708454393898647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34453146153138969595932431 51679719229708454393898647)
  ·
    refine ⟨77519578844562681590847971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51679719229708454393898647 77519578844562681590847971)
    ·
      refine ⟨116279368266844022386271957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77519578844562681590847971 116279368266844022386271957)
      ·
        refine ⟨2725297693754156774678249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 116279368266844022386271957 2725297693754156774678249)
        ·
          refine ⟨2043973270315617581008687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2725297693754156774678249 2043973270315617581008687)
          ·
            refine ⟨3065959905473426371513031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043973270315617581008687 3065959905473426371513031)
            ·
              refine ⟨4598939858210139557269547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3065959905473426371513031 4598939858210139557269547)
              ·
                refine ⟨6898409787315209335904321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4598939858210139557269547 6898409787315209335904321)
                ·
                  refine ⟨5173807340486407001928241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6898409787315209335904321 5173807340486407001928241)
                  ·
                    refine ⟨3880355505364805251446181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5173807340486407001928241 3880355505364805251446181)
                    ·
                      refine ⟨727566657255900984646159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3880355505364805251446181 727566657255900984646159)
                      ·
                        rfl

theorem cell23_1416931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1416931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416931 prefixEnd_1416931 := by exact prefixLift 1416931
  have htrace : WordTrace (prefixWord ++ tailWord_1416931) baseStart_1416931 baseEnd_1416931 := by
    simpa [prefixWord, tailWord_1416931, baseEnd_1416931] using wordTrace_append hprefix tailTrace_1416931
  have hstable : (prefixWord ++ tailWord_1416931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416931).length < 2 ^ (prefixWord ++ tailWord_1416931).sum := by decide
  have hdescent : baseEnd_1416931 < baseStart_1416931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416935 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_1416935 : Nat := 118140960795 + 1416935 * 2 ^ 59
def prefixEnd_1416935 : Nat := 4983230072969 + 3 ^ 40 * 1416935 * 2
def baseEnd_1416935 : Nat := 727568711178518968996141

theorem tailTrace_1416935 : CollatzResearch.WordTrace tailWord_1416935 prefixEnd_1416935 727568711178518968996141 := by
  unfold tailWord_1416935
  simp only [CollatzResearch.WordTrace]
  refine ⟨51679865121693963077044259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34453243414462642051362839 51679865121693963077044259)
  ·
    refine ⟨77519797682540944615566389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51679865121693963077044259 77519797682540944615566389)
    ·
      refine ⟨7267481032738213557709349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77519797682540944615566389 7267481032738213557709349)
      ·
        refine ⟨1362652693638415042070503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7267481032738213557709349 1362652693638415042070503)
        ·
          refine ⟨2043979040457622563105755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362652693638415042070503 2043979040457622563105755)
          ·
            refine ⟨3065968560686433844658633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043979040457622563105755 3065968560686433844658633)
            ·
              refine ⟨2299476420514825383493975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3065968560686433844658633 2299476420514825383493975)
              ·
                refine ⟨3449214630772238075240963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299476420514825383493975 3449214630772238075240963)
                ·
                  refine ⟨5173821946158357112861445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449214630772238075240963 5173821946158357112861445)
                  ·
                    refine ⟨970091614904691958661521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5173821946158357112861445 970091614904691958661521)
                    ·
                      refine ⟨727568711178518968996141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970091614904691958661521 727568711178518968996141)
                      ·
                        rfl

theorem cell23_1416935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_1416935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416935 prefixEnd_1416935 := by exact prefixLift 1416935
  have htrace : WordTrace (prefixWord ++ tailWord_1416935) baseStart_1416935 baseEnd_1416935 := by
    simpa [prefixWord, tailWord_1416935, baseEnd_1416935] using wordTrace_append hprefix tailTrace_1416935
  have hstable : (prefixWord ++ tailWord_1416935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416935).length < 2 ^ (prefixWord ++ tailWord_1416935).sum := by decide
  have hdescent : baseEnd_1416935 < baseStart_1416935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416937 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 1, 7]
def baseStart_1416937 : Nat := 118140960795 + 1416937 * 2 ^ 59
def prefixEnd_1416937 : Nat := 4983230072969 + 3 ^ 40 * 1416937 * 2
def baseEnd_1416937 : Nat := 242523246046609320390377

theorem tailTrace_1416937 : CollatzResearch.WordTrace tailWord_1416937 prefixEnd_1416937 242523246046609320390377 := by
  unfold tailWord_1416937
  simp only [CollatzResearch.WordTrace]
  refine ⟨51679938067686717418617065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34453292045124478279078043 51679938067686717418617065)
  ·
    refine ⟨38759953550765038063962799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51679938067686717418617065 38759953550765038063962799)
    ·
      refine ⟨58139930326147557095944199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38759953550765038063962799 58139930326147557095944199)
      ·
        refine ⟨87209895489221335643916299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58139930326147557095944199 87209895489221335643916299)
        ·
          refine ⟨130814843233832003465874449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87209895489221335643916299 130814843233832003465874449)
          ·
            refine ⟨98111132425374002599405837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130814843233832003465874449 98111132425374002599405837)
            ·
              refine ⟨36791674659515250974777189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98111132425374002599405837 36791674659515250974777189)
              ·
                refine ⟨6898438998659109557770723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36791674659515250974777189 6898438998659109557770723)
                ·
                  refine ⟨10347658497988664336656085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6898438998659109557770723 10347658497988664336656085)
                  ·
                    refine ⟨242523246046609320390377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10347658497988664336656085 242523246046609320390377)
                    ·
                      rfl

theorem cell23_1416937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_1416937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416937 prefixEnd_1416937 := by exact prefixLift 1416937
  have htrace : WordTrace (prefixWord ++ tailWord_1416937) baseStart_1416937 baseEnd_1416937 := by
    simpa [prefixWord, tailWord_1416937, baseEnd_1416937] using wordTrace_append hprefix tailTrace_1416937
  have hstable : (prefixWord ++ tailWord_1416937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416937).length < 2 ^ (prefixWord ++ tailWord_1416937).sum := by decide
  have hdescent : baseEnd_1416937 < baseStart_1416937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416947 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 7]
def baseStart_1416947 : Nat := 118140960795 + 1416947 * 2 ^ 59
def prefixEnd_1416947 : Nat := 4983230072969 + 3 ^ 40 * 1416947 * 2
def baseEnd_1416947 : Nat := 727574872946372922046085

theorem tailTrace_1416947 : CollatzResearch.WordTrace tailWord_1416947 prefixEnd_1416947 727574872946372922046085 := by
  unfold tailWord_1416947
  simp only [CollatzResearch.WordTrace]
  refine ⟨51680302797650489126481095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34453535198433659417654063 51680302797650489126481095)
  ·
    refine ⟨77520454196475733689721643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51680302797650489126481095 77520454196475733689721643)
    ·
      refine ⟨116280681294713600534582465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77520454196475733689721643 116280681294713600534582465)
      ·
        refine ⟨87210510971035200400936849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116280681294713600534582465 87210510971035200400936849)
        ·
          refine ⟨65407883228276400300702637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87210510971035200400936849 65407883228276400300702637)
          ·
            refine ⟨24527956210603650112763489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65407883228276400300702637 24527956210603650112763489)
            ·
              refine ⟨18395967157952737584572617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24527956210603650112763489 18395967157952737584572617)
              ·
                refine ⟨13796975368464553188429463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18395967157952737584572617 13796975368464553188429463)
                ·
                  refine ⟨20695463052696829782644195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13796975368464553188429463 20695463052696829782644195)
                  ·
                    refine ⟨31043194579045244673966293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20695463052696829782644195 31043194579045244673966293)
                    ·
                      refine ⟨727574872946372922046085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31043194579045244673966293 727574872946372922046085)
                      ·
                        rfl

theorem cell23_1416947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_1416947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416947 prefixEnd_1416947 := by exact prefixLift 1416947
  have htrace : WordTrace (prefixWord ++ tailWord_1416947) baseStart_1416947 baseEnd_1416947 := by
    simpa [prefixWord, tailWord_1416947, baseEnd_1416947] using wordTrace_append hprefix tailTrace_1416947
  have hstable : (prefixWord ++ tailWord_1416947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416947).length < 2 ^ (prefixWord ++ tailWord_1416947).sum := by decide
  have hdescent : baseEnd_1416947 < baseStart_1416947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1416991 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 2, 4, 2]
def baseStart_1416991 : Nat := 118140960795 + 1416991 * 2 ^ 59
def prefixEnd_1416991 : Nat := 4983230072969 + 3 ^ 40 * 1416991 * 2
def baseEnd_1416991 : Nat := 727597466095170749895883

theorem tailTrace_1416991 : CollatzResearch.WordTrace tailWord_1416991 prefixEnd_1416991 727597466095170749895883 := by
  unfold tailWord_1416991
  simp only [CollatzResearch.WordTrace]
  refine ⟨51681907609491084641082827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34454605072994056427388551 51681907609491084641082827)
  ·
    refine ⟨77522861414236626961624241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51681907609491084641082827 77522861414236626961624241)
    ·
      refine ⟨58142146060677470221218181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77522861414236626961624241 58142146060677470221218181)
      ·
        refine ⟨10901652386377025666478409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58142146060677470221218181 10901652386377025666478409)
        ·
          refine ⟨8176239289782769249858807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10901652386377025666478409 8176239289782769249858807)
          ·
            refine ⟨12264358934674153874788211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8176239289782769249858807 12264358934674153874788211)
            ·
              refine ⟨18396538402011230812182317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12264358934674153874788211 18396538402011230812182317)
              ·
                refine ⟨6898701900754211554568369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18396538402011230812182317 6898701900754211554568369)
                ·
                  refine ⟨5174026425565658665926277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6898701900754211554568369 5174026425565658665926277)
                  ·
                    refine ⟨970129954793560999861177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5174026425565658665926277 970129954793560999861177)
                    ·
                      refine ⟨727597466095170749895883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970129954793560999861177 727597466095170749895883)
                      ·
                        rfl

theorem cell23_1416991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_1416991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1416991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1416991 prefixEnd_1416991 := by exact prefixLift 1416991
  have htrace : WordTrace (prefixWord ++ tailWord_1416991) baseStart_1416991 baseEnd_1416991 := by
    simpa [prefixWord, tailWord_1416991, baseEnd_1416991] using wordTrace_append hprefix tailTrace_1416991
  have hstable : (prefixWord ++ tailWord_1416991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1416991).length < 2 ^ (prefixWord ++ tailWord_1416991).sum := by decide
  have hdescent : baseEnd_1416991 < baseStart_1416991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1416991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417068 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 2, 3, 2]
def baseStart_1417068 : Nat := 118140960795 + 1417068 * 2 ^ 59
def prefixEnd_1417068 : Nat := 4983230072969 + 3 ^ 40 * 1417068 * 2
def baseEnd_1417068 : Nat := 727637004105566948633029

theorem tailTrace_1417068 : CollatzResearch.WordTrace tailWord_1417068 prefixEnd_1417068 727637004105566948633029 := by
  unfold tailWord_1417068
  simp only [CollatzResearch.WordTrace]
  refine ⟨25842358015106063395817929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34456477353474751194423905 25842358015106063395817929)
  ·
    refine ⟨19381768511329547546863447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25842358015106063395817929 19381768511329547546863447)
    ·
      refine ⟨29072652766994321320295171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19381768511329547546863447 29072652766994321320295171)
      ·
        refine ⟨43608979150491481980442757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29072652766994321320295171 43608979150491481980442757)
        ·
          refine ⟨8176683590717152871333017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43608979150491481980442757 8176683590717152871333017)
          ·
            refine ⟨6132512693037864653499763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8176683590717152871333017 6132512693037864653499763)
            ·
              refine ⟨9198769039556796980249645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6132512693037864653499763 9198769039556796980249645)
              ·
                refine ⟨3449538389833798867593617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9198769039556796980249645 3449538389833798867593617)
                ·
                  refine ⟨2587153792375349150695213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3449538389833798867593617 2587153792375349150695213)
                  ·
                    refine ⟨970182672140755931510705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2587153792375349150695213 970182672140755931510705)
                    ·
                      refine ⟨727637004105566948633029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970182672140755931510705 727637004105566948633029)
                      ·
                        rfl

theorem cell23_1417068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 3, 2].length) (baseStart_1417068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417068 prefixEnd_1417068 := by exact prefixLift 1417068
  have htrace : WordTrace (prefixWord ++ tailWord_1417068) baseStart_1417068 baseEnd_1417068 := by
    simpa [prefixWord, tailWord_1417068, baseEnd_1417068] using wordTrace_append hprefix tailTrace_1417068
  have hstable : (prefixWord ++ tailWord_1417068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417068).length < 2 ^ (prefixWord ++ tailWord_1417068).sum := by decide
  have hdescent : baseEnd_1417068 < baseStart_1417068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417092 : List Nat := [2, 3, 2, 1, 1, 1, 6, 2, 1, 1, 3]
def baseStart_1417092 : Nat := 118140960795 + 1417092 * 2 ^ 59
def prefixEnd_1417092 : Nat := 4983230072969 + 3 ^ 40 * 1417092 * 2
def baseEnd_1417092 : Nat := 727649327641274854732919

theorem tailTrace_1417092 : CollatzResearch.WordTrace tailWord_1417092 prefixEnd_1417092 727649327641274854732919 := by
  unfold tailWord_1417092
  simp only [CollatzResearch.WordTrace]
  refine ⟨25842795691062589445254765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34457060921416785927006353 25842795691062589445254765)
  ·
    refine ⟨9691048384148471041970537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25842795691062589445254765 9691048384148471041970537)
    ·
      refine ⟨7268286288111353281477903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9691048384148471041970537 7268286288111353281477903)
      ·
        refine ⟨10902429432167029922216855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7268286288111353281477903 10902429432167029922216855)
        ·
          refine ⟨16353644148250544883325283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10902429432167029922216855 16353644148250544883325283)
          ·
            refine ⟨24530466222375817324987925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16353644148250544883325283 24530466222375817324987925)
            ·
              refine ⟨1149865604173866437108809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24530466222375817324987925 1149865604173866437108809)
              ·
                refine ⟨862399203130399827831607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149865604173866437108809 862399203130399827831607)
                ·
                  refine ⟨1293598804695599741747411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862399203130399827831607 1293598804695599741747411)
                  ·
                    refine ⟨1940398207043399612621117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1293598804695599741747411 1940398207043399612621117)
                    ·
                      refine ⟨727649327641274854732919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1940398207043399612621117 727649327641274854732919)
                      ·
                        rfl

theorem cell23_1417092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_1417092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417092 prefixEnd_1417092 := by exact prefixLift 1417092
  have htrace : WordTrace (prefixWord ++ tailWord_1417092) baseStart_1417092 baseEnd_1417092 := by
    simpa [prefixWord, tailWord_1417092, baseEnd_1417092] using wordTrace_append hprefix tailTrace_1417092
  have hstable : (prefixWord ++ tailWord_1417092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417092).length < 2 ^ (prefixWord ++ tailWord_1417092).sum := by decide
  have hdescent : baseEnd_1417092 < baseStart_1417092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417108 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1417108 : Nat := 118140960795 + 1417108 * 2 ^ 59
def prefixEnd_1417108 : Nat := 4983230072969 + 3 ^ 40 * 1417108 * 2
def baseEnd_1417108 : Nat := 242552514443915597377615

theorem tailTrace_1417108 : CollatzResearch.WordTrace tailWord_1417108 prefixEnd_1417108 242552514443915597377615 := by
  unfold tailWord_1417108
  simp only [CollatzResearch.WordTrace]
  refine ⟨25843087475033606811545989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34457449966711475748727985 25843087475033606811545989)
  ·
    refine ⟨4845578901568801277164873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25843087475033606811545989 4845578901568801277164873)
    ·
      refine ⟨3634184176176600957873655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4845578901568801277164873 3634184176176600957873655)
      ·
        refine ⟨5451276264264901436810483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3634184176176600957873655 5451276264264901436810483)
        ·
          refine ⟨8176914396397352155215725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5451276264264901436810483 8176914396397352155215725)
          ·
            refine ⟨3066342898649007058205897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8176914396397352155215725 3066342898649007058205897)
            ·
              refine ⟨2299757173986755293654423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3066342898649007058205897 2299757173986755293654423)
              ·
                refine ⟨3449635760980132940481635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299757173986755293654423 3449635760980132940481635)
                ·
                  refine ⟨5174453641470199410722453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449635760980132940481635 5174453641470199410722453)
                  ·
                    refine ⟨242552514443915597377615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5174453641470199410722453 242552514443915597377615)
                    ·
                      rfl

theorem cell23_1417108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1417108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417108 prefixEnd_1417108 := by exact prefixLift 1417108
  have htrace : WordTrace (prefixWord ++ tailWord_1417108) baseStart_1417108 baseEnd_1417108 := by
    simpa [prefixWord, tailWord_1417108, baseEnd_1417108] using wordTrace_append hprefix tailTrace_1417108
  have hstable : (prefixWord ++ tailWord_1417108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417108).length < 2 ^ (prefixWord ++ tailWord_1417108).sum := by decide
  have hdescent : baseEnd_1417108 < baseStart_1417108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417111 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_1417111 : Nat := 118140960795 + 1417111 * 2 ^ 59
def prefixEnd_1417111 : Nat := 4983230072969 + 3 ^ 40 * 1417111 * 2
def baseEnd_1417111 : Nat := 727659083773710280395331

theorem tailTrace_1417111 : CollatzResearch.WordTrace tailWord_1417111 prefixEnd_1417111 727659083773710280395331 := by
  unfold tailWord_1417111
  simp only [CollatzResearch.WordTrace]
  refine ⟨51686284369056345135451187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34457522912704230090300791 51686284369056345135451187)
  ·
    refine ⟨77529426553584517703176781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51686284369056345135451187 77529426553584517703176781)
    ·
      refine ⟨29073534957594194138691293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77529426553584517703176781 29073534957594194138691293)
      ·
        refine ⟨10902575609097822802009235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29073534957594194138691293 10902575609097822802009235)
        ·
          refine ⟨16353863413646734203013853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10902575609097822802009235 16353863413646734203013853)
          ·
            refine ⟨6132698780117525326130195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16353863413646734203013853 6132698780117525326130195)
            ·
              refine ⟨9199048170176287989195293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6132698780117525326130195 9199048170176287989195293)
              ·
                refine ⟨3449643063816107995948235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9199048170176287989195293 3449643063816107995948235)
                ·
                  refine ⟨5174464595724161993922353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449643063816107995948235 5174464595724161993922353)
                  ·
                    refine ⟨3880848446793121495441765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5174464595724161993922353 3880848446793121495441765)
                    ·
                      refine ⟨727659083773710280395331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3880848446793121495441765 727659083773710280395331)
                      ·
                        rfl

theorem cell23_1417111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_1417111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417111 prefixEnd_1417111 := by exact prefixLift 1417111
  have htrace : WordTrace (prefixWord ++ tailWord_1417111) baseStart_1417111 baseEnd_1417111 := by
    simpa [prefixWord, tailWord_1417111, baseEnd_1417111] using wordTrace_append hprefix tailTrace_1417111
  have hstable : (prefixWord ++ tailWord_1417111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417111).length < 2 ^ (prefixWord ++ tailWord_1417111).sum := by decide
  have hdescent : baseEnd_1417111 < baseStart_1417111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417175 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 1, 3, 2]
def baseStart_1417175 : Nat := 118140960795 + 1417175 * 2 ^ 59
def prefixEnd_1417175 : Nat := 4983230072969 + 3 ^ 40 * 1417175 * 2
def baseEnd_1417175 : Nat := 727691946535598029995037

theorem tailTrace_1417175 : CollatzResearch.WordTrace tailWord_1417175 prefixEnd_1417175 727691946535598029995037 := by
  unfold tailWord_1417175
  simp only [CollatzResearch.WordTrace]
  refine ⟨51688618640824484065780979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34459079093882989377187319 51688618640824484065780979)
  ·
    refine ⟨77532927961236726098671469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51688618640824484065780979 77532927961236726098671469)
    ·
      refine ⟨29074847985463772287001801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77532927961236726098671469 29074847985463772287001801)
      ·
        refine ⟨21806135989097829215251351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29074847985463772287001801 21806135989097829215251351)
        ·
          refine ⟨32709203983646743822877027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21806135989097829215251351 32709203983646743822877027)
          ·
            refine ⟨49063805975470115734315541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32709203983646743822877027 49063805975470115734315541)
            ·
              refine ⟨2299865905100161675046041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49063805975470115734315541 2299865905100161675046041)
              ·
                refine ⟨1724899428825121256284531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2299865905100161675046041 1724899428825121256284531)
                ·
                  refine ⟨2587349143237681884426797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1724899428825121256284531 2587349143237681884426797)
                  ·
                    refine ⟨970255928714130706660049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2587349143237681884426797 970255928714130706660049)
                    ·
                      refine ⟨727691946535598029995037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970255928714130706660049 727691946535598029995037)
                      ·
                        rfl

theorem cell23_1417175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_1417175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417175 prefixEnd_1417175 := by exact prefixLift 1417175
  have htrace : WordTrace (prefixWord ++ tailWord_1417175) baseStart_1417175 baseEnd_1417175 := by
    simpa [prefixWord, tailWord_1417175, baseEnd_1417175] using wordTrace_append hprefix tailTrace_1417175
  have hstable : (prefixWord ++ tailWord_1417175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417175).length < 2 ^ (prefixWord ++ tailWord_1417175).sum := by decide
  have hdescent : baseEnd_1417175 < baseStart_1417175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417188 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 3, 4, 2]
def baseStart_1417188 : Nat := 118140960795 + 1417188 * 2 ^ 59
def prefixEnd_1417188 : Nat := 4983230072969 + 3 ^ 40 * 1417188 * 2
def baseEnd_1417188 : Nat := 727698621784106479132477

theorem tailTrace_1417188 : CollatzResearch.WordTrace tailWord_1417188 prefixEnd_1417188 727698621784106479132477 := by
  unfold tailWord_1417188
  simp only [CollatzResearch.WordTrace]
  refine ⟨25844546394888693643002109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34459395193184924857336145 25844546394888693643002109)
  ·
    refine ⟨9691704898083260116125791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25844546394888693643002109 9691704898083260116125791)
    ·
      refine ⟨14537557347124890174188687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9691704898083260116125791 14537557347124890174188687)
      ·
        refine ⟨21806336020687335261283031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14537557347124890174188687 21806336020687335261283031)
        ·
          refine ⟨32709504031031002891924547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21806336020687335261283031 32709504031031002891924547)
          ·
            refine ⟨49064256046546504337886821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32709504031031002891924547 49064256046546504337886821)
            ·
              refine ⟨9199548008727469563353779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49064256046546504337886821 9199548008727469563353779)
              ·
                refine ⟨13799322013091204345030669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9199548008727469563353779 13799322013091204345030669)
                ·
                  refine ⟨5174745754909201629386501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13799322013091204345030669 5174745754909201629386501)
                  ·
                    refine ⟨970264829045475305509969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5174745754909201629386501 970264829045475305509969)
                    ·
                      refine ⟨727698621784106479132477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970264829045475305509969 727698621784106479132477)
                      ·
                        rfl

theorem cell23_1417188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_1417188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417188 prefixEnd_1417188 := by exact prefixLift 1417188
  have htrace : WordTrace (prefixWord ++ tailWord_1417188) baseStart_1417188 baseEnd_1417188 := by
    simpa [prefixWord, tailWord_1417188, baseEnd_1417188] using wordTrace_append hprefix tailTrace_1417188
  have hstable : (prefixWord ++ tailWord_1417188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417188).length < 2 ^ (prefixWord ++ tailWord_1417188).sum := by decide
  have hdescent : baseEnd_1417188 < baseStart_1417188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417211 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 7]
def baseStart_1417211 : Nat := 118140960795 + 1417211 * 2 ^ 59
def prefixEnd_1417211 : Nat := 4983230072969 + 3 ^ 40 * 1417211 * 2
def baseEnd_1417211 : Nat := 80856714648795543238319

theorem tailTrace_1417211 : CollatzResearch.WordTrace tailWord_1417211 prefixEnd_1417211 80856714648795543238319 := by
  unfold tailWord_1417211
  simp only [CollatzResearch.WordTrace]
  refine ⟨51689931668694062214091487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34459954445796041476060991 51689931668694062214091487)
  ·
    refine ⟨77534897503041093321137231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51689931668694062214091487 77534897503041093321137231)
    ·
      refine ⟨116302346254561639981705847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77534897503041093321137231 116302346254561639981705847)
      ·
        refine ⟨174453519381842459972558771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116302346254561639981705847 174453519381842459972558771)
        ·
          refine ⟨261680279072763689958838157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174453519381842459972558771 261680279072763689958838157)
          ·
            refine ⟨98130104652286383734564309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261680279072763689958838157 98130104652286383734564309)
            ·
              refine ⟨2299924327787962118778851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 98130104652286383734564309 2299924327787962118778851)
              ·
                refine ⟨3449886491681943178168277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2299924327787962118778851 3449886491681943178168277)
                ·
                  refine ⟨80856714648795543238319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3449886491681943178168277 80856714648795543238319)
                  ·
                    rfl

theorem cell23_1417211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 7].length) (baseStart_1417211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417211 prefixEnd_1417211 := by exact prefixLift 1417211
  have htrace : WordTrace (prefixWord ++ tailWord_1417211) baseStart_1417211 baseEnd_1417211 := by
    simpa [prefixWord, tailWord_1417211, baseEnd_1417211] using wordTrace_append hprefix tailTrace_1417211
  have hstable : (prefixWord ++ tailWord_1417211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417211).length < 2 ^ (prefixWord ++ tailWord_1417211).sum := by decide
  have hdescent : baseEnd_1417211 < baseStart_1417211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417251 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1417251 : Nat := 118140960795 + 1417251 * 2 ^ 59
def prefixEnd_1417251 : Nat := 4983230072969 + 3 ^ 40 * 1417251 * 2
def baseEnd_1417251 : Nat := 727730971065339732644687

theorem tailTrace_1417251 : CollatzResearch.WordTrace tailWord_1417251 prefixEnd_1417251 727730971065339732644687 := by
  unfold tailWord_1417251
  simp only [CollatzResearch.WordTrace]
  refine ⟨51691390588549149045547607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34460927059032766030365071 51691390588549149045547607)
  ·
    refine ⟨77537085882823723568321411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51691390588549149045547607 77537085882823723568321411)
    ·
      refine ⟨116305628824235585352482117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77537085882823723568321411 116305628824235585352482117)
      ·
        refine ⟨21807305404544172253590397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116305628824235585352482117 21807305404544172253590397)
        ·
          refine ⟨8177739526704064595096399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21807305404544172253590397 8177739526704064595096399)
          ·
            refine ⟨12266609290056096892644599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8177739526704064595096399 12266609290056096892644599)
            ·
              refine ⟨18399913935084145338966899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12266609290056096892644599 18399913935084145338966899)
              ·
                refine ⟨27599870902626218008450349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18399913935084145338966899 27599870902626218008450349)
                ·
                  refine ⟨10349951588484831753168881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27599870902626218008450349 10349951588484831753168881)
                  ·
                    refine ⟨7762463691363623814876661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10349951588484831753168881 7762463691363623814876661)
                    ·
                      refine ⟨727730971065339732644687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7762463691363623814876661 727730971065339732644687)
                      ·
                        rfl

theorem cell23_1417251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1417251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417251 prefixEnd_1417251 := by exact prefixLift 1417251
  have htrace : WordTrace (prefixWord ++ tailWord_1417251) baseStart_1417251 baseEnd_1417251 := by
    simpa [prefixWord, tailWord_1417251, baseEnd_1417251] using wordTrace_append hprefix tailTrace_1417251
  have hstable : (prefixWord ++ tailWord_1417251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417251).length < 2 ^ (prefixWord ++ tailWord_1417251).sum := by decide
  have hdescent : baseEnd_1417251 < baseStart_1417251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417256 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_1417256 : Nat := 118140960795 + 1417256 * 2 ^ 59
def prefixEnd_1417256 : Nat := 4983230072969 + 3 ^ 40 * 1417256 * 2
def baseEnd_1417256 : Nat := 727733538468612213082165

theorem tailTrace_1417256 : CollatzResearch.WordTrace tailWord_1417256 prefixEnd_1417256 727733538468612213082165 := by
  unfold tailWord_1417256
  simp only [CollatzResearch.WordTrace]
  refine ⟨25845786476765517449739811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34461048635687356599653081 25845786476765517449739811)
  ·
    refine ⟨38768679715148276174609717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25845786476765517449739811 38768679715148276174609717)
    ·
      refine ⟨3634563723295150891369661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38768679715148276174609717 3634563723295150891369661)
      ·
        refine ⟨1362961396235681584263623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3634563723295150891369661 1362961396235681584263623)
        ·
          refine ⟨2044442094353522376395435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362961396235681584263623 2044442094353522376395435)
          ·
            refine ⟨3066663141530283564593153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044442094353522376395435 3066663141530283564593153)
            ·
              refine ⟨2299997356147712673444865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3066663141530283564593153 2299997356147712673444865)
              ·
                refine ⟨1724998017110784505083649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2299997356147712673444865 1724998017110784505083649)
                ·
                  refine ⟨1293748512833088378812737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1724998017110784505083649 1293748512833088378812737)
                  ·
                    refine ⟨970311384624816284109553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1293748512833088378812737 970311384624816284109553)
                    ·
                      refine ⟨727733538468612213082165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970311384624816284109553 727733538468612213082165)
                      ·
                        rfl

theorem cell23_1417256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_1417256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417256 prefixEnd_1417256 := by exact prefixLift 1417256
  have htrace : WordTrace (prefixWord ++ tailWord_1417256) baseStart_1417256 baseEnd_1417256 := by
    simpa [prefixWord, tailWord_1417256, baseEnd_1417256] using wordTrace_append hprefix tailTrace_1417256
  have hstable : (prefixWord ++ tailWord_1417256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417256).length < 2 ^ (prefixWord ++ tailWord_1417256).sum := by decide
  have hdescent : baseEnd_1417256 < baseStart_1417256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417262 : List Nat := [4, 1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_1417262 : Nat := 118140960795 + 1417262 * 2 ^ 59
def prefixEnd_1417262 : Nat := 4983230072969 + 3 ^ 40 * 1417262 * 2
def baseEnd_1417262 : Nat := 80859624372504354400793

theorem tailTrace_1417262 : CollatzResearch.WordTrace tailWord_1417262 prefixEnd_1417262 80859624372504354400793 := by
  unfold tailWord_1417262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6461473973938662240524755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34461194527672865282798693 6461473973938662240524755)
  ·
    refine ⟨9692210960907993360787133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6461473973938662240524755 9692210960907993360787133)
    ·
      refine ⟨3634579110340497510295175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9692210960907993360787133 3634579110340497510295175)
      ·
        refine ⟨5451868665510746265442763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3634579110340497510295175 5451868665510746265442763)
        ·
          refine ⟨8177802998266119398164145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5451868665510746265442763 8177802998266119398164145)
          ·
            refine ⟨6133352248699589548623109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8177802998266119398164145 6133352248699589548623109)
            ·
              refine ⟨1150003546631173040366833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6133352248699589548623109 1150003546631173040366833)
              ·
                refine ⟨862502659973379780275125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150003546631173040366833 862502659973379780275125)
                ·
                  refine ⟨80859624372504354400793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 862502659973379780275125 80859624372504354400793)
                  ·
                    rfl

theorem cell23_1417262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_1417262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417262 prefixEnd_1417262 := by exact prefixLift 1417262
  have htrace : WordTrace (prefixWord ++ tailWord_1417262) baseStart_1417262 baseEnd_1417262 := by
    simpa [prefixWord, tailWord_1417262, baseEnd_1417262] using wordTrace_append hprefix tailTrace_1417262
  have hstable : (prefixWord ++ tailWord_1417262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417262).length < 2 ^ (prefixWord ++ tailWord_1417262).sum := by decide
  have hdescent : baseEnd_1417262 < baseStart_1417262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417291 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 4]
def baseStart_1417291 : Nat := 118140960795 + 1417291 * 2 ^ 59
def prefixEnd_1417291 : Nat := 4983230072969 + 3 ^ 40 * 1417291 * 2
def baseEnd_1417291 : Nat := 727751510291519576144503

theorem tailTrace_1417291 : CollatzResearch.WordTrace tailWord_1417291 prefixEnd_1417291 727751510291519576144503 := by
  unfold tailWord_1417291
  simp only [CollatzResearch.WordTrace]
  refine ⟨51692849508404235877003727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34461899672269490584669151 51692849508404235877003727)
  ·
    refine ⟨77539274262606353815505591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51692849508404235877003727 77539274262606353815505591)
    ·
      refine ⟨116308911393909530723258387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77539274262606353815505591 116308911393909530723258387)
      ·
        refine ⟨174463367090864296084887581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116308911393909530723258387 174463367090864296084887581)
        ·
          refine ⟨65423762659074111031832843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174463367090864296084887581 65423762659074111031832843)
          ·
            refine ⟨98135643988611166547749265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65423762659074111031832843 98135643988611166547749265)
            ·
              refine ⟨73601732991458374910811949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98135643988611166547749265 73601732991458374910811949)
              ·
                refine ⟨27600649871796890591554481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73601732991458374910811949 27600649871796890591554481)
                ·
                  refine ⟨20700487403847667943665861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27600649871796890591554481 20700487403847667943665861)
                  ·
                    refine ⟨3881341388221437739437349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20700487403847667943665861 3881341388221437739437349)
                    ·
                      refine ⟨727751510291519576144503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3881341388221437739437349 727751510291519576144503)
                      ·
                        rfl

theorem cell23_1417291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 4].length) (baseStart_1417291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417291 prefixEnd_1417291 := by exact prefixLift 1417291
  have htrace : WordTrace (prefixWord ++ tailWord_1417291) baseStart_1417291 baseEnd_1417291 := by
    simpa [prefixWord, tailWord_1417291, baseEnd_1417291] using wordTrace_append hprefix tailTrace_1417291
  have hstable : (prefixWord ++ tailWord_1417291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417291).length < 2 ^ (prefixWord ++ tailWord_1417291).sum := by decide
  have hdescent : baseEnd_1417291 < baseStart_1417291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417308 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1417308 : Nat := 118140960795 + 1417308 * 2 ^ 59
def prefixEnd_1417308 : Nat := 4983230072969 + 3 ^ 40 * 1417308 * 2
def baseEnd_1417308 : Nat := 727760239462646009631925

theorem tailTrace_1417308 : CollatzResearch.WordTrace tailWord_1417308 prefixEnd_1417308 727760239462646009631925 := by
  unfold tailWord_1417308
  simp only [CollatzResearch.WordTrace]
  refine ⟨25846734774671323890186289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34462313032895098520248385 25846734774671323890186289)
  ·
    refine ⟨19385051081003492917639717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25846734774671323890186289 19385051081003492917639717)
    ·
      refine ⟨3634697077688154922057447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19385051081003492917639717 3634697077688154922057447)
      ·
        refine ⟨5452045616532232383086171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3634697077688154922057447 5452045616532232383086171)
        ·
          refine ⟨8178068424798348574629257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5452045616532232383086171 8178068424798348574629257)
          ·
            refine ⟨6133551318598761430971943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8178068424798348574629257 6133551318598761430971943)
            ·
              refine ⟨9200326977898142146457915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6133551318598761430971943 9200326977898142146457915)
              ·
                refine ⟨13800490466847213219686873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9200326977898142146457915 13800490466847213219686873)
                ·
                  refine ⟨10350367850135409914765155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13800490466847213219686873 10350367850135409914765155)
                  ·
                    refine ⟨15525551775203114872147733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10350367850135409914765155 15525551775203114872147733)
                    ·
                      refine ⟨727760239462646009631925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15525551775203114872147733 727760239462646009631925)
                      ·
                        rfl

theorem cell23_1417308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1417308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417308 prefixEnd_1417308 := by exact prefixLift 1417308
  have htrace : WordTrace (prefixWord ++ tailWord_1417308) baseStart_1417308 baseEnd_1417308 := by
    simpa [prefixWord, tailWord_1417308, baseEnd_1417308] using wordTrace_append hprefix tailTrace_1417308
  have hstable : (prefixWord ++ tailWord_1417308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417308).length < 2 ^ (prefixWord ++ tailWord_1417308).sum := by decide
  have hdescent : baseEnd_1417308 < baseStart_1417308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417321 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_1417321 : Nat := 118140960795 + 1417321 * 2 ^ 59
def prefixEnd_1417321 : Nat := 4983230072969 + 3 ^ 40 * 1417321 * 2
def baseEnd_1417321 : Nat := 727766914711154458769365

theorem tailTrace_1417321 : CollatzResearch.WordTrace tailWord_1417321 prefixEnd_1417321 727766914711154458769365 := by
  unfold tailWord_1417321
  simp only [CollatzResearch.WordTrace]
  refine ⟨51693943698295551000595817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34462629132197034000397211 51693943698295551000595817)
  ·
    refine ⟨38770457773721663250446863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51693943698295551000595817 38770457773721663250446863)
    ·
      refine ⟨58155686660582494875670295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38770457773721663250446863 58155686660582494875670295)
      ·
        refine ⟨87233529990873742313505443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58155686660582494875670295 87233529990873742313505443)
        ·
          refine ⟨130850294986310613470258165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87233529990873742313505443 130850294986310613470258165)
          ·
            refine ⟨12267215154966620012836703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130850294986310613470258165 12267215154966620012836703)
            ·
              refine ⟨18400822732449930019255055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12267215154966620012836703 18400822732449930019255055)
              ·
                refine ⟨27601234098674895028882583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18400822732449930019255055 27601234098674895028882583)
                ·
                  refine ⟨41401851148012342543323875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27601234098674895028882583 41401851148012342543323875)
                  ·
                    refine ⟨62102776722018513814985813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41401851148012342543323875 62102776722018513814985813)
                    ·
                      refine ⟨727766914711154458769365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 62102776722018513814985813 727766914711154458769365)
                      ·
                        rfl

theorem cell23_1417321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_1417321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417321 prefixEnd_1417321 := by exact prefixLift 1417321
  have htrace : WordTrace (prefixWord ++ tailWord_1417321) baseStart_1417321 baseEnd_1417321 := by
    simpa [prefixWord, tailWord_1417321, baseEnd_1417321] using wordTrace_append hprefix tailTrace_1417321
  have hstable : (prefixWord ++ tailWord_1417321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417321).length < 2 ^ (prefixWord ++ tailWord_1417321).sum := by decide
  have hdescent : baseEnd_1417321 < baseStart_1417321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417322 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 3, 4]
def baseStart_1417322 : Nat := 118140960795 + 1417322 * 2 ^ 59
def prefixEnd_1417322 : Nat := 4983230072969 + 3 ^ 40 * 1417322 * 2
def baseEnd_1417322 : Nat := 242589142730602984952287

theorem tailTrace_1417322 : CollatzResearch.WordTrace tailWord_1417322 prefixEnd_1417322 242589142730602984952287 := by
  unfold tailWord_1417322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12923495042822982042845555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34462653447527952114254813 12923495042822982042845555)
  ·
    refine ⟨19385242564234473064268333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12923495042822982042845555 19385242564234473064268333)
    ·
      refine ⟨7269465961587927399100625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19385242564234473064268333 7269465961587927399100625)
      ·
        refine ⟨5452099471190945549325469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7269465961587927399100625 5452099471190945549325469)
        ·
          refine ⟨2044537301696604580997051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5452099471190945549325469 2044537301696604580997051)
          ·
            refine ⟨3066805952544906871495577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044537301696604580997051 3066805952544906871495577)
            ·
              refine ⟨2300104464408680153621683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3066805952544906871495577 2300104464408680153621683)
              ·
                refine ⟨3450156696613020230432525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2300104464408680153621683 3450156696613020230432525)
                ·
                  refine ⟨1293808761229882586412197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3450156696613020230432525 1293808761229882586412197)
                  ·
                    refine ⟨242589142730602984952287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1293808761229882586412197 242589142730602984952287)
                    ·
                      rfl

theorem cell23_1417322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_1417322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417322 prefixEnd_1417322 := by exact prefixLift 1417322
  have htrace : WordTrace (prefixWord ++ tailWord_1417322) baseStart_1417322 baseEnd_1417322 := by
    simpa [prefixWord, tailWord_1417322, baseEnd_1417322] using wordTrace_append hprefix tailTrace_1417322
  have hstable : (prefixWord ++ tailWord_1417322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417322).length < 2 ^ (prefixWord ++ tailWord_1417322).sum := by decide
  have hdescent : baseEnd_1417322 < baseStart_1417322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417335 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 6]
def baseStart_1417335 : Nat := 118140960795 + 1417335 * 2 ^ 59
def prefixEnd_1417335 : Nat := 4983230072969 + 3 ^ 40 * 1417335 * 2
def baseEnd_1417335 : Nat := 80863789271146378221589

theorem tailTrace_1417335 : CollatzResearch.WordTrace tailWord_1417335 prefixEnd_1417335 80863789271146378221589 := by
  unfold tailWord_1417335
  simp only [CollatzResearch.WordTrace]
  refine ⟨51694454320244831391605459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34462969546829887594403639 51694454320244831391605459)
  ·
    refine ⟨77541681480367247087408189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51694454320244831391605459 77541681480367247087408189)
    ·
      refine ⟨29078130555137717657778071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77541681480367247087408189 29078130555137717657778071)
      ·
        refine ⟨43617195832706576486667107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29078130555137717657778071 43617195832706576486667107)
        ·
          refine ⟨65425793749059864730000661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43617195832706576486667107 65425793749059864730000661)
          ·
            refine ⟨3066834081987181159218781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65425793749059864730000661 3066834081987181159218781)
            ·
              refine ⟨1150062780745192934707043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3066834081987181159218781 1150062780745192934707043)
              ·
                refine ⟨1725094171117789402060565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150062780745192934707043 1725094171117789402060565)
                ·
                  refine ⟨80863789271146378221589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1725094171117789402060565 80863789271146378221589)
                  ·
                    rfl

theorem cell23_1417335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 6].length) (baseStart_1417335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417335 prefixEnd_1417335 := by exact prefixLift 1417335
  have htrace : WordTrace (prefixWord ++ tailWord_1417335) baseStart_1417335 baseEnd_1417335 := by
    simpa [prefixWord, tailWord_1417335, baseEnd_1417335] using wordTrace_append hprefix tailTrace_1417335
  have hstable : (prefixWord ++ tailWord_1417335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417335).length < 2 ^ (prefixWord ++ tailWord_1417335).sum := by decide
  have hdescent : baseEnd_1417335 < baseStart_1417335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417372 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_1417372 : Nat := 118140960795 + 1417372 * 2 ^ 59
def prefixEnd_1417372 : Nat := 4983230072969 + 3 ^ 40 * 1417372 * 2
def baseEnd_1417372 : Nat := 727793102224533759231631

theorem tailTrace_1417372 : CollatzResearch.WordTrace tailWord_1417372 prefixEnd_1417372 727793102224533759231631 := by
  unfold tailWord_1417372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25847901910555393355351185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34463869214073857807134913 25847901910555393355351185)
  ·
    refine ⟨19385926432916545016513389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25847901910555393355351185 19385926432916545016513389)
    ·
      refine ⟨7269722412343704381192521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19385926432916545016513389 7269722412343704381192521)
      ·
        refine ⟨5452291809257778285894391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7269722412343704381192521 5452291809257778285894391)
        ·
          refine ⟨8178437713886667428841587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5452291809257778285894391 8178437713886667428841587)
          ·
            refine ⟨12267656570830001143262381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8178437713886667428841587 12267656570830001143262381)
            ·
              refine ⟨4600371214061250428723393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12267656570830001143262381 4600371214061250428723393)
              ·
                refine ⟨3450278410545937821542545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4600371214061250428723393 3450278410545937821542545)
                ·
                  refine ⟨2587708807909453366156909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3450278410545937821542545 2587708807909453366156909)
                  ·
                    refine ⟨970390802966045012308841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2587708807909453366156909 970390802966045012308841)
                    ·
                      refine ⟨727793102224533759231631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970390802966045012308841 727793102224533759231631)
                      ·
                        rfl

theorem cell23_1417372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_1417372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417372 prefixEnd_1417372 := by exact prefixLift 1417372
  have htrace : WordTrace (prefixWord ++ tailWord_1417372) baseStart_1417372 baseEnd_1417372 := by
    simpa [prefixWord, tailWord_1417372, baseEnd_1417372] using wordTrace_append hprefix tailTrace_1417372
  have hstable : (prefixWord ++ tailWord_1417372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417372).length < 2 ^ (prefixWord ++ tailWord_1417372).sum := by decide
  have hdescent : baseEnd_1417372 < baseStart_1417372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417386 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 6]
def baseStart_1417386 : Nat := 118140960795 + 1417386 * 2 ^ 59
def prefixEnd_1417386 : Nat := 4983230072969 + 3 ^ 40 * 1417386 * 2
def baseEnd_1417386 : Nat := 80866698994855189384063

theorem tailTrace_1417386 : CollatzResearch.WordTrace tailWord_1417386 prefixEnd_1417386 80866698994855189384063 := by
  unfold tailWord_1417386
  simp only [CollatzResearch.WordTrace]
  refine ⟨12924078610765016775428003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34464209628706711401141341 12924078610765016775428003)
  ·
    refine ⟨19386117916147525163142005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12924078610765016775428003 19386117916147525163142005)
    ·
      refine ⟨1817448554638830484044563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19386117916147525163142005 1817448554638830484044563)
      ·
        refine ⟨2726172831958245726066845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817448554638830484044563 2726172831958245726066845)
        ·
          refine ⟨1022314811984342147275067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2726172831958245726066845 1022314811984342147275067)
          ·
            refine ⟨1533472217976513220912601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022314811984342147275067 1533472217976513220912601)
            ·
              refine ⟨1150104163482384915684451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1533472217976513220912601 1150104163482384915684451)
              ·
                refine ⟨1725156245223577373526677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150104163482384915684451 1725156245223577373526677)
                ·
                  refine ⟨80866698994855189384063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1725156245223577373526677 80866698994855189384063)
                  ·
                    rfl

theorem cell23_1417386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_1417386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417386 prefixEnd_1417386 := by exact prefixLift 1417386
  have htrace : WordTrace (prefixWord ++ tailWord_1417386) baseStart_1417386 baseEnd_1417386 := by
    simpa [prefixWord, tailWord_1417386, baseEnd_1417386] using wordTrace_append hprefix tailTrace_1417386
  have hstable : (prefixWord ++ tailWord_1417386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417386).length < 2 ^ (prefixWord ++ tailWord_1417386).sum := by decide
  have hdescent : baseEnd_1417386 < baseStart_1417386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417402 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2]
def baseStart_1417402 : Nat := 118140960795 + 1417402 * 2 ^ 59
def prefixEnd_1417402 : Nat := 4983230072969 + 3 ^ 40 * 1417402 * 2
def baseEnd_1417402 : Nat := 727808506644168641856493

theorem tailTrace_1417402 : CollatzResearch.WordTrace tailWord_1417402 prefixEnd_1417402 727808506644168641856493 := by
  unfold tailWord_1417402
  simp only [CollatzResearch.WordTrace]
  refine ⟨12924224502750525458573615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34464598674001401222862973 12924224502750525458573615)
  ·
    refine ⟨19386336754125788187860423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12924224502750525458573615 19386336754125788187860423)
    ·
      refine ⟨29079505131188682281790635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19386336754125788187860423 29079505131188682281790635)
      ·
        refine ⟨43619257696783023422685953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29079505131188682281790635 43619257696783023422685953)
        ·
          refine ⟨32714443272587267567014465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43619257696783023422685953 32714443272587267567014465)
          ·
            refine ⟨24535832454440450675260849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32714443272587267567014465 24535832454440450675260849)
            ·
              refine ⟨18401874340830338006445637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24535832454440450675260849 18401874340830338006445637)
              ·
                refine ⟨3450351438905688376208557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18401874340830338006445637 3450351438905688376208557)
                ·
                  refine ⟨1293881789589633141078209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3450351438905688376208557 1293881789589633141078209)
                  ·
                    refine ⟨970411342192224855808657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1293881789589633141078209 970411342192224855808657)
                    ·
                      refine ⟨727808506644168641856493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970411342192224855808657 727808506644168641856493)
                      ·
                        rfl

theorem cell23_1417402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2].length) (baseStart_1417402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417402 prefixEnd_1417402 := by exact prefixLift 1417402
  have htrace : WordTrace (prefixWord ++ tailWord_1417402) baseStart_1417402 baseEnd_1417402 := by
    simpa [prefixWord, tailWord_1417402, baseEnd_1417402] using wordTrace_append hprefix tailTrace_1417402
  have hstable : (prefixWord ++ tailWord_1417402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417402).length < 2 ^ (prefixWord ++ tailWord_1417402).sum := by decide
  have hdescent : baseEnd_1417402 < baseStart_1417402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417408 : List Nat := [2, 1, 1, 2, 5, 1, 2, 9]
def baseStart_1417408 : Nat := 118140960795 + 1417408 * 2 ^ 59
def prefixEnd_1417408 : Nat := 4983230072969 + 3 ^ 40 * 1417408 * 2
def baseEnd_1417408 : Nat := 26955984723262800680795

theorem tailTrace_1417408 : CollatzResearch.WordTrace tailWord_1417408 prefixEnd_1417408 26955984723262800680795 := by
  unfold tailWord_1417408
  simp only [CollatzResearch.WordTrace]
  refine ⟨25848558424490182429506439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34464744565986909906008585 25848558424490182429506439)
  ·
    refine ⟨38772837636735273644259659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25848558424490182429506439 38772837636735273644259659)
    ·
      refine ⟨58159256455102910466389489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38772837636735273644259659 58159256455102910466389489)
      ·
        refine ⟨43619442341327182849792117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58159256455102910466389489 43619442341327182849792117)
        ·
          refine ⟨4089322719499423392168011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43619442341327182849792117 4089322719499423392168011)
          ·
            refine ⟨6133984079249135088252017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089322719499423392168011 6133984079249135088252017)
            ·
              refine ⟨4600488059436851316189013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6133984079249135088252017 4600488059436851316189013)
              ·
                refine ⟨26955984723262800680795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4600488059436851316189013 26955984723262800680795)
                ·
                  rfl

theorem cell23_1417408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 9].length) (baseStart_1417408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417408 prefixEnd_1417408 := by exact prefixLift 1417408
  have htrace : WordTrace (prefixWord ++ tailWord_1417408) baseStart_1417408 baseEnd_1417408 := by
    simpa [prefixWord, tailWord_1417408, baseEnd_1417408] using wordTrace_append hprefix tailTrace_1417408
  have hstable : (prefixWord ++ tailWord_1417408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417408).length < 2 ^ (prefixWord ++ tailWord_1417408).sum := by decide
  have hdescent : baseEnd_1417408 < baseStart_1417408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417419 : List Nat := [1, 1, 1, 1, 3, 2, 4, 5, 1, 2, 2]
def baseStart_1417419 : Nat := 118140960795 + 1417419 * 2 ^ 59
def prefixEnd_1417419 : Nat := 4983230072969 + 3 ^ 40 * 1417419 * 2
def baseEnd_1417419 : Nat := 727817235815295075343915

theorem tailTrace_1417419 : CollatzResearch.WordTrace tailWord_1417419 prefixEnd_1417419 727817235815295075343915 := by
  unfold tailWord_1417419
  simp only [CollatzResearch.WordTrace]
  refine ⟨51697518051940513737663311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34465012034627009158442207 51697518051940513737663311)
  ·
    refine ⟨77546277077910770606494967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51697518051940513737663311 77546277077910770606494967)
    ·
      refine ⟨116319415616866155909742451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77546277077910770606494967 116319415616866155909742451)
      ·
        refine ⟨174479123425299233864613677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116319415616866155909742451 174479123425299233864613677)
        ·
          refine ⟨65429671284487212699230129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174479123425299233864613677 65429671284487212699230129)
          ·
            refine ⟨49072253463365409524422597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65429671284487212699230129 49072253463365409524422597)
            ·
              refine ⟨9201047524381014285829237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49072253463365409524422597 9201047524381014285829237)
              ·
                refine ⟨862598205410720089296491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9201047524381014285829237 862598205410720089296491)
                ·
                  refine ⟨1293897308116080133944737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862598205410720089296491 1293897308116080133944737)
                  ·
                    refine ⟨970422981087060100458553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1293897308116080133944737 970422981087060100458553)
                    ·
                      refine ⟨727817235815295075343915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970422981087060100458553 727817235815295075343915)
                      ·
                        rfl

theorem cell23_1417419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 1, 2, 2].length) (baseStart_1417419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417419 prefixEnd_1417419 := by exact prefixLift 1417419
  have htrace : WordTrace (prefixWord ++ tailWord_1417419) baseStart_1417419 baseEnd_1417419 := by
    simpa [prefixWord, tailWord_1417419, baseEnd_1417419] using wordTrace_append hprefix tailTrace_1417419
  have hstable : (prefixWord ++ tailWord_1417419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417419).length < 2 ^ (prefixWord ++ tailWord_1417419).sum := by decide
  have hdescent : baseEnd_1417419 < baseStart_1417419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417422 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_1417422 : Nat := 118140960795 + 1417422 * 2 ^ 59
def prefixEnd_1417422 : Nat := 4983230072969 + 3 ^ 40 * 1417422 * 2
def baseEnd_1417422 : Nat := 727818776257258563606401

theorem tailTrace_1417422 : CollatzResearch.WordTrace tailWord_1417422 prefixEnd_1417422 727818776257258563606401 := by
  unfold tailWord_1417422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6462203433866205656252815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34465084980619763500015013 6462203433866205656252815)
  ·
    refine ⟨9693305150799308484379223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6462203433866205656252815 9693305150799308484379223)
    ·
      refine ⟨14539957726198962726568835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9693305150799308484379223 14539957726198962726568835)
      ·
        refine ⟨21809936589298444089853253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14539957726198962726568835 21809936589298444089853253)
        ·
          refine ⟨4089363110493458266847485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21809936589298444089853253 4089363110493458266847485)
          ·
            refine ⟨1533511166435046850067807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4089363110493458266847485 1533511166435046850067807)
            ·
              refine ⟨2300266749652570275101711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533511166435046850067807 2300266749652570275101711)
              ·
                refine ⟨3450400124478855412652567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2300266749652570275101711 3450400124478855412652567)
                ·
                  refine ⟨5175600186718283118978851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3450400124478855412652567 5175600186718283118978851)
                  ·
                    refine ⟨7763400280077424678468277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5175600186718283118978851 7763400280077424678468277)
                    ·
                      refine ⟨727818776257258563606401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7763400280077424678468277 727818776257258563606401)
                      ·
                        rfl

theorem cell23_1417422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_1417422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417422 prefixEnd_1417422 := by exact prefixLift 1417422
  have htrace : WordTrace (prefixWord ++ tailWord_1417422) baseStart_1417422 baseEnd_1417422 := by
    simpa [prefixWord, tailWord_1417422, baseEnd_1417422] using wordTrace_append hprefix tailTrace_1417422
  have hstable : (prefixWord ++ tailWord_1417422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417422).length < 2 ^ (prefixWord ++ tailWord_1417422).sum := by decide
  have hdescent : baseEnd_1417422 < baseStart_1417422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417429 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 2, 4]
def baseStart_1417429 : Nat := 118140960795 + 1417429 * 2 ^ 59
def prefixEnd_1417429 : Nat := 4983230072969 + 3 ^ 40 * 1417429 * 2
def baseEnd_1417429 : Nat := 242607456873946678739623

theorem tailTrace_1417429 : CollatzResearch.WordTrace tailWord_1417429 prefixEnd_1417429 242607456873946678739623 := by
  unfold tailWord_1417429
  simp only [CollatzResearch.WordTrace]
  refine ⟨51697882781904285445527341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34465255187936190297018227 51697882781904285445527341)
  ·
    refine ⟨19386706043214107042072753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51697882781904285445527341 19386706043214107042072753)
    ·
      refine ⟨14540029532410580281554565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19386706043214107042072753 14540029532410580281554565)
      ·
        refine ⟨2726255537326983802791481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14540029532410580281554565 2726255537326983802791481)
        ·
          refine ⟨2044691652995237852093611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2726255537326983802791481 2044691652995237852093611)
          ·
            refine ⟨3067037479492856778140417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044691652995237852093611 3067037479492856778140417)
            ·
              refine ⟨2300278109619642583605313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3067037479492856778140417 2300278109619642583605313)
              ·
                refine ⟨1725208582214731937703985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300278109619642583605313 1725208582214731937703985)
                ·
                  refine ⟨1293906436661048953277989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1725208582214731937703985 1293906436661048953277989)
                  ·
                    refine ⟨242607456873946678739623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1293906436661048953277989 242607456873946678739623)
                    ·
                      rfl

theorem cell23_1417429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_1417429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417429 prefixEnd_1417429 := by exact prefixLift 1417429
  have htrace : WordTrace (prefixWord ++ tailWord_1417429) baseStart_1417429 baseEnd_1417429 := by
    simpa [prefixWord, tailWord_1417429, baseEnd_1417429] using wordTrace_append hprefix tailTrace_1417429
  have hstable : (prefixWord ++ tailWord_1417429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417429).length < 2 ^ (prefixWord ++ tailWord_1417429).sum := by decide
  have hdescent : baseEnd_1417429 < baseStart_1417429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417430 : List Nat := [5, 2, 1, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_1417430 : Nat := 118140960795 + 1417430 * 2 ^ 59
def prefixEnd_1417430 : Nat := 4983230072969 + 3 ^ 40 * 1417430 * 2
def baseEnd_1417430 : Nat := 727822884102494532306365

theorem tailTrace_1417430 : CollatzResearch.WordTrace tailWord_1417430 prefixEnd_1417430 727822884102494532306365 := by
  unfold tailWord_1417430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231119953431291413519609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34465279503267108410875829 3231119953431291413519609)
  ·
    refine ⟨2423339965073468560139707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3231119953431291413519609 2423339965073468560139707)
    ·
      refine ⟨3635009947610202840209561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2423339965073468560139707 3635009947610202840209561)
      ·
        refine ⟨2726257460707652130157171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3635009947610202840209561 2726257460707652130157171)
        ·
          refine ⟨4089386191061478195235757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726257460707652130157171 4089386191061478195235757)
          ·
            refine ⟨1533519821648054323213409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4089386191061478195235757 1533519821648054323213409)
            ·
              refine ⟨1150139866236040742410057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1533519821648054323213409 1150139866236040742410057)
              ·
                refine ⟨862604899677030556807543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150139866236040742410057 862604899677030556807543)
                ·
                  refine ⟨1293907349515545835211315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862604899677030556807543 1293907349515545835211315)
                  ·
                    refine ⟨1940861024273318752816973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1293907349515545835211315 1940861024273318752816973)
                    ·
                      refine ⟨727822884102494532306365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1940861024273318752816973 727822884102494532306365)
                      ·
                        rfl

theorem cell23_1417430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_1417430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417430 prefixEnd_1417430 := by exact prefixLift 1417430
  have htrace : WordTrace (prefixWord ++ tailWord_1417430) baseStart_1417430 baseEnd_1417430 := by
    simpa [prefixWord, tailWord_1417430, baseEnd_1417430] using wordTrace_append hprefix tailTrace_1417430
  have hstable : (prefixWord ++ tailWord_1417430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417430).length < 2 ^ (prefixWord ++ tailWord_1417430).sum := by decide
  have hdescent : baseEnd_1417430 < baseStart_1417430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417452 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 3]
def baseStart_1417452 : Nat := 118140960795 + 1417452 * 2 ^ 59
def prefixEnd_1417452 : Nat := 4983230072969 + 3 ^ 40 * 1417452 * 2
def baseEnd_1417452 : Nat := 727834180676893446231263

theorem tailTrace_1417452 : CollatzResearch.WordTrace tailWord_1417452 prefixEnd_1417452 727834180676893446231263 := by
  unfold tailWord_1417452
  simp only [CollatzResearch.WordTrace]
  refine ⟨25849360830410480186807305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34465814440547306915743073 25849360830410480186807305)
  ·
    refine ⟨19387020622807860140105479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25849360830410480186807305 19387020622807860140105479)
    ·
      refine ⟨29080530934211790210158219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19387020622807860140105479 29080530934211790210158219)
      ·
        refine ⟨43620796401317685315237329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29080530934211790210158219 43620796401317685315237329)
        ·
          refine ⟨32715597300988263986427997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43620796401317685315237329 32715597300988263986427997)
          ·
            refine ⟨12268348987870598994910499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32715597300988263986427997 12268348987870598994910499)
            ·
              refine ⟨18402523481805898492365749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12268348987870598994910499 18402523481805898492365749)
              ·
                refine ⟨1725236576419302983659289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18402523481805898492365749 1725236576419302983659289)
                ·
                  refine ⟨1293927432314477237744467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1725236576419302983659289 1293927432314477237744467)
                  ·
                    refine ⟨1940891148471715856616701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1293927432314477237744467 1940891148471715856616701)
                    ·
                      refine ⟨727834180676893446231263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1940891148471715856616701 727834180676893446231263)
                      ·
                        rfl

theorem cell23_1417452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_1417452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417452 prefixEnd_1417452 := by exact prefixLift 1417452
  have htrace : WordTrace (prefixWord ++ tailWord_1417452) baseStart_1417452 baseEnd_1417452 := by
    simpa [prefixWord, tailWord_1417452, baseEnd_1417452] using wordTrace_append hprefix tailTrace_1417452
  have hstable : (prefixWord ++ tailWord_1417452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417452).length < 2 ^ (prefixWord ++ tailWord_1417452).sum := by decide
  have hdescent : baseEnd_1417452 < baseStart_1417452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417488 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 4]
def baseStart_1417488 : Nat := 118140960795 + 1417488 * 2 ^ 59
def prefixEnd_1417488 : Nat := 4983230072969 + 3 ^ 40 * 1417488 * 2
def baseEnd_1417488 : Nat := 727852665980455305381097

theorem tailTrace_1417488 : CollatzResearch.WordTrace tailWord_1417488 prefixEnd_1417488 727852665980455305381097 := by
  unfold tailWord_1417488
  simp only [CollatzResearch.WordTrace]
  refine ⟨25850017344345269260962559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34466689792460359014616745 25850017344345269260962559)
  ·
    refine ⟨38775026016517903891443839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25850017344345269260962559 38775026016517903891443839)
    ·
      refine ⟨58162539024776855837165759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38775026016517903891443839 58162539024776855837165759)
      ·
        refine ⟨87243808537165283755748639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58162539024776855837165759 87243808537165283755748639)
        ·
          refine ⟨130865712805747925633622959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87243808537165283755748639 130865712805747925633622959)
          ·
            refine ⟨196298569208621888450434439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130865712805747925633622959 196298569208621888450434439)
            ·
              refine ⟨294447853812932832675651659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196298569208621888450434439 294447853812932832675651659)
              ·
                refine ⟨441671780719399249013477489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294447853812932832675651659 441671780719399249013477489)
                ·
                  refine ⟨331253835539549436760108117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441671780719399249013477489 331253835539549436760108117)
                  ·
                    refine ⟨3881880885229094962032517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 331253835539549436760108117 3881880885229094962032517)
                    ·
                      refine ⟨727852665980455305381097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3881880885229094962032517 727852665980455305381097)
                      ·
                        rfl

theorem cell23_1417488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 4].length) (baseStart_1417488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417488 prefixEnd_1417488 := by exact prefixLift 1417488
  have htrace : WordTrace (prefixWord ++ tailWord_1417488) baseStart_1417488 baseEnd_1417488 := by
    simpa [prefixWord, tailWord_1417488, baseEnd_1417488] using wordTrace_append hprefix tailTrace_1417488
  have hstable : (prefixWord ++ tailWord_1417488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417488).length < 2 ^ (prefixWord ++ tailWord_1417488).sum := by decide
  have hdescent : baseEnd_1417488 < baseStart_1417488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417505 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_1417505 : Nat := 118140960795 + 1417505 * 2 ^ 59
def prefixEnd_1417505 : Nat := 4983230072969 + 3 ^ 40 * 1417505 * 2
def baseEnd_1417505 : Nat := 727861395151581738868519

theorem tailTrace_1417505 : CollatzResearch.WordTrace tailWord_1417505 prefixEnd_1417505 727861395151581738868519 := by
  unfold tailWord_1417505
  simp only [CollatzResearch.WordTrace]
  refine ⟨51700654729628950425293969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34467103153085966950195979 51700654729628950425293969)
  ·
    refine ⟨38775491047221712818970477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51700654729628950425293969 38775491047221712818970477)
    ·
      refine ⟨14540809142708142307113929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38775491047221712818970477 14540809142708142307113929)
      ·
        refine ⟨10905606857031106730335447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14540809142708142307113929 10905606857031106730335447)
        ·
          refine ⟨16358410285546660095503171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10905606857031106730335447 16358410285546660095503171)
          ·
            refine ⟨24537615428319990143254757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16358410285546660095503171 24537615428319990143254757)
            ·
              refine ⟨4600802892809998151860267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24537615428319990143254757 4600802892809998151860267)
              ·
                refine ⟨6901204339214997227790401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4600802892809998151860267 6901204339214997227790401)
                ·
                  refine ⟨5175903254411247920842801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6901204339214997227790401 5175903254411247920842801)
                  ·
                    refine ⟨3881927440808435940632101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5175903254411247920842801 3881927440808435940632101)
                    ·
                      refine ⟨727861395151581738868519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3881927440808435940632101 727861395151581738868519)
                      ·
                        rfl

theorem cell23_1417505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_1417505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417505 prefixEnd_1417505 := by exact prefixLift 1417505
  have htrace : WordTrace (prefixWord ++ tailWord_1417505) baseStart_1417505 baseEnd_1417505 := by
    simpa [prefixWord, tailWord_1417505, baseEnd_1417505] using wordTrace_append hprefix tailTrace_1417505
  have hstable : (prefixWord ++ tailWord_1417505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417505).length < 2 ^ (prefixWord ++ tailWord_1417505).sum := by decide
  have hdescent : baseEnd_1417505 < baseStart_1417505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417633 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 2, 1, 4]
def baseStart_1417633 : Nat := 118140960795 + 1417633 * 2 ^ 59
def prefixEnd_1417633 : Nat := 4983230072969 + 3 ^ 40 * 1417633 * 2
def baseEnd_1417633 : Nat := 727927120675357238067931

theorem tailTrace_1417633 : CollatzResearch.WordTrace tailWord_1417633 prefixEnd_1417633 727927120675357238067931 := by
  unfold tailWord_1417633
  simp only [CollatzResearch.WordTrace]
  refine ⟨51705323273165228285953553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34470215515443485523969035 51705323273165228285953553)
  ·
    refine ⟨38778992454873921214465165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51705323273165228285953553 38778992454873921214465165)
    ·
      refine ⟨14542122170577720455424437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38778992454873921214465165 14542122170577720455424437)
      ·
        refine ⟨1363323953491661292696041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14542122170577720455424437 1363323953491661292696041)
        ·
          refine ⟨1022492965118745969522031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1363323953491661292696041 1022492965118745969522031)
          ·
            refine ⟨1533739447678118954283047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022492965118745969522031 1533739447678118954283047)
            ·
              refine ⟨2300609171517178431424571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533739447678118954283047 2300609171517178431424571)
              ·
                refine ⟨3450913757275767647136857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2300609171517178431424571 3450913757275767647136857)
                ·
                  refine ⟨2588185317956825735352643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3450913757275767647136857 2588185317956825735352643)
                  ·
                    refine ⟨3882277976935238603028965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2588185317956825735352643 3882277976935238603028965)
                    ·
                      refine ⟨727927120675357238067931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3882277976935238603028965 727927120675357238067931)
                      ·
                        rfl

theorem cell23_1417633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_1417633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417633 prefixEnd_1417633 := by exact prefixLift 1417633
  have htrace : WordTrace (prefixWord ++ tailWord_1417633) baseStart_1417633 baseEnd_1417633 := by
    simpa [prefixWord, tailWord_1417633, baseEnd_1417633] using wordTrace_append hprefix tailTrace_1417633
  have hstable : (prefixWord ++ tailWord_1417633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417633).length < 2 ^ (prefixWord ++ tailWord_1417633).sum := by decide
  have hdescent : baseEnd_1417633 < baseStart_1417633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417686 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1417686 : Nat := 118140960795 + 1417686 * 2 ^ 59
def prefixEnd_1417686 : Nat := 4983230072969 + 3 ^ 40 * 1417686 * 2
def baseEnd_1417686 : Nat := 242651445050015176901729

theorem tailTrace_1417686 : CollatzResearch.WordTrace tailWord_1417686 prefixEnd_1417686 242651445050015176901729 := by
  unfold tailWord_1417686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231703521373326146102057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34471504227982145558421941 3231703521373326146102057)
  ·
    refine ⟨2423777641029994609576543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3231703521373326146102057 2423777641029994609576543)
    ·
      refine ⟨3635666461544991914364815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2423777641029994609576543 3635666461544991914364815)
      ·
        refine ⟨5453499692317487871547223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3635666461544991914364815 5453499692317487871547223)
        ·
          refine ⟨8180249538476231807320835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5453499692317487871547223 8180249538476231807320835)
          ·
            refine ⟨12270374307714347710981253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8180249538476231807320835 12270374307714347710981253)
            ·
              refine ⟨2300695182696440195808985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12270374307714347710981253 2300695182696440195808985)
              ·
                refine ⟨1725521387022330146856739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300695182696440195808985 1725521387022330146856739)
                ·
                  refine ⟨2588282080533495220285109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725521387022330146856739 2588282080533495220285109)
                  ·
                    refine ⟨242651445050015176901729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2588282080533495220285109 242651445050015176901729)
                    ·
                      rfl

theorem cell23_1417686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1417686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417686 prefixEnd_1417686 := by exact prefixLift 1417686
  have htrace : WordTrace (prefixWord ++ tailWord_1417686) baseStart_1417686 baseEnd_1417686 := by
    simpa [prefixWord, tailWord_1417686, baseEnd_1417686] using wordTrace_append hprefix tailTrace_1417686
  have hstable : (prefixWord ++ tailWord_1417686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417686).length < 2 ^ (prefixWord ++ tailWord_1417686).sum := by decide
  have hdescent : baseEnd_1417686 < baseStart_1417686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417689 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 4]
def baseStart_1417689 : Nat := 118140960795 + 1417689 * 2 ^ 59
def prefixEnd_1417689 : Nat := 4983230072969 + 3 ^ 40 * 1417689 * 2
def baseEnd_1417689 : Nat := 727955875592009018967673

theorem tailTrace_1417689 : CollatzResearch.WordTrace tailWord_1417689 prefixEnd_1417689 727955875592009018967673 := by
  unfold tailWord_1417689
  simp only [CollatzResearch.WordTrace]
  refine ⟨51707365760962349849992121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34471577173974899899994747 51707365760962349849992121)
  ·
    refine ⟨38780524320721762387494091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51707365760962349849992121 38780524320721762387494091)
    ·
      refine ⟨58170786481082643581241137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38780524320721762387494091 58170786481082643581241137)
      ·
        refine ⟨43628089860811982685930853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58170786481082643581241137 43628089860811982685930853)
        ·
          refine ⟨8180266848902246753612035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43628089860811982685930853 8180266848902246753612035)
          ·
            refine ⟨12270400273353370130418053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8180266848902246753612035 12270400273353370130418053)
            ·
              refine ⟨2300700051253756899453385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12270400273353370130418053 2300700051253756899453385)
              ·
                refine ⟨1725525038440317674590039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2300700051253756899453385 1725525038440317674590039)
                ·
                  refine ⟨2588287557660476511885059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725525038440317674590039 2588287557660476511885059)
                  ·
                    refine ⟨3882431336490714767827589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2588287557660476511885059 3882431336490714767827589)
                    ·
                      refine ⟨727955875592009018967673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3882431336490714767827589 727955875592009018967673)
                      ·
                        rfl

theorem cell23_1417689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_1417689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417689 prefixEnd_1417689 := by exact prefixLift 1417689
  have htrace : WordTrace (prefixWord ++ tailWord_1417689) baseStart_1417689 baseEnd_1417689 := by
    simpa [prefixWord, tailWord_1417689, baseEnd_1417689] using wordTrace_append hprefix tailTrace_1417689
  have hstable : (prefixWord ++ tailWord_1417689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417689).length < 2 ^ (prefixWord ++ tailWord_1417689).sum := by decide
  have hdescent : baseEnd_1417689 < baseStart_1417689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417709 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1417709 : Nat := 118140960795 + 1417709 * 2 ^ 59
def prefixEnd_1417709 : Nat := 4983230072969 + 3 ^ 40 * 1417709 * 2
def baseEnd_1417709 : Nat := 727966145205098940717581

theorem tailTrace_1417709 : CollatzResearch.WordTrace tailWord_1417709 prefixEnd_1417709 727966145205098940717581 := by
  unfold tailWord_1417709
  simp only [CollatzResearch.WordTrace]
  refine ⟨51708095220889893265720181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34472063480593262177146787 51708095220889893265720181)
  ·
    refine ⟨4847633926958427493661267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51708095220889893265720181 4847633926958427493661267)
    ·
      refine ⟨7271450890437641240491901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4847633926958427493661267 7271450890437641240491901)
      ·
        refine ⟨2726794083914115465184463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7271450890437641240491901 2726794083914115465184463)
        ·
          refine ⟨4090191125871173197776695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726794083914115465184463 4090191125871173197776695)
          ·
            refine ⟨6135286688806759796665043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4090191125871173197776695 6135286688806759796665043)
            ·
              refine ⟨9202930033210139694997565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6135286688806759796665043 9202930033210139694997565)
              ·
                refine ⟨3451098762453802385624087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9202930033210139694997565 3451098762453802385624087)
                ·
                  refine ⟨5176648143680703578436131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451098762453802385624087 5176648143680703578436131)
                  ·
                    refine ⟨7764972215521055367654197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5176648143680703578436131 7764972215521055367654197)
                    ·
                      refine ⟨727966145205098940717581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7764972215521055367654197 727966145205098940717581)
                      ·
                        rfl

theorem cell23_1417709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1417709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417709 prefixEnd_1417709 := by exact prefixLift 1417709
  have htrace : WordTrace (prefixWord ++ tailWord_1417709) baseStart_1417709 baseEnd_1417709 := by
    simpa [prefixWord, tailWord_1417709, baseEnd_1417709] using wordTrace_append hprefix tailTrace_1417709
  have hstable : (prefixWord ++ tailWord_1417709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417709).length < 2 ^ (prefixWord ++ tailWord_1417709).sum := by decide
  have hdescent : baseEnd_1417709 < baseStart_1417709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417717 : List Nat := [1, 3, 5, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1417717 : Nat := 118140960795 + 1417717 * 2 ^ 59
def prefixEnd_1417717 : Nat := 4983230072969 + 3 ^ 40 * 1417717 * 2
def baseEnd_1417717 : Nat := 727970253050334909417545

theorem tailTrace_1417717 : CollatzResearch.WordTrace tailWord_1417717 prefixEnd_1417717 727970253050334909417545 := by
  unfold tailWord_1417717
  simp only [CollatzResearch.WordTrace]
  refine ⟨51708387004860910632011405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34472258003240607088007603 51708387004860910632011405)
  ·
    refine ⟨19390645126822841487004277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51708387004860910632011405 19390645126822841487004277)
    ·
      refine ⟨1817872980639641389406651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19390645126822841487004277 1817872980639641389406651)
      ·
        refine ⟨2726809470959462084109977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817872980639641389406651 2726809470959462084109977)
        ·
          refine ⟨2045107103219596563082483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2726809470959462084109977 2045107103219596563082483)
          ·
            refine ⟨3067660654829394844623725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045107103219596563082483 3067660654829394844623725)
            ·
              refine ⟨1150372745561023066733897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3067660654829394844623725 1150372745561023066733897)
              ·
                refine ⟨862779559170767300050423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150372745561023066733897 862779559170767300050423)
                ·
                  refine ⟨1294169338756150950075635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862779559170767300050423 1294169338756150950075635)
                  ·
                    refine ⟨1941254008134226425113453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1294169338756150950075635 1941254008134226425113453)
                    ·
                      refine ⟨727970253050334909417545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1941254008134226425113453 727970253050334909417545)
                      ·
                        rfl

theorem cell23_1417717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1417717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417717 prefixEnd_1417717 := by exact prefixLift 1417717
  have htrace : WordTrace (prefixWord ++ tailWord_1417717) baseStart_1417717 baseEnd_1417717 := by
    simpa [prefixWord, tailWord_1417717, baseEnd_1417717] using wordTrace_append hprefix tailTrace_1417717
  have hstable : (prefixWord ++ tailWord_1417717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417717).length < 2 ^ (prefixWord ++ tailWord_1417717).sum := by decide
  have hdescent : baseEnd_1417717 < baseStart_1417717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417722 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3]
def baseStart_1417722 : Nat := 118140960795 + 1417722 * 2 ^ 59
def prefixEnd_1417722 : Nat := 4983230072969 + 3 ^ 40 * 1417722 * 2
def baseEnd_1417722 : Nat := 727972820453607389855021

theorem tailTrace_1417722 : CollatzResearch.WordTrace tailWord_1417722 prefixEnd_1417722 727972820453607389855021 := by
  unfold tailWord_1417722
  simp only [CollatzResearch.WordTrace]
  refine ⟨12927142342460699121485855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34472379579895197657295613 12927142342460699121485855)
  ·
    refine ⟨19390713513691048682228783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12927142342460699121485855 19390713513691048682228783)
    ·
      refine ⟨29086070270536573023343175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19390713513691048682228783 29086070270536573023343175)
      ·
        refine ⟨43629105405804859535014763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29086070270536573023343175 43629105405804859535014763)
        ·
          refine ⟨65443658108707289302522145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43629105405804859535014763 65443658108707289302522145)
          ·
            refine ⟨49082743581530466976891609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65443658108707289302522145 49082743581530466976891609)
            ·
              refine ⟨36812057686147850232668707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49082743581530466976891609 36812057686147850232668707)
              ·
                refine ⟨55218086529221775349003061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36812057686147850232668707 55218086529221775349003061)
                ·
                  refine ⟨5176695612114541438969037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55218086529221775349003061 5176695612114541438969037)
                  ·
                    refine ⟨1941260854542953039613389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5176695612114541438969037 1941260854542953039613389)
                    ·
                      refine ⟨727972820453607389855021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1941260854542953039613389 727972820453607389855021)
                      ·
                        rfl

theorem cell23_1417722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_1417722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417722 prefixEnd_1417722 := by exact prefixLift 1417722
  have htrace : WordTrace (prefixWord ++ tailWord_1417722) baseStart_1417722 baseEnd_1417722 := by
    simpa [prefixWord, tailWord_1417722, baseEnd_1417722] using wordTrace_append hprefix tailTrace_1417722
  have hstable : (prefixWord ++ tailWord_1417722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417722).length < 2 ^ (prefixWord ++ tailWord_1417722).sum := by decide
  have hdescent : baseEnd_1417722 < baseStart_1417722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417774 : List Nat := [4, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_1417774 : Nat := 118140960795 + 1417774 * 2 ^ 59
def prefixEnd_1417774 : Nat := 4983230072969 + 3 ^ 40 * 1417774 * 2
def baseEnd_1417774 : Nat := 727999521447641186404783

theorem tailTrace_1417774 : CollatzResearch.WordTrace tailWord_1417774 prefixEnd_1417774 727999521447641186404783 := by
  unfold tailWord_1417774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6463808245706801170854547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34473643977102939577890917 6463808245706801170854547)
  ·
    refine ⟨9695712368560201756281821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6463808245706801170854547 9695712368560201756281821)
    ·
      refine ⟨3635892138210075658605683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9695712368560201756281821 3635892138210075658605683)
      ·
        refine ⟨5453838207315113487908525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3635892138210075658605683 5453838207315113487908525)
        ·
          refine ⟨2045189327743167557965697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5453838207315113487908525 2045189327743167557965697)
          ·
            refine ⟨1533891995807375668474273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2045189327743167557965697 1533891995807375668474273)
            ·
              refine ⟨1150418996855531751355705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1533891995807375668474273 1150418996855531751355705)
              ·
                refine ⟨862814247641648813516779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150418996855531751355705 862814247641648813516779)
                ·
                  refine ⟨1294221371462473220275169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 862814247641648813516779 1294221371462473220275169)
                  ·
                    refine ⟨970666028596854915206377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1294221371462473220275169 970666028596854915206377)
                    ·
                      refine ⟨727999521447641186404783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970666028596854915206377 727999521447641186404783)
                      ·
                        rfl

theorem cell23_1417774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_1417774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417774 prefixEnd_1417774 := by exact prefixLift 1417774
  have htrace : WordTrace (prefixWord ++ tailWord_1417774) baseStart_1417774 baseEnd_1417774 := by
    simpa [prefixWord, tailWord_1417774, baseEnd_1417774] using wordTrace_append hprefix tailTrace_1417774
  have hstable : (prefixWord ++ tailWord_1417774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417774).length < 2 ^ (prefixWord ++ tailWord_1417774).sum := by decide
  have hdescent : baseEnd_1417774 < baseStart_1417774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417779 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 3, 4, 2]
def baseStart_1417779 : Nat := 118140960795 + 1417779 * 2 ^ 59
def prefixEnd_1417779 : Nat := 4983230072969 + 3 ^ 40 * 1417779 * 2
def baseEnd_1417779 : Nat := 728002088850913666842259

theorem tailTrace_1417779 : CollatzResearch.WordTrace tailWord_1417779 prefixEnd_1417779 728002088850913666842259 := by
  unfold tailWord_1417779
  simp only [CollatzResearch.WordTrace]
  refine ⟨51710648330636295220768391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34473765553757530147178927 51710648330636295220768391)
  ·
    refine ⟨77565972495954442831152587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51710648330636295220768391 77565972495954442831152587)
    ·
      refine ⟨116348958743931664246728881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77565972495954442831152587 116348958743931664246728881)
      ·
        refine ⟨87261719057948748185046661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116348958743931664246728881 87261719057948748185046661)
        ·
          refine ⟨16361572323365390284696249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87261719057948748185046661 16361572323365390284696249)
          ·
            refine ⟨12271179242524042713522187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16361572323365390284696249 12271179242524042713522187)
            ·
              refine ⟨18406768863786064070283281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12271179242524042713522187 18406768863786064070283281)
              ·
                refine ⟨13805076647839548052712461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18406768863786064070283281 13805076647839548052712461)
                ·
                  refine ⟨5176903742939830519767173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13805076647839548052712461 5176903742939830519767173)
                  ·
                    refine ⟨970669451801218222456345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5176903742939830519767173 970669451801218222456345)
                    ·
                      refine ⟨728002088850913666842259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970669451801218222456345 728002088850913666842259)
                      ·
                        rfl

theorem cell23_1417779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 4, 2].length) (baseStart_1417779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417779 prefixEnd_1417779 := by exact prefixLift 1417779
  have htrace : WordTrace (prefixWord ++ tailWord_1417779) baseStart_1417779 baseEnd_1417779 := by
    simpa [prefixWord, tailWord_1417779, baseEnd_1417779] using wordTrace_append hprefix tailTrace_1417779
  have hstable : (prefixWord ++ tailWord_1417779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417779).length < 2 ^ (prefixWord ++ tailWord_1417779).sum := by decide
  have hdescent : baseEnd_1417779 < baseStart_1417779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417789 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_1417789 : Nat := 118140960795 + 1417789 * 2 ^ 59
def prefixEnd_1417789 : Nat := 4983230072969 + 3 ^ 40 * 1417789 * 2
def baseEnd_1417789 : Nat := 242669074552486209239071

theorem tailTrace_1417789 : CollatzResearch.WordTrace tailWord_1417789 prefixEnd_1417789 242669074552486209239071 := by
  unfold tailWord_1417789
  simp only [CollatzResearch.WordTrace]
  refine ⟨51711013060600066928632421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34474008707066711285754947 51711013060600066928632421)
  ·
    refine ⟨9695814948862512549118579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51711013060600066928632421 9695814948862512549118579)
    ·
      refine ⟨14543722423293768823677869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9695814948862512549118579 14543722423293768823677869)
      ·
        refine ⟨5453895908735163308879201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14543722423293768823677869 5453895908735163308879201)
        ·
          refine ⟨4090421931551372481659401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5453895908735163308879201 4090421931551372481659401)
          ·
            refine ⟨3067816448663529361244551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4090421931551372481659401 3067816448663529361244551)
            ·
              refine ⟨4601724672995294041866827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3067816448663529361244551 4601724672995294041866827)
              ·
                refine ⟨6902587009492941062800241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4601724672995294041866827 6902587009492941062800241)
                ·
                  refine ⟨5176940257119705797100181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6902587009492941062800241 5176940257119705797100181)
                  ·
                    refine ⟨242669074552486209239071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5176940257119705797100181 242669074552486209239071)
                    ·
                      rfl

theorem cell23_1417789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_1417789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417789 prefixEnd_1417789 := by exact prefixLift 1417789
  have htrace : WordTrace (prefixWord ++ tailWord_1417789) baseStart_1417789 baseEnd_1417789 := by
    simpa [prefixWord, tailWord_1417789, baseEnd_1417789] using wordTrace_append hprefix tailTrace_1417789
  have hstable : (prefixWord ++ tailWord_1417789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417789).length < 2 ^ (prefixWord ++ tailWord_1417789).sum := by decide
  have hdescent : baseEnd_1417789 < baseStart_1417789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417792 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 4]
def baseStart_1417792 : Nat := 118140960795 + 1417792 * 2 ^ 59
def prefixEnd_1417792 : Nat := 4983230072969 + 3 ^ 40 * 1417792 * 2
def baseEnd_1417792 : Nat := 728008764099422115979699

theorem tailTrace_1417792 : CollatzResearch.WordTrace tailWord_1417792 prefixEnd_1417792 728008764099422115979699 := by
  unfold tailWord_1417792
  simp only [CollatzResearch.WordTrace]
  refine ⟨25855561239794599220495815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34474081653059465627327753 25855561239794599220495815)
  ·
    refine ⟨38783341859691898830743723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25855561239794599220495815 38783341859691898830743723)
    ·
      refine ⟨58175012789537848246115585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38783341859691898830743723 58175012789537848246115585)
      ·
        refine ⟨43631259592153386184586689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58175012789537848246115585 43631259592153386184586689)
        ·
          refine ⟨32723444694115039638440017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43631259592153386184586689 32723444694115039638440017)
          ·
            refine ⟨24542583520586279728830013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32723444694115039638440017 24542583520586279728830013)
            ·
              refine ⟨9203468820219854898311255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24542583520586279728830013 9203468820219854898311255)
              ·
                refine ⟨13805203230329782347466883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9203468820219854898311255 13805203230329782347466883)
                ·
                  refine ⟨20707804845494673521200325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13805203230329782347466883 20707804845494673521200325)
                  ·
                    refine ⟨3882713408530251285225061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20707804845494673521200325 3882713408530251285225061)
                    ·
                      refine ⟨728008764099422115979699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3882713408530251285225061 728008764099422115979699)
                      ·
                        rfl

theorem cell23_1417792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_1417792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417792 prefixEnd_1417792 := by exact prefixLift 1417792
  have htrace : WordTrace (prefixWord ++ tailWord_1417792) baseStart_1417792 baseEnd_1417792 := by
    simpa [prefixWord, tailWord_1417792, baseEnd_1417792] using wordTrace_append hprefix tailTrace_1417792
  have hstable : (prefixWord ++ tailWord_1417792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417792).length < 2 ^ (prefixWord ++ tailWord_1417792).sum := by decide
  have hdescent : baseEnd_1417792 < baseStart_1417792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417802 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 9]
def baseStart_1417802 : Nat := 118140960795 + 1417802 * 2 ^ 59
def prefixEnd_1417802 : Nat := 4983230072969 + 3 ^ 40 * 1417802 * 2
def baseEnd_1417802 : Nat := 80890433211774119650517

theorem tailTrace_1417802 : CollatzResearch.WordTrace tailWord_1417802 prefixEnd_1417802 80890433211774119650517 := by
  unfold tailWord_1417802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12927871802388242537213915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34474324806368646765903773 12927871802388242537213915)
  ·
    refine ⟨19391807703582363805820873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12927871802388242537213915 19391807703582363805820873)
    ·
      refine ⟨14543855777686772854365655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19391807703582363805820873 14543855777686772854365655)
      ·
        refine ⟨21815783666530159281548483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14543855777686772854365655 21815783666530159281548483)
        ·
          refine ⟨32723675499795238922322725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21815783666530159281548483 32723675499795238922322725)
          ·
            refine ⟨6135689156211607297935511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32723675499795238922322725 6135689156211607297935511)
            ·
              refine ⟨9203533734317410946903267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6135689156211607297935511 9203533734317410946903267)
              ·
                refine ⟨13805300601476116420354901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9203533734317410946903267 13805300601476116420354901)
                ·
                  refine ⟨80890433211774119650517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13805300601476116420354901 80890433211774119650517)
                  ·
                    rfl

theorem cell23_1417802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_1417802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417802 prefixEnd_1417802 := by exact prefixLift 1417802
  have htrace : WordTrace (prefixWord ++ tailWord_1417802) baseStart_1417802 baseEnd_1417802 := by
    simpa [prefixWord, tailWord_1417802, baseEnd_1417802] using wordTrace_append hprefix tailTrace_1417802
  have hstable : (prefixWord ++ tailWord_1417802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417802).length < 2 ^ (prefixWord ++ tailWord_1417802).sum := by decide
  have hdescent : baseEnd_1417802 < baseStart_1417802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417839 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 1, 7, 2]
def baseStart_1417839 : Nat := 118140960795 + 1417839 * 2 ^ 59
def prefixEnd_1417839 : Nat := 4983230072969 + 3 ^ 40 * 1417839 * 2
def baseEnd_1417839 : Nat := 728032897690183432091983

theorem tailTrace_1417839 : CollatzResearch.WordTrace tailWord_1417839 prefixEnd_1417839 728032897690183432091983 := by
  unfold tailWord_1417839
  simp only [CollatzResearch.WordTrace]
  refine ⟨51712836710418925467952571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34475224473612616978635047 51712836710418925467952571)
  ·
    refine ⟨77569255065628388201928857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51712836710418925467952571 77569255065628388201928857)
    ·
      refine ⟨58176941299221291151446643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77569255065628388201928857 58176941299221291151446643)
      ·
        refine ⟨87265411948831936727169965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58176941299221291151446643 87265411948831936727169965)
        ·
          refine ⟨32724529480811976272688737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87265411948831936727169965 32724529480811976272688737)
          ·
            refine ⟨24543397110608982204516553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32724529480811976272688737 24543397110608982204516553)
            ·
              refine ⟨18407547832956736653387415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24543397110608982204516553 18407547832956736653387415)
              ·
                refine ⟨27611321749435104980081123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18407547832956736653387415 27611321749435104980081123)
                ·
                  refine ⟨41416982624152657470121685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27611321749435104980081123 41416982624152657470121685)
                  ·
                    refine ⟨970710530253577909455977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41416982624152657470121685 970710530253577909455977)
                    ·
                      refine ⟨728032897690183432091983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970710530253577909455977 728032897690183432091983)
                      ·
                        rfl

theorem cell23_1417839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 7, 2].length) (baseStart_1417839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417839 prefixEnd_1417839 := by exact prefixLift 1417839
  have htrace : WordTrace (prefixWord ++ tailWord_1417839) baseStart_1417839 baseEnd_1417839 := by
    simpa [prefixWord, tailWord_1417839, baseEnd_1417839] using wordTrace_append hprefix tailTrace_1417839
  have hstable : (prefixWord ++ tailWord_1417839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417839).length < 2 ^ (prefixWord ++ tailWord_1417839).sum := by decide
  have hdescent : baseEnd_1417839 < baseStart_1417839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417872 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_1417872 : Nat := 118140960795 + 1417872 * 2 ^ 59
def prefixEnd_1417872 : Nat := 4983230072969 + 3 ^ 40 * 1417872 * 2
def baseEnd_1417872 : Nat := 728049842551781802979331

theorem tailTrace_1417872 : CollatzResearch.WordTrace tailWord_1417872 prefixEnd_1417872 728049842551781802979331 := by
  unfold tailWord_1417872
  simp only [CollatzResearch.WordTrace]
  refine ⟨25857020159649686051951935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34476026879532914735935913 25857020159649686051951935)
  ·
    refine ⟨38785530239474529077927903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25857020159649686051951935 38785530239474529077927903)
    ·
      refine ⟨58178295359211793616891855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38785530239474529077927903 58178295359211793616891855)
      ·
        refine ⟨87267443038817690425337783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58178295359211793616891855 87267443038817690425337783)
        ·
          refine ⟨130901164558226535638006675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87267443038817690425337783 130901164558226535638006675)
          ·
            refine ⟨196351746837339803457010013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130901164558226535638006675 196351746837339803457010013)
            ·
              refine ⟨73631905064002426296378755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196351746837339803457010013 73631905064002426296378755)
              ·
                refine ⟨110447857596003639444568133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73631905064002426296378755 110447857596003639444568133)
                ·
                  refine ⟨20708973299250682395856525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110447857596003639444568133 20708973299250682395856525)
                  ·
                    refine ⟨7765864987219005898446197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20708973299250682395856525 7765864987219005898446197)
                    ·
                      refine ⟨728049842551781802979331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7765864987219005898446197 728049842551781802979331)
                      ·
                        rfl

theorem cell23_1417872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_1417872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417872 prefixEnd_1417872 := by exact prefixLift 1417872
  have htrace : WordTrace (prefixWord ++ tailWord_1417872) baseStart_1417872 baseEnd_1417872 := by
    simpa [prefixWord, tailWord_1417872, baseEnd_1417872] using wordTrace_append hprefix tailTrace_1417872
  have hstable : (prefixWord ++ tailWord_1417872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417872).length < 2 ^ (prefixWord ++ tailWord_1417872).sum := by decide
  have hdescent : baseEnd_1417872 < baseStart_1417872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417976 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 1, 1, 4]
def baseStart_1417976 : Nat := 118140960795 + 1417976 * 2 ^ 59
def prefixEnd_1417976 : Nat := 4983230072969 + 3 ^ 40 * 1417976 * 2
def baseEnd_1417976 : Nat := 728103244539849396078853

theorem tailTrace_1417976 : CollatzResearch.WordTrace tailWord_1417976 prefixEnd_1417976 728103244539849396078853 := by
  unfold tailWord_1417976
  simp only [CollatzResearch.WordTrace]
  refine ⟨25858916755461298932844891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34478555673948398577126521 25858916755461298932844891)
  ·
    refine ⟨38788375133191948399267337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25858916755461298932844891 38788375133191948399267337)
    ·
      refine ⟨29091281349893961299450503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38788375133191948399267337 29091281349893961299450503)
      ·
        refine ⟨43636922024840941949175755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29091281349893961299450503 43636922024840941949175755)
        ·
          refine ⟨65455383037261412923763633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43636922024840941949175755 65455383037261412923763633)
          ·
            refine ⟨49091537277946059692822725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65455383037261412923763633 49091537277946059692822725)
            ·
              refine ⟨9204663239614886192404261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49091537277946059692822725 9204663239614886192404261)
              ·
                refine ⟨1725874357427791161075799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9204663239614886192404261 1725874357427791161075799)
                ·
                  refine ⟨2588811536141686741613699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725874357427791161075799 2588811536141686741613699)
                  ·
                    refine ⟨3883217304212530112420549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2588811536141686741613699 3883217304212530112420549)
                    ·
                      refine ⟨728103244539849396078853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3883217304212530112420549 728103244539849396078853)
                      ·
                        rfl

theorem cell23_1417976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 1, 1, 4].length) (baseStart_1417976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417976 prefixEnd_1417976 := by exact prefixLift 1417976
  have htrace : WordTrace (prefixWord ++ tailWord_1417976) baseStart_1417976 baseEnd_1417976 := by
    simpa [prefixWord, tailWord_1417976, baseEnd_1417976] using wordTrace_append hprefix tailTrace_1417976
  have hstable : (prefixWord ++ tailWord_1417976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417976).length < 2 ^ (prefixWord ++ tailWord_1417976).sum := by decide
  have hdescent : baseEnd_1417976 < baseStart_1417976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417980 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 2, 3, 2]
def baseStart_1417980 : Nat := 118140960795 + 1417980 * 2 ^ 59
def prefixEnd_1417980 : Nat := 4983230072969 + 3 ^ 40 * 1417980 * 2
def baseEnd_1417980 : Nat := 728105298462467380428835

theorem tailTrace_1417980 : CollatzResearch.WordTrace tailWord_1417980 prefixEnd_1417980 728105298462467380428835 := by
  unfold tailWord_1417980
  simp only [CollatzResearch.WordTrace]
  refine ⟨25858989701454053274417697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34478652935272071032556929 25858989701454053274417697)
  ·
    refine ⟨19394242276090539955813273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25858989701454053274417697 19394242276090539955813273)
    ·
      refine ⟨14545681707067904966859955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19394242276090539955813273 14545681707067904966859955)
      ·
        refine ⟨21818522560601857450289933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14545681707067904966859955 21818522560601857450289933)
        ·
          refine ⟨8181945960225696543858725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21818522560601857450289933 8181945960225696543858725)
          ·
            refine ⟨1534114867542318101973511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8181945960225696543858725 1534114867542318101973511)
            ·
              refine ⟨2301172301313477152960267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1534114867542318101973511 2301172301313477152960267)
              ·
                refine ⟨3451758451970215729440401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2301172301313477152960267 3451758451970215729440401)
                ·
                  refine ⟨2588818838977661797080301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3451758451970215729440401 2588818838977661797080301)
                  ·
                    refine ⟨970807064616623173905113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2588818838977661797080301 970807064616623173905113)
                    ·
                      refine ⟨728105298462467380428835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970807064616623173905113 728105298462467380428835)
                      ·
                        rfl

theorem cell23_1417980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_1417980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417980 prefixEnd_1417980 := by exact prefixLift 1417980
  have htrace : WordTrace (prefixWord ++ tailWord_1417980) baseStart_1417980 baseEnd_1417980 := by
    simpa [prefixWord, tailWord_1417980, baseEnd_1417980] using wordTrace_append hprefix tailTrace_1417980
  have hstable : (prefixWord ++ tailWord_1417980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417980).length < 2 ^ (prefixWord ++ tailWord_1417980).sum := by decide
  have hdescent : baseEnd_1417980 < baseStart_1417980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1417993 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 1, 1, 4]
def baseStart_1417993 : Nat := 118140960795 + 1417993 * 2 ^ 59
def prefixEnd_1417993 : Nat := 4983230072969 + 3 ^ 40 * 1417993 * 2
def baseEnd_1417993 : Nat := 728111973710975829566275

theorem tailTrace_1417993 : CollatzResearch.WordTrace tailWord_1417993 prefixEnd_1417993 728111973710975829566275 := by
  unfold tailWord_1417993
  simp only [CollatzResearch.WordTrace]
  refine ⟨51718453551861009769058633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34478969034574006512705755 51718453551861009769058633)
  ·
    refine ⟨38788840163895757326793975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51718453551861009769058633 38788840163895757326793975)
    ·
      refine ⟨58183260245843635990190963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38788840163895757326793975 58183260245843635990190963)
      ·
        refine ⟨87274890368765453985286445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58183260245843635990190963 87274890368765453985286445)
        ·
          refine ⟨32728083888287045244482417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87274890368765453985286445 32728083888287045244482417)
          ·
            refine ⟨24546062916215283933361813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32728083888287045244482417 24546062916215283933361813)
            ·
              refine ⟨1150596699197591434376335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24546062916215283933361813 1150596699197591434376335)
              ·
                refine ⟨1725895048796387151564503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150596699197591434376335 1725895048796387151564503)
                ·
                  refine ⟨2588842573194580727346755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725895048796387151564503 2588842573194580727346755)
                  ·
                    refine ⟨3883263859791871091020133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2588842573194580727346755 3883263859791871091020133)
                    ·
                      refine ⟨728111973710975829566275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3883263859791871091020133 728111973710975829566275)
                      ·
                        rfl

theorem cell23_1417993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 1, 1, 4].length) (baseStart_1417993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1417993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1417993 prefixEnd_1417993 := by exact prefixLift 1417993
  have htrace : WordTrace (prefixWord ++ tailWord_1417993) baseStart_1417993 baseEnd_1417993 := by
    simpa [prefixWord, tailWord_1417993, baseEnd_1417993] using wordTrace_append hprefix tailTrace_1417993
  have hstable : (prefixWord ++ tailWord_1417993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1417993).length < 2 ^ (prefixWord ++ tailWord_1417993).sum := by decide
  have hdescent : baseEnd_1417993 < baseStart_1417993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1417993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418010 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2]
def baseStart_1418010 : Nat := 118140960795 + 1418010 * 2 ^ 59
def prefixEnd_1418010 : Nat := 4983230072969 + 3 ^ 40 * 1418010 * 2
def baseEnd_1418010 : Nat := 728120702882102263053697

theorem tailTrace_1418010 : CollatzResearch.WordTrace tailWord_1418010 prefixEnd_1418010 728120702882102263053697 := by
  unfold tailWord_1418010
  simp only [CollatzResearch.WordTrace]
  refine ⟨12929768398199855418106871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34479382395199614448284989 12929768398199855418106871)
  ·
    refine ⟨19394652597299783127160307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12929768398199855418106871 19394652597299783127160307)
    ·
      refine ⟨29091978895949674690740461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19394652597299783127160307 29091978895949674690740461)
      ·
        refine ⟨10909492085981128009027673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29091978895949674690740461 10909492085981128009027673)
        ·
          refine ⟨8182119064485846006770755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10909492085981128009027673 8182119064485846006770755)
          ·
            refine ⟨12273178596728769010156133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8182119064485846006770755 12273178596728769010156133)
            ·
              refine ⟨2301220986886644189404275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12273178596728769010156133 2301220986886644189404275)
              ·
                refine ⟨3451831480329966284106413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2301220986886644189404275 3451831480329966284106413)
                ·
                  refine ⟨1294436805123737356539905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3451831480329966284106413 1294436805123737356539905)
                  ·
                    refine ⟨970827603842803017404929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1294436805123737356539905 970827603842803017404929)
                    ·
                      refine ⟨728120702882102263053697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970827603842803017404929 728120702882102263053697)
                      ·
                        rfl

theorem cell23_1418010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_1418010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418010 prefixEnd_1418010 := by exact prefixLift 1418010
  have htrace : WordTrace (prefixWord ++ tailWord_1418010) baseStart_1418010 baseEnd_1418010 := by
    simpa [prefixWord, tailWord_1418010, baseEnd_1418010] using wordTrace_append hprefix tailTrace_1418010
  have hstable : (prefixWord ++ tailWord_1418010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418010).length < 2 ^ (prefixWord ++ tailWord_1418010).sum := by decide
  have hdescent : baseEnd_1418010 < baseStart_1418010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418020 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 1, 6]
def baseStart_1418020 : Nat := 118140960795 + 1418020 * 2 ^ 59
def prefixEnd_1418020 : Nat := 4983230072969 + 3 ^ 40 * 1418020 * 2
def baseEnd_1418020 : Nat := 242708612562882407976217

theorem tailTrace_1418020 : CollatzResearch.WordTrace tailWord_1418020 prefixEnd_1418020 242708612562882407976217 := by
  unfold tailWord_1418020
  simp only [CollatzResearch.WordTrace]
  refine ⟨25859719161381596690145757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34479625548508795586861009 25859719161381596690145757)
  ·
    refine ⟨9697394685518098758804659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25859719161381596690145757 9697394685518098758804659)
    ·
      refine ⟨14546092028277148138206989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9697394685518098758804659 14546092028277148138206989)
      ·
        refine ⟨5454784510603930551827621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14546092028277148138206989 5454784510603930551827621)
        ·
          refine ⟨1022772095738236978467679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5454784510603930551827621 1022772095738236978467679)
          ·
            refine ⟨1534158143607355467701519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022772095738236978467679 1534158143607355467701519)
            ·
              refine ⟨2301237215411033201552279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1534158143607355467701519 2301237215411033201552279)
              ·
                refine ⟨3451855823116549802328419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2301237215411033201552279 3451855823116549802328419)
                ·
                  refine ⟨5177783734674824703492629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451855823116549802328419 5177783734674824703492629)
                  ·
                    refine ⟨242708612562882407976217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5177783734674824703492629 242708612562882407976217)
                    ·
                      rfl

theorem cell23_1418020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_1418020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418020 prefixEnd_1418020 := by exact prefixLift 1418020
  have htrace : WordTrace (prefixWord ++ tailWord_1418020) baseStart_1418020 baseEnd_1418020 := by
    simpa [prefixWord, tailWord_1418020, baseEnd_1418020] using wordTrace_append hprefix tailTrace_1418020
  have hstable : (prefixWord ++ tailWord_1418020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418020).length < 2 ^ (prefixWord ++ tailWord_1418020).sum := by decide
  have hdescent : baseEnd_1418020 < baseStart_1418020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418030 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1418030 : Nat := 118140960795 + 1418030 * 2 ^ 59
def prefixEnd_1418030 : Nat := 4983230072969 + 3 ^ 40 * 1418030 * 2
def baseEnd_1418030 : Nat := 728130972495192184803605

theorem tailTrace_1418030 : CollatzResearch.WordTrace tailWord_1418030 prefixEnd_1418030 728130972495192184803605 := by
  unfold tailWord_1418030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6464975381590870636019443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34479868701817976725437029 6464975381590870636019443)
  ·
    refine ⟨9697463072386305954029165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6464975381590870636019443 9697463072386305954029165)
    ·
      refine ⟨3636548652144864732760937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9697463072386305954029165 3636548652144864732760937)
      ·
        refine ⟨2727411489108648549570703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3636548652144864732760937 2727411489108648549570703)
        ·
          refine ⟨4091117233662972824356055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2727411489108648549570703 4091117233662972824356055)
          ·
            refine ⟨6136675850494459236534083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4091117233662972824356055 6136675850494459236534083)
            ·
              refine ⟨9205013775741688854801125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6136675850494459236534083 9205013775741688854801125)
              ·
                refine ⟨1725940082951566660275211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9205013775741688854801125 1725940082951566660275211)
                ·
                  refine ⟨2588910124427349990412817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725940082951566660275211 2588910124427349990412817)
                  ·
                    refine ⟨1941682593320512492809613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2588910124427349990412817 1941682593320512492809613)
                    ·
                      refine ⟨728130972495192184803605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1941682593320512492809613 728130972495192184803605)
                      ·
                        rfl

theorem cell23_1418030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1418030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418030 prefixEnd_1418030 := by exact prefixLift 1418030
  have htrace : WordTrace (prefixWord ++ tailWord_1418030) baseStart_1418030 baseEnd_1418030 := by
    simpa [prefixWord, tailWord_1418030, baseEnd_1418030] using wordTrace_append hprefix tailTrace_1418030
  have hstable : (prefixWord ++ tailWord_1418030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418030).length < 2 ^ (prefixWord ++ tailWord_1418030).sum := by decide
  have hdescent : baseEnd_1418030 < baseStart_1418030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418039 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_1418039 : Nat := 118140960795 + 1418039 * 2 ^ 59
def prefixEnd_1418039 : Nat := 4983230072969 + 3 ^ 40 * 1418039 * 2
def baseEnd_1418039 : Nat := 728135593821082649591063

theorem tailTrace_1418039 : CollatzResearch.WordTrace tailWord_1418039 prefixEnd_1418039 728135593821082649591063 := by
  unfold tailWord_1418039
  simp only [CollatzResearch.WordTrace]
  refine ⟨51720131309694359625233171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34480087539796239750155447 51720131309694359625233171)
  ·
    refine ⟨77580196964541539437849757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51720131309694359625233171 77580196964541539437849757)
    ·
      refine ⟨29092573861703077289193659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77580196964541539437849757 29092573861703077289193659)
      ·
        refine ⟨43638860792554615933790489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29092573861703077289193659 43638860792554615933790489)
        ·
          refine ⟨32729145594415961950342867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43638860792554615933790489 32729145594415961950342867)
          ·
            refine ⟨49093718391623942925514301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32729145594415961950342867 49093718391623942925514301)
            ·
              refine ⟨18410144396858978597067863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49093718391623942925514301 18410144396858978597067863)
              ·
                refine ⟨27615216595288467895601795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18410144396858978597067863 27615216595288467895601795)
                ·
                  refine ⟨41422824892932701843402693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27615216595288467895601795 41422824892932701843402693)
                  ·
                    refine ⟨7766779667424881595638005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41422824892932701843402693 7766779667424881595638005)
                    ·
                      refine ⟨728135593821082649591063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7766779667424881595638005 728135593821082649591063)
                      ·
                        rfl

theorem cell23_1418039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_1418039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418039 prefixEnd_1418039 := by exact prefixLift 1418039
  have htrace : WordTrace (prefixWord ++ tailWord_1418039) baseStart_1418039 baseEnd_1418039 := by
    simpa [prefixWord, tailWord_1418039, baseEnd_1418039] using wordTrace_append hprefix tailTrace_1418039
  have hstable : (prefixWord ++ tailWord_1418039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418039).length < 2 ^ (prefixWord ++ tailWord_1418039).sum := by decide
  have hdescent : baseEnd_1418039 < baseStart_1418039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418061 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_1418061 : Nat := 118140960795 + 1418061 * 2 ^ 59
def prefixEnd_1418061 : Nat := 4983230072969 + 3 ^ 40 * 1418061 * 2
def baseEnd_1418061 : Nat := 728146890395481563515963

theorem tailTrace_1418061 : CollatzResearch.WordTrace tailWord_1418061 prefixEnd_1418061 728146890395481563515963 := by
  unfold tailWord_1418061
  simp only [CollatzResearch.WordTrace]
  refine ⟨51720933715614657382534037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34480622477076438255022691 51720933715614657382534037)
  ·
    refine ⟨2424418767919437064806283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51720933715614657382534037 2424418767919437064806283)
    ·
      refine ⟨3636628151879155597209425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2424418767919437064806283 3636628151879155597209425)
      ·
        refine ⟨2727471113909366697907069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3636628151879155597209425 2727471113909366697907069)
        ·
          refine ⟨1022801667716012511715151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2727471113909366697907069 1022801667716012511715151)
          ·
            refine ⟨1534202501574018767572727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022801667716012511715151 1534202501574018767572727)
            ·
              refine ⟨2301303752361028151359091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1534202501574018767572727 2301303752361028151359091)
              ·
                refine ⟨3451955628541542227038637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2301303752361028151359091 3451955628541542227038637)
                ·
                  refine ⟨1294483360703078335139489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3451955628541542227038637 1294483360703078335139489)
                  ·
                    refine ⟨970862520527308751354617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1294483360703078335139489 970862520527308751354617)
                    ·
                      refine ⟨728146890395481563515963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970862520527308751354617 728146890395481563515963)
                      ·
                        rfl

theorem cell23_1418061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_1418061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418061 prefixEnd_1418061 := by exact prefixLift 1418061
  have htrace : WordTrace (prefixWord ++ tailWord_1418061) baseStart_1418061 baseEnd_1418061 := by
    simpa [prefixWord, tailWord_1418061, baseEnd_1418061] using wordTrace_append hprefix tailTrace_1418061
  have hstable : (prefixWord ++ tailWord_1418061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418061).length < 2 ^ (prefixWord ++ tailWord_1418061).sum := by decide
  have hdescent : baseEnd_1418061 < baseStart_1418061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418066 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1418066 : Nat := 118140960795 + 1418066 * 2 ^ 59
def prefixEnd_1418066 : Nat := 4983230072969 + 3 ^ 40 * 1418066 * 2
def baseEnd_1418066 : Nat := 728149457798754043953439

theorem tailTrace_1418066 : CollatzResearch.WordTrace tailWord_1418066 prefixEnd_1418066 728149457798754043953439 := by
  unfold tailWord_1418066
  simp only [CollatzResearch.WordTrace]
  refine ⟨12930279020149135809116513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34480744053731028824310701 12930279020149135809116513)
  ·
    refine ⟨9697709265111851856837385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12930279020149135809116513 9697709265111851856837385)
    ·
      refine ⟨7273281948833888892628039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9697709265111851856837385 7273281948833888892628039)
      ·
        refine ⟨10909922923250833338942059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7273281948833888892628039 10909922923250833338942059)
        ·
          refine ⟨16364884384876250008413089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10909922923250833338942059 16364884384876250008413089)
          ·
            refine ⟨12273663288657187506309817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16364884384876250008413089 12273663288657187506309817)
            ·
              refine ⟨9205247466492890629732363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12273663288657187506309817 9205247466492890629732363)
              ·
                refine ⟨13807871199739335944598545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9205247466492890629732363 13807871199739335944598545)
                ·
                  refine ⟨10355903399804501958448909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13807871199739335944598545 10355903399804501958448909)
                  ·
                    refine ⟨3883463774926688234418341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10355903399804501958448909 3883463774926688234418341)
                    ·
                      refine ⟨728149457798754043953439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3883463774926688234418341 728149457798754043953439)
                      ·
                        rfl

theorem cell23_1418066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1418066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418066 prefixEnd_1418066 := by exact prefixLift 1418066
  have htrace : WordTrace (prefixWord ++ tailWord_1418066) baseStart_1418066 baseEnd_1418066 := by
    simpa [prefixWord, tailWord_1418066, baseEnd_1418066] using wordTrace_append hprefix tailTrace_1418066
  have hstable : (prefixWord ++ tailWord_1418066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418066).length < 2 ^ (prefixWord ++ tailWord_1418066).sum := by decide
  have hdescent : baseEnd_1418066 < baseStart_1418066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418087 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_1418087 : Nat := 118140960795 + 1418087 * 2 ^ 59
def prefixEnd_1418087 : Nat := 4983230072969 + 3 ^ 40 * 1418087 * 2
def baseEnd_1418087 : Nat := 728160240892498461790843

theorem tailTrace_1418087 : CollatzResearch.WordTrace tailWord_1418087 prefixEnd_1418087 728160240892498461790843 := by
  unfold tailWord_1418087
  simp only [CollatzResearch.WordTrace]
  refine ⟨51721882013520463822980515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34481254675680309215320343 51721882013520463822980515)
  ·
    refine ⟨77582823020280695734470773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51721882013520463822980515 77582823020280695734470773)
    ·
      refine ⟨7273389658151315225106635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77582823020280695734470773 7273389658151315225106635)
      ·
        refine ⟨10910084487226972837659953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7273389658151315225106635 10910084487226972837659953)
        ·
          refine ⟨8182563365420229628244965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10910084487226972837659953 8182563365420229628244965)
          ·
            refine ⟨1534230631016293055295931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8182563365420229628244965 1534230631016293055295931)
            ·
              refine ⟨2301345946524439582943897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1534230631016293055295931 2301345946524439582943897)
              ·
                refine ⟨1726009459893329687207923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2301345946524439582943897 1726009459893329687207923)
                ·
                  refine ⟨2589014189839994530811885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726009459893329687207923 2589014189839994530811885)
                  ·
                    refine ⟨970880321189997949054457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2589014189839994530811885 970880321189997949054457)
                    ·
                      refine ⟨728160240892498461790843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970880321189997949054457 728160240892498461790843)
                      ·
                        rfl

theorem cell23_1418087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_1418087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418087 prefixEnd_1418087 := by exact prefixLift 1418087
  have htrace : WordTrace (prefixWord ++ tailWord_1418087) baseStart_1418087 baseEnd_1418087 := by
    simpa [prefixWord, tailWord_1418087, baseEnd_1418087] using wordTrace_append hprefix tailTrace_1418087
  have hstable : (prefixWord ++ tailWord_1418087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418087).length < 2 ^ (prefixWord ++ tailWord_1418087).sum := by decide
  have hdescent : baseEnd_1418087 < baseStart_1418087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418117 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 2, 2, 2]
def baseStart_1418117 : Nat := 118140960795 + 1418117 * 2 ^ 59
def prefixEnd_1418117 : Nat := 4983230072969 + 3 ^ 40 * 1418117 * 2
def baseEnd_1418117 : Nat := 728175645312133344415705

theorem tailTrace_1418117 : CollatzResearch.WordTrace tailWord_1418117 prefixEnd_1418117 728175645312133344415705 := by
  unfold tailWord_1418117
  simp only [CollatzResearch.WordTrace]
  refine ⟨51722976203411778946572605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34481984135607852631048403 51722976203411778946572605)
  ·
    refine ⟨19396116076279417104964727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51722976203411778946572605 19396116076279417104964727)
    ·
      refine ⟨29094174114419125657447091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19396116076279417104964727 29094174114419125657447091)
      ·
        refine ⟨43641261171628688486170637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29094174114419125657447091 43641261171628688486170637)
        ·
          refine ⟨16365472939360758182313989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43641261171628688486170637 16365472939360758182313989)
          ·
            refine ⟨3068526176130142159183873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16365472939360758182313989 3068526176130142159183873)
            ·
              refine ⟨2301394632097606619387905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3068526176130142159183873 2301394632097606619387905)
              ·
                refine ⟨1726045974073204964540929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2301394632097606619387905 1726045974073204964540929)
                ·
                  refine ⟨1294534480554903723405697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1726045974073204964540929 1294534480554903723405697)
                  ·
                    refine ⟨970900860416177792554273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1294534480554903723405697 970900860416177792554273)
                    ·
                      refine ⟨728175645312133344415705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970900860416177792554273 728175645312133344415705)
                      ·
                        rfl

theorem cell23_1418117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 2, 2].length) (baseStart_1418117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418117 prefixEnd_1418117 := by exact prefixLift 1418117
  have htrace : WordTrace (prefixWord ++ tailWord_1418117) baseStart_1418117 baseEnd_1418117 := by
    simpa [prefixWord, tailWord_1418117, baseEnd_1418117] using wordTrace_append hprefix tailTrace_1418117
  have hstable : (prefixWord ++ tailWord_1418117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418117).length < 2 ^ (prefixWord ++ tailWord_1418117).sum := by decide
  have hdescent : baseEnd_1418117 < baseStart_1418117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418130 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1418130 : Nat := 118140960795 + 1418130 * 2 ^ 59
def prefixEnd_1418130 : Nat := 4983230072969 + 3 ^ 40 * 1418130 * 2
def baseEnd_1418130 : Nat := 728182320560641793553145

theorem tailTrace_1418130 : CollatzResearch.WordTrace tailWord_1418130 prefixEnd_1418130 728182320560641793553145 := by
  unfold tailWord_1418130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12930862588091170541698961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34482300234909788111197229 12930862588091170541698961)
  ·
    refine ⟨9698146941068377906274221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12930862588091170541698961 9698146941068377906274221)
    ·
      refine ⟨3636805102900641714852833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9698146941068377906274221 3636805102900641714852833)
      ·
        refine ⟨2727603827175481286139625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3636805102900641714852833 2727603827175481286139625)
        ·
          refine ⟨2045702870381610964604719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2727603827175481286139625 2045702870381610964604719)
          ·
            refine ⟨3068554305572416446907079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045702870381610964604719 3068554305572416446907079)
            ·
              refine ⟨4602831458358624670360619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3068554305572416446907079 4602831458358624670360619)
              ·
                refine ⟨6904247187537937005540929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602831458358624670360619 6904247187537937005540929)
                ·
                  refine ⟨5178185390653452754155697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6904247187537937005540929 5178185390653452754155697)
                  ·
                    refine ⟨3883639042990089565616773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5178185390653452754155697 3883639042990089565616773)
                    ·
                      refine ⟨728182320560641793553145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3883639042990089565616773 728182320560641793553145)
                      ·
                        rfl

theorem cell23_1418130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1418130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418130 prefixEnd_1418130 := by exact prefixLift 1418130
  have htrace : WordTrace (prefixWord ++ tailWord_1418130) baseStart_1418130 baseEnd_1418130 := by
    simpa [prefixWord, tailWord_1418130, baseEnd_1418130] using wordTrace_append hprefix tailTrace_1418130
  have hstable : (prefixWord ++ tailWord_1418130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418130).length < 2 ^ (prefixWord ++ tailWord_1418130).sum := by decide
  have hdescent : baseEnd_1418130 < baseStart_1418130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418133 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_1418133 : Nat := 118140960795 + 1418133 * 2 ^ 59
def prefixEnd_1418133 : Nat := 4983230072969 + 3 ^ 40 * 1418133 * 2
def baseEnd_1418133 : Nat := 728183861002605281815631

theorem tailTrace_1418133 : CollatzResearch.WordTrace tailWord_1418133 prefixEnd_1418133 728183861002605281815631 := by
  unfold tailWord_1418133
  simp only [CollatzResearch.WordTrace]
  refine ⟨51723559771353813679155053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34482373180902542452770035 51723559771353813679155053)
  ·
    refine ⟨19396334914257680129683145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51723559771353813679155053 19396334914257680129683145)
    ·
      refine ⟨14547251185693260097262359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19396334914257680129683145 14547251185693260097262359)
      ·
        refine ⟨21820876778539890145893539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14547251185693260097262359 21820876778539890145893539)
        ·
          refine ⟨32731315167809835218840309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21820876778539890145893539 32731315167809835218840309)
          ·
            refine ⟨3068560796982172051766279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32731315167809835218840309 3068560796982172051766279)
            ·
              refine ⟨4602841195473258077649419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3068560796982172051766279 4602841195473258077649419)
              ·
                refine ⟨6904261793209887116474129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602841195473258077649419 6904261793209887116474129)
                ·
                  refine ⟨5178196344907415337355597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6904261793209887116474129 5178196344907415337355597)
                  ·
                    refine ⟨1941823629340280751508349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5178196344907415337355597 1941823629340280751508349)
                    ·
                      refine ⟨728183861002605281815631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1941823629340280751508349 728183861002605281815631)
                      ·
                        rfl

theorem cell23_1418133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_1418133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418133 prefixEnd_1418133 := by exact prefixLift 1418133
  have htrace : WordTrace (prefixWord ++ tailWord_1418133) baseStart_1418133 baseEnd_1418133 := by
    simpa [prefixWord, tailWord_1418133, baseEnd_1418133] using wordTrace_append hprefix tailTrace_1418133
  have hstable : (prefixWord ++ tailWord_1418133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418133).length < 2 ^ (prefixWord ++ tailWord_1418133).sum := by decide
  have hdescent : baseEnd_1418133 < baseStart_1418133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418134 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1418134 : Nat := 118140960795 + 1418134 * 2 ^ 59
def prefixEnd_1418134 : Nat := 4983230072969 + 3 ^ 40 * 1418134 * 2
def baseEnd_1418134 : Nat := 728184374483259777903127

theorem tailTrace_1418134 : CollatzResearch.WordTrace tailWord_1418134 prefixEnd_1418134 728184374483259777903127 := by
  unfold tailWord_1418134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3232724765271886928121341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34482397496233460566627637 3232724765271886928121341)
  ·
    refine ⟨1212271786976957598045503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3232724765271886928121341 1212271786976957598045503)
    ·
      refine ⟨1818407680465436397068255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1212271786976957598045503 1818407680465436397068255)
      ·
        refine ⟨2727611520698154595602383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1818407680465436397068255 2727611520698154595602383)
        ·
          refine ⟨4091417281047231893403575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2727611520698154595602383 4091417281047231893403575)
          ·
            refine ⟨6137125921570847840105363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4091417281047231893403575 6137125921570847840105363)
            ·
              refine ⟨9205688882356271760158045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6137125921570847840105363 9205688882356271760158045)
              ·
                refine ⟨3452133330883601910059267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9205688882356271760158045 3452133330883601910059267)
                ·
                  refine ⟨5178199996325402865088901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3452133330883601910059267 5178199996325402865088901)
                  ·
                    refine ⟨970912499311013037204169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5178199996325402865088901 970912499311013037204169)
                    ·
                      refine ⟨728184374483259777903127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970912499311013037204169 728184374483259777903127)
                      ·
                        rfl

theorem cell23_1418134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1418134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418134 prefixEnd_1418134 := by exact prefixLift 1418134
  have htrace : WordTrace (prefixWord ++ tailWord_1418134) baseStart_1418134 baseEnd_1418134 := by
    simpa [prefixWord, tailWord_1418134, baseEnd_1418134] using wordTrace_append hprefix tailTrace_1418134
  have hstable : (prefixWord ++ tailWord_1418134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418134).length < 2 ^ (prefixWord ++ tailWord_1418134).sum := by decide
  have hdescent : baseEnd_1418134 < baseStart_1418134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418156 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_1418156 : Nat := 118140960795 + 1418156 * 2 ^ 59
def prefixEnd_1418156 : Nat := 4983230072969 + 3 ^ 40 * 1418156 * 2
def baseEnd_1418156 : Nat := 728195671057658691828025

theorem tailTrace_1418156 : CollatzResearch.WordTrace tailWord_1418156 prefixEnd_1418156 728195671057658691828025 := by
  unfold tailWord_1418156
  simp only [CollatzResearch.WordTrace]
  refine ⟨25862199325135244303621161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34482932433513659071494881 25862199325135244303621161)
  ·
    refine ⟨19396649493851433227715871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25862199325135244303621161 19396649493851433227715871)
    ·
      refine ⟨29094974240777149841573807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19396649493851433227715871 29094974240777149841573807)
      ·
        refine ⟨43642461361165724762360711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29094974240777149841573807 43642461361165724762360711)
        ·
          refine ⟨65463692041748587143541067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43642461361165724762360711 65463692041748587143541067)
          ·
            refine ⟨98195538062622880715311601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65463692041748587143541067 98195538062622880715311601)
            ·
              refine ⟨73646653546967160536483701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98195538062622880715311601 73646653546967160536483701)
              ·
                refine ⟨6904373770028171300295347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73646653546967160536483701 6904373770028171300295347)
                ·
                  refine ⟨10356560655042256950443021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6904373770028171300295347 10356560655042256950443021)
                  ·
                    refine ⟨3883710245640846356416133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10356560655042256950443021 3883710245640846356416133)
                    ·
                      refine ⟨728195671057658691828025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3883710245640846356416133 728195671057658691828025)
                      ·
                        rfl

theorem cell23_1418156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_1418156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418156 prefixEnd_1418156 := by exact prefixLift 1418156
  have htrace : WordTrace (prefixWord ++ tailWord_1418156) baseStart_1418156 baseEnd_1418156 := by
    simpa [prefixWord, tailWord_1418156, baseEnd_1418156] using wordTrace_append hprefix tailTrace_1418156
  have hstable : (prefixWord ++ tailWord_1418156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418156).length < 2 ^ (prefixWord ++ tailWord_1418156).sum := by decide
  have hdescent : baseEnd_1418156 < baseStart_1418156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418183 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 3, 4]
def baseStart_1418183 : Nat := 118140960795 + 1418183 * 2 ^ 59
def prefixEnd_1418183 : Nat := 4983230072969 + 3 ^ 40 * 1418183 * 2
def baseEnd_1418183 : Nat := 242736511678443362063467

theorem tailTrace_1418183 : CollatzResearch.WordTrace tailWord_1418183 prefixEnd_1418183 242736511678443362063467 := by
  unfold tailWord_1418183
  simp only [CollatzResearch.WordTrace]
  refine ⟨51725383421172672218475203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34483588947448448145650135 51725383421172672218475203)
  ·
    refine ⟨77588075131759008327712805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51725383421172672218475203 77588075131759008327712805)
    ·
      refine ⟨14547764087204814061446151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77588075131759008327712805 14547764087204814061446151)
      ·
        refine ⟨21821646130807221092169227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14547764087204814061446151 21821646130807221092169227)
        ·
          refine ⟨32732469196210831638253841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21821646130807221092169227 32732469196210831638253841)
          ·
            refine ⟨24549351897158123728690381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32732469196210831638253841 24549351897158123728690381)
            ·
              refine ⟨9206006961434296398258893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24549351897158123728690381 9206006961434296398258893)
              ·
                refine ⟨3452252610537861149347085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9206006961434296398258893 3452252610537861149347085)
                ·
                  refine ⟨1294594728951697931005157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3452252610537861149347085 1294594728951697931005157)
                  ·
                    refine ⟨242736511678443362063467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1294594728951697931005157 242736511678443362063467)
                    ·
                      rfl

theorem cell23_1418183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_1418183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418183 prefixEnd_1418183 := by exact prefixLift 1418183
  have htrace : WordTrace (prefixWord ++ tailWord_1418183) baseStart_1418183 baseEnd_1418183 := by
    simpa [prefixWord, tailWord_1418183, baseEnd_1418183] using wordTrace_append hprefix tailTrace_1418183
  have hstable : (prefixWord ++ tailWord_1418183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418183).length < 2 ^ (prefixWord ++ tailWord_1418183).sum := by decide
  have hdescent : baseEnd_1418183 < baseStart_1418183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418186 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_1418186 : Nat := 118140960795 + 1418186 * 2 ^ 59
def prefixEnd_1418186 : Nat := 4983230072969 + 3 ^ 40 * 1418186 * 2
def baseEnd_1418186 : Nat := 728211075477293574452887

theorem tailTrace_1418186 : CollatzResearch.WordTrace tailWord_1418186 prefixEnd_1418186 728211075477293574452887 := by
  unfold tailWord_1418186
  simp only [CollatzResearch.WordTrace]
  refine ⟨12931373210040450932708603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34483661893441202487222941 12931373210040450932708603)
  ·
    refine ⟨19397059815060676399062905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12931373210040450932708603 19397059815060676399062905)
    ·
      refine ⟨14547794861295507299297179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19397059815060676399062905 14547794861295507299297179)
      ·
        refine ⟨21821692291943260948945769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14547794861295507299297179 21821692291943260948945769)
        ·
          refine ⟨16366269218957445711709327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21821692291943260948945769 16366269218957445711709327)
          ·
            refine ⟨24549403828436168567563991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16366269218957445711709327 24549403828436168567563991)
            ·
              refine ⟨36824105742654252851345987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24549403828436168567563991 36824105742654252851345987)
              ·
                refine ⟨55236158613981379277018981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36824105742654252851345987 55236158613981379277018981)
                ·
                  refine ⟨10356779740121508614441059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55236158613981379277018981 10356779740121508614441059)
                  ·
                    refine ⟨15535169610182262921661589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10356779740121508614441059 15535169610182262921661589)
                    ·
                      refine ⟨728211075477293574452887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15535169610182262921661589 728211075477293574452887)
                      ·
                        rfl

theorem cell23_1418186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_1418186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418186 prefixEnd_1418186 := by exact prefixLift 1418186
  have htrace : WordTrace (prefixWord ++ tailWord_1418186) baseStart_1418186 baseEnd_1418186 := by
    simpa [prefixWord, tailWord_1418186, baseEnd_1418186] using wordTrace_append hprefix tailTrace_1418186
  have hstable : (prefixWord ++ tailWord_1418186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418186).length < 2 ^ (prefixWord ++ tailWord_1418186).sum := by decide
  have hdescent : baseEnd_1418186 < baseStart_1418186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418190 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2]
def baseStart_1418190 : Nat := 118140960795 + 1418190 * 2 ^ 59
def prefixEnd_1418190 : Nat := 4983230072969 + 3 ^ 40 * 1418190 * 2
def baseEnd_1418190 : Nat := 728213129399911558802869

theorem tailTrace_1418190 : CollatzResearch.WordTrace tailWord_1418190 prefixEnd_1418190 728213129399911558802869 := by
  unfold tailWord_1418190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6465704841518414051747503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34483759154764874942653349 6465704841518414051747503)
  ·
    refine ⟨9698557262277621077621255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6465704841518414051747503 9698557262277621077621255)
    ·
      refine ⟨14547835893416431616431883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9698557262277621077621255 14547835893416431616431883)
      ·
        refine ⟨21821753840124647424647825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14547835893416431616431883 21821753840124647424647825)
        ·
          refine ⟨16366315380093485568485869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21821753840124647424647825 16366315380093485568485869)
          ·
            refine ⟨6137368267535057088182201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16366315380093485568485869 6137368267535057088182201)
            ·
              refine ⟨4603026200651292816136651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6137368267535057088182201 4603026200651292816136651)
              ·
                refine ⟨6904539300976939224204977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4603026200651292816136651 6904539300976939224204977)
                ·
                  refine ⟨5178404475732704418153733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6904539300976939224204977 5178404475732704418153733)
                  ·
                    refine ⟨970950839199882078403825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5178404475732704418153733 970950839199882078403825)
                    ·
                      refine ⟨728213129399911558802869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 970950839199882078403825 728213129399911558802869)
                      ·
                        rfl

theorem cell23_1418190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_1418190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418190 prefixEnd_1418190 := by exact prefixLift 1418190
  have htrace : WordTrace (prefixWord ++ tailWord_1418190) baseStart_1418190 baseEnd_1418190 := by
    simpa [prefixWord, tailWord_1418190, baseEnd_1418190] using wordTrace_append hprefix tailTrace_1418190
  have hstable : (prefixWord ++ tailWord_1418190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418190).length < 2 ^ (prefixWord ++ tailWord_1418190).sum := by decide
  have hdescent : baseEnd_1418190 < baseStart_1418190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418273 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 3, 6]
def baseStart_1418273 : Nat := 118140960795 + 1418273 * 2 ^ 59
def prefixEnd_1418273 : Nat := 4983230072969 + 3 ^ 40 * 1418273 * 2
def baseEnd_1418273 : Nat := 242751916098078244688329

theorem tailTrace_1418273 : CollatzResearch.WordTrace tailWord_1418273 prefixEnd_1418273 242751916098078244688329 := by
  unfold tailWord_1418273
  simp only [CollatzResearch.WordTrace]
  refine ⟨51728665990846617589251473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34485777327231078392834315 51728665990846617589251473)
  ·
    refine ⟨38796499493134963191938605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51728665990846617589251473 38796499493134963191938605)
    ·
      refine ⟨14548687309925611196976977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38796499493134963191938605 14548687309925611196976977)
      ·
        refine ⟨10911515482444208397732733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14548687309925611196976977 10911515482444208397732733)
        ·
          refine ⟨4091818305916578149149775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10911515482444208397732733 4091818305916578149149775)
          ·
            refine ⟨6137727458874867223724663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4091818305916578149149775 6137727458874867223724663)
            ·
              refine ⟨9206591188312300835586995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6137727458874867223724663 9206591188312300835586995)
              ·
                refine ⟨13809886782468451253380493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9206591188312300835586995 13809886782468451253380493)
                ·
                  refine ⟨5178707543425669220017685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13809886782468451253380493 5178707543425669220017685)
                  ·
                    refine ⟨242751916098078244688329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5178707543425669220017685 242751916098078244688329)
                    ·
                      rfl

theorem cell23_1418273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_1418273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418273 prefixEnd_1418273 := by exact prefixLift 1418273
  have htrace : WordTrace (prefixWord ++ tailWord_1418273) baseStart_1418273 baseEnd_1418273 := by
    simpa [prefixWord, tailWord_1418273, baseEnd_1418273] using wordTrace_append hprefix tailTrace_1418273
  have hstable : (prefixWord ++ tailWord_1418273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418273).length < 2 ^ (prefixWord ++ tailWord_1418273).sum := by decide
  have hdescent : baseEnd_1418273 < baseStart_1418273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418293 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1418293 : Nat := 118140960795 + 1418293 * 2 ^ 59
def prefixEnd_1418293 : Nat := 4983230072969 + 3 ^ 40 * 1418293 * 2
def baseEnd_1418293 : Nat := 728266017907324655814895

theorem tailTrace_1418293 : CollatzResearch.WordTrace tailWord_1418293 prefixEnd_1418293 728266017907324655814895 := by
  unfold tailWord_1418293
  simp only [CollatzResearch.WordTrace]
  refine ⟨51729395450774161004979533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34486263633849440669986355 51729395450774161004979533)
  ·
    refine ⟨19398523294040310376867325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51729395450774161004979533 19398523294040310376867325)
    ·
      refine ⟨7274446235265116391325247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19398523294040310376867325 7274446235265116391325247)
      ·
        refine ⟨10911669352897674586987871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7274446235265116391325247 10911669352897674586987871)
        ·
          refine ⟨16367504029346511880481807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10911669352897674586987871 16367504029346511880481807)
          ·
            refine ⟨24551256044019767820722711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16367504029346511880481807 24551256044019767820722711)
            ·
              refine ⟨36826884066029651731084067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24551256044019767820722711 36826884066029651731084067)
              ·
                refine ⟨55240326099044477596626101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36826884066029651731084067 55240326099044477596626101)
                ·
                  refine ⟨5178780571785419774683697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55240326099044477596626101 5178780571785419774683697)
                  ·
                    refine ⟨3884085428839064831012773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5178780571785419774683697 3884085428839064831012773)
                    ·
                      refine ⟨728266017907324655814895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3884085428839064831012773 728266017907324655814895)
                      ·
                        rfl

theorem cell23_1418293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1418293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418293 prefixEnd_1418293 := by exact prefixLift 1418293
  have htrace : WordTrace (prefixWord ++ tailWord_1418293) baseStart_1418293 baseEnd_1418293 := by
    simpa [prefixWord, tailWord_1418293, baseEnd_1418293] using wordTrace_append hprefix tailTrace_1418293
  have hstable : (prefixWord ++ tailWord_1418293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418293).length < 2 ^ (prefixWord ++ tailWord_1418293).sum := by decide
  have hdescent : baseEnd_1418293 < baseStart_1418293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418300 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_1418300 : Nat := 118140960795 + 1418300 * 2 ^ 59
def prefixEnd_1418300 : Nat := 4983230072969 + 3 ^ 40 * 1418300 * 2
def baseEnd_1418300 : Nat := 728269612271906128427363

theorem tailTrace_1418300 : CollatzResearch.WordTrace tailWord_1418300 prefixEnd_1418300 728269612271906128427363 := by
  unfold tailWord_1418300
  simp only [CollatzResearch.WordTrace]
  refine ⟨25864825380874400600242177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34486433841165867466989569 25864825380874400600242177)
  ·
    refine ⟨19398619035655800450181633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25864825380874400600242177 19398619035655800450181633)
    ·
      refine ⟨14548964276741850337636225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19398619035655800450181633 14548964276741850337636225)
      ·
        refine ⟨10911723207556387753227169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14548964276741850337636225 10911723207556387753227169)
        ·
          refine ⟨8183792405667290814920377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10911723207556387753227169 8183792405667290814920377)
          ·
            refine ⟨6137844304250468111190283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8183792405667290814920377 6137844304250468111190283)
            ·
              refine ⟨9206766456375702166785425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6137844304250468111190283 9206766456375702166785425)
              ·
                refine ⟨6905074842281776625089069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9206766456375702166785425 6905074842281776625089069)
                ·
                  refine ⟨2589403065855666234408401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6905074842281776625089069 2589403065855666234408401)
                  ·
                    refine ⟨1942052299391749675806301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2589403065855666234408401 1942052299391749675806301)
                    ·
                      refine ⟨728269612271906128427363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1942052299391749675806301 728269612271906128427363)
                      ·
                        rfl

theorem cell23_1418300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_1418300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418300 prefixEnd_1418300 := by exact prefixLift 1418300
  have htrace : WordTrace (prefixWord ++ tailWord_1418300) baseStart_1418300 baseEnd_1418300 := by
    simpa [prefixWord, tailWord_1418300, baseEnd_1418300] using wordTrace_append hprefix tailTrace_1418300
  have hstable : (prefixWord ++ tailWord_1418300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418300).length < 2 ^ (prefixWord ++ tailWord_1418300).sum := by decide
  have hdescent : baseEnd_1418300 < baseStart_1418300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418317 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1418317 : Nat := 118140960795 + 1418317 * 2 ^ 59
def prefixEnd_1418317 : Nat := 4983230072969 + 3 ^ 40 * 1418317 * 2
def baseEnd_1418317 : Nat := 728278341443032561914785

theorem tailTrace_1418317 : CollatzResearch.WordTrace tailWord_1418317 prefixEnd_1418317 728278341443032561914785 := by
  unfold tailWord_1418317
  simp only [CollatzResearch.WordTrace]
  refine ⟨51730270802687213103853205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34486847201791475402568803 51730270802687213103853205)
  ·
    refine ⟨2424856443875963114243119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51730270802687213103853205 2424856443875963114243119)
    ·
      refine ⟨3637284665813944671364679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2424856443875963114243119 3637284665813944671364679)
      ·
        refine ⟨5455926998720917007047019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3637284665813944671364679 5455926998720917007047019)
        ·
          refine ⟨8183890498081375510570529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5455926998720917007047019 8183890498081375510570529)
          ·
            refine ⟨6137917873561031632927897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8183890498081375510570529 6137917873561031632927897)
            ·
              refine ⟨4603438405170773724695923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6137917873561031632927897 4603438405170773724695923)
              ·
                refine ⟨6905157607756160587043885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4603438405170773724695923 6905157607756160587043885)
                ·
                  refine ⟨2589434102908560220141457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6905157607756160587043885 2589434102908560220141457)
                  ·
                    refine ⟨1942075577181420165106093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2589434102908560220141457 1942075577181420165106093)
                    ·
                      refine ⟨728278341443032561914785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1942075577181420165106093 728278341443032561914785)
                      ·
                        rfl

theorem cell23_1418317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1418317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418317 prefixEnd_1418317 := by exact prefixLift 1418317
  have htrace : WordTrace (prefixWord ++ tailWord_1418317) baseStart_1418317 baseEnd_1418317 := by
    simpa [prefixWord, tailWord_1418317, baseEnd_1418317] using wordTrace_append hprefix tailTrace_1418317
  have hstable : (prefixWord ++ tailWord_1418317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418317).length < 2 ^ (prefixWord ++ tailWord_1418317).sum := by decide
  have hdescent : baseEnd_1418317 < baseStart_1418317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418353 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_1418353 : Nat := 118140960795 + 1418353 * 2 ^ 59
def prefixEnd_1418353 : Nat := 4983230072969 + 3 ^ 40 * 1418353 * 2
def baseEnd_1418353 : Nat := 728296826746594421064619

theorem tailTrace_1418353 : CollatzResearch.WordTrace tailWord_1418353 prefixEnd_1418353 728296826746594421064619 := by
  unfold tailWord_1418353
  simp only [CollatzResearch.WordTrace]
  refine ⟨51731583830556791252163713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34487722553704527501442475 51731583830556791252163713)
  ·
    refine ⟨38798687872917593439122785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51731583830556791252163713 38798687872917593439122785)
    ·
      refine ⟨29099015904688195079342089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38798687872917593439122785 29099015904688195079342089)
      ·
        refine ⟨21824261928516146309506567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29099015904688195079342089 21824261928516146309506567)
        ·
          refine ⟨32736392892774219464259851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21824261928516146309506567 32736392892774219464259851)
          ·
            refine ⟨49104589339161329196389777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32736392892774219464259851 49104589339161329196389777)
            ·
              refine ⟨36828442004370996897292333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49104589339161329196389777 36828442004370996897292333)
              ·
                refine ⟨13810665751639123836484625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36828442004370996897292333 13810665751639123836484625)
                ·
                  refine ⟨10357999313729342877363469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13810665751639123836484625 10357999313729342877363469)
                  ·
                    refine ⟨3884249742648503579011301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10357999313729342877363469 3884249742648503579011301)
                    ·
                      refine ⟨728296826746594421064619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3884249742648503579011301 728296826746594421064619)
                      ·
                        rfl

theorem cell23_1418353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_1418353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418353 prefixEnd_1418353 := by exact prefixLift 1418353
  have htrace : WordTrace (prefixWord ++ tailWord_1418353) baseStart_1418353 baseEnd_1418353 := by
    simpa [prefixWord, tailWord_1418353, baseEnd_1418353] using wordTrace_append hprefix tailTrace_1418353
  have hstable : (prefixWord ++ tailWord_1418353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418353).length < 2 ^ (prefixWord ++ tailWord_1418353).sum := by decide
  have hdescent : baseEnd_1418353 < baseStart_1418353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418364 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 2, 1, 3]
def baseStart_1418364 : Nat := 118140960795 + 1418364 * 2 ^ 59
def prefixEnd_1418364 : Nat := 4983230072969 + 3 ^ 40 * 1418364 * 2
def baseEnd_1418364 : Nat := 728302475033793878027069

theorem tailTrace_1418364 : CollatzResearch.WordTrace tailWord_1418364 prefixEnd_1418364 728302475033793878027069 := by
  unfold tailWord_1418364
  simp only [CollatzResearch.WordTrace]
  refine ⟨25865992516758470065407073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34487990022344626753876097 25865992516758470065407073)
  ·
    refine ⟨19399494387568852549055305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25865992516758470065407073 19399494387568852549055305)
    ·
      refine ⟨14549620790676639411791479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19399494387568852549055305 14549620790676639411791479)
      ·
        refine ⟨21824431186014959117687219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14549620790676639411791479 21824431186014959117687219)
        ·
          refine ⟨32736646779022438676530829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21824431186014959117687219 32736646779022438676530829)
          ·
            refine ⟨12276242542133414503699061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32736646779022438676530829 12276242542133414503699061)
            ·
              refine ⟨1150897738325007609721787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12276242542133414503699061 1150897738325007609721787)
              ·
                refine ⟨1726346607487511414582681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150897738325007609721787 1726346607487511414582681)
                ·
                  refine ⟨1294759955615633560937011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1726346607487511414582681 1294759955615633560937011)
                  ·
                    refine ⟨1942139933423450341405517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1294759955615633560937011 1942139933423450341405517)
                    ·
                      refine ⟨728302475033793878027069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1942139933423450341405517 728302475033793878027069)
                      ·
                        rfl

theorem cell23_1418364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_1418364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418364 prefixEnd_1418364 := by exact prefixLift 1418364
  have htrace : WordTrace (prefixWord ++ tailWord_1418364) baseStart_1418364 baseEnd_1418364 := by
    simpa [prefixWord, tailWord_1418364, baseEnd_1418364] using wordTrace_append hprefix tailTrace_1418364
  have hstable : (prefixWord ++ tailWord_1418364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418364).length < 2 ^ (prefixWord ++ tailWord_1418364).sum := by decide
  have hdescent : baseEnd_1418364 < baseStart_1418364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418387 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 4, 2, 2]
def baseStart_1418387 : Nat := 118140960795 + 1418387 * 2 ^ 59
def prefixEnd_1418387 : Nat := 4983230072969 + 3 ^ 40 * 1418387 * 2
def baseEnd_1418387 : Nat := 728314285088847288039463

theorem tailTrace_1418387 : CollatzResearch.WordTrace tailWord_1418387 prefixEnd_1418387 728314285088847288039463 := by
  unfold tailWord_1418387
  simp only [CollatzResearch.WordTrace]
  refine ⟨51732823912433615058901415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34488549274955743372600943 51732823912433615058901415)
  ·
    refine ⟨77599235868650422588352123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51732823912433615058901415 77599235868650422588352123)
    ·
      refine ⟨116398853802975633882528185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77599235868650422588352123 116398853802975633882528185)
      ·
        refine ⟨87299140352231725411896139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116398853802975633882528185 87299140352231725411896139)
        ·
          refine ⟨130948710528347588117844209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87299140352231725411896139 130948710528347588117844209)
          ·
            refine ⟨98211532896260691088383157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130948710528347588117844209 98211532896260691088383157)
            ·
              refine ⟨9207331209024439789535921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98211532896260691088383157 9207331209024439789535921)
              ·
                refine ⟨6905498406768329842151941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9207331209024439789535921 6905498406768329842151941)
                ·
                  refine ⟨1294780951269061845403489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6905498406768329842151941 1294780951269061845403489)
                  ·
                    refine ⟨971085713451796384052617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1294780951269061845403489 971085713451796384052617)
                    ·
                      refine ⟨728314285088847288039463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 971085713451796384052617 728314285088847288039463)
                      ·
                        rfl

theorem cell23_1418387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 2, 2].length) (baseStart_1418387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418387 prefixEnd_1418387 := by exact prefixLift 1418387
  have htrace : WordTrace (prefixWord ++ tailWord_1418387) baseStart_1418387 baseEnd_1418387 := by
    simpa [prefixWord, tailWord_1418387, baseEnd_1418387] using wordTrace_append hprefix tailTrace_1418387
  have hstable : (prefixWord ++ tailWord_1418387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418387).length < 2 ^ (prefixWord ++ tailWord_1418387).sum := by decide
  have hdescent : baseEnd_1418387 < baseStart_1418387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418404 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 4, 2, 2]
def baseStart_1418404 : Nat := 118140960795 + 1418404 * 2 ^ 59
def prefixEnd_1418404 : Nat := 4983230072969 + 3 ^ 40 * 1418404 * 2
def baseEnd_1418404 : Nat := 728323014259973721526885

theorem tailTrace_1418404 : CollatzResearch.WordTrace tailWord_1418404 prefixEnd_1418404 728323014259973721526885 := by
  unfold tailWord_1418404
  simp only [CollatzResearch.WordTrace]
  refine ⟨25866721976686013481135133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34488962635581351308180177 25866721976686013481135133)
  ·
    refine ⟨9700020741257255055425675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25866721976686013481135133 9700020741257255055425675)
    ·
      refine ⟨14550031111885882583138513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9700020741257255055425675 14550031111885882583138513)
      ·
        refine ⟨10912523333914411937353885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14550031111885882583138513 10912523333914411937353885)
        ·
          refine ⟨4092196250217904476507707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10912523333914411937353885 4092196250217904476507707)
          ·
            refine ⟨6138294375326856714761561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4092196250217904476507707 6138294375326856714761561)
            ·
              refine ⟨4603720781495142536071171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6138294375326856714761561 4603720781495142536071171)
              ·
                refine ⟨6905581172242713804106757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4603720781495142536071171 6905581172242713804106757)
                ·
                  refine ⟨1294796469795508838270017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6905581172242713804106757 1294796469795508838270017)
                  ·
                    refine ⟨971097352346631628702513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1294796469795508838270017 971097352346631628702513)
                    ·
                      refine ⟨728323014259973721526885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 971097352346631628702513 728323014259973721526885)
                      ·
                        rfl

theorem cell23_1418404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_1418404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418404 prefixEnd_1418404 := by exact prefixLift 1418404
  have htrace : WordTrace (prefixWord ++ tailWord_1418404) baseStart_1418404 baseEnd_1418404 := by
    simpa [prefixWord, tailWord_1418404, baseEnd_1418404] using wordTrace_append hprefix tailTrace_1418404
  have hstable : (prefixWord ++ tailWord_1418404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418404).length < 2 ^ (prefixWord ++ tailWord_1418404).sum := by decide
  have hdescent : baseEnd_1418404 < baseStart_1418404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418440 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 2, 5]
def baseStart_1418440 : Nat := 118140960795 + 1418440 * 2 ^ 59
def prefixEnd_1418440 : Nat := 4983230072969 + 3 ^ 40 * 1418440 * 2
def baseEnd_1418440 : Nat := 242780499854511860225573

theorem tailTrace_1418440 : CollatzResearch.WordTrace tailWord_1418440 prefixEnd_1418440 242780499854511860225573 := by
  unfold tailWord_1418440
  simp only [CollatzResearch.WordTrace]
  refine ⟨25867378490620802555290387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34489837987494403407053849 25867378490620802555290387)
  ·
    refine ⟨38801067735931203832935581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25867378490620802555290387 38801067735931203832935581)
    ·
      refine ⟨14550400400974201437350843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38801067735931203832935581 14550400400974201437350843)
      ·
        refine ⟨21825600601461302156026265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14550400400974201437350843 21825600601461302156026265)
        ·
          refine ⟨16369200451095976617019699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21825600601461302156026265 16369200451095976617019699)
          ·
            refine ⟨24553800676643964925529549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16369200451095976617019699 24553800676643964925529549)
            ·
              refine ⟨9207675253741486847073581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24553800676643964925529549 9207675253741486847073581)
              ·
                refine ⟨3452878220153057567652593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9207675253741486847073581 3452878220153057567652593)
                ·
                  refine ⟨2589658665114793175739445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3452878220153057567652593 2589658665114793175739445)
                  ·
                    refine ⟨242780499854511860225573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2589658665114793175739445 242780499854511860225573)
                    ·
                      rfl

theorem cell23_1418440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_1418440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418440 prefixEnd_1418440 := by exact prefixLift 1418440
  have htrace : WordTrace (prefixWord ++ tailWord_1418440) baseStart_1418440 baseEnd_1418440 := by
    simpa [prefixWord, tailWord_1418440, baseEnd_1418440] using wordTrace_append hprefix tailTrace_1418440
  have hstable : (prefixWord ++ tailWord_1418440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418440).length < 2 ^ (prefixWord ++ tailWord_1418440).sum := by decide
  have hdescent : baseEnd_1418440 < baseStart_1418440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418450 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1418450 : Nat := 118140960795 + 1418450 * 2 ^ 59
def prefixEnd_1418450 : Nat := 4983230072969 + 3 ^ 40 * 1418450 * 2
def baseEnd_1418450 : Nat := 728346634370080541551673

theorem tailTrace_1418450 : CollatzResearch.WordTrace tailWord_1418450 prefixEnd_1418450 728346634370080541551673 := by
  unfold tailWord_1418450
  simp only [CollatzResearch.WordTrace]
  refine ⟨12933780427801344204611201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34490081140803584545629869 12933780427801344204611201)
  ·
    refine ⟨9700335320851008153458401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12933780427801344204611201 9700335320851008153458401)
    ·
      refine ⟨7275251490638256115093801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9700335320851008153458401 7275251490638256115093801)
      ·
        refine ⟨5456438617978692086320351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7275251490638256115093801 5456438617978692086320351)
        ·
          refine ⟨8184657926968038129480527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5456438617978692086320351 8184657926968038129480527)
          ·
            refine ⟨12276986890452057194220791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8184657926968038129480527 12276986890452057194220791)
            ·
              refine ⟨18415480335678085791331187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12276986890452057194220791 18415480335678085791331187)
              ·
                refine ⟨27623220503517128686996781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18415480335678085791331187 27623220503517128686996781)
                ·
                  refine ⟨10358707688818923257623793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27623220503517128686996781 10358707688818923257623793)
                  ·
                    refine ⟨7769030766614192443217845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10358707688818923257623793 7769030766614192443217845)
                    ·
                      refine ⟨728346634370080541551673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7769030766614192443217845 728346634370080541551673)
                      ·
                        rfl

theorem cell23_1418450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1418450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418450 prefixEnd_1418450 := by exact prefixLift 1418450
  have htrace : WordTrace (prefixWord ++ tailWord_1418450) baseStart_1418450 baseEnd_1418450 := by
    simpa [prefixWord, tailWord_1418450, baseEnd_1418450] using wordTrace_append hprefix tailTrace_1418450
  have hstable : (prefixWord ++ tailWord_1418450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418450).length < 2 ^ (prefixWord ++ tailWord_1418450).sum := by decide
  have hdescent : baseEnd_1418450 < baseStart_1418450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418494 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_1418494 : Nat := 118140960795 + 1418494 * 2 ^ 59
def prefixEnd_1418494 : Nat := 4983230072969 + 3 ^ 40 * 1418494 * 2
def baseEnd_1418494 : Nat := 728369227518878369401471

theorem tailTrace_1418494 : CollatzResearch.WordTrace tailWord_1418494 prefixEnd_1418494 728369227518878369401471 := by
  unfold tailWord_1418494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6467090815380746541630817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34491151015363981555364357 6467090815380746541630817)
  ·
    refine ⟨4850318111535559906223113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6467090815380746541630817 4850318111535559906223113)
    ·
      refine ⟨3637738583651669929667335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4850318111535559906223113 3637738583651669929667335)
      ·
        refine ⟨5456607875477504894501003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3637738583651669929667335 5456607875477504894501003)
        ·
          refine ⟨8184911813216257341751505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5456607875477504894501003 8184911813216257341751505)
          ·
            refine ⟨6138683859912193006313629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8184911813216257341751505 6138683859912193006313629)
            ·
              refine ⟨2302006447467072377367611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6138683859912193006313629 2302006447467072377367611)
              ·
                refine ⟨3453009671200608566051417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2302006447467072377367611 3453009671200608566051417)
                ·
                  refine ⟨2589757253400456424538563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3453009671200608566051417 2589757253400456424538563)
                  ·
                    refine ⟨3884635880100684636807845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2589757253400456424538563 3884635880100684636807845)
                    ·
                      refine ⟨728369227518878369401471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3884635880100684636807845 728369227518878369401471)
                      ·
                        rfl

theorem cell23_1418494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_1418494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418494 prefixEnd_1418494 := by exact prefixLift 1418494
  have htrace : WordTrace (prefixWord ++ tailWord_1418494) baseStart_1418494 baseEnd_1418494 := by
    simpa [prefixWord, tailWord_1418494, baseEnd_1418494] using wordTrace_append hprefix tailTrace_1418494
  have hstable : (prefixWord ++ tailWord_1418494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418494).length < 2 ^ (prefixWord ++ tailWord_1418494).sum := by decide
  have hdescent : baseEnd_1418494 < baseStart_1418494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418497 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_1418497 : Nat := 118140960795 + 1418497 * 2 ^ 59
def prefixEnd_1418497 : Nat := 4983230072969 + 3 ^ 40 * 1418497 * 2
def baseEnd_1418497 : Nat := 728370767960841857663957

theorem tailTrace_1418497 : CollatzResearch.WordTrace tailWord_1418497 prefixEnd_1418497 728370767960841857663957 := by
  unfold tailWord_1418497
  simp only [CollatzResearch.WordTrace]
  refine ⟨51736835942035103845405745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34491223961356735896937163 51736835942035103845405745)
  ·
    refine ⟨38802626956526327884054309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51736835942035103845405745 38802626956526327884054309)
    ·
      refine ⟨7275492554348686478260183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38802626956526327884054309 7275492554348686478260183)
      ·
        refine ⟨10913238831523029717390275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7275492554348686478260183 10913238831523029717390275)
        ·
          refine ⟨16369858247284544576085413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10913238831523029717390275 16369858247284544576085413)
          ·
            refine ⟨3069348421365852108016015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16369858247284544576085413 3069348421365852108016015)
            ·
              refine ⟨4604022632048778162024023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069348421365852108016015 4604022632048778162024023)
              ·
                refine ⟨6906033948073167243036035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604022632048778162024023 6906033948073167243036035)
                ·
                  refine ⟨10359050922109750864554053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6906033948073167243036035 10359050922109750864554053)
                  ·
                    refine ⟨1942322047895578287103885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10359050922109750864554053 1942322047895578287103885)
                    ·
                      refine ⟨728370767960841857663957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1942322047895578287103885 728370767960841857663957)
                      ·
                        rfl

theorem cell23_1418497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_1418497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418497 prefixEnd_1418497 := by exact prefixLift 1418497
  have htrace : WordTrace (prefixWord ++ tailWord_1418497) baseStart_1418497 baseEnd_1418497 := by
    simpa [prefixWord, tailWord_1418497, baseEnd_1418497] using wordTrace_append hprefix tailTrace_1418497
  have hstable : (prefixWord ++ tailWord_1418497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418497).length < 2 ^ (prefixWord ++ tailWord_1418497).sum := by decide
  have hdescent : baseEnd_1418497 < baseStart_1418497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418520 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_1418520 : Nat := 118140960795 + 1418520 * 2 ^ 59
def prefixEnd_1418520 : Nat := 4983230072969 + 3 ^ 40 * 1418520 * 2
def baseEnd_1418520 : Nat := 728382578015895267676351

theorem tailTrace_1418520 : CollatzResearch.WordTrace tailWord_1418520 prefixEnd_1418520 728382578015895267676351 := by
  unfold tailWord_1418520
  simp only [CollatzResearch.WordTrace]
  refine ⟨25868837410475889386746507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34491783213967852515662009 25868837410475889386746507)
  ·
    refine ⟨38803256115713834080119761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25868837410475889386746507 38803256115713834080119761)
    ·
      refine ⟨29102442086785375560089821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38803256115713834080119761 29102442086785375560089821)
      ·
        refine ⟨10913415782544515835033683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29102442086785375560089821 10913415782544515835033683)
        ·
          refine ⟨16370123673816773752550525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10913415782544515835033683 16370123673816773752550525)
          ·
            refine ⟨6138796377681290157206447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16370123673816773752550525 6138796377681290157206447)
            ·
              refine ⟨9208194566521935235809671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6138796377681290157206447 9208194566521935235809671)
              ·
                refine ⟨13812291849782902853714507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9208194566521935235809671 13812291849782902853714507)
                ·
                  refine ⟨20718437774674354280571761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13812291849782902853714507 20718437774674354280571761)
                  ·
                    refine ⟨15538828331005765710428821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20718437774674354280571761 15538828331005765710428821)
                    ·
                      refine ⟨728382578015895267676351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15538828331005765710428821 728382578015895267676351)
                      ·
                        rfl

theorem cell23_1418520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_1418520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418520 prefixEnd_1418520 := by exact prefixLift 1418520
  have htrace : WordTrace (prefixWord ++ tailWord_1418520) baseStart_1418520 baseEnd_1418520 := by
    simpa [prefixWord, tailWord_1418520, baseEnd_1418520] using wordTrace_append hprefix tailTrace_1418520
  have hstable : (prefixWord ++ tailWord_1418520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418520).length < 2 ^ (prefixWord ++ tailWord_1418520).sum := by decide
  have hdescent : baseEnd_1418520 < baseStart_1418520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418547 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 1, 5]
def baseStart_1418547 : Nat := 118140960795 + 1418547 * 2 ^ 59
def prefixEnd_1418547 : Nat := 4983230072969 + 3 ^ 40 * 1418547 * 2
def baseEnd_1418547 : Nat := 242798813997855554012909

theorem tailTrace_1418547 : CollatzResearch.WordTrace tailWord_1418547 prefixEnd_1418547 242798813997855554012909 := by
  unfold tailWord_1418547
  simp only [CollatzResearch.WordTrace]
  refine ⟨51738659591853962384725895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34492439727902641589817263 51738659591853962384725895)
  ·
    refine ⟨77607989387780943577088843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51738659591853962384725895 77607989387780943577088843)
    ·
      refine ⟨116411984081671415365633265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77607989387780943577088843 116411984081671415365633265)
      ·
        refine ⟨87308988061253561524224949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116411984081671415365633265 87308988061253561524224949)
        ·
          refine ⟨8185217630742521392896089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87308988061253561524224949 8185217630742521392896089)
          ·
            refine ⟨6138913223056891044672067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8185217630742521392896089 6138913223056891044672067)
            ·
              refine ⟨9208369834585336567008101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6138913223056891044672067 9208369834585336567008101)
              ·
                refine ⟨1726569343984750606314019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9208369834585336567008101 1726569343984750606314019)
                ·
                  refine ⟨2589854015977125909471029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726569343984750606314019 2589854015977125909471029)
                  ·
                    refine ⟨242798813997855554012909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2589854015977125909471029 242798813997855554012909)
                    ·
                      rfl

theorem cell23_1418547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 5].length) (baseStart_1418547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418547 prefixEnd_1418547 := by exact prefixLift 1418547
  have htrace : WordTrace (prefixWord ++ tailWord_1418547) baseStart_1418547 baseEnd_1418547 := by
    simpa [prefixWord, tailWord_1418547, baseEnd_1418547] using wordTrace_append hprefix tailTrace_1418547
  have hstable : (prefixWord ++ tailWord_1418547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418547).length < 2 ^ (prefixWord ++ tailWord_1418547).sum := by decide
  have hdescent : baseEnd_1418547 < baseStart_1418547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418554 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2]
def baseStart_1418554 : Nat := 118140960795 + 1418554 * 2 ^ 59
def prefixEnd_1418554 : Nat := 4983230072969 + 3 ^ 40 * 1418554 * 2
def baseEnd_1418554 : Nat := 728400036358148134651195

theorem tailTrace_1418554 : CollatzResearch.WordTrace tailWord_1418554 prefixEnd_1418554 728400036358148134651195 := by
  unfold tailWord_1418554
  simp only [CollatzResearch.WordTrace]
  refine ⟨12934728725707150645057679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34492609935219068386820477 12934728725707150645057679)
  ·
    refine ⟨19402093088560725967586519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12934728725707150645057679 19402093088560725967586519)
    ·
      refine ⟨29103139632841088951379779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19402093088560725967586519 29103139632841088951379779)
      ·
        refine ⟨43654709449261633427069669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29103139632841088951379779 43654709449261633427069669)
        ·
          refine ⟨8185258021736556267575563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43654709449261633427069669 8185258021736556267575563)
          ·
            refine ⟨12277887032604834401363345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8185258021736556267575563 12277887032604834401363345)
            ·
              refine ⟨9208415274453625801022509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12277887032604834401363345 9208415274453625801022509)
              ·
                refine ⟨3453155727920109675383441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9208415274453625801022509 3453155727920109675383441)
                ·
                  refine ⟨2589866795940082256537581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3453155727920109675383441 2589866795940082256537581)
                  ·
                    refine ⟨971200048477530846201593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2589866795940082256537581 971200048477530846201593)
                    ·
                      refine ⟨728400036358148134651195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 971200048477530846201593 728400036358148134651195)
                      ·
                        rfl

theorem cell23_1418554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2].length) (baseStart_1418554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418554 prefixEnd_1418554 := by exact prefixLift 1418554
  have htrace : WordTrace (prefixWord ++ tailWord_1418554) baseStart_1418554 baseEnd_1418554 := by
    simpa [prefixWord, tailWord_1418554, baseEnd_1418554] using wordTrace_append hprefix tailTrace_1418554
  have hstable : (prefixWord ++ tailWord_1418554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418554).length < 2 ^ (prefixWord ++ tailWord_1418554).sum := by decide
  have hdescent : baseEnd_1418554 < baseStart_1418554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418560 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 3, 6]
def baseStart_1418560 : Nat := 118140960795 + 1418560 * 2 ^ 59
def prefixEnd_1418560 : Nat := 4983230072969 + 3 ^ 40 * 1418560 * 2
def baseEnd_1418560 : Nat := 242801039080691703725389

theorem tailTrace_1418560 : CollatzResearch.WordTrace tailWord_1418560 prefixEnd_1418560 242801039080691703725389 := by
  unfold tailWord_1418560
  simp only [CollatzResearch.WordTrace]
  refine ⟨25869566870403432802474567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34492755827204577069966089 25869566870403432802474567)
  ·
    refine ⟨38804350305605149203711851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25869566870403432802474567 38804350305605149203711851)
    ·
      refine ⟨58206525458407723805567777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38804350305605149203711851 58206525458407723805567777)
      ·
        refine ⟨43654894093805792854175833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58206525458407723805567777 43654894093805792854175833)
        ·
          refine ⟨32741170570354344640631875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43654894093805792854175833 32741170570354344640631875)
          ·
            refine ⟨49111755855531516960947813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32741170570354344640631875 49111755855531516960947813)
            ·
              refine ⟨9208454222912159430177715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49111755855531516960947813 9208454222912159430177715)
              ·
                refine ⟨13812681334368239145266573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9208454222912159430177715 13812681334368239145266573)
                ·
                  refine ⟨5179755500388089679474965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13812681334368239145266573 5179755500388089679474965)
                  ·
                    refine ⟨242801039080691703725389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5179755500388089679474965 242801039080691703725389)
                    ·
                      rfl

theorem cell23_1418560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_1418560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418560 prefixEnd_1418560 := by exact prefixLift 1418560
  have htrace : WordTrace (prefixWord ++ tailWord_1418560) baseStart_1418560 baseEnd_1418560 := by
    simpa [prefixWord, tailWord_1418560, baseEnd_1418560] using wordTrace_append hprefix tailTrace_1418560
  have hstable : (prefixWord ++ tailWord_1418560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418560).length < 2 ^ (prefixWord ++ tailWord_1418560).sum := by decide
  have hdescent : baseEnd_1418560 < baseStart_1418560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418577 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 4, 4]
def baseStart_1418577 : Nat := 118140960795 + 1418577 * 2 ^ 59
def prefixEnd_1418577 : Nat := 4983230072969 + 3 ^ 40 * 1418577 * 2
def baseEnd_1418577 : Nat := 242803948804400514887863

theorem tailTrace_1418577 : CollatzResearch.WordTrace tailWord_1418577 prefixEnd_1418577 242803948804400514887863 := by
  unfold tailWord_1418577
  simp only [CollatzResearch.WordTrace]
  refine ⟨51739753781745277508317985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34493169187830185005545323 51739753781745277508317985)
  ·
    refine ⟨38804815336308958131238489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51739753781745277508317985 38804815336308958131238489)
    ·
      refine ⟨29103611502231718598428867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38804815336308958131238489 29103611502231718598428867)
      ·
        refine ⟨43655417253347577897643301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29103611502231718598428867 43655417253347577897643301)
        ·
          refine ⟨8185390735002670855808119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43655417253347577897643301 8185390735002670855808119)
          ·
            refine ⟨12278086102504006283712179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8185390735002670855808119 12278086102504006283712179)
            ·
              refine ⟨18417129153756009425568269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12278086102504006283712179 18417129153756009425568269)
              ·
                refine ⟨6906423432658503534588101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18417129153756009425568269 6906423432658503534588101)
                ·
                  refine ⟨1294954393623469412735269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6906423432658503534588101 1294954393623469412735269)
                  ·
                    refine ⟨242803948804400514887863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1294954393623469412735269 242803948804400514887863)
                    ·
                      rfl

theorem cell23_1418577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 4].length) (baseStart_1418577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418577 prefixEnd_1418577 := by exact prefixLift 1418577
  have htrace : WordTrace (prefixWord ++ tailWord_1418577) baseStart_1418577 baseEnd_1418577 := by
    simpa [prefixWord, tailWord_1418577, baseEnd_1418577] using wordTrace_append hprefix tailTrace_1418577
  have hstable : (prefixWord ++ tailWord_1418577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418577).length < 2 ^ (prefixWord ++ tailWord_1418577).sum := by decide
  have hdescent : baseEnd_1418577 < baseStart_1418577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418597 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_1418597 : Nat := 118140960795 + 1418597 * 2 ^ 59
def prefixEnd_1418597 : Nat := 4983230072969 + 3 ^ 40 * 1418597 * 2
def baseEnd_1418597 : Nat := 728422116026291466413497

theorem tailTrace_1418597 : CollatzResearch.WordTrace tailWord_1418597 prefixEnd_1418597 728422116026291466413497 := by
  unfold tailWord_1418597
  simp only [CollatzResearch.WordTrace]
  refine ⟨51740483241672820924046045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34493655494448547282697363 51740483241672820924046045)
  ·
    refine ⟨19402681215627307846517267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51740483241672820924046045 19402681215627307846517267)
    ·
      refine ⟨29104021823440961769775901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19402681215627307846517267 29104021823440961769775901)
      ·
        refine ⟨10914008183790360663665963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29104021823440961769775901 10914008183790360663665963)
        ·
          refine ⟨16371012275685540995498945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10914008183790360663665963 16371012275685540995498945)
          ·
            refine ⟨12278259206764155746624209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16371012275685540995498945 12278259206764155746624209)
            ·
              refine ⟨9208694405073116809968157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12278259206764155746624209 9208694405073116809968157)
              ·
                refine ⟨3453260401902418803738059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9208694405073116809968157 3453260401902418803738059)
                ·
                  refine ⟨5179890602853628205607089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453260401902418803738059 5179890602853628205607089)
                  ·
                    refine ⟨3884917952140221154205317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5179890602853628205607089 3884917952140221154205317)
                    ·
                      refine ⟨728422116026291466413497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3884917952140221154205317 728422116026291466413497)
                      ·
                        rfl

theorem cell23_1418597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_1418597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418597 prefixEnd_1418597 := by exact prefixLift 1418597
  have htrace : WordTrace (prefixWord ++ tailWord_1418597) baseStart_1418597 baseEnd_1418597 := by
    simpa [prefixWord, tailWord_1418597, baseEnd_1418597] using wordTrace_append hprefix tailTrace_1418597
  have hstable : (prefixWord ++ tailWord_1418597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418597).length < 2 ^ (prefixWord ++ tailWord_1418597).sum := by decide
  have hdescent : baseEnd_1418597 < baseStart_1418597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418604 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 3]
def baseStart_1418604 : Nat := 118140960795 + 1418604 * 2 ^ 59
def prefixEnd_1418604 : Nat := 4983230072969 + 3 ^ 40 * 1418604 * 2
def baseEnd_1418604 : Nat := 728425710390872939025965

theorem tailTrace_1418604 : CollatzResearch.WordTrace tailWord_1418604 prefixEnd_1418604 728425710390872939025965 := by
  unfold tailWord_1418604
  simp only [CollatzResearch.WordTrace]
  refine ⟨25870369276323730559775433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34493825701764974079700577 25870369276323730559775433)
  ·
    refine ⟨19402776957242797919831575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25870369276323730559775433 19402776957242797919831575)
    ·
      refine ⟨29104165435864196879747363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19402776957242797919831575 29104165435864196879747363)
      ·
        refine ⟨43656248153796295319621045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29104165435864196879747363 43656248153796295319621045)
        ·
          refine ⟨4092773264418402686214473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43656248153796295319621045 4092773264418402686214473)
          ·
            refine ⟨3069579948313802014660855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4092773264418402686214473 3069579948313802014660855)
            ·
              refine ⟨4604369922470703021991283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069579948313802014660855 4604369922470703021991283)
              ·
                refine ⟨6906554883706054532986925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4604369922470703021991283 6906554883706054532986925)
                ·
                  refine ⟨2589958081389770449870097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6906554883706054532986925 2589958081389770449870097)
                  ·
                    refine ⟨1942468561042327837402573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2589958081389770449870097 1942468561042327837402573)
                    ·
                      refine ⟨728425710390872939025965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1942468561042327837402573 728425710390872939025965)
                      ·
                        rfl

theorem cell23_1418604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_1418604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418604 prefixEnd_1418604 := by exact prefixLift 1418604
  have htrace : WordTrace (prefixWord ++ tailWord_1418604) baseStart_1418604 baseEnd_1418604 := by
    simpa [prefixWord, tailWord_1418604, baseEnd_1418604] using wordTrace_append hprefix tailTrace_1418604
  have hstable : (prefixWord ++ tailWord_1418604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418604).length < 2 ^ (prefixWord ++ tailWord_1418604).sum := by decide
  have hdescent : baseEnd_1418604 < baseStart_1418604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418617 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 3, 3, 3]
def baseStart_1418617 : Nat := 118140960795 + 1418617 * 2 ^ 59
def prefixEnd_1418617 : Nat := 4983230072969 + 3 ^ 40 * 1418617 * 2
def baseEnd_1418617 : Nat := 728432385639381388163405

theorem tailTrace_1418617 : CollatzResearch.WordTrace tailWord_1418617 prefixEnd_1418617 728432385639381388163405 := by
  unfold tailWord_1418617
  simp only [CollatzResearch.WordTrace]
  refine ⟨51741212701600364339774105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34494141801066909559849403 51741212701600364339774105)
  ·
    refine ⟨38805909526200273254830579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51741212701600364339774105 38805909526200273254830579)
    ·
      refine ⟨58208864289300409882245869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38805909526200273254830579 58208864289300409882245869)
      ·
        refine ⟨21828324108487653705842201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58208864289300409882245869 21828324108487653705842201)
        ·
          refine ⟨16371243081365740279381651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21828324108487653705842201 16371243081365740279381651)
          ·
            refine ⟨24556864622048610419072477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16371243081365740279381651 24556864622048610419072477)
            ·
              refine ⟨9208824233268228907152179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24556864622048610419072477 9208824233268228907152179)
              ·
                refine ⟨13813236349902343360728269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9208824233268228907152179 13813236349902343360728269)
                ·
                  refine ⟨5179963631213378760273101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13813236349902343360728269 5179963631213378760273101)
                  ·
                    refine ⟨1942486361705017035102413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5179963631213378760273101 1942486361705017035102413)
                    ·
                      refine ⟨728432385639381388163405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1942486361705017035102413 728432385639381388163405)
                      ·
                        rfl

theorem cell23_1418617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_1418617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418617 prefixEnd_1418617 := by exact prefixLift 1418617
  have htrace : WordTrace (prefixWord ++ tailWord_1418617) baseStart_1418617 baseEnd_1418617 := by
    simpa [prefixWord, tailWord_1418617, baseEnd_1418617] using wordTrace_append hprefix tailTrace_1418617
  have hstable : (prefixWord ++ tailWord_1418617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418617).length < 2 ^ (prefixWord ++ tailWord_1418617).sum := by decide
  have hdescent : baseEnd_1418617 < baseStart_1418617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418621 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 1, 2, 3]
def baseStart_1418621 : Nat := 118140960795 + 1418621 * 2 ^ 59
def prefixEnd_1418621 : Nat := 4983230072969 + 3 ^ 40 * 1418621 * 2
def baseEnd_1418621 : Nat := 728434439561999372513387

theorem tailTrace_1418621 : CollatzResearch.WordTrace tailWord_1418621 prefixEnd_1418621 728434439561999372513387 := by
  unfold tailWord_1418621
  simp only [CollatzResearch.WordTrace]
  refine ⟨51741358593585873022919717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34494239062390582015279811 51741358593585873022919717)
  ·
    refine ⟨9701504736297351191797447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51741358593585873022919717 9701504736297351191797447)
    ·
      refine ⟨14552257104446026787696171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9701504736297351191797447 14552257104446026787696171)
      ·
        refine ⟨21828385656669040181544257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14552257104446026787696171 21828385656669040181544257)
        ·
          refine ⟨16371289242501780136158193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21828385656669040181544257 16371289242501780136158193)
          ·
            refine ⟨12278466931876335102118645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16371289242501780136158193 12278466931876335102118645)
            ·
              refine ⟨1151106274863406415823623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12278466931876335102118645 1151106274863406415823623)
              ·
                refine ⟨1726659412295109623735435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151106274863406415823623 1726659412295109623735435)
                ·
                  refine ⟨2589989118442664435603153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726659412295109623735435 2589989118442664435603153)
                  ·
                    refine ⟨1942491838831998326702365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2589989118442664435603153 1942491838831998326702365)
                    ·
                      refine ⟨728434439561999372513387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1942491838831998326702365 728434439561999372513387)
                      ·
                        rfl

theorem cell23_1418621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_1418621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418621 prefixEnd_1418621 := by exact prefixLift 1418621
  have htrace : WordTrace (prefixWord ++ tailWord_1418621) baseStart_1418621 baseEnd_1418621 := by
    simpa [prefixWord, tailWord_1418621, baseEnd_1418621] using wordTrace_append hprefix tailTrace_1418621
  have hstable : (prefixWord ++ tailWord_1418621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418621).length < 2 ^ (prefixWord ++ tailWord_1418621).sum := by decide
  have hdescent : baseEnd_1418621 < baseStart_1418621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418674 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2]
def baseStart_1418674 : Nat := 118140960795 + 1418674 * 2 ^ 59
def prefixEnd_1418674 : Nat := 4983230072969 + 3 ^ 40 * 1418674 * 2
def baseEnd_1418674 : Nat := 728461654036687665150643

theorem tailTrace_1418674 : CollatzResearch.WordTrace tailWord_1418674 prefixEnd_1418674 728461654036687665150643 := by
  unfold tailWord_1418674
  simp only [CollatzResearch.WordTrace]
  refine ⟨12935822915598465768649769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34495527774929242049732717 12935822915598465768649769)
  ·
    refine ⟨9701867186698849326487327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12935822915598465768649769 9701867186698849326487327)
    ·
      refine ⟨14552800780048273989730991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9701867186698849326487327 14552800780048273989730991)
      ·
        refine ⟨21829201170072410984596487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14552800780048273989730991 21829201170072410984596487)
        ·
          refine ⟨32743801755108616476894731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21829201170072410984596487 32743801755108616476894731)
          ·
            refine ⟨49115702632662924715342097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32743801755108616476894731 49115702632662924715342097)
            ·
              refine ⟨36836776974497193536506573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49115702632662924715342097 36836776974497193536506573)
              ·
                refine ⟨13813791365436447576189965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36836776974497193536506573 13813791365436447576189965)
                ·
                  refine ⟨5180171762038667841071237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13813791365436447576189965 5180171762038667841071237)
                  ·
                    refine ⟨971282205382250220200857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5180171762038667841071237 971282205382250220200857)
                    ·
                      refine ⟨728461654036687665150643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 971282205382250220200857 728461654036687665150643)
                      ·
                        rfl

theorem cell23_1418674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_1418674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418674 prefixEnd_1418674 := by exact prefixLift 1418674
  have htrace : WordTrace (prefixWord ++ tailWord_1418674) baseStart_1418674 baseEnd_1418674 := by
    simpa [prefixWord, tailWord_1418674, baseEnd_1418674] using wordTrace_append hprefix tailTrace_1418674
  have hstable : (prefixWord ++ tailWord_1418674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418674).length < 2 ^ (prefixWord ++ tailWord_1418674).sum := by decide
  have hdescent : baseEnd_1418674 < baseStart_1418674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418744 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 2, 5]
def baseStart_1418744 : Nat := 118140960795 + 1418744 * 2 ^ 59
def prefixEnd_1418744 : Nat := 4983230072969 + 3 ^ 40 * 1418744 * 2
def baseEnd_1418744 : Nat := 242832532560834130425107

theorem tailTrace_1418744 : CollatzResearch.WordTrace tailWord_1418744 prefixEnd_1418744 242832532560834130425107 := by
  unfold tailWord_1418744
  simp only [CollatzResearch.WordTrace]
  refine ⟨25872922386070132514823643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34497229848093510019764857 25872922386070132514823643)
  ·
    refine ⟨38809383579105198772235465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25872922386070132514823643 38809383579105198772235465)
    ·
      refine ⟨29107037684328899079176599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38809383579105198772235465 29107037684328899079176599)
      ·
        refine ⟨43660556526493348618764899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29107037684328899079176599 43660556526493348618764899)
        ·
          refine ⟨65490834789740022928147349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43660556526493348618764899 65490834789740022928147349)
          ·
            refine ⟨3069882880769063574756907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65490834789740022928147349 3069882880769063574756907)
            ·
              refine ⟨4604824321153595362135361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069882880769063574756907 4604824321153595362135361)
              ·
                refine ⟨3453618240865196521601521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4604824321153595362135361 3453618240865196521601521)
                ·
                  refine ⟨2590213680648897391201141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3453618240865196521601521 2590213680648897391201141)
                  ·
                    refine ⟨242832532560834130425107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2590213680648897391201141 242832532560834130425107)
                    ·
                      rfl

theorem cell23_1418744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_1418744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418744 prefixEnd_1418744 := by exact prefixLift 1418744
  have htrace : WordTrace (prefixWord ++ tailWord_1418744) baseStart_1418744 baseEnd_1418744 := by
    simpa [prefixWord, tailWord_1418744, baseEnd_1418744] using wordTrace_append hprefix tailTrace_1418744
  have hstable : (prefixWord ++ tailWord_1418744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418744).length < 2 ^ (prefixWord ++ tailWord_1418744).sum := by decide
  have hdescent : baseEnd_1418744 < baseStart_1418744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418781 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_1418781 : Nat := 118140960795 + 1418781 * 2 ^ 59
def prefixEnd_1418781 : Nat := 4983230072969 + 3 ^ 40 * 1418781 * 2
def baseEnd_1418781 : Nat := 728516596466718746512651

theorem tailTrace_1418781 : CollatzResearch.WordTrace tailWord_1418781 prefixEnd_1418781 728516596466718746512651 := by
  unfold tailWord_1418781
  simp only [CollatzResearch.WordTrace]
  refine ⟨51747194273006220348744197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34498129515337480232496131 51747194273006220348744197)
  ·
    refine ⟨9702598926188666315389537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51747194273006220348744197 9702598926188666315389537)
    ·
      refine ⟨7276949194641499736542153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9702598926188666315389537 7276949194641499736542153)
      ·
        refine ⟨5457711895981124802406615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7276949194641499736542153 5457711895981124802406615)
        ·
          refine ⟨8186567843971687203609923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5457711895981124802406615 8186567843971687203609923)
          ·
            refine ⟨12279851765957530805414885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8186567843971687203609923 12279851765957530805414885)
            ·
              refine ⟨2302472206117037026015291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12279851765957530805414885 2302472206117037026015291)
              ·
                refine ⟨3453708309175555539022937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2302472206117037026015291 3453708309175555539022937)
                ·
                  refine ⟨2590281231881666654267203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3453708309175555539022937 2590281231881666654267203)
                  ·
                    refine ⟨3885421847822499981400805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2590281231881666654267203 3885421847822499981400805)
                    ·
                      refine ⟨728516596466718746512651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3885421847822499981400805 728516596466718746512651)
                      ·
                        rfl

theorem cell23_1418781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_1418781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418781 prefixEnd_1418781 := by exact prefixLift 1418781
  have htrace : WordTrace (prefixWord ++ tailWord_1418781) baseStart_1418781 baseEnd_1418781 := by
    simpa [prefixWord, tailWord_1418781, baseEnd_1418781] using wordTrace_append hprefix tailTrace_1418781
  have hstable : (prefixWord ++ tailWord_1418781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418781).length < 2 ^ (prefixWord ++ tailWord_1418781).sum := by decide
  have hdescent : baseEnd_1418781 < baseStart_1418781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418794 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1418794 : Nat := 118140960795 + 1418794 * 2 ^ 59
def prefixEnd_1418794 : Nat := 4983230072969 + 3 ^ 40 * 1418794 * 2
def baseEnd_1418794 : Nat := 728523271715227195650091

theorem tailTrace_1418794 : CollatzResearch.WordTrace tailWord_1418794 prefixEnd_1418794 728523271715227195650091 := by
  unfold tailWord_1418794
  simp only [CollatzResearch.WordTrace]
  refine ⟨12936917105489780892241859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34498445614639415712644957 12936917105489780892241859)
  ·
    refine ⟨19405375658234671338362789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12936917105489780892241859 19405375658234671338362789)
    ·
      refine ⟨3638507935919000875943023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19405375658234671338362789 3638507935919000875943023)
      ·
        refine ⟨5457761903878501313914535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3638507935919000875943023 5457761903878501313914535)
        ·
          refine ⟨8186642855817751970871803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5457761903878501313914535 8186642855817751970871803)
          ·
            refine ⟨12279964283726627956307705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8186642855817751970871803 12279964283726627956307705)
            ·
              refine ⟨9209973212794970967230779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12279964283726627956307705 9209973212794970967230779)
              ·
                refine ⟨13814959819192456450846169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9209973212794970967230779 13814959819192456450846169)
                ·
                  refine ⟨10361219864394342338134627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13814959819192456450846169 10361219864394342338134627)
                  ·
                    refine ⟨15541829796591513507201941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10361219864394342338134627 15541829796591513507201941)
                    ·
                      refine ⟨728523271715227195650091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15541829796591513507201941 728523271715227195650091)
                      ·
                        rfl

theorem cell23_1418794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1418794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418794 prefixEnd_1418794 := by exact prefixLift 1418794
  have htrace : WordTrace (prefixWord ++ tailWord_1418794) baseStart_1418794 baseEnd_1418794 := by
    simpa [prefixWord, tailWord_1418794, baseEnd_1418794] using wordTrace_append hprefix tailTrace_1418794
  have hstable : (prefixWord ++ tailWord_1418794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418794).length < 2 ^ (prefixWord ++ tailWord_1418794).sum := by decide
  have hdescent : baseEnd_1418794 < baseStart_1418794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418808 : List Nat := [2, 1, 2, 1, 4, 3, 1, 4, 1, 4]
def baseStart_1418808 : Nat := 118140960795 + 1418808 * 2 ^ 59
def prefixEnd_1418808 : Nat := 4983230072969 + 3 ^ 40 * 1418808 * 2
def baseEnd_1418808 : Nat := 242843486814796713625009

theorem tailTrace_1418808 : CollatzResearch.WordTrace tailWord_1418808 prefixEnd_1418808 242843486814796713625009 := by
  unfold tailWord_1418808
  simp only [CollatzResearch.WordTrace]
  refine ⟨25874089521954201979988539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34498786029272269306651385 25874089521954201979988539)
  ·
    refine ⟨38811134282931302969982809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25874089521954201979988539 38811134282931302969982809)
    ·
      refine ⟨29108350712198477227487107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38811134282931302969982809 29108350712198477227487107)
      ·
        refine ⟨43662526068297715841230661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29108350712198477227487107 43662526068297715841230661)
        ·
          refine ⟨8186723637805821720230749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43662526068297715841230661 8186723637805821720230749)
          ·
            refine ⟨3070021364177183145086531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8186723637805821720230749 3070021364177183145086531)
            ·
              refine ⟨4605032046265774717629797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070021364177183145086531 4605032046265774717629797)
              ·
                refine ⟨863443508674832759555587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4605032046265774717629797 863443508674832759555587)
                ·
                  refine ⟨1295165263012249139333381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863443508674832759555587 1295165263012249139333381)
                  ·
                    refine ⟨242843486814796713625009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1295165263012249139333381 242843486814796713625009)
                    ·
                      rfl

theorem cell23_1418808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_1418808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418808 prefixEnd_1418808 := by exact prefixLift 1418808
  have htrace : WordTrace (prefixWord ++ tailWord_1418808) baseStart_1418808 baseEnd_1418808 := by
    simpa [prefixWord, tailWord_1418808, baseEnd_1418808] using wordTrace_append hprefix tailTrace_1418808
  have hstable : (prefixWord ++ tailWord_1418808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418808).length < 2 ^ (prefixWord ++ tailWord_1418808).sum := by decide
  have hdescent : baseEnd_1418808 < baseStart_1418808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418827 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 7]
def baseStart_1418827 : Nat := 118140960795 + 1418827 * 2 ^ 59
def prefixEnd_1418827 : Nat := 4983230072969 + 3 ^ 40 * 1418827 * 2
def baseEnd_1418827 : Nat := 728540216576825566537439

theorem tailTrace_1418827 : CollatzResearch.WordTrace tailWord_1418827 prefixEnd_1418827 728540216576825566537439 := by
  unfold tailWord_1418827
  simp only [CollatzResearch.WordTrace]
  refine ⟨51748872030839570204918735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34499248020559713469945823 51748872030839570204918735)
  ·
    refine ⟨77623308046259355307378103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51748872030839570204918735 77623308046259355307378103)
    ·
      refine ⟨116434962069389032961067155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77623308046259355307378103 116434962069389032961067155)
      ·
        refine ⟨174652443104083549441600733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116434962069389032961067155 174652443104083549441600733)
        ·
          refine ⟨65494666164031331040600275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174652443104083549441600733 65494666164031331040600275)
          ·
            refine ⟨98241999246046996560900413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65494666164031331040600275 98241999246046996560900413)
            ·
              refine ⟨36840749717267623710337655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98241999246046996560900413 36840749717267623710337655)
              ·
                refine ⟨55261124575901435565506483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36840749717267623710337655 55261124575901435565506483)
                ·
                  refine ⟨82891686863852153348259725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55261124575901435565506483 82891686863852153348259725)
                  ·
                    refine ⟨31084382573944557505597397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82891686863852153348259725 31084382573944557505597397)
                    ·
                      refine ⟨728540216576825566537439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31084382573944557505597397 728540216576825566537439)
                      ·
                        rfl

theorem cell23_1418827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 7].length) (baseStart_1418827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418827 prefixEnd_1418827 := by exact prefixLift 1418827
  have htrace : WordTrace (prefixWord ++ tailWord_1418827) baseStart_1418827 baseEnd_1418827 := by
    simpa [prefixWord, tailWord_1418827, baseEnd_1418827] using wordTrace_append hprefix tailTrace_1418827
  have hstable : (prefixWord ++ tailWord_1418827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418827).length < 2 ^ (prefixWord ++ tailWord_1418827).sum := by decide
  have hdescent : baseEnd_1418827 < baseStart_1418827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418851 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 1, 5]
def baseStart_1418851 : Nat := 118140960795 + 1418851 * 2 ^ 59
def prefixEnd_1418851 : Nat := 4983230072969 + 3 ^ 40 * 1418851 * 2
def baseEnd_1418851 : Nat := 242850846704177824212443

theorem tailTrace_1418851 : CollatzResearch.WordTrace tailWord_1418851 prefixEnd_1418851 242850846704177824212443 := by
  unfold tailWord_1418851
  simp only [CollatzResearch.WordTrace]
  refine ⟨51749747382752622303792407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34499831588501748202528271 51749747382752622303792407)
  ·
    refine ⟨77624621074128933455688611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51749747382752622303792407 77624621074128933455688611)
    ·
      refine ⟨116436931611193400183532917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77624621074128933455688611 116436931611193400183532917)
      ·
        refine ⟨10915962338549381267206211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116436931611193400183532917 10915962338549381267206211)
        ·
          refine ⟨16373943507824071900809317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10915962338549381267206211 16373943507824071900809317)
          ·
            refine ⟨3070114407717013481401747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16373943507824071900809317 3070114407717013481401747)
            ·
              refine ⟨4605171611575520222102621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070114407717013481401747 4605171611575520222102621)
              ·
                refine ⟨1726939354340820083288483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4605171611575520222102621 1726939354340820083288483)
                ·
                  refine ⟨2590409031511230124932725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726939354340820083288483 2590409031511230124932725)
                  ·
                    refine ⟨242850846704177824212443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2590409031511230124932725 242850846704177824212443)
                    ·
                      rfl

theorem cell23_1418851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 5].length) (baseStart_1418851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418851 prefixEnd_1418851 := by exact prefixLift 1418851
  have htrace : WordTrace (prefixWord ++ tailWord_1418851) baseStart_1418851 baseEnd_1418851 := by
    simpa [prefixWord, tailWord_1418851, baseEnd_1418851] using wordTrace_append hprefix tailTrace_1418851
  have hstable : (prefixWord ++ tailWord_1418851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418851).length < 2 ^ (prefixWord ++ tailWord_1418851).sum := by decide
  have hdescent : baseEnd_1418851 < baseStart_1418851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418874 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3]
def baseStart_1418874 : Nat := 118140960795 + 1418874 * 2 ^ 59
def prefixEnd_1418874 : Nat := 4983230072969 + 3 ^ 40 * 1418874 * 2
def baseEnd_1418874 : Nat := 728564350167586882649723

theorem tailTrace_1418874 : CollatzResearch.WordTrace tailWord_1418874 prefixEnd_1418874 728564350167586882649723 := by
  unfold tailWord_1418874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12937646565417324307969919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34500390841112864821253117 12937646565417324307969919)
  ·
    refine ⟨19406469848125986461954879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12937646565417324307969919 19406469848125986461954879)
    ·
      refine ⟨29109704772188979692932319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19406469848125986461954879 29109704772188979692932319)
      ·
        refine ⟨43664557158283469539398479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29109704772188979692932319 43664557158283469539398479)
        ·
          refine ⟨65496835737425204309097719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43664557158283469539398479 65496835737425204309097719)
          ·
            refine ⟨98245253606137806463646579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65496835737425204309097719 98245253606137806463646579)
            ·
              refine ⟨147367880409206709695469869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98245253606137806463646579 147367880409206709695469869)
              ·
                refine ⟨55262955153452516135801201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147367880409206709695469869 55262955153452516135801201)
                ·
                  refine ⟨41447216365089387101850901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55262955153452516135801201 41447216365089387101850901)
                  ·
                    refine ⟨1942838267113565020399261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41447216365089387101850901 1942838267113565020399261)
                    ·
                      refine ⟨728564350167586882649723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1942838267113565020399261 728564350167586882649723)
                      ·
                        rfl

theorem cell23_1418874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_1418874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418874 prefixEnd_1418874 := by exact prefixLift 1418874
  have htrace : WordTrace (prefixWord ++ tailWord_1418874) baseStart_1418874 baseEnd_1418874 := by
    simpa [prefixWord, tailWord_1418874, baseEnd_1418874] using wordTrace_append hprefix tailTrace_1418874
  have hstable : (prefixWord ++ tailWord_1418874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418874).length < 2 ^ (prefixWord ++ tailWord_1418874).sum := by decide
  have hdescent : baseEnd_1418874 < baseStart_1418874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418881 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1418881 : Nat := 118140960795 + 1418881 * 2 ^ 59
def prefixEnd_1418881 : Nat := 4983230072969 + 3 ^ 40 * 1418881 * 2
def baseEnd_1418881 : Nat := 242855981510722785087397

theorem tailTrace_1418881 : CollatzResearch.WordTrace tailWord_1418881 prefixEnd_1418881 242855981510722785087397 := by
  unfold tailWord_1418881
  simp only [CollatzResearch.WordTrace]
  refine ⟨51750841572643937427384497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34500561048429291618256331 51750841572643937427384497)
  ·
    refine ⟨38813131179482953070538373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51750841572643937427384497 38813131179482953070538373)
    ·
      refine ⟨7277462096153053700725945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38813131179482953070538373 7277462096153053700725945)
      ·
        refine ⟨5458096572114790275544459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7277462096153053700725945 5458096572114790275544459)
        ·
          refine ⟨8187144858172185413316689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458096572114790275544459 8187144858172185413316689)
          ·
            refine ⟨6140358643629139059987517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8187144858172185413316689 6140358643629139059987517)
            ·
              refine ⟨2302634491360927147495319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6140358643629139059987517 2302634491360927147495319)
              ·
                refine ⟨3453951737041390721242979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2302634491360927147495319 3453951737041390721242979)
                ·
                  refine ⟨5180927605562086081864469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3453951737041390721242979 5180927605562086081864469)
                  ·
                    refine ⟨242855981510722785087397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5180927605562086081864469 242855981510722785087397)
                    ·
                      rfl

theorem cell23_1418881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1418881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418881 prefixEnd_1418881 := by exact prefixLift 1418881
  have htrace : WordTrace (prefixWord ++ tailWord_1418881) baseStart_1418881 baseEnd_1418881 := by
    simpa [prefixWord, tailWord_1418881, baseEnd_1418881] using wordTrace_append hprefix tailTrace_1418881
  have hstable : (prefixWord ++ tailWord_1418881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418881).length < 2 ^ (prefixWord ++ tailWord_1418881).sum := by decide
  have hdescent : baseEnd_1418881 < baseStart_1418881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418905 : List Nat := [1, 2, 1, 2, 1, 2, 2, 7, 1, 2, 2]
def baseStart_1418905 : Nat := 118140960795 + 1418905 * 2 ^ 59
def prefixEnd_1418905 : Nat := 4983230072969 + 3 ^ 40 * 1418905 * 2
def baseEnd_1418905 : Nat := 728580268067876261362081

theorem tailTrace_1418905 : CollatzResearch.WordTrace tailWord_1418905 prefixEnd_1418905 728580268067876261362081 := by
  unfold tailWord_1418905
  simp only [CollatzResearch.WordTrace]
  refine ⟨51751716924556989526258169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34501144616371326350838779 51751716924556989526258169)
  ·
    refine ⟨38813787693417742144693627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51751716924556989526258169 38813787693417742144693627)
    ·
      refine ⟨58220681540126613217040441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38813787693417742144693627 58220681540126613217040441)
      ·
        refine ⟨43665511155094959912780331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58220681540126613217040441 43665511155094959912780331)
        ·
          refine ⟨65498266732642439869170497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43665511155094959912780331 65498266732642439869170497)
          ·
            refine ⟨49123700049481829901877873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65498266732642439869170497 49123700049481829901877873)
            ·
              refine ⟨36842775037111372426408405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49123700049481829901877873 36842775037111372426408405)
              ·
                refine ⟨863502539932297791243947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36842775037111372426408405 863502539932297791243947)
                ·
                  refine ⟨1295253809898446686865921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863502539932297791243947 1295253809898446686865921)
                  ·
                    refine ⟨971440357423835015149441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1295253809898446686865921 971440357423835015149441)
                    ·
                      refine ⟨728580268067876261362081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 971440357423835015149441 728580268067876261362081)
                      ·
                        rfl

theorem cell23_1418905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 1, 2, 2].length) (baseStart_1418905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418905 prefixEnd_1418905 := by exact prefixLift 1418905
  have htrace : WordTrace (prefixWord ++ tailWord_1418905) baseStart_1418905 baseEnd_1418905 := by
    simpa [prefixWord, tailWord_1418905, baseEnd_1418905] using wordTrace_append hprefix tailTrace_1418905
  have hstable : (prefixWord ++ tailWord_1418905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418905).length < 2 ^ (prefixWord ++ tailWord_1418905).sum := by decide
  have hdescent : baseEnd_1418905 < baseStart_1418905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418908 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1418908 : Nat := 118140960795 + 1418908 * 2 ^ 59
def prefixEnd_1418908 : Nat := 4983230072969 + 3 ^ 40 * 1418908 * 2
def baseEnd_1418908 : Nat := 728581808509839749624567

theorem tailTrace_1418908 : CollatzResearch.WordTrace tailWord_1418908 prefixEnd_1418908 728581808509839749624567 := by
  unfold tailWord_1418908
  simp only [CollatzResearch.WordTrace]
  refine ⟨25875913171773060519308689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34501217562364080692411585 25875913171773060519308689)
  ·
    refine ⟨19406934878829795389481517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25875913171773060519308689 19406934878829795389481517)
    ·
      refine ⟨7277600579561173271055569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19406934878829795389481517 7277600579561173271055569)
      ·
        refine ⟨5458200434670879953291677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7277600579561173271055569 5458200434670879953291677)
        ·
          refine ⟨2046825163001579982484379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5458200434670879953291677 2046825163001579982484379)
          ·
            refine ⟨3070237744502369973726569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2046825163001579982484379 3070237744502369973726569)
            ·
              refine ⟨2302678308376777480294927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3070237744502369973726569 2302678308376777480294927)
              ·
                refine ⟨3454017462565166220442391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2302678308376777480294927 3454017462565166220442391)
                ·
                  refine ⟨5181026193847749330663587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3454017462565166220442391 5181026193847749330663587)
                  ·
                    refine ⟨7771539290771623995995381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5181026193847749330663587 7771539290771623995995381)
                    ·
                      refine ⟨728581808509839749624567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7771539290771623995995381 728581808509839749624567)
                      ·
                        rfl

theorem cell23_1418908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1418908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418908 prefixEnd_1418908 := by exact prefixLift 1418908
  have htrace : WordTrace (prefixWord ++ tailWord_1418908) baseStart_1418908 baseEnd_1418908 := by
    simpa [prefixWord, tailWord_1418908, baseEnd_1418908] using wordTrace_append hprefix tailTrace_1418908
  have hstable : (prefixWord ++ tailWord_1418908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418908).length < 2 ^ (prefixWord ++ tailWord_1418908).sum := by decide
  have hdescent : baseEnd_1418908 < baseStart_1418908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418921 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 8, 1, 3]
def baseStart_1418921 : Nat := 118140960795 + 1418921 * 2 ^ 59
def prefixEnd_1418921 : Nat := 4983230072969 + 3 ^ 40 * 1418921 * 2
def baseEnd_1418921 : Nat := 728588483758348198762007

theorem tailTrace_1418921 : CollatzResearch.WordTrace tailWord_1418921 prefixEnd_1418921 728588483758348198762007 := by
  unfold tailWord_1418921
  simp only [CollatzResearch.WordTrace]
  refine ⟨51752300492499024258840617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34501533661666016172560411 51752300492499024258840617)
  ·
    refine ⟨38814225369374268194130463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51752300492499024258840617 38814225369374268194130463)
    ·
      refine ⟨58221338054061402291195695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38814225369374268194130463 58221338054061402291195695)
      ·
        refine ⟨87332007081092103436793543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58221338054061402291195695 87332007081092103436793543)
        ·
          refine ⟨130998010621638155155190315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87332007081092103436793543 130998010621638155155190315)
          ·
            refine ⟨196497015932457232732785473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130998010621638155155190315 196497015932457232732785473)
            ·
              refine ⟨147372761949342924549589105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196497015932457232732785473 147372761949342924549589105)
              ·
                refine ⟨110529571462007193412191829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147372761949342924549589105 110529571462007193412191829)
                ·
                  refine ⟨1295268415570396797799123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 110529571462007193412191829 1295268415570396797799123)
                  ·
                    refine ⟨1942902623355595196698685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1295268415570396797799123 1942902623355595196698685)
                    ·
                      refine ⟨728588483758348198762007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1942902623355595196698685 728588483758348198762007)
                      ·
                        rfl

theorem cell23_1418921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 1, 3].length) (baseStart_1418921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418921 prefixEnd_1418921 := by exact prefixLift 1418921
  have htrace : WordTrace (prefixWord ++ tailWord_1418921) baseStart_1418921 baseEnd_1418921 := by
    simpa [prefixWord, tailWord_1418921, baseEnd_1418921] using wordTrace_append hprefix tailTrace_1418921
  have hstable : (prefixWord ++ tailWord_1418921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418921).length < 2 ^ (prefixWord ++ tailWord_1418921).sum := by decide
  have hdescent : baseEnd_1418921 < baseStart_1418921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418973 : List Nat := [1, 4, 3, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_1418973 : Nat := 118140960795 + 1418973 * 2 ^ 59
def prefixEnd_1418973 : Nat := 4983230072969 + 3 ^ 40 * 1418973 * 2
def baseEnd_1418973 : Nat := 728615184752381995311769

theorem tailTrace_1418973 : CollatzResearch.WordTrace tailWord_1418973 prefixEnd_1418973 728615184752381995311769 := by
  unfold tailWord_1418973
  simp only [CollatzResearch.WordTrace]
  refine ⟨51754197088310637139733573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34502798058873758093155715 51754197088310637139733573)
  ·
    refine ⟨9703911954058244463700045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51754197088310637139733573 9703911954058244463700045)
    ·
      refine ⟨3638966982771841673887517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9703911954058244463700045 3638966982771841673887517)
      ·
        refine ⟨1364612618539440627707819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3638966982771841673887517 1364612618539440627707819)
        ·
          refine ⟨2046918927809160941561729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1364612618539440627707819 2046918927809160941561729)
          ·
            refine ⟨1535189195856870706171297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2046918927809160941561729 1535189195856870706171297)
            ·
              refine ⟨1151391896892653029628473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535189195856870706171297 1151391896892653029628473)
              ·
                refine ⟨863543922669489772221355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151391896892653029628473 863543922669489772221355)
                ·
                  refine ⟨1295315884004234658332033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863543922669489772221355 1295315884004234658332033)
                  ·
                    refine ⟨971486913003175993749025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1295315884004234658332033 971486913003175993749025)
                    ·
                      refine ⟨728615184752381995311769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 971486913003175993749025 728615184752381995311769)
                      ·
                        rfl

theorem cell23_1418973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_1418973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418973 prefixEnd_1418973 := by exact prefixLift 1418973
  have htrace : WordTrace (prefixWord ++ tailWord_1418973) baseStart_1418973 baseEnd_1418973 := by
    simpa [prefixWord, tailWord_1418973, baseEnd_1418973] using wordTrace_append hprefix tailTrace_1418973
  have hstable : (prefixWord ++ tailWord_1418973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418973).length < 2 ^ (prefixWord ++ tailWord_1418973).sum := by decide
  have hdescent : baseEnd_1418973 < baseStart_1418973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418981 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1418981 : Nat := 118140960795 + 1418981 * 2 ^ 59
def prefixEnd_1418981 : Nat := 4983230072969 + 3 ^ 40 * 1418981 * 2
def baseEnd_1418981 : Nat := 728619292597617964011731

theorem tailTrace_1418981 : CollatzResearch.WordTrace tailWord_1418981 prefixEnd_1418981 728619292597617964011731 := by
  unfold tailWord_1418981
  simp only [CollatzResearch.WordTrace]
  refine ⟨51754488872281654506024797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34502992581521103004016531 51754488872281654506024797)
  ·
    refine ⟨19407933327105620439759299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51754488872281654506024797 19407933327105620439759299)
    ·
      refine ⟨29111899990658430659638949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19407933327105620439759299 29111899990658430659638949)
      ·
        refine ⟨5458481248248455748682303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29111899990658430659638949 5458481248248455748682303)
        ·
          refine ⟨8187721872372683623023455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5458481248248455748682303 8187721872372683623023455)
          ·
            refine ⟨12281582808559025434535183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8187721872372683623023455 12281582808559025434535183)
            ·
              refine ⟨18422374212838538151802775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12281582808559025434535183 18422374212838538151802775)
              ·
                refine ⟨27633561319257807227704163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18422374212838538151802775 27633561319257807227704163)
                ·
                  refine ⟨41450341978886710841556245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27633561319257807227704163 41450341978886710841556245)
                  ·
                    refine ⟨1942984780260314570697949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41450341978886710841556245 1942984780260314570697949)
                    ·
                      refine ⟨728619292597617964011731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1942984780260314570697949 728619292597617964011731)
                      ·
                        rfl

theorem cell23_1418981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1418981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418981 prefixEnd_1418981 := by exact prefixLift 1418981
  have htrace : WordTrace (prefixWord ++ tailWord_1418981) baseStart_1418981 baseEnd_1418981 := by
    simpa [prefixWord, tailWord_1418981, baseEnd_1418981] using wordTrace_append hprefix tailTrace_1418981
  have hstable : (prefixWord ++ tailWord_1418981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418981).length < 2 ^ (prefixWord ++ tailWord_1418981).sum := by decide
  have hdescent : baseEnd_1418981 < baseStart_1418981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418991 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 4]
def baseStart_1418991 : Nat := 118140960795 + 1418991 * 2 ^ 59
def prefixEnd_1418991 : Nat := 4983230072969 + 3 ^ 40 * 1418991 * 2
def baseEnd_1418991 : Nat := 728624427404162924886685

theorem tailTrace_1418991 : CollatzResearch.WordTrace tailWord_1418991 prefixEnd_1418991 728624427404162924886685 := by
  unfold tailWord_1418991
  simp only [CollatzResearch.WordTrace]
  refine ⟨51754853602245426213888827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34503235734830284142592551 51754853602245426213888827)
  ·
    refine ⟨77632280403368139320833241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51754853602245426213888827 77632280403368139320833241)
    ·
      refine ⟨58224210302526104490624931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77632280403368139320833241 58224210302526104490624931)
      ·
        refine ⟨87336315453789156735937397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58224210302526104490624931 87336315453789156735937397)
        ·
          refine ⟨8187779573792733443994131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87336315453789156735937397 8187779573792733443994131)
          ·
            refine ⟨12281669360689100165991197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8187779573792733443994131 12281669360689100165991197)
            ·
              refine ⟨4605626010258412562246699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12281669360689100165991197 4605626010258412562246699)
              ·
                refine ⟨6908439015387618843370049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4605626010258412562246699 6908439015387618843370049)
                ·
                  refine ⟨5181329261540714132527537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6908439015387618843370049 5181329261540714132527537)
                  ·
                    refine ⟨3885996946155535599395653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5181329261540714132527537 3885996946155535599395653)
                    ·
                      refine ⟨728624427404162924886685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3885996946155535599395653 728624427404162924886685)
                      ·
                        rfl

theorem cell23_1418991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_1418991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418991 prefixEnd_1418991 := by exact prefixLift 1418991
  have htrace : WordTrace (prefixWord ++ tailWord_1418991) baseStart_1418991 baseEnd_1418991 := by
    simpa [prefixWord, tailWord_1418991, baseEnd_1418991] using wordTrace_append hprefix tailTrace_1418991
  have hstable : (prefixWord ++ tailWord_1418991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418991).length < 2 ^ (prefixWord ++ tailWord_1418991).sum := by decide
  have hdescent : baseEnd_1418991 < baseStart_1418991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1418995 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 2, 2, 2]
def baseStart_1418995 : Nat := 118140960795 + 1418995 * 2 ^ 59
def prefixEnd_1418995 : Nat := 4983230072969 + 3 ^ 40 * 1418995 * 2
def baseEnd_1418995 : Nat := 728626481326780909236667

theorem tailTrace_1418995 : CollatzResearch.WordTrace tailWord_1418995 prefixEnd_1418995 728626481326780909236667 := by
  unfold tailWord_1418995
  simp only [CollatzResearch.WordTrace]
  refine ⟨51754999494230934897034439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34503332996153956598022959 51754999494230934897034439)
  ·
    refine ⟨77632499241346402345551659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51754999494230934897034439 77632499241346402345551659)
    ·
      refine ⟨116448748862019603518327489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77632499241346402345551659 116448748862019603518327489)
      ·
        refine ⟨87336561646514702638745617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116448748862019603518327489 87336561646514702638745617)
        ·
          refine ⟨65502421234886026979059213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87336561646514702638745617 65502421234886026979059213)
          ·
            refine ⟨24563407963082260117147205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65502421234886026979059213 24563407963082260117147205)
            ·
              refine ⟨4605638993077923771965101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24563407963082260117147205 4605638993077923771965101)
              ·
                refine ⟨1727114622404221414486913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4605638993077923771965101 1727114622404221414486913)
                ·
                  refine ⟨1295335966803166060865185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1727114622404221414486913 1295335966803166060865185)
                  ·
                    refine ⟨971501975102374545648889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1295335966803166060865185 971501975102374545648889)
                    ·
                      refine ⟨728626481326780909236667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 971501975102374545648889 728626481326780909236667)
                      ·
                        rfl

theorem cell23_1418995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 2, 2].length) (baseStart_1418995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1418995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1418995 prefixEnd_1418995 := by exact prefixLift 1418995
  have htrace : WordTrace (prefixWord ++ tailWord_1418995) baseStart_1418995 baseEnd_1418995 := by
    simpa [prefixWord, tailWord_1418995, baseEnd_1418995] using wordTrace_append hprefix tailTrace_1418995
  have hstable : (prefixWord ++ tailWord_1418995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1418995).length < 2 ^ (prefixWord ++ tailWord_1418995).sum := by decide
  have hdescent : baseEnd_1418995 < baseStart_1418995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1418995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419018 : List Nat := [3, 1, 2, 2, 1, 3, 1, 5, 5]
def baseStart_1419018 : Nat := 118140960795 + 1419018 * 2 ^ 59
def prefixEnd_1419018 : Nat := 4983230072969 + 3 ^ 40 * 1419018 * 2
def baseEnd_1419018 : Nat := 80959810153537146583229

theorem tailTrace_1419018 : CollatzResearch.WordTrace tailWord_1419018 prefixEnd_1419018 80959810153537146583229 := by
  unfold tailWord_1419018
  simp only [CollatzResearch.WordTrace]
  refine ⟨12938959593286902456280427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34503892248765073216747805 12938959593286902456280427)
  ·
    refine ⟨19408439389930353684420641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12938959593286902456280427 19408439389930353684420641)
    ·
      refine ⟨14556329542447765263315481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19408439389930353684420641 14556329542447765263315481)
      ·
        refine ⟨10917247156835823947486611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14556329542447765263315481 10917247156835823947486611)
        ·
          refine ⟨16375870735253735921229917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10917247156835823947486611 16375870735253735921229917)
          ·
            refine ⟨6140951525720150970461219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16375870735253735921229917 6140951525720150970461219)
            ·
              refine ⟨9211427288580226455691829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6140951525720150970461219 9211427288580226455691829)
              ·
                refine ⟨863571308304396230221109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9211427288580226455691829 863571308304396230221109)
                ·
                  refine ⟨80959810153537146583229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 863571308304396230221109 80959810153537146583229)
                  ·
                    rfl

theorem cell23_1419018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_1419018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419018 prefixEnd_1419018 := by exact prefixLift 1419018
  have htrace : WordTrace (prefixWord ++ tailWord_1419018) baseStart_1419018 baseEnd_1419018 := by
    simpa [prefixWord, tailWord_1419018, baseEnd_1419018] using wordTrace_append hprefix tailTrace_1419018
  have hstable : (prefixWord ++ tailWord_1419018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419018).length < 2 ^ (prefixWord ++ tailWord_1419018).sum := by decide
  have hdescent : baseEnd_1419018 < baseStart_1419018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419068 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 1, 6, 2]
def baseStart_1419068 : Nat := 118140960795 + 1419068 * 2 ^ 59
def prefixEnd_1419068 : Nat := 4983230072969 + 3 ^ 40 * 1419068 * 2
def baseEnd_1419068 : Nat := 728663965414559123623831

theorem tailTrace_1419068 : CollatzResearch.WordTrace tailWord_1419068 prefixEnd_1419068 728663965414559123623831 := by
  unfold tailWord_1419068
  simp only [CollatzResearch.WordTrace]
  refine ⟨25878831011483234182220929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34505108015310978909627905 25878831011483234182220929)
  ·
    refine ⟨19409123258612425636665697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25878831011483234182220929 19409123258612425636665697)
    ·
      refine ⟨14556842443959319227499273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19409123258612425636665697 14556842443959319227499273)
      ·
        refine ⟨10917631832969489420624455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14556842443959319227499273 10917631832969489420624455)
        ·
          refine ⟨16376447749454234130936683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10917631832969489420624455 16376447749454234130936683)
          ·
            refine ⟨24564671624181351196405025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16376447749454234130936683 24564671624181351196405025)
            ·
              refine ⟨18423503718136013397303769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24564671624181351196405025 18423503718136013397303769)
              ·
                refine ⟨13817627788602010047977827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18423503718136013397303769 13817627788602010047977827)
                ·
                  refine ⟨20726441682903015071966741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13817627788602010047977827 20726441682903015071966741)
                  ·
                    refine ⟨971551953886078831498441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20726441682903015071966741 971551953886078831498441)
                    ·
                      refine ⟨728663965414559123623831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 971551953886078831498441 728663965414559123623831)
                      ·
                        rfl

theorem cell23_1419068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_1419068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419068 prefixEnd_1419068 := by exact prefixLift 1419068
  have htrace : WordTrace (prefixWord ++ tailWord_1419068) baseStart_1419068 baseEnd_1419068 := by
    simpa [prefixWord, tailWord_1419068, baseEnd_1419068] using wordTrace_append hprefix tailTrace_1419068
  have hstable : (prefixWord ++ tailWord_1419068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419068).length < 2 ^ (prefixWord ++ tailWord_1419068).sum := by decide
  have hdescent : baseEnd_1419068 < baseStart_1419068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419085 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_1419085 : Nat := 118140960795 + 1419085 * 2 ^ 59
def prefixEnd_1419085 : Nat := 4983230072969 + 3 ^ 40 * 1419085 * 2
def baseEnd_1419085 : Nat := 728672694585685557111253

theorem tailTrace_1419085 : CollatzResearch.WordTrace tailWord_1419085 prefixEnd_1419085 728672694585685557111253 := by
  unfold tailWord_1419085
  simp only [CollatzResearch.WordTrace]
  refine ⟨51758282063904880267810709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34505521375936586845207139 51758282063904880267810709)
  ·
    refine ⟨2426169471745541262553627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51758282063904880267810709 2426169471745541262553627)
    ·
      refine ⟨3639254207618311893830441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2426169471745541262553627 3639254207618311893830441)
      ·
        refine ⟨2729440655713733920372831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3639254207618311893830441 2729440655713733920372831)
        ·
          refine ⟨4094160983570600880559247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2729440655713733920372831 4094160983570600880559247)
          ·
            refine ⟨6141241475355901320838871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094160983570600880559247 6141241475355901320838871)
            ·
              refine ⟨9211862213033851981258307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6141241475355901320838871 9211862213033851981258307)
              ·
                refine ⟨13817793319550777971887461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9211862213033851981258307 13817793319550777971887461)
                ·
                  refine ⟨2590836247415770869728899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13817793319550777971887461 2590836247415770869728899)
                  ·
                    refine ⟨3886254371123656304593349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2590836247415770869728899 3886254371123656304593349)
                    ·
                      refine ⟨728672694585685557111253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3886254371123656304593349 728672694585685557111253)
                      ·
                        rfl

theorem cell23_1419085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_1419085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419085 prefixEnd_1419085 := by exact prefixLift 1419085
  have htrace : WordTrace (prefixWord ++ tailWord_1419085) baseStart_1419085 baseEnd_1419085 := by
    simpa [prefixWord, tailWord_1419085, baseEnd_1419085] using wordTrace_append hprefix tailTrace_1419085
  have hstable : (prefixWord ++ tailWord_1419085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419085).length < 2 ^ (prefixWord ++ tailWord_1419085).sum := by decide
  have hdescent : baseEnd_1419085 < baseStart_1419085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419128 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 5, 5, 2]
def baseStart_1419128 : Nat := 118140960795 + 1419128 * 2 ^ 59
def prefixEnd_1419128 : Nat := 4983230072969 + 3 ^ 40 * 1419128 * 2
def baseEnd_1419128 : Nat := 728694774253828888873555

theorem tailTrace_1419128 : CollatzResearch.WordTrace tailWord_1419128 prefixEnd_1419128 728694774253828888873555 := by
  unfold tailWord_1419128
  simp only [CollatzResearch.WordTrace]
  refine ⟨25879925201374549305813019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34506566935166065741084025 25879925201374549305813019)
  ·
    refine ⟨38819887802061823958719529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25879925201374549305813019 38819887802061823958719529)
    ·
      refine ⟨29114915851546367969039647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38819887802061823958719529 29114915851546367969039647)
      ·
        refine ⟨43672373777319551953559471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29114915851546367969039647 43672373777319551953559471)
        ·
          refine ⟨65508560665979327930339207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43672373777319551953559471 65508560665979327930339207)
          ·
            refine ⟨98262840998968991895508811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65508560665979327930339207 98262840998968991895508811)
            ·
              refine ⟨147394261498453487843263217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98262840998968991895508811 147394261498453487843263217)
              ·
                refine ⟨110545696123840115882447413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147394261498453487843263217 110545696123840115882447413)
                ·
                  refine ⟨10363659011610010863979445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110545696123840115882447413 10363659011610010863979445)
                  ·
                    refine ⟨971593032338438518498073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10363659011610010863979445 971593032338438518498073)
                    ·
                      refine ⟨728694774253828888873555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 971593032338438518498073 728694774253828888873555)
                      ·
                        rfl

theorem cell23_1419128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5, 5, 2].length) (baseStart_1419128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419128 prefixEnd_1419128 := by exact prefixLift 1419128
  have htrace : WordTrace (prefixWord ++ tailWord_1419128) baseStart_1419128 baseEnd_1419128 := by
    simpa [prefixWord, tailWord_1419128, baseEnd_1419128] using wordTrace_append hprefix tailTrace_1419128
  have hstable : (prefixWord ++ tailWord_1419128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419128).length < 2 ^ (prefixWord ++ tailWord_1419128).sum := by decide
  have hdescent : baseEnd_1419128 < baseStart_1419128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419145 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 2, 3, 2]
def baseStart_1419145 : Nat := 118140960795 + 1419145 * 2 ^ 59
def prefixEnd_1419145 : Nat := 4983230072969 + 3 ^ 40 * 1419145 * 2
def baseEnd_1419145 : Nat := 728703503424955322360977

theorem tailTrace_1419145 : CollatzResearch.WordTrace tailWord_1419145 prefixEnd_1419145 728703503424955322360977 := by
  unfold tailWord_1419145
  simp only [CollatzResearch.WordTrace]
  refine ⟨51760470443687510514994889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34506980295791673676663259 51760470443687510514994889)
  ·
    refine ⟨38820352832765632886246167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51760470443687510514994889 38820352832765632886246167)
    ·
      refine ⟨58230529249148449329369251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38820352832765632886246167 58230529249148449329369251)
      ·
        refine ⟨87345793873722673994053877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58230529249148449329369251 87345793873722673994053877)
        ·
          refine ⟨8188668175661500686942551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87345793873722673994053877 8188668175661500686942551)
          ·
            refine ⟨12283002263492251030413827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8188668175661500686942551 12283002263492251030413827)
            ·
              refine ⟨18424503395238376545620741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12283002263492251030413827 18424503395238376545620741)
              ·
                refine ⟨3454594386607195602303889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18424503395238376545620741 3454594386607195602303889)
                ·
                  refine ⟨2590945789955396701727917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3454594386607195602303889 2590945789955396701727917)
                  ·
                    refine ⟨971604671233273763147969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2590945789955396701727917 971604671233273763147969)
                    ·
                      refine ⟨728703503424955322360977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 971604671233273763147969 728703503424955322360977)
                      ·
                        rfl

theorem cell23_1419145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 3, 2].length) (baseStart_1419145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419145 prefixEnd_1419145 := by exact prefixLift 1419145
  have htrace : WordTrace (prefixWord ++ tailWord_1419145) baseStart_1419145 baseEnd_1419145 := by
    simpa [prefixWord, tailWord_1419145, baseEnd_1419145] using wordTrace_append hprefix tailTrace_1419145
  have hstable : (prefixWord ++ tailWord_1419145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419145).length < 2 ^ (prefixWord ++ tailWord_1419145).sum := by decide
  have hdescent : baseEnd_1419145 < baseStart_1419145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419146 : List Nat := [3, 1, 2, 4, 2, 2, 2, 2, 1, 4]
def baseStart_1419146 : Nat := 118140960795 + 1419146 * 2 ^ 59
def prefixEnd_1419146 : Nat := 4983230072969 + 3 ^ 40 * 1419146 * 2
def baseEnd_1419146 : Nat := 242901338968536606149491

theorem tailTrace_1419146 : CollatzResearch.WordTrace tailWord_1419146 prefixEnd_1419146 242901338968536606149491 := by
  unfold tailWord_1419146
  simp only [CollatzResearch.WordTrace]
  refine ⟨12940126729170971921445323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34507004611122591790520861 12940126729170971921445323)
  ·
    refine ⟨19410190093756457882167985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12940126729170971921445323 19410190093756457882167985)
    ·
      refine ⟨14557642570317343411625989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19410190093756457882167985 14557642570317343411625989)
      ·
        refine ⟨2729557981934501889679873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14557642570317343411625989 2729557981934501889679873)
        ·
          refine ⟨2047168486450876417259905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2729557981934501889679873 2047168486450876417259905)
          ·
            refine ⟨1535376364838157312944929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2047168486450876417259905 1535376364838157312944929)
            ·
              refine ⟨1151532273628617984708697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535376364838157312944929 1151532273628617984708697)
              ·
                refine ⟨863649205221463488531523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151532273628617984708697 863649205221463488531523)
                ·
                  refine ⟨1295473807832195232797285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863649205221463488531523 1295473807832195232797285)
                  ·
                    refine ⟨242901338968536606149491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1295473807832195232797285 242901338968536606149491)
                    ·
                      rfl

theorem cell23_1419146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_1419146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419146 prefixEnd_1419146 := by exact prefixLift 1419146
  have htrace : WordTrace (prefixWord ++ tailWord_1419146) baseStart_1419146 baseEnd_1419146 := by
    simpa [prefixWord, tailWord_1419146, baseEnd_1419146] using wordTrace_append hprefix tailTrace_1419146
  have hstable : (prefixWord ++ tailWord_1419146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419146).length < 2 ^ (prefixWord ++ tailWord_1419146).sum := by decide
  have hdescent : baseEnd_1419146 < baseStart_1419146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419168 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 6, 4]
def baseStart_1419168 : Nat := 118140960795 + 1419168 * 2 ^ 59
def prefixEnd_1419168 : Nat := 4983230072969 + 3 ^ 40 * 1419168 * 2
def baseEnd_1419168 : Nat := 242905104493336244124457

theorem tailTrace_1419168 : CollatzResearch.WordTrace tailWord_1419168 prefixEnd_1419168 242905104493336244124457 := by
  unfold tailWord_1419168
  simp only [CollatzResearch.WordTrace]
  refine ⟨25880654661302092721541079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34507539548402790295388105 25880654661302092721541079)
  ·
    refine ⟨38820981991953139082311619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25880654661302092721541079 38820981991953139082311619)
    ·
      refine ⟨58231472987929708623467429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38820981991953139082311619 58231472987929708623467429)
      ·
        refine ⟨10918401185236820366900143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58231472987929708623467429 10918401185236820366900143)
        ·
          refine ⟨16377601777855230550350215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10918401185236820366900143 16377601777855230550350215)
          ·
            refine ⟨24566402666782845825525323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16377601777855230550350215 24566402666782845825525323)
            ·
              refine ⟨36849604000174268738287985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24566402666782845825525323 36849604000174268738287985)
              ·
                refine ⟨27637203000130701553715989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36849604000174268738287985 27637203000130701553715989)
                ·
                  refine ⟨1295493890631126635330437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27637203000130701553715989 1295493890631126635330437)
                  ·
                    refine ⟨242905104493336244124457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1295493890631126635330437 242905104493336244124457)
                    ·
                      rfl

theorem cell23_1419168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6, 4].length) (baseStart_1419168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419168 prefixEnd_1419168 := by exact prefixLift 1419168
  have htrace : WordTrace (prefixWord ++ tailWord_1419168) baseStart_1419168 baseEnd_1419168 := by
    simpa [prefixWord, tailWord_1419168, baseEnd_1419168] using wordTrace_append hprefix tailTrace_1419168
  have hstable : (prefixWord ++ tailWord_1419168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419168).length < 2 ^ (prefixWord ++ tailWord_1419168).sum := by decide
  have hdescent : baseEnd_1419168 < baseStart_1419168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419175 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1419175 : Nat := 118140960795 + 1419175 * 2 ^ 59
def prefixEnd_1419175 : Nat := 4983230072969 + 3 ^ 40 * 1419175 * 2
def baseEnd_1419175 : Nat := 728718907844590204985839

theorem tailTrace_1419175 : CollatzResearch.WordTrace tailWord_1419175 prefixEnd_1419175 728718907844590204985839 := by
  unfold tailWord_1419175
  simp only [CollatzResearch.WordTrace]
  refine ⟨51761564633578825638586979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34507709755719217092391319 51761564633578825638586979)
  ·
    refine ⟨77642346950368238457880469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51761564633578825638586979 77642346950368238457880469)
    ·
      refine ⟨3639485013298511177713147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 77642346950368238457880469 3639485013298511177713147)
      ·
        refine ⟨5459227519947766766569721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3639485013298511177713147 5459227519947766766569721)
        ·
          refine ⟨4094420639960825074927291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5459227519947766766569721 4094420639960825074927291)
          ·
            refine ⟨6141630959941237612390937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094420639960825074927291 6141630959941237612390937)
            ·
              refine ⟨4606223219955928209293203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6141630959941237612390937 4606223219955928209293203)
              ·
                refine ⟨6909334829933892313939805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4606223219955928209293203 6909334829933892313939805)
                ·
                  refine ⟨2591000561225209617727427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6909334829933892313939805 2591000561225209617727427)
                  ·
                    refine ⟨3886500841837814426591141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2591000561225209617727427 3886500841837814426591141)
                    ·
                      refine ⟨728718907844590204985839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3886500841837814426591141 728718907844590204985839)
                      ·
                        rfl

theorem cell23_1419175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1419175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419175 prefixEnd_1419175 := by exact prefixLift 1419175
  have htrace : WordTrace (prefixWord ++ tailWord_1419175) baseStart_1419175 baseEnd_1419175 := by
    simpa [prefixWord, tailWord_1419175, baseEnd_1419175] using wordTrace_append hprefix tailTrace_1419175
  have hstable : (prefixWord ++ tailWord_1419175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419175).length < 2 ^ (prefixWord ++ tailWord_1419175).sum := by decide
  have hdescent : baseEnd_1419175 < baseStart_1419175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419198 : List Nat := [4, 2, 1, 1, 1, 4, 10]
def baseStart_1419198 : Nat := 118140960795 + 1419198 * 2 ^ 59
def prefixEnd_1419198 : Nat := 4983230072969 + 3 ^ 40 * 1419198 * 2
def baseEnd_1419198 : Nat := 8996675529625229814793

theorem tailTrace_1419198 : CollatzResearch.WordTrace tailWord_1419198 prefixEnd_1419198 8996675529625229814793 := by
  unfold tailWord_1419198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6470300439061937570834281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34508269008330333711116165 6470300439061937570834281)
  ·
    refine ⟨4852725329296453178125711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6470300439061937570834281 4852725329296453178125711)
    ·
      refine ⟨7279087993944679767188567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4852725329296453178125711 7279087993944679767188567)
      ·
        refine ⟨10918631990917019650782851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7279087993944679767188567 10918631990917019650782851)
        ·
          refine ⟨16377947986375529476174277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10918631990917019650782851 16377947986375529476174277)
          ·
            refine ⟨3070865247445411776782677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16377947986375529476174277 3070865247445411776782677)
            ·
              refine ⟨8996675529625229814793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3070865247445411776782677 8996675529625229814793)
              ·
                rfl

theorem cell23_1419198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 10].length) (baseStart_1419198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419198 prefixEnd_1419198 := by exact prefixLift 1419198
  have htrace : WordTrace (prefixWord ++ tailWord_1419198) baseStart_1419198 baseEnd_1419198 := by
    simpa [prefixWord, tailWord_1419198, baseEnd_1419198] using wordTrace_append hprefix tailTrace_1419198
  have hstable : (prefixWord ++ tailWord_1419198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419198).length < 2 ^ (prefixWord ++ tailWord_1419198).sum := by decide
  have hdescent : baseEnd_1419198 < baseStart_1419198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419222 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1419222 : Nat := 118140960795 + 1419222 * 2 ^ 59
def prefixEnd_1419222 : Nat := 4983230072969 + 3 ^ 40 * 1419222 * 2
def baseEnd_1419222 : Nat := 728743041435351521098123

theorem tailTrace_1419222 : CollatzResearch.WordTrace tailWord_1419222 prefixEnd_1419222 728743041435351521098123 := by
  unfold tailWord_1419222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3235204929025534541596745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34508852576272368443698613 3235204929025534541596745)
  ·
    refine ⟨2426403696769150906197559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3235204929025534541596745 2426403696769150906197559)
    ·
      refine ⟨3639605545153726359296339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2426403696769150906197559 3639605545153726359296339)
      ·
        refine ⟨5459408317730589538944509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3639605545153726359296339 5459408317730589538944509)
        ·
          refine ⟨2047278119148971077104191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5459408317730589538944509 2047278119148971077104191)
          ·
            refine ⟨3070917178723456615656287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047278119148971077104191 3070917178723456615656287)
            ·
              refine ⟨4606375768085184923484431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070917178723456615656287 4606375768085184923484431)
              ·
                refine ⟨6909563652127777385226647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4606375768085184923484431 6909563652127777385226647)
                ·
                  refine ⟨10364345478191666077839971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6909563652127777385226647 10364345478191666077839971)
                  ·
                    refine ⟨15546518217287499116759957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10364345478191666077839971 15546518217287499116759957)
                    ·
                      refine ⟨728743041435351521098123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15546518217287499116759957 728743041435351521098123)
                      ·
                        rfl

theorem cell23_1419222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1419222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419222 prefixEnd_1419222 := by exact prefixLift 1419222
  have htrace : WordTrace (prefixWord ++ tailWord_1419222) baseStart_1419222 baseEnd_1419222 := by
    simpa [prefixWord, tailWord_1419222, baseEnd_1419222] using wordTrace_append hprefix tailTrace_1419222
  have hstable : (prefixWord ++ tailWord_1419222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419222).length < 2 ^ (prefixWord ++ tailWord_1419222).sum := by decide
  have hdescent : baseEnd_1419222 < baseStart_1419222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419229 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_1419229 : Nat := 118140960795 + 1419229 * 2 ^ 59
def prefixEnd_1419229 : Nat := 4983230072969 + 3 ^ 40 * 1419229 * 2
def baseEnd_1419229 : Nat := 728746635799932993710591

theorem tailTrace_1419229 : CollatzResearch.WordTrace tailWord_1419229 prefixEnd_1419229 728746635799932993710591 := by
  unfold tailWord_1419229
  simp only [CollatzResearch.WordTrace]
  refine ⟨51763534175383192861052741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34509022783588795240701827 51763534175383192861052741)
  ·
    refine ⟨9705662657884348661447389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51763534175383192861052741 9705662657884348661447389)
    ·
      refine ⟨3639623496706630748042771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9705662657884348661447389 3639623496706630748042771)
      ·
        refine ⟨5459435245059946122064157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3639623496706630748042771 5459435245059946122064157)
        ·
          refine ⟨2047288216897479795774059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5459435245059946122064157 2047288216897479795774059)
          ·
            refine ⟨3070932325346219693661089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047288216897479795774059 3070932325346219693661089)
            ·
              refine ⟨2303199244009664770245817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3070932325346219693661089 2303199244009664770245817)
              ·
                refine ⟨1727399433007248577684363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2303199244009664770245817 1727399433007248577684363)
                ·
                  refine ⟨2591099149510872866526545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1727399433007248577684363 2591099149510872866526545)
                  ·
                    refine ⟨1943324362133154649894909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2591099149510872866526545 1943324362133154649894909)
                    ·
                      refine ⟨728746635799932993710591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1943324362133154649894909 728746635799932993710591)
                      ·
                        rfl

theorem cell23_1419229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_1419229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419229 prefixEnd_1419229 := by exact prefixLift 1419229
  have htrace : WordTrace (prefixWord ++ tailWord_1419229) baseStart_1419229 baseEnd_1419229 := by
    simpa [prefixWord, tailWord_1419229, baseEnd_1419229] using wordTrace_append hprefix tailTrace_1419229
  have hstable : (prefixWord ++ tailWord_1419229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419229).length < 2 ^ (prefixWord ++ tailWord_1419229).sum := by decide
  have hdescent : baseEnd_1419229 < baseStart_1419229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419288 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 9]
def baseStart_1419288 : Nat := 118140960795 + 1419288 * 2 ^ 59
def prefixEnd_1419288 : Nat := 4983230072969 + 3 ^ 40 * 1419288 * 2
def baseEnd_1419288 : Nat := 80975214573172029208091

theorem tailTrace_1419288 : CollatzResearch.WordTrace tailWord_1419288 prefixEnd_1419288 80975214573172029208091 := by
  unfold tailWord_1419288
  simp only [CollatzResearch.WordTrace]
  refine ⟨25882843041084722968725259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34510457388112963958300345 25882843041084722968725259)
  ·
    refine ⟨38824264561627084453087889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25882843041084722968725259 38824264561627084453087889)
    ·
      refine ⟨29118198421220313339815917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38824264561627084453087889 29118198421220313339815917)
      ·
        refine ⟨10919324407957617502430969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29118198421220313339815917 10919324407957617502430969)
        ·
          refine ⟨8189493305968213126823227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10919324407957617502430969 8189493305968213126823227)
          ·
            refine ⟨12284239958952319690234841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8189493305968213126823227 12284239958952319690234841)
            ·
              refine ⟨9213179969214239767676131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12284239958952319690234841 9213179969214239767676131)
              ·
                refine ⟨13819769953821359651514197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9213179969214239767676131 13819769953821359651514197)
                ·
                  refine ⟨80975214573172029208091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13819769953821359651514197 80975214573172029208091)
                  ·
                    rfl

theorem cell23_1419288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 9].length) (baseStart_1419288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419288 prefixEnd_1419288 := by exact prefixLift 1419288
  have htrace : WordTrace (prefixWord ++ tailWord_1419288) baseStart_1419288 baseEnd_1419288 := by
    simpa [prefixWord, tailWord_1419288, baseEnd_1419288] using wordTrace_append hprefix tailTrace_1419288
  have hstable : (prefixWord ++ tailWord_1419288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419288).length < 2 ^ (prefixWord ++ tailWord_1419288).sum := by decide
  have hdescent : baseEnd_1419288 < baseStart_1419288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419303 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_1419303 : Nat := 118140960795 + 1419303 * 2 ^ 59
def prefixEnd_1419303 : Nat := 4983230072969 + 3 ^ 40 * 1419303 * 2
def baseEnd_1419303 : Nat := 728784633368365704185251

theorem tailTrace_1419303 : CollatzResearch.WordTrace tailWord_1419303 prefixEnd_1419303 728784633368365704185251 := by
  unfold tailWord_1419303
  simp only [CollatzResearch.WordTrace]
  refine ⟨51766233177115103499246563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34510822118076735666164375 51766233177115103499246563)
  ·
    refine ⟨77649349765672655248869845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51766233177115103499246563 77649349765672655248869845)
    ·
      refine ⟨1819906635132952857395387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 77649349765672655248869845 1819906635132952857395387)
      ·
        refine ⟨2729859952699429286093081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1819906635132952857395387 2729859952699429286093081)
        ·
          refine ⟨2047394964524571964569811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2729859952699429286093081 2047394964524571964569811)
          ·
            refine ⟨3071092446786857946854717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047394964524571964569811 3071092446786857946854717)
            ·
              refine ⟨1151659667545071730070519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3071092446786857946854717 1151659667545071730070519)
              ·
                refine ⟨1727489501317607595105779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151659667545071730070519 1727489501317607595105779)
                ·
                  refine ⟨2591234251976411392658669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1727489501317607595105779 2591234251976411392658669)
                  ·
                    refine ⟨971712844491154272247001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2591234251976411392658669 971712844491154272247001)
                    ·
                      refine ⟨728784633368365704185251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 971712844491154272247001 728784633368365704185251)
                      ·
                        rfl

theorem cell23_1419303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_1419303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419303 prefixEnd_1419303 := by exact prefixLift 1419303
  have htrace : WordTrace (prefixWord ++ tailWord_1419303) baseStart_1419303 baseEnd_1419303 := by
    simpa [prefixWord, tailWord_1419303, baseEnd_1419303] using wordTrace_append hprefix tailTrace_1419303
  have hstable : (prefixWord ++ tailWord_1419303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419303).length < 2 ^ (prefixWord ++ tailWord_1419303).sum := by decide
  have hdescent : baseEnd_1419303 < baseStart_1419303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419352 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 2, 5]
def baseStart_1419352 : Nat := 118140960795 + 1419352 * 2 ^ 59
def prefixEnd_1419352 : Nat := 4983230072969 + 3 ^ 40 * 1419352 * 2
def baseEnd_1419352 : Nat := 242936597973478670824175

theorem tailTrace_1419352 : CollatzResearch.WordTrace tailWord_1419352 prefixEnd_1419352 242936597973478670824175 := by
  unfold tailWord_1419352
  simp only [CollatzResearch.WordTrace]
  refine ⟨25884010176968792433890155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34512013569291723245186873 25884010176968792433890155)
  ·
    refine ⟨38826015265453188650835233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25884010176968792433890155 38826015265453188650835233)
    ·
      refine ⟨29119511449089891488126425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38826015265453188650835233 29119511449089891488126425)
      ·
        refine ⟨21839633586817418616094819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29119511449089891488126425 21839633586817418616094819)
        ·
          refine ⟨32759450380226127924142229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21839633586817418616094819 32759450380226127924142229)
          ·
            refine ⟨1535599236573099746444167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32759450380226127924142229 1535599236573099746444167)
            ·
              refine ⟨2303398854859649619666251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535599236573099746444167 2303398854859649619666251)
              ·
                refine ⟨3455098282289474429499377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303398854859649619666251 3455098282289474429499377)
                ·
                  refine ⟨2591323711717105822124533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3455098282289474429499377 2591323711717105822124533)
                  ·
                    refine ⟨242936597973478670824175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2591323711717105822124533 242936597973478670824175)
                    ·
                      rfl

theorem cell23_1419352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_1419352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419352 prefixEnd_1419352 := by exact prefixLift 1419352
  have htrace : WordTrace (prefixWord ++ tailWord_1419352) baseStart_1419352 baseEnd_1419352 := by
    simpa [prefixWord, tailWord_1419352, baseEnd_1419352] using wordTrace_append hprefix tailTrace_1419352
  have hstable : (prefixWord ++ tailWord_1419352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419352).length < 2 ^ (prefixWord ++ tailWord_1419352).sum := by decide
  have hdescent : baseEnd_1419352 < baseStart_1419352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419372 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 2, 4, 2]
def baseStart_1419372 : Nat := 118140960795 + 1419372 * 2 ^ 59
def prefixEnd_1419372 : Nat := 4983230072969 + 3 ^ 40 * 1419372 * 2
def baseEnd_1419372 : Nat := 728820063533525934222433

theorem tailTrace_1419372 : CollatzResearch.WordTrace tailWord_1419372 prefixEnd_1419372 728820063533525934222433 := by
  unfold tailWord_1419372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25884374906932564141754185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34512499875910085522338913 25884374906932564141754185)
  ·
    refine ⟨19413281180199423106315639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25884374906932564141754185 19413281180199423106315639)
    ·
      refine ⟨29119921770299134659473459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19413281180199423106315639 29119921770299134659473459)
      ·
        refine ⟨43679882655448701989210189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29119921770299134659473459 43679882655448701989210189)
        ·
          refine ⟨16379955995793263245953821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43679882655448701989210189 16379955995793263245953821)
          ·
            refine ⟨6142483498422473717232683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16379955995793263245953821 6142483498422473717232683)
            ·
              refine ⟨9213725247633710575849025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6142483498422473717232683 9213725247633710575849025)
              ·
                refine ⟨6910293935725282931886769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9213725247633710575849025 6910293935725282931886769)
                ·
                  refine ⟨5182720451793962198915077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6910293935725282931886769 5182720451793962198915077)
                  ·
                    refine ⟨971760084711367912296577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5182720451793962198915077 971760084711367912296577)
                    ·
                      refine ⟨728820063533525934222433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 971760084711367912296577 728820063533525934222433)
                      ·
                        rfl

theorem cell23_1419372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 4, 2].length) (baseStart_1419372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419372 prefixEnd_1419372 := by exact prefixLift 1419372
  have htrace : WordTrace (prefixWord ++ tailWord_1419372) baseStart_1419372 baseEnd_1419372 := by
    simpa [prefixWord, tailWord_1419372, baseEnd_1419372] using wordTrace_append hprefix tailTrace_1419372
  have hstable : (prefixWord ++ tailWord_1419372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419372).length < 2 ^ (prefixWord ++ tailWord_1419372).sum := by decide
  have hdescent : baseEnd_1419372 < baseStart_1419372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419455 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 1, 6]
def baseStart_1419455 : Nat := 118140960795 + 1419455 * 2 ^ 59
def prefixEnd_1419455 : Nat := 4983230072969 + 3 ^ 40 * 1419455 * 2
def baseEnd_1419455 : Nat := 242954227475949703161517

theorem tailTrace_1419455 : CollatzResearch.WordTrace tailWord_1419455 prefixEnd_1419455 242954227475949703161517 := by
  unfold tailWord_1419455
  simp only [CollatzResearch.WordTrace]
  refine ⟨51771777072564433458779819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34514518048376288972519879 51771777072564433458779819)
  ·
    refine ⟨77657665608846650188169729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51771777072564433458779819 77657665608846650188169729)
    ·
      refine ⟨58243249206634987641127297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77657665608846650188169729 58243249206634987641127297)
      ·
        refine ⟨43682436904976240730845473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58243249206634987641127297 43682436904976240730845473)
        ·
          refine ⟨32761827678732180548134105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43682436904976240730845473 32761827678732180548134105)
          ·
            refine ⟨24571370759049135411100579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32761827678732180548134105 24571370759049135411100579)
            ·
              refine ⟨36857056138573703116650869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24571370759049135411100579 36857056138573703116650869)
              ·
                refine ⟨3455349012991284667186019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36857056138573703116650869 3455349012991284667186019)
                ·
                  refine ⟨5183023519486927000779029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3455349012991284667186019 5183023519486927000779029)
                  ·
                    refine ⟨242954227475949703161517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5183023519486927000779029 242954227475949703161517)
                    ·
                      rfl

theorem cell23_1419455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_1419455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419455 prefixEnd_1419455 := by exact prefixLift 1419455
  have htrace : WordTrace (prefixWord ++ tailWord_1419455) baseStart_1419455 baseEnd_1419455 := by
    simpa [prefixWord, tailWord_1419455, baseEnd_1419455] using wordTrace_append hprefix tailTrace_1419455
  have hstable : (prefixWord ++ tailWord_1419455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419455).length < 2 ^ (prefixWord ++ tailWord_1419455).sum := by decide
  have hdescent : baseEnd_1419455 < baseStart_1419455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419482 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5]
def baseStart_1419482 : Nat := 118140960795 + 1419482 * 2 ^ 59
def prefixEnd_1419482 : Nat := 4983230072969 + 3 ^ 40 * 1419482 * 2
def baseEnd_1419482 : Nat := 728876546405520503846927

theorem tailTrace_1419482 : CollatzResearch.WordTrace tailWord_1419482 prefixEnd_1419482 728876546405520503846927 := by
  unfold tailWord_1419482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12943190460866654267503175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34515174562311078046675133 12943190460866654267503175)
  ·
    refine ⟨19414785691299981401254763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12943190460866654267503175 19414785691299981401254763)
    ·
      refine ⟨29122178536949972101882145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19414785691299981401254763 29122178536949972101882145)
      ·
        refine ⟨21841633902712479076411609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29122178536949972101882145 21841633902712479076411609)
        ·
          refine ⟨16381225427034359307308707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21841633902712479076411609 16381225427034359307308707)
          ·
            refine ⟨24571838140551538960963061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16381225427034359307308707 24571838140551538960963061)
            ·
              refine ⟨2303609825676706777590287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24571838140551538960963061 2303609825676706777590287)
              ·
                refine ⟨3455414738515060166385431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303609825676706777590287 3455414738515060166385431)
                ·
                  refine ⟨5183122107772590249578147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3455414738515060166385431 5183122107772590249578147)
                  ·
                    refine ⟨7774683161658885374367221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5183122107772590249578147 7774683161658885374367221)
                    ·
                      refine ⟨728876546405520503846927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7774683161658885374367221 728876546405520503846927)
                      ·
                        rfl

theorem cell23_1419482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_1419482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419482 prefixEnd_1419482 := by exact prefixLift 1419482
  have htrace : WordTrace (prefixWord ++ tailWord_1419482) baseStart_1419482 baseEnd_1419482 := by
    simpa [prefixWord, tailWord_1419482, baseEnd_1419482] using wordTrace_append hprefix tailTrace_1419482
  have hstable : (prefixWord ++ tailWord_1419482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419482).length < 2 ^ (prefixWord ++ tailWord_1419482).sum := by decide
  have hdescent : baseEnd_1419482 < baseStart_1419482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419489 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 2, 4]
def baseStart_1419489 : Nat := 118140960795 + 1419489 * 2 ^ 59
def prefixEnd_1419489 : Nat := 4983230072969 + 3 ^ 40 * 1419489 * 2
def baseEnd_1419489 : Nat := 242960046923367325486465

theorem tailTrace_1419489 : CollatzResearch.WordTrace tailWord_1419489 prefixEnd_1419489 242960046923367325486465 := by
  unfold tailWord_1419489
  simp only [CollatzResearch.WordTrace]
  refine ⟨51773017154441257265517521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34515344769627504843678347 51773017154441257265517521)
  ·
    refine ⟨38829762865830942949138141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51773017154441257265517521 38829762865830942949138141)
    ·
      refine ⟨14561161074686603605926803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38829762865830942949138141 14561161074686603605926803)
      ·
        refine ⟨21841741612029905408890205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14561161074686603605926803 21841741612029905408890205)
        ·
          refine ⟨8190653104511214528333827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21841741612029905408890205 8190653104511214528333827)
          ·
            refine ⟨12285979656766821792500741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8190653104511214528333827 12285979656766821792500741)
            ·
              refine ⟨2303621185643779086093889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12285979656766821792500741 2303621185643779086093889)
              ·
                refine ⟨1727715889232834314570417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2303621185643779086093889 1727715889232834314570417)
                ·
                  refine ⟨1295786916924625735927813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1727715889232834314570417 1295786916924625735927813)
                  ·
                    refine ⟨242960046923367325486465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1295786916924625735927813 242960046923367325486465)
                    ·
                      rfl

theorem cell23_1419489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_1419489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419489 prefixEnd_1419489 := by exact prefixLift 1419489
  have htrace : WordTrace (prefixWord ++ tailWord_1419489) baseStart_1419489 baseEnd_1419489 := by
    simpa [prefixWord, tailWord_1419489, baseEnd_1419489] using wordTrace_append hprefix tailTrace_1419489
  have hstable : (prefixWord ++ tailWord_1419489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419489).length < 2 ^ (prefixWord ++ tailWord_1419489).sum := by decide
  have hdescent : baseEnd_1419489 < baseStart_1419489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419505 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_1419505 : Nat := 118140960795 + 1419505 * 2 ^ 59
def prefixEnd_1419505 : Nat := 4983230072969 + 3 ^ 40 * 1419505 * 2
def baseEnd_1419505 : Nat := 728888356460573913859321

theorem tailTrace_1419505 : CollatzResearch.WordTrace tailWord_1419505 prefixEnd_1419505 728888356460573913859321 := by
  unfold tailWord_1419505
  simp only [CollatzResearch.WordTrace]
  refine ⟨51773600722383291998099969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34515733814922194665399979 51773600722383291998099969)
  ·
    refine ⟨38830200541787468998574977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51773600722383291998099969 38830200541787468998574977)
    ·
      refine ⟨29122650406340601748931233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38830200541787468998574977 29122650406340601748931233)
      ·
        refine ⟨21841987804755451311698425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29122650406340601748931233 21841987804755451311698425)
        ·
          refine ⟨16381490853566588483773819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21841987804755451311698425 16381490853566588483773819)
          ·
            refine ⟨24572236280349882725660729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16381490853566588483773819 24572236280349882725660729)
            ·
              refine ⟨18429177210262412044245547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24572236280349882725660729 18429177210262412044245547)
              ·
                refine ⟨27643765815393618066368321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18429177210262412044245547 27643765815393618066368321)
                ·
                  refine ⟨20732824361545213549776241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27643765815393618066368321 20732824361545213549776241)
                  ·
                    refine ⟨15549618271158910162332181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20732824361545213549776241 15549618271158910162332181)
                    ·
                      refine ⟨728888356460573913859321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15549618271158910162332181 728888356460573913859321)
                      ·
                        rfl

theorem cell23_1419505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_1419505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419505 prefixEnd_1419505 := by exact prefixLift 1419505
  have htrace : WordTrace (prefixWord ++ tailWord_1419505) baseStart_1419505 baseEnd_1419505 := by
    simpa [prefixWord, tailWord_1419505, baseEnd_1419505] using wordTrace_append hprefix tailTrace_1419505
  have hstable : (prefixWord ++ tailWord_1419505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419505).length < 2 ^ (prefixWord ++ tailWord_1419505).sum := by decide
  have hdescent : baseEnd_1419505 < baseStart_1419505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419546 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3]
def baseStart_1419546 : Nat := 118140960795 + 1419546 * 2 ^ 59
def prefixEnd_1419546 : Nat := 4983230072969 + 3 ^ 40 * 1419546 * 2
def baseEnd_1419546 : Nat := 728909409167408253446633

theorem tailTrace_1419546 : CollatzResearch.WordTrace tailWord_1419546 prefixEnd_1419546 728909409167408253446633 := by
  unfold tailWord_1419546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12943774028808689000085623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34516730743489837333561661 12943774028808689000085623)
  ·
    refine ⟨19415661043213033500128435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12943774028808689000085623 19415661043213033500128435)
    ·
      refine ⟨29123491564819550250192653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19415661043213033500128435 29123491564819550250192653)
      ·
        refine ⟨10921309336807331343822245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29123491564819550250192653 10921309336807331343822245)
        ·
          refine ⟨2047745500651374626966671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10921309336807331343822245 2047745500651374626966671)
          ·
            refine ⟨3071618250977061940450007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047745500651374626966671 3071618250977061940450007)
            ·
              refine ⟨4607427376465592910675011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3071618250977061940450007 4607427376465592910675011)
              ·
                refine ⟨6911141064698389366012517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4607427376465592910675011 6911141064698389366012517)
                ·
                  refine ⟨1295838949630948006127347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6911141064698389366012517 1295838949630948006127347)
                  ·
                    refine ⟨1943758424446422009191021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1295838949630948006127347 1943758424446422009191021)
                    ·
                      refine ⟨728909409167408253446633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1943758424446422009191021 728909409167408253446633)
                      ·
                        rfl

theorem cell23_1419546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_1419546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419546 prefixEnd_1419546 := by exact prefixLift 1419546
  have htrace : WordTrace (prefixWord ++ tailWord_1419546) baseStart_1419546 baseEnd_1419546 := by
    simpa [prefixWord, tailWord_1419546, baseEnd_1419546] using wordTrace_append hprefix tailTrace_1419546
  have hstable : (prefixWord ++ tailWord_1419546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419546).length < 2 ^ (prefixWord ++ tailWord_1419546).sum := by decide
  have hdescent : baseEnd_1419546 < baseStart_1419546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419614 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_1419614 : Nat := 118140960795 + 1419614 * 2 ^ 59
def prefixEnd_1419614 : Nat := 4983230072969 + 3 ^ 40 * 1419614 * 2
def baseEnd_1419614 : Nat := 728944325851913987396321

theorem tailTrace_1419614 : CollatzResearch.WordTrace tailWord_1419614 prefixEnd_1419614 728944325851913987396321 := by
  unfold tailWord_1419614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6472197034873550451727237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34518384185992269075878597 6472197034873550451727237)
  ·
    refine ⟨1213536944038790709698857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6472197034873550451727237 1213536944038790709698857)
    ·
      refine ⟨910152708029093032274143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1213536944038790709698857 910152708029093032274143)
      ·
        refine ⟨1365229062043639548411215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 910152708029093032274143 1365229062043639548411215)
        ·
          refine ⟨2047843593065459322616823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365229062043639548411215 2047843593065459322616823)
          ·
            refine ⟨3071765389598188983925235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047843593065459322616823 3071765389598188983925235)
            ·
              refine ⟨4607648084397283475887853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3071765389598188983925235 4607648084397283475887853)
              ·
                refine ⟨1727868031648981303457945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4607648084397283475887853 1727868031648981303457945)
                ·
                  refine ⟨1295901023736735977593459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1727868031648981303457945 1295901023736735977593459)
                  ·
                    refine ⟨1943851535605103966390189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1295901023736735977593459 1943851535605103966390189)
                    ·
                      refine ⟨728944325851913987396321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1943851535605103966390189 728944325851913987396321)
                      ·
                        rfl

theorem cell23_1419614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_1419614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419614 prefixEnd_1419614 := by exact prefixLift 1419614
  have htrace : WordTrace (prefixWord ++ tailWord_1419614) baseStart_1419614 baseEnd_1419614 := by
    simpa [prefixWord, tailWord_1419614, baseEnd_1419614] using wordTrace_append hprefix tailTrace_1419614
  have hstable : (prefixWord ++ tailWord_1419614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419614).length < 2 ^ (prefixWord ++ tailWord_1419614).sum := by decide
  have hdescent : baseEnd_1419614 < baseStart_1419614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419649 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1419649 : Nat := 118140960795 + 1419649 * 2 ^ 59
def prefixEnd_1419649 : Nat := 4983230072969 + 3 ^ 40 * 1419649 * 2
def baseEnd_1419649 : Nat := 728962297674821350458659

theorem tailTrace_1419649 : CollatzResearch.WordTrace tailWord_1419649 prefixEnd_1419649 728962297674821350458659 := by
  unfold tailWord_1419649
  simp only [CollatzResearch.WordTrace]
  refine ⟨51778852833861604591342001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34519235222574403060894667 51778852833861604591342001)
  ·
    refine ⟨38834139625396203443506501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51778852833861604591342001 38834139625396203443506501)
    ·
      refine ⟨7281401179761788145657469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38834139625396203443506501 7281401179761788145657469)
      ·
        refine ⟨2730525442410670554621551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7281401179761788145657469 2730525442410670554621551)
        ·
          refine ⟨4095788163616005831932327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2730525442410670554621551 4095788163616005831932327)
          ·
            refine ⟨6143682245424008747898491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4095788163616005831932327 6143682245424008747898491)
            ·
              refine ⟨9215523368136013121847737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6143682245424008747898491 9215523368136013121847737)
              ·
                refine ⟨6911642526102009841385803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9215523368136013121847737 6911642526102009841385803)
                ·
                  refine ⟨10367463789153014762078705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6911642526102009841385803 10367463789153014762078705)
                  ·
                    refine ⟨7775597841864761071559029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10367463789153014762078705 7775597841864761071559029)
                    ·
                      refine ⟨728962297674821350458659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7775597841864761071559029 728962297674821350458659)
                      ·
                        rfl

theorem cell23_1419649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1419649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419649 prefixEnd_1419649 := by exact prefixLift 1419649
  have htrace : WordTrace (prefixWord ++ tailWord_1419649) baseStart_1419649 baseEnd_1419649 := by
    simpa [prefixWord, tailWord_1419649, baseEnd_1419649] using wordTrace_append hprefix tailTrace_1419649
  have hstable : (prefixWord ++ tailWord_1419649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419649).length < 2 ^ (prefixWord ++ tailWord_1419649).sum := by decide
  have hdescent : baseEnd_1419649 < baseStart_1419649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419659 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 4]
def baseStart_1419659 : Nat := 118140960795 + 1419659 * 2 ^ 59
def prefixEnd_1419659 : Nat := 4983230072969 + 3 ^ 40 * 1419659 * 2
def baseEnd_1419659 : Nat := 728967432481366311333613

theorem tailTrace_1419659 : CollatzResearch.WordTrace tailWord_1419659 prefixEnd_1419659 728967432481366311333613 := by
  unfold tailWord_1419659
  simp only [CollatzResearch.WordTrace]
  refine ⟨51779217563825376299206031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34519478375883584199470687 51779217563825376299206031)
  ·
    refine ⟨77668826345738064448809047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51779217563825376299206031 77668826345738064448809047)
    ·
      refine ⟨116503239518607096673213571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77668826345738064448809047 116503239518607096673213571)
      ·
        refine ⟨174754859277910645009820357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116503239518607096673213571 174754859277910645009820357)
        ·
          refine ⟨32766536114608245939341317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174754859277910645009820357 32766536114608245939341317)
          ·
            refine ⟨6143725521489046113626497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32766536114608245939341317 6143725521489046113626497)
            ·
              refine ⟨4607794141116784585219873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6143725521489046113626497 4607794141116784585219873)
              ·
                refine ⟨3455845605837588438914905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4607794141116784585219873 3455845605837588438914905)
                ·
                  refine ⟨2591884204378191329186179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3455845605837588438914905 2591884204378191329186179)
                  ·
                    refine ⟨3887826306567286993779269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2591884204378191329186179 3887826306567286993779269)
                    ·
                      refine ⟨728967432481366311333613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3887826306567286993779269 728967432481366311333613)
                      ·
                        rfl

theorem cell23_1419659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 4].length) (baseStart_1419659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419659 prefixEnd_1419659 := by exact prefixLift 1419659
  have htrace : WordTrace (prefixWord ++ tailWord_1419659) baseStart_1419659 baseEnd_1419659 := by
    simpa [prefixWord, tailWord_1419659, baseEnd_1419659] using wordTrace_append hprefix tailTrace_1419659
  have hstable : (prefixWord ++ tailWord_1419659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419659).length < 2 ^ (prefixWord ++ tailWord_1419659).sum := by decide
  have hdescent : baseEnd_1419659 < baseStart_1419659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419669 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 3, 4]
def baseStart_1419669 : Nat := 118140960795 + 1419669 * 2 ^ 59
def prefixEnd_1419669 : Nat := 4983230072969 + 3 ^ 40 * 1419669 * 2
def baseEnd_1419669 : Nat := 242990855762637090736189

theorem tailTrace_1419669 : CollatzResearch.WordTrace tailWord_1419669 prefixEnd_1419669 242990855762637090736189 := by
  unfold tailWord_1419669
  simp only [CollatzResearch.WordTrace]
  refine ⟨51779582293789148007070061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34519721529192765338046707 51779582293789148007070061)
  ·
    refine ⟨19417343360170930502651273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51779582293789148007070061 19417343360170930502651273)
    ·
      refine ⟨14563007520128197876988455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19417343360170930502651273 14563007520128197876988455)
      ·
        refine ⟨21844511280192296815482683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14563007520128197876988455 21844511280192296815482683)
        ·
          refine ⟨32766766920288445223224025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21844511280192296815482683 32766766920288445223224025)
          ·
            refine ⟨24575075190216333917418019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32766766920288445223224025 24575075190216333917418019)
            ·
              refine ⟨36862612785324500876127029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24575075190216333917418019 36862612785324500876127029)
              ·
                refine ⟨3455869948624171957136909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36862612785324500876127029 3455869948624171957136909)
                ·
                  refine ⟨1295951230734064483926341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3455869948624171957136909 1295951230734064483926341)
                  ·
                    refine ⟨242990855762637090736189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1295951230734064483926341 242990855762637090736189)
                    ·
                      rfl

theorem cell23_1419669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_1419669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419669 prefixEnd_1419669 := by exact prefixLift 1419669
  have htrace : WordTrace (prefixWord ++ tailWord_1419669) baseStart_1419669 baseEnd_1419669 := by
    simpa [prefixWord, tailWord_1419669, baseEnd_1419669] using wordTrace_append hprefix tailTrace_1419669
  have hstable : (prefixWord ++ tailWord_1419669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419669).length < 2 ^ (prefixWord ++ tailWord_1419669).sum := by decide
  have hdescent : baseEnd_1419669 < baseStart_1419669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419679 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 3]
def baseStart_1419679 : Nat := 118140960795 + 1419679 * 2 ^ 59
def prefixEnd_1419679 : Nat := 4983230072969 + 3 ^ 40 * 1419679 * 2
def baseEnd_1419679 : Nat := 728977702094456233083521

theorem tailTrace_1419679 : CollatzResearch.WordTrace tailWord_1419679 prefixEnd_1419679 728977702094456233083521 := by
  unfold tailWord_1419679
  simp only [CollatzResearch.WordTrace]
  refine ⟨51779947023752919714934091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34519964682501946476622727 51779947023752919714934091)
  ·
    refine ⟨77669920535629379572401137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51779947023752919714934091 77669920535629379572401137)
    ·
      refine ⟨58252440401722034679300853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77669920535629379572401137 58252440401722034679300853)
      ·
        refine ⟨5461166287661440751184455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58252440401722034679300853 5461166287661440751184455)
        ·
          refine ⟨8191749431492161126776683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5461166287661440751184455 8191749431492161126776683)
          ·
            refine ⟨12287624147238241690165025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8191749431492161126776683 12287624147238241690165025)
            ·
              refine ⟨9215718110428681267623769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12287624147238241690165025 9215718110428681267623769)
              ·
                refine ⟨6911788582821510950717827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9215718110428681267623769 6911788582821510950717827)
                ·
                  refine ⟨10367682874232266426076741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6911788582821510950717827 10367682874232266426076741)
                  ·
                    refine ⟨1943940538918549954889389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10367682874232266426076741 1943940538918549954889389)
                    ·
                      refine ⟨728977702094456233083521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1943940538918549954889389 728977702094456233083521)
                      ·
                        rfl

theorem cell23_1419679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_1419679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419679 prefixEnd_1419679 := by exact prefixLift 1419679
  have htrace : WordTrace (prefixWord ++ tailWord_1419679) baseStart_1419679 baseEnd_1419679 := by
    simpa [prefixWord, tailWord_1419679, baseEnd_1419679] using wordTrace_append hprefix tailTrace_1419679
  have hstable : (prefixWord ++ tailWord_1419679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419679).length < 2 ^ (prefixWord ++ tailWord_1419679).sum := by decide
  have hdescent : baseEnd_1419679 < baseStart_1419679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419703 : List Nat := [1, 1, 3, 1, 3, 4, 2, 3, 1, 4]
def baseStart_1419703 : Nat := 118140960795 + 1419703 * 2 ^ 59
def prefixEnd_1419703 : Nat := 4983230072969 + 3 ^ 40 * 1419703 * 2
def baseEnd_1419703 : Nat := 242996675210054713061137

theorem tailTrace_1419703 : CollatzResearch.WordTrace tailWord_1419703 prefixEnd_1419703 242996675210054713061137 := by
  unfold tailWord_1419703
  simp only [CollatzResearch.WordTrace]
  refine ⟨51780822375665971813807763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34520548250443981209205175 51780822375665971813807763)
  ·
    refine ⟨77671233563498957720711645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51780822375665971813807763 77671233563498957720711645)
    ·
      refine ⟨29126712586312109145266867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77671233563498957720711645 29126712586312109145266867)
      ·
        refine ⟨43690068879468163717900301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29126712586312109145266867 43690068879468163717900301)
        ·
          refine ⟨16383775829800561394212613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43690068879468163717900301 16383775829800561394212613)
          ·
            refine ⟨3071957968087605261414865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16383775829800561394212613 3071957968087605261414865)
            ·
              refine ⟨2303968476065703946061149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3071957968087605261414865 2303968476065703946061149)
              ·
                refine ⟨863988178524638979772931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2303968476065703946061149 863988178524638979772931)
                ·
                  refine ⟨1295982267786958469659397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 863988178524638979772931 1295982267786958469659397)
                  ·
                    refine ⟨242996675210054713061137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1295982267786958469659397 242996675210054713061137)
                    ·
                      rfl

theorem cell23_1419703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_1419703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419703 prefixEnd_1419703 := by exact prefixLift 1419703
  have htrace : WordTrace (prefixWord ++ tailWord_1419703) baseStart_1419703 baseEnd_1419703 := by
    simpa [prefixWord, tailWord_1419703, baseEnd_1419703] using wordTrace_append hprefix tailTrace_1419703
  have hstable : (prefixWord ++ tailWord_1419703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419703).length < 2 ^ (prefixWord ++ tailWord_1419703).sum := by decide
  have hdescent : baseEnd_1419703 < baseStart_1419703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419716 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 8]
def baseStart_1419716 : Nat := 118140960795 + 1419716 * 2 ^ 59
def prefixEnd_1419716 : Nat := 4983230072969 + 3 ^ 40 * 1419716 * 2
def baseEnd_1419716 : Nat := 80999633430963620924539

theorem tailTrace_1419716 : CollatzResearch.WordTrace tailWord_1419716 prefixEnd_1419716 80999633430963620924539 := by
  unfold tailWord_1419716
  simp only [CollatzResearch.WordTrace]
  refine ⟨25890648262309437517015501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34520864349745916689354001 25890648262309437517015501)
  ·
    refine ⟨9708993098366039068880813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25890648262309437517015501 9708993098366039068880813)
    ·
      refine ⟨3640872411887264650830305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9708993098366039068880813 3640872411887264650830305)
      ·
        refine ⟨2730654308915448488122729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3640872411887264650830305 2730654308915448488122729)
        ·
          refine ⟨2047990731686586366092047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2730654308915448488122729 2047990731686586366092047)
          ·
            refine ⟨3071986097529879549138071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047990731686586366092047 3071986097529879549138071)
            ·
              refine ⟨4607979146294819323707107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3071986097529879549138071 4607979146294819323707107)
              ·
                refine ⟨6911968719442228985560661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4607979146294819323707107 6911968719442228985560661)
                ·
                  refine ⟨80999633430963620924539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6911968719442228985560661 80999633430963620924539)
                  ·
                    rfl

theorem cell23_1419716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_1419716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419716 prefixEnd_1419716 := by exact prefixLift 1419716
  have htrace : WordTrace (prefixWord ++ tailWord_1419716) baseStart_1419716 baseEnd_1419716 := by
    simpa [prefixWord, tailWord_1419716, baseEnd_1419716] using wordTrace_append hprefix tailTrace_1419716
  have hstable : (prefixWord ++ tailWord_1419716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419716).length < 2 ^ (prefixWord ++ tailWord_1419716).sum := by decide
  have hdescent : baseEnd_1419716 < baseStart_1419716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419769 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 5]
def baseStart_1419769 : Nat := 118140960795 + 1419769 * 2 ^ 59
def prefixEnd_1419769 : Nat := 4983230072969 + 3 ^ 40 * 1419769 * 2
def baseEnd_1419769 : Nat := 729023915353360880958107

theorem tailTrace_1419769 : CollatzResearch.WordTrace tailWord_1419769 prefixEnd_1419769 729023915353360880958107 := by
  unfold tailWord_1419769
  simp only [CollatzResearch.WordTrace]
  refine ⟨51783229593426865085710361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34522153062284576723806907 51783229593426865085710361)
  ·
    refine ⟨38837422195070148814282771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51783229593426865085710361 38837422195070148814282771)
    ·
      refine ⟨58256133292605223221424157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38837422195070148814282771 58256133292605223221424157)
      ·
        refine ⟨21846049984726958708034059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58256133292605223221424157 21846049984726958708034059)
        ·
          refine ⟨32769074977090438062051089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21846049984726958708034059 32769074977090438062051089)
          ·
            refine ⟨24576806232817828546538317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32769074977090438062051089 24576806232817828546538317)
            ·
              refine ⟨9216302337306685704951869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24576806232817828546538317 9216302337306685704951869)
              ·
                refine ⟨3456113376490007139356951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9216302337306685704951869 3456113376490007139356951)
                ·
                  refine ⟨5184170064735010709035427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456113376490007139356951 5184170064735010709035427)
                  ·
                    refine ⟨7776255097102516063553141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5184170064735010709035427 7776255097102516063553141)
                    ·
                      refine ⟨729023915353360880958107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7776255097102516063553141 729023915353360880958107)
                      ·
                        rfl

theorem cell23_1419769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_1419769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419769 prefixEnd_1419769 := by exact prefixLift 1419769
  have htrace : WordTrace (prefixWord ++ tailWord_1419769) baseStart_1419769 baseEnd_1419769 := by
    simpa [prefixWord, tailWord_1419769, baseEnd_1419769] using wordTrace_append hprefix tailTrace_1419769
  have hstable : (prefixWord ++ tailWord_1419769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419769).length < 2 ^ (prefixWord ++ tailWord_1419769).sum := by decide
  have hdescent : baseEnd_1419769 < baseStart_1419769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419777 : List Nat := [1, 2, 4, 1, 3, 2, 3, 2, 1, 1, 3]
def baseStart_1419777 : Nat := 118140960795 + 1419777 * 2 ^ 59
def prefixEnd_1419777 : Nat := 4983230072969 + 3 ^ 40 * 1419777 * 2
def baseEnd_1419777 : Nat := 729028023198596849658071

theorem tailTrace_1419777 : CollatzResearch.WordTrace tailWord_1419777 prefixEnd_1419777 729028023198596849658071 := by
  unfold tailWord_1419777
  simp only [CollatzResearch.WordTrace]
  refine ⟨51783521377397882452001585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34522347584931921634667723 51783521377397882452001585)
  ·
    refine ⟨38837641033048411839001189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51783521377397882452001585 38837641033048411839001189)
    ·
      refine ⟨7282057693696577219812723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38837641033048411839001189 7282057693696577219812723)
      ·
        refine ⟨10923086540544865829719085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7282057693696577219812723 10923086540544865829719085)
        ·
          refine ⟨4096157452704324686144657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10923086540544865829719085 4096157452704324686144657)
          ·
            refine ⟨3072118089528243514608493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4096157452704324686144657 3072118089528243514608493)
            ·
              refine ⟨1152044283573091317978185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3072118089528243514608493 1152044283573091317978185)
              ·
                refine ⟨864033212679818488483639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152044283573091317978185 864033212679818488483639)
                ·
                  refine ⟨1296049819019727732725459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864033212679818488483639 1296049819019727732725459)
                  ·
                    refine ⟨1944074728529591599088189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1296049819019727732725459 1944074728529591599088189)
                    ·
                      refine ⟨729028023198596849658071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1944074728529591599088189 729028023198596849658071)
                      ·
                        rfl

theorem cell23_1419777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_1419777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419777 prefixEnd_1419777 := by exact prefixLift 1419777
  have htrace : WordTrace (prefixWord ++ tailWord_1419777) baseStart_1419777 baseEnd_1419777 := by
    simpa [prefixWord, tailWord_1419777, baseEnd_1419777] using wordTrace_append hprefix tailTrace_1419777
  have hstable : (prefixWord ++ tailWord_1419777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419777).length < 2 ^ (prefixWord ++ tailWord_1419777).sum := by decide
  have hdescent : baseEnd_1419777 < baseStart_1419777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419786 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_1419786 : Nat := 118140960795 + 1419786 * 2 ^ 59
def prefixEnd_1419786 : Nat := 4983230072969 + 3 ^ 40 * 1419786 * 2
def baseEnd_1419786 : Nat := 729032644524487314445529

theorem tailTrace_1419786 : CollatzResearch.WordTrace tailWord_1419786 prefixEnd_1419786 729032644524487314445529 := by
  unfold tailWord_1419786
  simp only [CollatzResearch.WordTrace]
  refine ⟨12945962408591319247269803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34522566422910184659386141 12945962408591319247269803)
  ·
    refine ⟨19418943612886978870904705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12945962408591319247269803 19418943612886978870904705)
    ·
      refine ⟨14564207709665234153178529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19418943612886978870904705 14564207709665234153178529)
      ·
        refine ⟨10923155782248925614883897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14564207709665234153178529 10923155782248925614883897)
        ·
          refine ⟨8192366836686694211162923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10923155782248925614883897 8192366836686694211162923)
          ·
            refine ⟨12288550255030041316744385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8192366836686694211162923 12288550255030041316744385)
            ·
              refine ⟨9216412691272530987558289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12288550255030041316744385 9216412691272530987558289)
              ·
                refine ⟨6912309518454398240668717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9216412691272530987558289 6912309518454398240668717)
                ·
                  refine ⟨2592116069420399340250769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6912309518454398240668717 2592116069420399340250769)
                  ·
                    refine ⟨1944087052065299505188077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2592116069420399340250769 1944087052065299505188077)
                    ·
                      refine ⟨729032644524487314445529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1944087052065299505188077 729032644524487314445529)
                      ·
                        rfl

theorem cell23_1419786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_1419786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419786 prefixEnd_1419786 := by exact prefixLift 1419786
  have htrace : WordTrace (prefixWord ++ tailWord_1419786) baseStart_1419786 baseEnd_1419786 := by
    simpa [prefixWord, tailWord_1419786, baseEnd_1419786] using wordTrace_append hprefix tailTrace_1419786
  have hstable : (prefixWord ++ tailWord_1419786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419786).length < 2 ^ (prefixWord ++ tailWord_1419786).sum := by decide
  have hdescent : baseEnd_1419786 < baseStart_1419786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419828 : List Nat := [2, 5, 1, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_1419828 : Nat := 118140960795 + 1419828 * 2 ^ 59
def prefixEnd_1419828 : Nat := 4983230072969 + 3 ^ 40 * 1419828 * 2
def baseEnd_1419828 : Nat := 729054210711976150120337

theorem tailTrace_1419828 : CollatzResearch.WordTrace tailWord_1419828 prefixEnd_1419828 729054210711976150120337 := by
  unfold tailWord_1419828
  simp only [CollatzResearch.WordTrace]
  refine ⟨25892690750106559081054069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34523587666808745441405425 25892690750106559081054069)
  ·
    refine ⟨2427439757822489913848819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25892690750106559081054069 2427439757822489913848819)
    ·
      refine ⟨3641159636733734870773229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2427439757822489913848819 3641159636733734870773229)
      ·
        refine ⟨1365434863775150576539961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3641159636733734870773229 1365434863775150576539961)
        ·
          refine ⟨1024076147831362932404971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1365434863775150576539961 1024076147831362932404971)
          ·
            refine ⟨1536114221747044398607457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024076147831362932404971 1536114221747044398607457)
            ·
              refine ⟨1152085666310283298955593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536114221747044398607457 1152085666310283298955593)
              ·
                refine ⟨864064249732712474216695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152085666310283298955593 864064249732712474216695)
                ·
                  refine ⟨1296096374599068711325043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864064249732712474216695 1296096374599068711325043)
                  ·
                    refine ⟨1944144561898603066987565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1296096374599068711325043 1944144561898603066987565)
                    ·
                      refine ⟨729054210711976150120337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1944144561898603066987565 729054210711976150120337)
                      ·
                        rfl

theorem cell23_1419828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_1419828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419828 prefixEnd_1419828 := by exact prefixLift 1419828
  have htrace : WordTrace (prefixWord ++ tailWord_1419828) baseStart_1419828 baseEnd_1419828 := by
    simpa [prefixWord, tailWord_1419828, baseEnd_1419828] using wordTrace_append hprefix tailTrace_1419828
  have hstable : (prefixWord ++ tailWord_1419828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419828).length < 2 ^ (prefixWord ++ tailWord_1419828).sum := by decide
  have hdescent : baseEnd_1419828 < baseStart_1419828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419834 : List Nat := [3, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2]
def baseStart_1419834 : Nat := 118140960795 + 1419834 * 2 ^ 59
def prefixEnd_1419834 : Nat := 4983230072969 + 3 ^ 40 * 1419834 * 2
def baseEnd_1419834 : Nat := 729057291595903126645309

theorem tailTrace_1419834 : CollatzResearch.WordTrace tailWord_1419834 prefixEnd_1419834 729057291595903126645309 := by
  unfold tailWord_1419834
  simp only [CollatzResearch.WordTrace]
  refine ⟨12946400084547845296706639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34523733558794254124551037 12946400084547845296706639)
  ·
    refine ⟨19419600126821767945059959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12946400084547845296706639 19419600126821767945059959)
    ·
      refine ⟨29129400190232651917589939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19419600126821767945059959 29129400190232651917589939)
      ·
        refine ⟨43694100285348977876384909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29129400190232651917589939 43694100285348977876384909)
        ·
          refine ⟨16385287607005866703644341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43694100285348977876384909 16385287607005866703644341)
          ·
            refine ⟨1536120713156800003466657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16385287607005866703644341 1536120713156800003466657)
            ·
              refine ⟨1152090534867600002599993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536120713156800003466657 1152090534867600002599993)
              ·
                refine ⟨864067901150700001949995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152090534867600002599993 864067901150700001949995)
                ·
                  refine ⟨1296101851726050002924993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 864067901150700001949995 1296101851726050002924993)
                  ·
                    refine ⟨972076388794537502193745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1296101851726050002924993 972076388794537502193745)
                    ·
                      refine ⟨729057291595903126645309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972076388794537502193745 729057291595903126645309)
                      ·
                        rfl

theorem cell23_1419834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 1, 2, 2].length) (baseStart_1419834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419834 prefixEnd_1419834 := by exact prefixLift 1419834
  have htrace : WordTrace (prefixWord ++ tailWord_1419834) baseStart_1419834 baseEnd_1419834 := by
    simpa [prefixWord, tailWord_1419834, baseEnd_1419834] using wordTrace_append hprefix tailTrace_1419834
  have hstable : (prefixWord ++ tailWord_1419834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419834).length < 2 ^ (prefixWord ++ tailWord_1419834).sum := by decide
  have hdescent : baseEnd_1419834 < baseStart_1419834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419839 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 4]
def baseStart_1419839 : Nat := 118140960795 + 1419839 * 2 ^ 59
def prefixEnd_1419839 : Nat := 4983230072969 + 3 ^ 40 * 1419839 * 2
def baseEnd_1419839 : Nat := 729059858999175607082785

theorem tailTrace_1419839 : CollatzResearch.WordTrace tailWord_1419839 prefixEnd_1419839 729059858999175607082785 := by
  unfold tailWord_1419839
  simp only [CollatzResearch.WordTrace]
  refine ⟨51785782703173267040758571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34523855135448844693839047 51785782703173267040758571)
  ·
    refine ⟨77678674054759900561137857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51785782703173267040758571 77678674054759900561137857)
    ·
      refine ⟨58259005541069925420853393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77678674054759900561137857 58259005541069925420853393)
      ·
        refine ⟨43694254155802444065640045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58259005541069925420853393 43694254155802444065640045)
        ·
          refine ⟨16385345308425916524615017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43694254155802444065640045 16385345308425916524615017)
          ·
            refine ⟨12289008981319437393461263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16385345308425916524615017 12289008981319437393461263)
            ·
              refine ⟨18433513471979156090191895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12289008981319437393461263 18433513471979156090191895)
              ·
                refine ⟨27650270207968734135287843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18433513471979156090191895 27650270207968734135287843)
                ·
                  refine ⟨41475405311953101202931765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27650270207968734135287843 41475405311953101202931765)
                  ·
                    refine ⟨3888319247995603237774853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41475405311953101202931765 3888319247995603237774853)
                    ·
                      refine ⟨729059858999175607082785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3888319247995603237774853 729059858999175607082785)
                      ·
                        rfl

theorem cell23_1419839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_1419839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419839 prefixEnd_1419839 := by exact prefixLift 1419839
  have htrace : WordTrace (prefixWord ++ tailWord_1419839) baseStart_1419839 baseEnd_1419839 := by
    simpa [prefixWord, tailWord_1419839, baseEnd_1419839] using wordTrace_append hprefix tailTrace_1419839
  have hstable : (prefixWord ++ tailWord_1419839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419839).length < 2 ^ (prefixWord ++ tailWord_1419839).sum := by decide
  have hdescent : baseEnd_1419839 < baseStart_1419839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419873 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 1, 4, 2]
def baseStart_1419873 : Nat := 118140960795 + 1419873 * 2 ^ 59
def prefixEnd_1419873 : Nat := 4983230072969 + 3 ^ 40 * 1419873 * 2
def baseEnd_1419873 : Nat := 729077317341428474057629

theorem tailTrace_1419873 : CollatzResearch.WordTrace tailWord_1419873 prefixEnd_1419873 729077317341428474057629 := by
  unfold tailWord_1419873
  simp only [CollatzResearch.WordTrace]
  refine ⟨51787022785050090847496273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34524681856700060564997515 51787022785050090847496273)
  ·
    refine ⟨38840267088787568135622205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51787022785050090847496273 38840267088787568135622205)
    ·
      refine ⟨14565100158295338050858327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38840267088787568135622205 14565100158295338050858327)
      ·
        refine ⟨21847650237443007076287491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14565100158295338050858327 21847650237443007076287491)
        ·
          refine ⟨32771475356164510614431237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21847650237443007076287491 32771475356164510614431237)
          ·
            refine ⟨6144651629280845740205857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32771475356164510614431237 6144651629280845740205857)
            ·
              refine ⟨4608488721960634305154393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6144651629280845740205857 4608488721960634305154393)
              ·
                refine ⟨3456366541470475728865795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4608488721960634305154393 3456366541470475728865795)
                ·
                  refine ⟨5184549812205713593298693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3456366541470475728865795 5184549812205713593298693)
                  ·
                    refine ⟨972103089788571298743505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5184549812205713593298693 972103089788571298743505)
                    ·
                      refine ⟨729077317341428474057629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 972103089788571298743505 729077317341428474057629)
                      ·
                        rfl

theorem cell23_1419873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_1419873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419873 prefixEnd_1419873 := by exact prefixLift 1419873
  have htrace : WordTrace (prefixWord ++ tailWord_1419873) baseStart_1419873 baseEnd_1419873 := by
    simpa [prefixWord, tailWord_1419873, baseEnd_1419873] using wordTrace_append hprefix tailTrace_1419873
  have hstable : (prefixWord ++ tailWord_1419873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419873).length < 2 ^ (prefixWord ++ tailWord_1419873).sum := by decide
  have hdescent : baseEnd_1419873 < baseStart_1419873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419879 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 11]
def baseStart_1419879 : Nat := 118140960795 + 1419879 * 2 ^ 59
def prefixEnd_1419879 : Nat := 4983230072969 + 3 ^ 40 * 1419879 * 2
def baseEnd_1419879 : Nat := 81008933136150605620289

theorem tailTrace_1419879 : CollatzResearch.WordTrace tailWord_1419879 prefixEnd_1419879 81008933136150605620289 := by
  unfold tailWord_1419879
  simp only [CollatzResearch.WordTrace]
  refine ⟨51787241623028353872214691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34524827748685569248143127 51787241623028353872214691)
  ·
    refine ⟨77680862434542530808322037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51787241623028353872214691 77680862434542530808322037)
    ·
      refine ⟨7282580853238362263280191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77680862434542530808322037 7282580853238362263280191)
      ·
        refine ⟨10923871279857543394920287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7282580853238362263280191 10923871279857543394920287)
        ·
          refine ⟨16385806919786315092380431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10923871279857543394920287 16385806919786315092380431)
          ·
            refine ⟨24578710379679472638570647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16385806919786315092380431 24578710379679472638570647)
            ·
              refine ⟨36868065569519208957855971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24578710379679472638570647 36868065569519208957855971)
              ·
                refine ⟨55302098354278813436783957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36868065569519208957855971 55302098354278813436783957)
                ·
                  refine ⟨81008933136150605620289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 55302098354278813436783957 81008933136150605620289)
                  ·
                    rfl

theorem cell23_1419879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 11].length) (baseStart_1419879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419879 prefixEnd_1419879 := by exact prefixLift 1419879
  have htrace : WordTrace (prefixWord ++ tailWord_1419879) baseStart_1419879 baseEnd_1419879 := by
    simpa [prefixWord, tailWord_1419879, baseEnd_1419879] using wordTrace_append hprefix tailTrace_1419879
  have hstable : (prefixWord ++ tailWord_1419879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419879).length < 2 ^ (prefixWord ++ tailWord_1419879).sum := by decide
  have hdescent : baseEnd_1419879 < baseStart_1419879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1419919 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_1419919 : Nat := 118140960795 + 1419919 * 2 ^ 59
def prefixEnd_1419919 : Nat := 4983230072969 + 3 ^ 40 * 1419919 * 2
def baseEnd_1419919 : Nat := 729100937451535294082417

theorem tailTrace_1419919 : CollatzResearch.WordTrace tailWord_1419919 prefixEnd_1419919 729100937451535294082417 := by
  unfold tailWord_1419919
  simp only [CollatzResearch.WordTrace]
  refine ⟨51788700542883440703670811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34525800361922293802447207 51788700542883440703670811)
  ·
    refine ⟨77683050814325161055506217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51788700542883440703670811 77683050814325161055506217)
    ·
      refine ⟨58262288110743870791629663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77683050814325161055506217 58262288110743870791629663)
      ·
        refine ⟨87393432166115806187444495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58262288110743870791629663 87393432166115806187444495)
        ·
          refine ⟨131090148249173709281166743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87393432166115806187444495 131090148249173709281166743)
          ·
            refine ⟨196635222373760563921750115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131090148249173709281166743 196635222373760563921750115)
            ·
              refine ⟨294952833560640845882625173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196635222373760563921750115 294952833560640845882625173)
              ·
                refine ⟨13825914073155039650748055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 294952833560640845882625173 13825914073155039650748055)
                ·
                  refine ⟨20738871109732559476122083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13825914073155039650748055 20738871109732559476122083)
                  ·
                    refine ⟨31108306664598839214183125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20738871109732559476122083 31108306664598839214183125)
                    ·
                      refine ⟨729100937451535294082417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31108306664598839214183125 729100937451535294082417)
                      ·
                        rfl

theorem cell23_1419919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_1419919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1419919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1419919 prefixEnd_1419919 := by exact prefixLift 1419919
  have htrace : WordTrace (prefixWord ++ tailWord_1419919) baseStart_1419919 baseEnd_1419919 := by
    simpa [prefixWord, tailWord_1419919, baseEnd_1419919] using wordTrace_append hprefix tailTrace_1419919
  have hstable : (prefixWord ++ tailWord_1419919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1419919).length < 2 ^ (prefixWord ++ tailWord_1419919).sum := by decide
  have hdescent : baseEnd_1419919 < baseStart_1419919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1419919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
