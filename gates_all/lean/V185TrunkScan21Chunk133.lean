import V185TrunkScan21Chunk132

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1620559 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 4]
def baseStart_1620559 : Nat := 118140960795 + 1620559 * 2 ^ 59
def prefixEnd_1620559 : Nat := 4983230072969 + 3 ^ 40 * 1620559 * 2
def baseEnd_1620559 : Nat := 369833642653169017404307

theorem tailTrace_1620559 : CollatzResearch.WordTrace tailWord_1620559 prefixEnd_1620559 369833642653169017404307 := by
  unfold tailWord_1620559
  simp only [CollatzResearch.WordTrace]
  refine ⟨59106642535998987287568731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39404428357332658191712487 59106642535998987287568731)
  ·
    refine ⟨88659963803998480931353097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59106642535998987287568731 88659963803998480931353097)
    ·
      refine ⟨66494972852998860698514823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88659963803998480931353097 66494972852998860698514823)
      ·
        refine ⟨99742459279498291047772235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66494972852998860698514823 99742459279498291047772235)
        ·
          refine ⟨149613688919247436571658353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99742459279498291047772235 149613688919247436571658353)
          ·
            refine ⟨112210266689435577428743765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149613688919247436571658353 112210266689435577428743765)
            ·
              refine ⟨1314964062766823172993091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 112210266689435577428743765 1314964062766823172993091)
              ·
                refine ⟨1972446094150234759489637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314964062766823172993091 1972446094150234759489637)
                ·
                  refine ⟨369833642653169017404307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1972446094150234759489637 369833642653169017404307)
                  ·
                    rfl

theorem cell21_1620559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 4].length) (baseStart_1620559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620559 prefixEnd_1620559 := by exact prefixLift 1620559
  have htrace : WordTrace (prefixWord ++ tailWord_1620559) baseStart_1620559 baseEnd_1620559 := by
    simpa [prefixWord, tailWord_1620559, baseEnd_1620559] using wordTrace_append hprefix tailTrace_1620559
  have hstable : (prefixWord ++ tailWord_1620559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620559).length < 2 ^ (prefixWord ++ tailWord_1620559).sum := by decide
  have hdescent : baseEnd_1620559 < baseStart_1620559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620638 : List Nat := [4, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1620638 : Nat := 118140960795 + 1620638 * 2 ^ 59
def prefixEnd_1620638 : Nat := 4983230072969 + 3 ^ 40 * 1620638 * 2
def baseEnd_1620638 : Nat := 369851671529482435587479

theorem tailTrace_1620638 : CollatzResearch.WordTrace tailWord_1620638 prefixEnd_1620638 369851671529482435587479 := by
  unfold tailWord_1620638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7388690487839097972461821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39406349268475189186463045 7388690487839097972461821)
  ·
    refine ⟨2770758932939661739673183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7388690487839097972461821 2770758932939661739673183)
    ·
      refine ⟨4156138399409492609509775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2770758932939661739673183 4156138399409492609509775)
      ·
        refine ⟨6234207599114238914264663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4156138399409492609509775 6234207599114238914264663)
        ·
          refine ⟨9351311398671358371396995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6234207599114238914264663 9351311398671358371396995)
          ·
            refine ⟨14026967098007037557095493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9351311398671358371396995 14026967098007037557095493)
            ·
              refine ⟨2630056330876319541955405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14026967098007037557095493 2630056330876319541955405)
              ·
                refine ⟨986271124078619828233277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2630056330876319541955405 986271124078619828233277)
                ·
                  refine ⟨369851671529482435587479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986271124078619828233277 369851671529482435587479)
                  ·
                    rfl

theorem cell21_1620638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1620638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620638 prefixEnd_1620638 := by exact prefixLift 1620638
  have htrace : WordTrace (prefixWord ++ tailWord_1620638) baseStart_1620638 baseEnd_1620638 := by
    simpa [prefixWord, tailWord_1620638, baseEnd_1620638] using wordTrace_append hprefix tailTrace_1620638
  have hstable : (prefixWord ++ tailWord_1620638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620638).length < 2 ^ (prefixWord ++ tailWord_1620638).sum := by decide
  have hdescent : baseEnd_1620638 < baseStart_1620638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620677 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 10]
def baseStart_1620677 : Nat := 118140960795 + 1620677 * 2 ^ 59
def prefixEnd_1620677 : Nat := 4983230072969 + 3 ^ 40 * 1620677 * 2
def baseEnd_1620677 : Nat := 369860571860827034437399

theorem tailTrace_1620677 : CollatzResearch.WordTrace tailWord_1620677 prefixEnd_1620677 369860571860827034437399 := by
  unfold tailWord_1620677
  simp only [CollatzResearch.WordTrace]
  refine ⟨59110946349571493440364285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39407297566380995626909523 59110946349571493440364285)
  ·
    refine ⟨22166604881089310040136607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59110946349571493440364285 22166604881089310040136607)
    ·
      refine ⟨33249907321633965060204911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22166604881089310040136607 33249907321633965060204911)
      ·
        refine ⟨49874860982450947590307367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33249907321633965060204911 49874860982450947590307367)
        ·
          refine ⟨74812291473676421385461051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49874860982450947590307367 74812291473676421385461051)
          ·
            refine ⟨112218437210514632078191577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74812291473676421385461051 112218437210514632078191577)
            ·
              refine ⟨84163827907885974058643683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112218437210514632078191577 84163827907885974058643683)
              ·
                refine ⟨126245741861828961087965525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84163827907885974058643683 126245741861828961087965525)
                ·
                  refine ⟨369860571860827034437399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 126245741861828961087965525 369860571860827034437399)
                  ·
                    rfl

theorem cell21_1620677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_1620677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620677 prefixEnd_1620677 := by exact prefixLift 1620677
  have htrace : WordTrace (prefixWord ++ tailWord_1620677) baseStart_1620677 baseEnd_1620677 := by
    simpa [prefixWord, tailWord_1620677, baseEnd_1620677] using wordTrace_append hprefix tailTrace_1620677
  have hstable : (prefixWord ++ tailWord_1620677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620677).length < 2 ^ (prefixWord ++ tailWord_1620677).sum := by decide
  have hdescent : baseEnd_1620677 < baseStart_1620677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620708 : List Nat := [2, 3, 1, 1, 1, 4, 9]
def baseStart_1620708 : Nat := 118140960795 + 1620708 * 2 ^ 59
def prefixEnd_1620708 : Nat := 4983230072969 + 3 ^ 40 * 1620708 * 2
def baseEnd_1620708 : Nat := 41096405164797541046741

theorem tailTrace_1620708 : CollatzResearch.WordTrace tailWord_1620708 prefixEnd_1620708 41096405164797541046741 := by
  unfold tailWord_1620708
  simp only [CollatzResearch.WordTrace]
  refine ⟨29556038506229592867371389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39408051341639457156495185 29556038506229592867371389)
  ·
    refine ⟨11083514439836097325264271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29556038506229592867371389 11083514439836097325264271)
    ·
      refine ⟨16625271659754145987896407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11083514439836097325264271 16625271659754145987896407)
      ·
        refine ⟨24937907489631218981844611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16625271659754145987896407 24937907489631218981844611)
        ·
          refine ⟨37406861234446828472766917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24937907489631218981844611 37406861234446828472766917)
          ·
            refine ⟨7013786481458780338643797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37406861234446828472766917 7013786481458780338643797)
            ·
              refine ⟨41096405164797541046741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7013786481458780338643797 41096405164797541046741)
              ·
                rfl

theorem cell21_1620708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 9].length) (baseStart_1620708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620708 prefixEnd_1620708 := by exact prefixLift 1620708
  have htrace : WordTrace (prefixWord ++ tailWord_1620708) baseStart_1620708 baseEnd_1620708 := by
    simpa [prefixWord, tailWord_1620708, baseEnd_1620708] using wordTrace_append hprefix tailTrace_1620708
  have hstable : (prefixWord ++ tailWord_1620708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620708).length < 2 ^ (prefixWord ++ tailWord_1620708).sum := by decide
  have hdescent : baseEnd_1620708 < baseStart_1620708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620753 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 8]
def baseStart_1620753 : Nat := 118140960795 + 1620753 * 2 ^ 59
def prefixEnd_1620753 : Nat := 4983230072969 + 3 ^ 40 * 1620753 * 2
def baseEnd_1620753 : Nat := 369877916096267791170577

theorem tailTrace_1620753 : CollatzResearch.WordTrace tailWord_1620753 prefixEnd_1620753 369877916096267791170577 := by
  unfold tailWord_1620753
  simp only [CollatzResearch.WordTrace]
  refine ⟨59113718297296158420130913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39409145531530772280087275 59113718297296158420130913)
  ·
    refine ⟨44335288722972118815098185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59113718297296158420130913 44335288722972118815098185)
    ·
      refine ⟨33251466542229089111323639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44335288722972118815098185 33251466542229089111323639)
      ·
        refine ⟨49877199813343633666985459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33251466542229089111323639 49877199813343633666985459)
        ·
          refine ⟨74815799720015450500478189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49877199813343633666985459 74815799720015450500478189)
          ·
            refine ⟨28055924895005793937679321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74815799720015450500478189 28055924895005793937679321)
            ·
              refine ⟨21041943671254345453259491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28055924895005793937679321 21041943671254345453259491)
              ·
                refine ⟨31562915506881518179889237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21041943671254345453259491 31562915506881518179889237)
                ·
                  refine ⟨369877916096267791170577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31562915506881518179889237 369877916096267791170577)
                  ·
                    rfl

theorem cell21_1620753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_1620753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620753 prefixEnd_1620753 := by exact prefixLift 1620753
  have htrace : WordTrace (prefixWord ++ tailWord_1620753) baseStart_1620753 baseEnd_1620753 := by
    simpa [prefixWord, tailWord_1620753, baseEnd_1620753] using wordTrace_append hprefix tailTrace_1620753
  have hstable : (prefixWord ++ tailWord_1620753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620753).length < 2 ^ (prefixWord ++ tailWord_1620753).sum := by decide
  have hdescent : baseEnd_1620753 < baseStart_1620753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620832 : List Nat := [2, 1, 1, 3, 3, 1, 1, 6, 3]
def baseStart_1620832 : Nat := 118140960795 + 1620832 * 2 ^ 59
def prefixEnd_1620832 : Nat := 4983230072969 + 3 ^ 40 * 1620832 * 2
def baseEnd_1620832 : Nat := 369895944972581209353749

theorem tailTrace_1620832 : CollatzResearch.WordTrace tailWord_1620832 prefixEnd_1620832 369895944972581209353749 := by
  unfold tailWord_1620832
  simp only [CollatzResearch.WordTrace]
  refine ⟨29558299832004977456128375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39411066442673303274837833 29558299832004977456128375)
  ·
    refine ⟨44337449748007466184192563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29558299832004977456128375 44337449748007466184192563)
    ·
      refine ⟨66506174622011199276288845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44337449748007466184192563 66506174622011199276288845)
      ·
        refine ⟨24939815483254199728608317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66506174622011199276288845 24939815483254199728608317)
        ·
          refine ⟨9352430806220324898228119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24939815483254199728608317 9352430806220324898228119)
          ·
            refine ⟨14028646209330487347342179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9352430806220324898228119 14028646209330487347342179)
            ·
              refine ⟨21042969313995731021013269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14028646209330487347342179 21042969313995731021013269)
              ·
                refine ⟨986389186593549891609997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21042969313995731021013269 986389186593549891609997)
                ·
                  refine ⟨369895944972581209353749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986389186593549891609997 369895944972581209353749)
                  ·
                    rfl

theorem cell21_1620832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6, 3].length) (baseStart_1620832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620832 prefixEnd_1620832 := by exact prefixLift 1620832
  have htrace : WordTrace (prefixWord ++ tailWord_1620832) baseStart_1620832 baseEnd_1620832 := by
    simpa [prefixWord, tailWord_1620832, baseEnd_1620832] using wordTrace_append hprefix tailTrace_1620832
  have hstable : (prefixWord ++ tailWord_1620832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620832).length < 2 ^ (prefixWord ++ tailWord_1620832).sum := by decide
  have hdescent : baseEnd_1620832 < baseStart_1620832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620934 : List Nat := [6, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_1620934 : Nat := 118140960795 + 1620934 * 2 ^ 59
def prefixEnd_1620934 : Nat := 4983230072969 + 3 ^ 40 * 1620934 * 2
def baseEnd_1620934 : Nat := 369919222762251698653541

theorem tailTrace_1620934 : CollatzResearch.WordTrace tailWord_1620934 prefixEnd_1620934 369919222762251698653541 := by
  unfold tailWord_1620934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847509997176263322889683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39413546606426950888313237 1847509997176263322889683)
  ·
    refine ⟨2771264995764394984334525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1847509997176263322889683 2771264995764394984334525)
    ·
      refine ⟨1039224373411648119125447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2771264995764394984334525 1039224373411648119125447)
      ·
        refine ⟨1558836560117472178688171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039224373411648119125447 1558836560117472178688171)
        ·
          refine ⟨2338254840176208268032257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558836560117472178688171 2338254840176208268032257)
          ·
            refine ⟨1753691130132156201024193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2338254840176208268032257 1753691130132156201024193)
            ·
              refine ⟨1315268347599117150768145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753691130132156201024193 1315268347599117150768145)
              ·
                refine ⟨986451260699337863076109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315268347599117150768145 986451260699337863076109)
                ·
                  refine ⟨369919222762251698653541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986451260699337863076109 369919222762251698653541)
                  ·
                    rfl

theorem cell21_1620934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_1620934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620934 prefixEnd_1620934 := by exact prefixLift 1620934
  have htrace : WordTrace (prefixWord ++ tailWord_1620934) baseStart_1620934 baseEnd_1620934 := by
    simpa [prefixWord, tailWord_1620934, baseEnd_1620934] using wordTrace_append hprefix tailTrace_1620934
  have hstable : (prefixWord ++ tailWord_1620934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620934).length < 2 ^ (prefixWord ++ tailWord_1620934).sum := by decide
  have hdescent : baseEnd_1620934 < baseStart_1620934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620936 : List Nat := [2, 1, 3, 1, 5, 9]
def baseStart_1620936 : Nat := 118140960795 + 1620936 * 2 ^ 59
def prefixEnd_1620936 : Nat := 4983230072969 + 3 ^ 40 * 1620936 * 2
def baseEnd_1620936 : Nat := 13700728858870375541489

theorem tailTrace_1620936 : CollatzResearch.WordTrace tailWord_1620936 prefixEnd_1620936 13700728858870375541489 := by
  unfold tailWord_1620936
  simp only [CollatzResearch.WordTrace]
  refine ⟨29560196427816590337021331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39413595237088787116028441 29560196427816590337021331)
  ·
    refine ⟨44340294641724885505531997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29560196427816590337021331 44340294641724885505531997)
    ·
      refine ⟨16627610490646832064574499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44340294641724885505531997 16627610490646832064574499)
      ·
        refine ⟨24941415735970248096861749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16627610490646832064574499 24941415735970248096861749)
        ·
          refine ⟨2338257725247210759080789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24941415735970248096861749 2338257725247210759080789)
          ·
            refine ⟨13700728858870375541489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2338257725247210759080789 13700728858870375541489)
            ·
              rfl

theorem cell21_1620936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 9].length) (baseStart_1620936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620936 prefixEnd_1620936 := by exact prefixLift 1620936
  have htrace : WordTrace (prefixWord ++ tailWord_1620936) baseStart_1620936 baseEnd_1620936 := by
    simpa [prefixWord, tailWord_1620936, baseEnd_1620936] using wordTrace_append hprefix tailTrace_1620936
  have hstable : (prefixWord ++ tailWord_1620936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620936).length < 2 ^ (prefixWord ++ tailWord_1620936).sum := by decide
  have hdescent : baseEnd_1620936 < baseStart_1620936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620942 : List Nat := [4, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_1620942 : Nat := 118140960795 + 1620942 * 2 ^ 59
def prefixEnd_1620942 : Nat := 4983230072969 + 3 ^ 40 * 1620942 * 2
def baseEnd_1620942 : Nat := 369921048471245462520191

theorem tailTrace_1620942 : CollatzResearch.WordTrace tailWord_1620942 prefixEnd_1620942 369921048471245462520191 := by
  unfold tailWord_1620942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7390076461701430462345135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39413741129074295799174053 7390076461701430462345135)
  ·
    refine ⟨11085114692552145693517703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7390076461701430462345135 11085114692552145693517703)
    ·
      refine ⟨16627672038828218540276555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11085114692552145693517703 16627672038828218540276555)
      ·
        refine ⟨24941508058242327810414833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16627672038828218540276555 24941508058242327810414833)
        ·
          refine ⟨18706131043681745857811125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24941508058242327810414833 18706131043681745857811125)
          ·
            refine ⟨1753699785345163674169793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18706131043681745857811125 1753699785345163674169793)
            ·
              refine ⟨1315274839008872755627345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753699785345163674169793 1315274839008872755627345)
              ·
                refine ⟨986456129256654566720509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315274839008872755627345 986456129256654566720509)
                ·
                  refine ⟨369921048471245462520191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986456129256654566720509 369921048471245462520191)
                  ·
                    rfl

theorem cell21_1620942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_1620942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620942 prefixEnd_1620942 := by exact prefixLift 1620942
  have htrace : WordTrace (prefixWord ++ tailWord_1620942) baseStart_1620942 baseEnd_1620942 := by
    simpa [prefixWord, tailWord_1620942, baseEnd_1620942] using wordTrace_append hprefix tailTrace_1620942
  have hstable : (prefixWord ++ tailWord_1620942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620942).length < 2 ^ (prefixWord ++ tailWord_1620942).sum := by decide
  have hdescent : baseEnd_1620942 < baseStart_1620942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620953 : List Nat := [1, 2, 1, 2, 5, 3, 1, 6]
def baseStart_1620953 : Nat := 118140960795 + 1620953 * 2 ^ 59
def prefixEnd_1620953 : Nat := 4983230072969 + 3 ^ 40 * 1620953 * 2
def baseEnd_1620953 : Nat := 123307852940370629278945

theorem tailTrace_1620953 : CollatzResearch.WordTrace tailWord_1620953 prefixEnd_1620953 123307852940370629278945 := by
  unfold tailWord_1620953
  simp only [CollatzResearch.WordTrace]
  refine ⟨59121012896571592577411513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39414008597714395051607675 59121012896571592577411513)
  ·
    refine ⟨44340759672428694433058635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59121012896571592577411513 44340759672428694433058635)
    ·
      refine ⟨66511139508643041649587953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44340759672428694433058635 66511139508643041649587953)
      ·
        refine ⟨49883354631482281237190965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66511139508643041649587953 49883354631482281237190965)
        ·
          refine ⟨4676564496701463865986653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49883354631482281237190965 4676564496701463865986653)
          ·
            refine ⟨1753711686263048949744995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4676564496701463865986653 1753711686263048949744995)
            ·
              refine ⟨2630567529394573424617493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753711686263048949744995 2630567529394573424617493)
              ·
                refine ⟨123307852940370629278945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2630567529394573424617493 123307852940370629278945)
                ·
                  rfl

theorem cell21_1620953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 6].length) (baseStart_1620953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620953 prefixEnd_1620953 := by exact prefixLift 1620953
  have htrace : WordTrace (prefixWord ++ tailWord_1620953) baseStart_1620953 baseEnd_1620953 := by
    simpa [prefixWord, tailWord_1620953, baseEnd_1620953] using wordTrace_append hprefix tailTrace_1620953
  have hstable : (prefixWord ++ tailWord_1620953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620953).length < 2 ^ (prefixWord ++ tailWord_1620953).sum := by decide
  have hdescent : baseEnd_1620953 < baseStart_1620953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620967 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 7]
def baseStart_1620967 : Nat := 118140960795 + 1620967 * 2 ^ 59
def prefixEnd_1620967 : Nat := 4983230072969 + 3 ^ 40 * 1620967 * 2
def baseEnd_1620967 : Nat := 369926753811850974603473

theorem tailTrace_1620967 : CollatzResearch.WordTrace tailWord_1620967 prefixEnd_1620967 369926753811850974603473 := by
  unfold tailWord_1620967
  simp only [CollatzResearch.WordTrace]
  refine ⟨59121523518520872968421155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39414349012347248645614103 59121523518520872968421155)
  ·
    refine ⟨88682285277781309452631733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59121523518520872968421155 88682285277781309452631733)
    ·
      refine ⟨8313964244791997761184225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88682285277781309452631733 8313964244791997761184225)
      ·
        refine ⟨6235473183593998320888169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8313964244791997761184225 6235473183593998320888169)
        ·
          refine ⟨4676604887695498740666127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6235473183593998320888169 4676604887695498740666127)
          ·
            refine ⟨7014907331543248110999191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676604887695498740666127 7014907331543248110999191)
            ·
              refine ⟨10522360997314872166498787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7014907331543248110999191 10522360997314872166498787)
              ·
                refine ⟨15783541495972308249748181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10522360997314872166498787 15783541495972308249748181)
                ·
                  refine ⟨369926753811850974603473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15783541495972308249748181 369926753811850974603473)
                  ·
                    rfl

theorem cell21_1620967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 7].length) (baseStart_1620967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1620967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1620967 prefixEnd_1620967 := by exact prefixLift 1620967
  have htrace : WordTrace (prefixWord ++ tailWord_1620967) baseStart_1620967 baseEnd_1620967 := by
    simpa [prefixWord, tailWord_1620967, baseEnd_1620967] using wordTrace_append hprefix tailTrace_1620967
  have hstable : (prefixWord ++ tailWord_1620967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620967).length < 2 ^ (prefixWord ++ tailWord_1620967).sum := by decide
  have hdescent : baseEnd_1620967 < baseStart_1620967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621198 : List Nat := [4, 1, 1, 1, 5, 2, 2, 5]
def baseStart_1621198 : Nat := 118140960795 + 1621198 * 2 ^ 59
def prefixEnd_1621198 : Nat := 4983230072969 + 3 ^ 40 * 1621198 * 2
def baseEnd_1621198 : Nat := 123326490386348635417667

theorem tailTrace_1621198 : CollatzResearch.WordTrace tailWord_1621198 prefixEnd_1621198 123326490386348635417667 := by
  unfold tailWord_1621198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391243597585499927510031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39419965853789332946720165 7391243597585499927510031)
  ·
    refine ⟨11086865396378249891265047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7391243597585499927510031 11086865396378249891265047)
    ·
      refine ⟨16630298094567374836897571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11086865396378249891265047 16630298094567374836897571)
      ·
        refine ⟨24945447141851062255346357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16630298094567374836897571 24945447141851062255346357)
        ·
          refine ⟨2338635669548537086438721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24945447141851062255346357 2338635669548537086438721)
          ·
            refine ⟨1753976752161402814829041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2338635669548537086438721 1753976752161402814829041)
            ·
              refine ⟨1315482564121052111121781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753976752161402814829041 1315482564121052111121781)
              ·
                refine ⟨123326490386348635417667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1315482564121052111121781 123326490386348635417667)
                ·
                  rfl

theorem cell21_1621198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_1621198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621198 prefixEnd_1621198 := by exact prefixLift 1621198
  have htrace : WordTrace (prefixWord ++ tailWord_1621198) baseStart_1621198 baseEnd_1621198 := by
    simpa [prefixWord, tailWord_1621198, baseEnd_1621198] using wordTrace_append hprefix tailTrace_1621198
  have hstable : (prefixWord ++ tailWord_1621198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621198).length < 2 ^ (prefixWord ++ tailWord_1621198).sum := by decide
  have hdescent : baseEnd_1621198 < baseStart_1621198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621330 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_1621330 : Nat := 118140960795 + 1621330 * 2 ^ 59
def prefixEnd_1621330 : Nat := 4983230072969 + 3 ^ 40 * 1621330 * 2
def baseEnd_1621330 : Nat := 370009595357443010052731

theorem tailTrace_1621330 : CollatzResearch.WordTrace tailWord_1621330 prefixEnd_1621330 370009595357443010052731 := by
  unfold tailWord_1621330
  simp only [CollatzResearch.WordTrace]
  refine ⟨14783690804051446490971361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39423175477470523975923629 14783690804051446490971361)
  ·
    refine ⟨11087768103038584868228521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14783690804051446490971361 11087768103038584868228521)
    ·
      refine ⟨8315826077278938651171391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11087768103038584868228521 8315826077278938651171391)
      ·
        refine ⟨12473739115918407976757087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8315826077278938651171391 12473739115918407976757087)
        ·
          refine ⟨18710608673877611965135631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12473739115918407976757087 18710608673877611965135631)
          ·
            refine ⟨28065913010816417947703447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18710608673877611965135631 28065913010816417947703447)
            ·
              refine ⟨42098869516224626921555171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28065913010816417947703447 42098869516224626921555171)
              ·
                refine ⟨63148304274336940382332757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42098869516224626921555171 63148304274336940382332757)
                ·
                  refine ⟨370009595357443010052731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63148304274336940382332757 370009595357443010052731)
                  ·
                    rfl

theorem cell21_1621330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_1621330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621330 prefixEnd_1621330 := by exact prefixLift 1621330
  have htrace : WordTrace (prefixWord ++ tailWord_1621330) baseStart_1621330 baseEnd_1621330 := by
    simpa [prefixWord, tailWord_1621330, baseEnd_1621330] using wordTrace_append hprefix tailTrace_1621330
  have hstable : (prefixWord ++ tailWord_1621330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621330).length < 2 ^ (prefixWord ++ tailWord_1621330).sum := by decide
  have hdescent : baseEnd_1621330 < baseStart_1621330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621347 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 5]
def baseStart_1621347 : Nat := 118140960795 + 1621347 * 2 ^ 59
def prefixEnd_1621347 : Nat := 4983230072969 + 3 ^ 40 * 1621347 * 2
def baseEnd_1621347 : Nat := 370013474989054758269363

theorem tailTrace_1621347 : CollatzResearch.WordTrace tailWord_1621347 prefixEnd_1621347 370013474989054758269363 := by
  unfold tailWord_1621347
  simp only [CollatzResearch.WordTrace]
  refine ⟨59135383257144197867254295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39423588838096131911502863 59135383257144197867254295)
  ·
    refine ⟨88703074885716296800881443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59135383257144197867254295 88703074885716296800881443)
    ·
      refine ⟨133054612328574445201322165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88703074885716296800881443 133054612328574445201322165)
      ·
        refine ⟨12473869905803854237623953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133054612328574445201322165 12473869905803854237623953)
        ·
          refine ⟨9355402429352890678217965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12473869905803854237623953 9355402429352890678217965)
          ·
            refine ⟨3508275911007334004331737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9355402429352890678217965 3508275911007334004331737)
            ·
              refine ⟨2631206933255500503248803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508275911007334004331737 2631206933255500503248803)
              ·
                refine ⟨3946810399883250754873205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631206933255500503248803 3946810399883250754873205)
                ·
                  refine ⟨370013474989054758269363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3946810399883250754873205 370013474989054758269363)
                  ·
                    rfl

theorem cell21_1621347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 5].length) (baseStart_1621347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621347 prefixEnd_1621347 := by exact prefixLift 1621347
  have htrace : WordTrace (prefixWord ++ tailWord_1621347) baseStart_1621347 baseEnd_1621347 := by
    simpa [prefixWord, tailWord_1621347, baseEnd_1621347] using wordTrace_append hprefix tailTrace_1621347
  have hstable : (prefixWord ++ tailWord_1621347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621347).length < 2 ^ (prefixWord ++ tailWord_1621347).sum := by decide
  have hdescent : baseEnd_1621347 < baseStart_1621347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621361 : List Nat := [1, 2, 2, 2, 1, 2, 2, 5, 4]
def baseStart_1621361 : Nat := 118140960795 + 1621361 * 2 ^ 59
def prefixEnd_1621361 : Nat := 4983230072969 + 3 ^ 40 * 1621361 * 2
def baseEnd_1621361 : Nat := 370016669979793845036001

theorem tailTrace_1621361 : CollatzResearch.WordTrace tailWord_1621361 prefixEnd_1621361 370016669979793845036001 := by
  unfold tailWord_1621361
  simp only [CollatzResearch.WordTrace]
  refine ⟨59135893879093478258263937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39423929252728985505509291 59135893879093478258263937)
  ·
    refine ⟨44351920409320108693697953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59135893879093478258263937 44351920409320108693697953)
    ·
      refine ⟨33263940306990081520273465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44351920409320108693697953 33263940306990081520273465)
      ·
        refine ⟨24947955230242561140205099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33263940306990081520273465 24947955230242561140205099)
        ·
          refine ⟨37421932845363841710307649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24947955230242561140205099 37421932845363841710307649)
          ·
            refine ⟨28066449634022881282730737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37421932845363841710307649 28066449634022881282730737)
            ·
              refine ⟨21049837225517160962048053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28066449634022881282730737 21049837225517160962048053)
              ·
                refine ⟨1973422239892233840192005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21049837225517160962048053 1973422239892233840192005)
                ·
                  refine ⟨370016669979793845036001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1973422239892233840192005 370016669979793845036001)
                  ·
                    rfl

theorem cell21_1621361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_1621361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621361 prefixEnd_1621361 := by exact prefixLift 1621361
  have htrace : WordTrace (prefixWord ++ tailWord_1621361) baseStart_1621361 baseEnd_1621361 := by
    simpa [prefixWord, tailWord_1621361, baseEnd_1621361] using wordTrace_append hprefix tailTrace_1621361
  have hstable : (prefixWord ++ tailWord_1621361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621361).length < 2 ^ (prefixWord ++ tailWord_1621361).sum := by decide
  have hdescent : baseEnd_1621361 < baseStart_1621361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621581 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 4]
def baseStart_1621581 : Nat := 118140960795 + 1621581 * 2 ^ 59
def prefixEnd_1621581 : Nat := 4983230072969 + 3 ^ 40 * 1621581 * 2
def baseEnd_1621581 : Nat := 370066876977122351368885

theorem tailTrace_1621581 : CollatzResearch.WordTrace tailWord_1621581 prefixEnd_1621581 370066876977122351368885 := by
  unfold tailWord_1621581
  simp only [CollatzResearch.WordTrace]
  refine ⟨59143917938296455831272597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39429278625530970554181731 59143917938296455831272597)
  ·
    refine ⟨2772371153357646367090903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59143917938296455831272597 2772371153357646367090903)
    ·
      refine ⟨4158556730036469550636355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2772371153357646367090903 4158556730036469550636355)
      ·
        refine ⟨6237835095054704325954533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4158556730036469550636355 6237835095054704325954533)
        ·
          refine ⟨1169594080322757061116475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6237835095054704325954533 1169594080322757061116475)
          ·
            refine ⟨1754391120484135591674713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169594080322757061116475 1754391120484135591674713)
            ·
              refine ⟨1315793340363101693756035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1754391120484135591674713 1315793340363101693756035)
              ·
                refine ⟨1973690010544652540634053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315793340363101693756035 1973690010544652540634053)
                ·
                  refine ⟨370066876977122351368885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1973690010544652540634053 370066876977122351368885)
                  ·
                    rfl

theorem cell21_1621581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_1621581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621581 prefixEnd_1621581 := by exact prefixLift 1621581
  have htrace : WordTrace (prefixWord ++ tailWord_1621581) baseStart_1621581 baseEnd_1621581 := by
    simpa [prefixWord, tailWord_1621581, baseEnd_1621581] using wordTrace_append hprefix tailTrace_1621581
  have hstable : (prefixWord ++ tailWord_1621581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621581).length < 2 ^ (prefixWord ++ tailWord_1621581).sum := by decide
  have hdescent : baseEnd_1621581 < baseStart_1621581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621603 : List Nat := [1, 1, 1, 5, 1, 3, 2, 7]
def baseStart_1621603 : Nat := 118140960795 + 1621603 * 2 ^ 59
def prefixEnd_1621603 : Nat := 4983230072969 + 3 ^ 40 * 1621603 * 2
def baseEnd_1621603 : Nat := 123357299225618400667391

theorem tailTrace_1621603 : CollatzResearch.WordTrace tailWord_1621603 prefixEnd_1621603 123357299225618400667391 := by
  unfold tailWord_1621603
  simp only [CollatzResearch.WordTrace]
  refine ⟨59144720344216753588573463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39429813562811169059048975 59144720344216753588573463)
  ·
    refine ⟨88717080516325130382860195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59144720344216753588573463 88717080516325130382860195)
    ·
      refine ⟨133075620774487695574290293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88717080516325130382860195 133075620774487695574290293)
      ·
        refine ⟨12475839447608221460089715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133075620774487695574290293 12475839447608221460089715)
        ·
          refine ⟨18713759171412332190134573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12475839447608221460089715 18713759171412332190134573)
          ·
            refine ⟨7017659689279624571300465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18713759171412332190134573 7017659689279624571300465)
            ·
              refine ⟨5263244766959718428475349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7017659689279624571300465 5263244766959718428475349)
              ·
                refine ⟨123357299225618400667391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5263244766959718428475349 123357299225618400667391)
                ·
                  rfl

theorem cell21_1621603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 7].length) (baseStart_1621603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621603 prefixEnd_1621603 := by exact prefixLift 1621603
  have htrace : WordTrace (prefixWord ++ tailWord_1621603) baseStart_1621603 baseEnd_1621603 := by
    simpa [prefixWord, tailWord_1621603, baseEnd_1621603] using wordTrace_append hprefix tailTrace_1621603
  have hstable : (prefixWord ++ tailWord_1621603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621603).length < 2 ^ (prefixWord ++ tailWord_1621603).sum := by decide
  have hdescent : baseEnd_1621603 < baseStart_1621603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621668 : List Nat := [2, 3, 1, 2, 2, 3, 2, 3, 3]
def baseStart_1621668 : Nat := 118140960795 + 1621668 * 2 ^ 59
def prefixEnd_1621668 : Nat := 4983230072969 + 3 ^ 40 * 1621668 * 2
def baseEnd_1621668 : Nat := 370086731562429533418707

theorem tailTrace_1621668 : CollatzResearch.WordTrace tailWord_1621668 prefixEnd_1621668 370086731562429533418707 := by
  unfold tailWord_1621668
  simp only [CollatzResearch.WordTrace]
  refine ⟨29573545544490634844844829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39431394059320846459793105 29573545544490634844844829)
  ·
    refine ⟨11090079579183988066816811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29573545544490634844844829 11090079579183988066816811)
    ·
      refine ⟨16635119368775982100225217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11090079579183988066816811 16635119368775982100225217)
      ·
        refine ⟨12476339526581986575168913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16635119368775982100225217 12476339526581986575168913)
        ·
          refine ⟨9357254644936489931376685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12476339526581986575168913 9357254644936489931376685)
          ·
            refine ⟨3508970491851183724266257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9357254644936489931376685 3508970491851183724266257)
            ·
              refine ⟨2631727868888387793199693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508970491851183724266257 2631727868888387793199693)
              ·
                refine ⟨986897950833145422449885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2631727868888387793199693 986897950833145422449885)
                ·
                  refine ⟨370086731562429533418707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986897950833145422449885 370086731562429533418707)
                  ·
                    rfl

theorem cell21_1621668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_1621668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621668 prefixEnd_1621668 := by exact prefixLift 1621668
  have htrace : WordTrace (prefixWord ++ tailWord_1621668) baseStart_1621668 baseEnd_1621668 := by
    simpa [prefixWord, tailWord_1621668, baseEnd_1621668] using wordTrace_append hprefix tailTrace_1621668
  have hstable : (prefixWord ++ tailWord_1621668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621668).length < 2 ^ (prefixWord ++ tailWord_1621668).sum := by decide
  have hdescent : baseEnd_1621668 < baseStart_1621668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621710 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1621710 : Nat := 118140960795 + 1621710 * 2 ^ 59
def prefixEnd_1621710 : Nat := 4983230072969 + 3 ^ 40 * 1621710 * 2
def baseEnd_1621710 : Nat := 370096316534646793718621

theorem tailTrace_1621710 : CollatzResearch.WordTrace tailWord_1621710 prefixEnd_1621710 370096316534646793718621 := by
  unfold tailWord_1621710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393577869353638857839823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39432415303219407241812389 7393577869353638857839823)
  ·
    refine ⟨11090366804030458286759735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7393577869353638857839823 11090366804030458286759735)
    ·
      refine ⟨16635550206045687430139603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11090366804030458286759735 16635550206045687430139603)
      ·
        refine ⟨24953325309068531145209405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16635550206045687430139603 24953325309068531145209405)
        ·
          refine ⟨9357496990900699179453527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24953325309068531145209405 9357496990900699179453527)
          ·
            refine ⟨14036245486351048769180291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9357496990900699179453527 14036245486351048769180291)
            ·
              refine ⟨21054368229526573153770437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14036245486351048769180291 21054368229526573153770437)
              ·
                refine ⟨3947694043036232466331957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21054368229526573153770437 3947694043036232466331957)
                ·
                  refine ⟨370096316534646793718621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3947694043036232466331957 370096316534646793718621)
                  ·
                    rfl

theorem cell21_1621710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1621710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621710 prefixEnd_1621710 := by exact prefixLift 1621710
  have htrace : WordTrace (prefixWord ++ tailWord_1621710) baseStart_1621710 baseEnd_1621710 := by
    simpa [prefixWord, tailWord_1621710, baseEnd_1621710] using wordTrace_append hprefix tailTrace_1621710
  have hstable : (prefixWord ++ tailWord_1621710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621710).length < 2 ^ (prefixWord ++ tailWord_1621710).sum := by decide
  have hdescent : baseEnd_1621710 < baseStart_1621710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621741 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 6]
def baseStart_1621741 : Nat := 118140960795 + 1621741 * 2 ^ 59
def prefixEnd_1621741 : Nat := 4983230072969 + 3 ^ 40 * 1621741 * 2
def baseEnd_1621741 : Nat := 370103391156997628701891

theorem tailTrace_1621741 : CollatzResearch.WordTrace tailWord_1621741 prefixEnd_1621741 370103391156997628701891 := by
  unfold tailWord_1621741
  simp only [CollatzResearch.WordTrace]
  refine ⟨59149753617716803157097077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39433169078477868771398051 59149753617716803157097077)
  ·
    refine ⟨5545289401660950295977851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59149753617716803157097077 5545289401660950295977851)
    ·
      refine ⟨8317934102491425443966777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5545289401660950295977851 8317934102491425443966777)
      ·
        refine ⟨6238450576868569082975083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8317934102491425443966777 6238450576868569082975083)
        ·
          refine ⟨9357675865302853624462625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6238450576868569082975083 9357675865302853624462625)
          ·
            refine ⟨7018256898977140218346969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9357675865302853624462625 7018256898977140218346969)
            ·
              refine ⟨5263692674232855163760227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7018256898977140218346969 5263692674232855163760227)
              ·
                refine ⟨7895539011349282745640341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5263692674232855163760227 7895539011349282745640341)
                ·
                  refine ⟨370103391156997628701891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7895539011349282745640341 370103391156997628701891)
                  ·
                    rfl

theorem cell21_1621741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_1621741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621741 prefixEnd_1621741 := by exact prefixLift 1621741
  have htrace : WordTrace (prefixWord ++ tailWord_1621741) baseStart_1621741 baseEnd_1621741 := by
    simpa [prefixWord, tailWord_1621741, baseEnd_1621741] using wordTrace_append hprefix tailTrace_1621741
  have hstable : (prefixWord ++ tailWord_1621741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621741).length < 2 ^ (prefixWord ++ tailWord_1621741).sum := by decide
  have hdescent : baseEnd_1621741 < baseStart_1621741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621769 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 7]
def baseStart_1621769 : Nat := 118140960795 + 1621769 * 2 ^ 59
def prefixEnd_1621769 : Nat := 4983230072969 + 3 ^ 40 * 1621769 * 2
def baseEnd_1621769 : Nat := 370109781138475802235167

theorem tailTrace_1621769 : CollatzResearch.WordTrace tailWord_1621769 prefixEnd_1621769 370109781138475802235167 := by
  unfold tailWord_1621769
  simp only [CollatzResearch.WordTrace]
  refine ⟨59150774861615363939116361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39433849907743575959410907 59150774861615363939116361)
  ·
    refine ⟨44363081146211522954337271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59150774861615363939116361 44363081146211522954337271)
    ·
      refine ⟨66544621719317284431505907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44363081146211522954337271 66544621719317284431505907)
      ·
        refine ⟨99816932578975926647258861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66544621719317284431505907 99816932578975926647258861)
        ·
          refine ⟨37431349717115972492722073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99816932578975926647258861 37431349717115972492722073)
          ·
            refine ⟨28073512287836979369541555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37431349717115972492722073 28073512287836979369541555)
            ·
              refine ⟨42110268431755469054312333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28073512287836979369541555 42110268431755469054312333)
              ·
                refine ⟨15791350661908300895367125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42110268431755469054312333 15791350661908300895367125)
                ·
                  refine ⟨370109781138475802235167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15791350661908300895367125 370109781138475802235167)
                  ·
                    rfl

theorem cell21_1621769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_1621769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621769 prefixEnd_1621769 := by exact prefixLift 1621769
  have htrace : WordTrace (prefixWord ++ tailWord_1621769) baseStart_1621769 baseEnd_1621769 := by
    simpa [prefixWord, tailWord_1621769, baseEnd_1621769] using wordTrace_append hprefix tailTrace_1621769
  have hstable : (prefixWord ++ tailWord_1621769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621769).length < 2 ^ (prefixWord ++ tailWord_1621769).sum := by decide
  have hdescent : baseEnd_1621769 < baseStart_1621769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621806 : List Nat := [4, 1, 3, 2, 3, 1, 1, 6]
def baseStart_1621806 : Nat := 118140960795 + 1621806 * 2 ^ 59
def prefixEnd_1621806 : Nat := 4983230072969 + 3 ^ 40 * 1621806 * 2
def baseEnd_1621806 : Nat := 123372741680857320039475

theorem tailTrace_1621806 : CollatzResearch.WordTrace tailWord_1621806 prefixEnd_1621806 123372741680857320039475 := by
  unfold tailWord_1621806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7394015545310164907276659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39434749574987546172142181 7394015545310164907276659)
  ·
    refine ⟨11091023317965247360914989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7394015545310164907276659 11091023317965247360914989)
    ·
      refine ⟨4159133744236967760343121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11091023317965247360914989 4159133744236967760343121)
      ·
        refine ⟨3119350308177725820257341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4159133744236967760343121 3119350308177725820257341)
        ·
          refine ⟨1169756365566647182596503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3119350308177725820257341 1169756365566647182596503)
          ·
            refine ⟨1754634548349970773894755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169756365566647182596503 1754634548349970773894755)
            ·
              refine ⟨2631951822524956160842133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754634548349970773894755 2631951822524956160842133)
              ·
                refine ⟨123372741680857320039475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2631951822524956160842133 123372741680857320039475)
                ·
                  rfl

theorem cell21_1621806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_1621806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621806 prefixEnd_1621806 := by exact prefixLift 1621806
  have htrace : WordTrace (prefixWord ++ tailWord_1621806) baseStart_1621806 baseEnd_1621806 := by
    simpa [prefixWord, tailWord_1621806, baseEnd_1621806] using wordTrace_append hprefix tailTrace_1621806
  have hstable : (prefixWord ++ tailWord_1621806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621806).length < 2 ^ (prefixWord ++ tailWord_1621806).sum := by decide
  have hdescent : baseEnd_1621806 < baseStart_1621806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621837 : List Nat := [1, 6, 1, 2, 1, 2, 2, 3, 3]
def baseStart_1621837 : Nat := 118140960795 + 1621837 * 2 ^ 59
def prefixEnd_1621837 : Nat := 4983230072969 + 3 ^ 40 * 1621837 * 2
def baseEnd_1621837 : Nat := 370125299664922795101695

theorem tailTrace_1621837 : CollatzResearch.WordTrace tailWord_1621837 prefixEnd_1621837 370125299664922795101695 := by
  unfold tailWord_1621837
  simp only [CollatzResearch.WordTrace]
  refine ⟨59153255025369011552591765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39435503350246007701727843 59153255025369011552591765)
  ·
    refine ⟨2772808829314172416527739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59153255025369011552591765 2772808829314172416527739)
    ·
      refine ⟨4159213243971258624791609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2772808829314172416527739 4159213243971258624791609)
      ·
        refine ⟨3119409932978443968593707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4159213243971258624791609 3119409932978443968593707)
        ·
          refine ⟨4679114899467665952890561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119409932978443968593707 4679114899467665952890561)
          ·
            refine ⟨3509336174600749464667921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4679114899467665952890561 3509336174600749464667921)
            ·
              refine ⟨2632002130950562098500941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3509336174600749464667921 2632002130950562098500941)
              ·
                refine ⟨987000799106460786937853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2632002130950562098500941 987000799106460786937853)
                ·
                  refine ⟨370125299664922795101695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987000799106460786937853 370125299664922795101695)
                  ·
                    rfl

theorem cell21_1621837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_1621837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621837 prefixEnd_1621837 := by exact prefixLift 1621837
  have htrace : WordTrace (prefixWord ++ tailWord_1621837) baseStart_1621837 baseEnd_1621837 := by
    simpa [prefixWord, tailWord_1621837, baseEnd_1621837] using wordTrace_append hprefix tailTrace_1621837
  have hstable : (prefixWord ++ tailWord_1621837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621837).length < 2 ^ (prefixWord ++ tailWord_1621837).sum := by decide
  have hdescent : baseEnd_1621837 < baseStart_1621837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621927 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 4]
def baseStart_1621927 : Nat := 118140960795 + 1621927 * 2 ^ 59
def prefixEnd_1621927 : Nat := 4983230072969 + 3 ^ 40 * 1621927 * 2
def baseEnd_1621927 : Nat := 370145838891102638601511

theorem tailTrace_1621927 : CollatzResearch.WordTrace tailWord_1621927 prefixEnd_1621927 370145838891102638601511 := by
  unfold tailWord_1621927
  simp only [CollatzResearch.WordTrace]
  refine ⟨59156537595042956923368035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39437691730028637948912023 59156537595042956923368035)
  ·
    refine ⟨88734806392564435385052053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59156537595042956923368035 88734806392564435385052053)
    ·
      refine ⟨4159444049651457908674315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88734806392564435385052053 4159444049651457908674315)
      ·
        refine ⟨6239166074477186863011473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4159444049651457908674315 6239166074477186863011473)
        ·
          refine ⟨4679374555857890147258605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6239166074477186863011473 4679374555857890147258605)
          ·
            refine ⟨1754765458446708805221977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4679374555857890147258605 1754765458446708805221977)
            ·
              refine ⟨1316074093835031603916483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1754765458446708805221977 1316074093835031603916483)
              ·
                refine ⟨1974111140752547405874725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316074093835031603916483 1974111140752547405874725)
                ·
                  refine ⟨370145838891102638601511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1974111140752547405874725 370145838891102638601511)
                  ·
                    rfl

theorem cell21_1621927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 4].length) (baseStart_1621927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621927 prefixEnd_1621927 := by exact prefixLift 1621927
  have htrace : WordTrace (prefixWord ++ tailWord_1621927) baseStart_1621927 baseEnd_1621927 := by
    simpa [prefixWord, tailWord_1621927, baseEnd_1621927] using wordTrace_append hprefix tailTrace_1621927
  have hstable : (prefixWord ++ tailWord_1621927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621927).length < 2 ^ (prefixWord ++ tailWord_1621927).sum := by decide
  have hdescent : baseEnd_1621927 < baseStart_1621927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621983 : List Nat := [1, 1, 2, 3, 4, 1, 3, 6]
def baseStart_1621983 : Nat := 118140960795 + 1621983 * 2 ^ 59
def prefixEnd_1621983 : Nat := 4983230072969 + 3 ^ 40 * 1621983 * 2
def baseEnd_1621983 : Nat := 123386206284686328556021

theorem tailTrace_1621983 : CollatzResearch.WordTrace tailWord_1621983 prefixEnd_1621983 123386206284686328556021 := by
  unfold tailWord_1621983
  simp only [CollatzResearch.WordTrace]
  refine ⟨59158580082840078487406603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39439053388560052324937735 59158580082840078487406603)
  ·
    refine ⟨88737870124260117731109905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59158580082840078487406603 88737870124260117731109905)
    ·
      refine ⟨66553402593195088298332429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88737870124260117731109905 66553402593195088298332429)
      ·
        refine ⟨24957525972448158111874661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66553402593195088298332429 24957525972448158111874661)
        ·
          refine ⟨4679536119834029645976499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24957525972448158111874661 4679536119834029645976499)
          ·
            refine ⟨7019304179751044468964749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679536119834029645976499 7019304179751044468964749)
            ·
              refine ⟨2632239067406641675861781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7019304179751044468964749 2632239067406641675861781)
              ·
                refine ⟨123386206284686328556021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2632239067406641675861781 123386206284686328556021)
                ·
                  rfl

theorem cell21_1621983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 6].length) (baseStart_1621983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1621983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1621983 prefixEnd_1621983 := by exact prefixLift 1621983
  have htrace : WordTrace (prefixWord ++ tailWord_1621983) baseStart_1621983 baseEnd_1621983 := by
    simpa [prefixWord, tailWord_1621983, baseEnd_1621983] using wordTrace_append hprefix tailTrace_1621983
  have hstable : (prefixWord ++ tailWord_1621983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621983).length < 2 ^ (prefixWord ++ tailWord_1621983).sum := by decide
  have hdescent : baseEnd_1621983 < baseStart_1621983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622020 : List Nat := [2, 3, 2, 4, 2, 1, 1, 2, 4]
def baseStart_1622020 : Nat := 118140960795 + 1622020 * 2 ^ 59
def prefixEnd_1622020 : Nat := 4983230072969 + 3 ^ 40 * 1622020 * 2
def baseEnd_1622020 : Nat := 370167062758155143551321

theorem tailTrace_1622020 : CollatzResearch.WordTrace tailWord_1622020 prefixEnd_1622020 370167062758155143551321 := by
  unfold tailWord_1622020
  simp only [CollatzResearch.WordTrace]
  refine ⟨29579964791853016903251757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39439953055804022537669009 29579964791853016903251757)
  ·
    refine ⟨11092486796944881338719409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29579964791853016903251757 11092486796944881338719409)
    ·
      refine ⟨8319365097708661004039557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11092486796944881338719409 8319365097708661004039557)
      ·
        refine ⟨1559880955820373938257417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8319365097708661004039557 1559880955820373938257417)
        ·
          refine ⟨1169910716865280453693063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559880955820373938257417 1169910716865280453693063)
          ·
            refine ⟨1754866075297920680539595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169910716865280453693063 1754866075297920680539595)
            ·
              refine ⟨2632299112946881020809393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754866075297920680539595 2632299112946881020809393)
              ·
                refine ⟨1974224334710160765607045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632299112946881020809393 1974224334710160765607045)
                ·
                  refine ⟨370167062758155143551321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1974224334710160765607045 370167062758155143551321)
                  ·
                    rfl

theorem cell21_1622020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_1622020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622020 prefixEnd_1622020 := by exact prefixLift 1622020
  have htrace : WordTrace (prefixWord ++ tailWord_1622020) baseStart_1622020 baseEnd_1622020 := by
    simpa [prefixWord, tailWord_1622020, baseEnd_1622020] using wordTrace_append hprefix tailTrace_1622020
  have hstable : (prefixWord ++ tailWord_1622020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622020).length < 2 ^ (prefixWord ++ tailWord_1622020).sum := by decide
  have hdescent : baseEnd_1622020 < baseStart_1622020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622028 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_1622028 : Nat := 118140960795 + 1622028 * 2 ^ 59
def prefixEnd_1622028 : Nat := 4983230072969 + 3 ^ 40 * 1622028 * 2
def baseEnd_1622028 : Nat := 370168888467148907417971

theorem tailTrace_1622028 : CollatzResearch.WordTrace tailWord_1622028 prefixEnd_1622028 370168888467148907417971 := by
  unfold tailWord_1622028
  simp only [CollatzResearch.WordTrace]
  refine ⟨29580110683838525586397369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39440147578451367448529825 29580110683838525586397369)
  ·
    refine ⟨22185083012878894189798027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29580110683838525586397369 22185083012878894189798027)
    ·
      refine ⟨33277624519318341284697041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22185083012878894189798027 33277624519318341284697041)
      ·
        refine ⟨24958218389488755963522781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33277624519318341284697041 24958218389488755963522781)
        ·
          refine ⟨9359331896058283486321043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24958218389488755963522781 9359331896058283486321043)
          ·
            refine ⟨14038997844087425229481565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9359331896058283486321043 14038997844087425229481565)
            ·
              refine ⟨5264624191532784461055587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14038997844087425229481565 5264624191532784461055587)
              ·
                refine ⟨7896936287299176691583381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5264624191532784461055587 7896936287299176691583381)
                ·
                  refine ⟨370168888467148907417971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7896936287299176691583381 370168888467148907417971)
                  ·
                    rfl

theorem cell21_1622028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_1622028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622028 prefixEnd_1622028 := by exact prefixLift 1622028
  have htrace : WordTrace (prefixWord ++ tailWord_1622028) baseStart_1622028 baseEnd_1622028 := by
    simpa [prefixWord, tailWord_1622028, baseEnd_1622028] using wordTrace_append hprefix tailTrace_1622028
  have hstable : (prefixWord ++ tailWord_1622028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622028).length < 2 ^ (prefixWord ++ tailWord_1622028).sum := by decide
  have hdescent : baseEnd_1622028 < baseStart_1622028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622152 : List Nat := [2, 1, 3, 4, 1, 3, 1, 6]
def baseStart_1622152 : Nat := 118140960795 + 1622152 * 2 ^ 59
def prefixEnd_1622152 : Nat := 4983230072969 + 3 ^ 40 * 1622152 * 2
def baseEnd_1622152 : Nat := 123399062318850749117017

theorem tailTrace_1622152 : CollatzResearch.WordTrace tailWord_1622152 prefixEnd_1622152 123399062318850749117017 := by
  unfold tailWord_1622152
  simp only [CollatzResearch.WordTrace]
  refine ⟨29582372009613910175154355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39443162679485213566872473 29582372009613910175154355)
  ·
    refine ⟨44373558014420865262731533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29582372009613910175154355 44373558014420865262731533)
    ·
      refine ⟨16640084255407824473524325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44373558014420865262731533 16640084255407824473524325)
      ·
        refine ⟨3120015797888967088785811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16640084255407824473524325 3120015797888967088785811)
        ·
          refine ⟨4680023696833450633178717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120015797888967088785811 4680023696833450633178717)
          ·
            refine ⟨1755008886312543987442019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4680023696833450633178717 1755008886312543987442019)
            ·
              refine ⟨2632513329468815981163029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755008886312543987442019 2632513329468815981163029)
              ·
                refine ⟨123399062318850749117017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2632513329468815981163029 123399062318850749117017)
                ·
                  rfl

theorem cell21_1622152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_1622152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622152 prefixEnd_1622152 := by exact prefixLift 1622152
  have htrace : WordTrace (prefixWord ++ tailWord_1622152) baseStart_1622152 baseEnd_1622152 := by
    simpa [prefixWord, tailWord_1622152, baseEnd_1622152] using wordTrace_append hprefix tailTrace_1622152
  have hstable : (prefixWord ++ tailWord_1622152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622152).length < 2 ^ (prefixWord ++ tailWord_1622152).sum := by decide
  have hdescent : baseEnd_1622152 < baseStart_1622152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622163 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 8]
def baseStart_1622163 : Nat := 118140960795 + 1622163 * 2 ^ 59
def prefixEnd_1622163 : Nat := 4983230072969 + 3 ^ 40 * 1622163 * 2
def baseEnd_1622163 : Nat := 370199697306418672667695

theorem tailTrace_1622163 : CollatzResearch.WordTrace tailWord_1622163 prefixEnd_1622163 370199697306418672667695 := by
  unfold tailWord_1622163
  simp only [CollatzResearch.WordTrace]
  refine ⟨59165145222187969228959143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39443430148125312819306095 59165145222187969228959143)
  ·
    refine ⟨88747717833281953843438715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59165145222187969228959143 88747717833281953843438715)
    ·
      refine ⟨133121576749922930765158073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88747717833281953843438715 133121576749922930765158073)
      ·
        refine ⟨99841182562442198073868555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133121576749922930765158073 99841182562442198073868555)
        ·
          refine ⟨149761773843663297110802833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99841182562442198073868555 149761773843663297110802833)
          ·
            refine ⟨112321330382747472833102125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149761773843663297110802833 112321330382747472833102125)
            ·
              refine ⟨42120498893530302312413297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112321330382747472833102125 42120498893530302312413297)
              ·
                refine ⟨31590374170147726734309973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42120498893530302312413297 31590374170147726734309973)
                ·
                  refine ⟨370199697306418672667695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31590374170147726734309973 370199697306418672667695)
                  ·
                    rfl

theorem cell21_1622163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_1622163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622163 prefixEnd_1622163 := by exact prefixLift 1622163
  have htrace : WordTrace (prefixWord ++ tailWord_1622163) baseStart_1622163 baseEnd_1622163 := by
    simpa [prefixWord, tailWord_1622163, baseEnd_1622163] using wordTrace_append hprefix tailTrace_1622163
  have hstable : (prefixWord ++ tailWord_1622163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622163).length < 2 ^ (prefixWord ++ tailWord_1622163).sum := by decide
  have hdescent : baseEnd_1622163 < baseStart_1622163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622194 : List Nat := [3, 2, 1, 1, 1, 3, 10]
def baseStart_1622194 : Nat := 118140960795 + 1622194 * 2 ^ 59
def prefixEnd_1622194 : Nat := 4983230072969 + 3 ^ 40 * 1622194 * 2
def baseEnd_1622194 : Nat := 41134085769863278627885

theorem tailTrace_1622194 : CollatzResearch.WordTrace tailWord_1622194 prefixEnd_1622194 41134085769863278627885 := by
  unfold tailWord_1622194
  simp only [CollatzResearch.WordTrace]
  refine ⟨14791568971268915380834409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39444183923383774348891757 14791568971268915380834409)
  ·
    refine ⟨11093676728451686535625807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14791568971268915380834409 11093676728451686535625807)
    ·
      refine ⟨16640515092677529803438711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11093676728451686535625807 16640515092677529803438711)
      ·
        refine ⟨24960772639016294705158067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16640515092677529803438711 24960772639016294705158067)
        ·
          refine ⟨37441158958524442057737101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24960772639016294705158067 37441158958524442057737101)
          ·
            refine ⟨14040434609446665771651413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37441158958524442057737101 14040434609446665771651413)
            ·
              refine ⟨41134085769863278627885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14040434609446665771651413 41134085769863278627885)
              ·
                rfl

theorem cell21_1622194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 10].length) (baseStart_1622194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622194 prefixEnd_1622194 := by exact prefixLift 1622194
  have htrace : WordTrace (prefixWord ++ tailWord_1622194) baseStart_1622194 baseEnd_1622194 := by
    simpa [prefixWord, tailWord_1622194, baseEnd_1622194] using wordTrace_append hprefix tailTrace_1622194
  have hstable : (prefixWord ++ tailWord_1622194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622194).length < 2 ^ (prefixWord ++ tailWord_1622194).sum := by decide
  have hdescent : baseEnd_1622194 < baseStart_1622194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622225 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 5]
def baseStart_1622225 : Nat := 118140960795 + 1622225 * 2 ^ 59
def prefixEnd_1622225 : Nat := 4983230072969 + 3 ^ 40 * 1622225 * 2
def baseEnd_1622225 : Nat := 370213846551120342634235

theorem tailTrace_1622225 : CollatzResearch.WordTrace tailWord_1622225 prefixEnd_1622225 370213846551120342634235 := by
  unfold tailWord_1622225
  simp only [CollatzResearch.WordTrace]
  refine ⟨59167406547963353817716129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39444937698642235878477419 59167406547963353817716129)
  ·
    refine ⟨44375554910972515363287097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59167406547963353817716129 44375554910972515363287097)
    ·
      refine ⟨33281666183229386522465323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44375554910972515363287097 33281666183229386522465323)
      ·
        refine ⟨49922499274844079783697985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33281666183229386522465323 49922499274844079783697985)
        ·
          refine ⟨37441874456133059837773489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49922499274844079783697985 37441874456133059837773489)
          ·
            refine ⟨28081405842099794878330117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37441874456133059837773489 28081405842099794878330117)
            ·
              refine ⟨5265263595393711539686897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28081405842099794878330117 5265263595393711539686897)
              ·
                refine ⟨3948947696545283654765173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5265263595393711539686897 3948947696545283654765173)
                ·
                  refine ⟨370213846551120342634235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3948947696545283654765173 370213846551120342634235)
                  ·
                    rfl

theorem cell21_1622225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_1622225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622225 prefixEnd_1622225 := by exact prefixLift 1622225
  have htrace : WordTrace (prefixWord ++ tailWord_1622225) baseStart_1622225 baseEnd_1622225 := by
    simpa [prefixWord, tailWord_1622225, baseEnd_1622225] using wordTrace_append hprefix tailTrace_1622225
  have hstable : (prefixWord ++ tailWord_1622225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622225).length < 2 ^ (prefixWord ++ tailWord_1622225).sum := by decide
  have hdescent : baseEnd_1622225 < baseStart_1622225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622259 : List Nat := [1, 1, 1, 2, 2, 4, 5, 2, 3]
def baseStart_1622259 : Nat := 118140960795 + 1622259 * 2 ^ 59
def prefixEnd_1622259 : Nat := 4983230072969 + 3 ^ 40 * 1622259 * 2
def baseEnd_1622259 : Nat := 370221605814343839067499

theorem tailTrace_1622259 : CollatzResearch.WordTrace tailWord_1622259 prefixEnd_1622259 370221605814343839067499 := by
  unfold tailWord_1622259
  simp only [CollatzResearch.WordTrace]
  refine ⟨59168646629840177624453831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39445764419893451749635887 59168646629840177624453831)
  ·
    refine ⟨88752969944760266436680747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59168646629840177624453831 88752969944760266436680747)
    ·
      refine ⟨133129454917140399655021121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88752969944760266436680747 133129454917140399655021121)
      ·
        refine ⟨99847091187855299741265841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133129454917140399655021121 99847091187855299741265841)
        ·
          refine ⟨74885318390891474805949381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99847091187855299741265841 74885318390891474805949381)
          ·
            refine ⟨14040997198292151526115509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74885318390891474805949381 14040997198292151526115509)
            ·
              refine ⟨1316343487339889205573329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14040997198292151526115509 1316343487339889205573329)
              ·
                refine ⟨987257615504916904179997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316343487339889205573329 987257615504916904179997)
                ·
                  refine ⟨370221605814343839067499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987257615504916904179997 370221605814343839067499)
                  ·
                    rfl

theorem cell21_1622259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 2, 3].length) (baseStart_1622259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622259 prefixEnd_1622259 := by exact prefixLift 1622259
  have htrace : WordTrace (prefixWord ++ tailWord_1622259) baseStart_1622259 baseEnd_1622259 := by
    simpa [prefixWord, tailWord_1622259, baseEnd_1622259] using wordTrace_append hprefix tailTrace_1622259
  have hstable : (prefixWord ++ tailWord_1622259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622259).length < 2 ^ (prefixWord ++ tailWord_1622259).sum := by decide
  have hdescent : baseEnd_1622259 < baseStart_1622259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622332 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 4]
def baseStart_1622332 : Nat := 118140960795 + 1622332 * 2 ^ 59
def prefixEnd_1622332 : Nat := 4983230072969 + 3 ^ 40 * 1622332 * 2
def baseEnd_1622332 : Nat := 370238265408911934350683

theorem tailTrace_1622332 : CollatzResearch.WordTrace tailWord_1622332 prefixEnd_1622332 370238265408911934350683 := by
  unfold tailWord_1622332
  simp only [CollatzResearch.WordTrace]
  refine ⟨29585654579287855545930625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39447539439050474061240833 29585654579287855545930625)
  ·
    refine ⟨22189240934465891659447969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29585654579287855545930625 22189240934465891659447969)
    ·
      refine ⟨16641930700849418744585977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22189240934465891659447969 16641930700849418744585977)
      ·
        refine ⟨12481448025637064058439483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16641930700849418744585977 12481448025637064058439483)
        ·
          refine ⟨18722172038455596087659225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12481448025637064058439483 18722172038455596087659225)
          ·
            refine ⟨14041629028841697065744419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18722172038455596087659225 14041629028841697065744419)
            ·
              refine ⟨21062443543262545598616629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14041629028841697065744419 21062443543262545598616629)
              ·
                refine ⟨1974604082180863649870309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21062443543262545598616629 1974604082180863649870309)
                ·
                  refine ⟨370238265408911934350683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1974604082180863649870309 370238265408911934350683)
                  ·
                    rfl

theorem cell21_1622332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_1622332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622332 prefixEnd_1622332 := by exact prefixLift 1622332
  have htrace : WordTrace (prefixWord ++ tailWord_1622332) baseStart_1622332 baseEnd_1622332 := by
    simpa [prefixWord, tailWord_1622332, baseEnd_1622332] using wordTrace_append hprefix tailTrace_1622332
  have hstable : (prefixWord ++ tailWord_1622332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622332).length < 2 ^ (prefixWord ++ tailWord_1622332).sum := by decide
  have hdescent : baseEnd_1622332 < baseStart_1622332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622377 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 5]
def baseStart_1622377 : Nat := 118140960795 + 1622377 * 2 ^ 59
def prefixEnd_1622377 : Nat := 4983230072969 + 3 ^ 40 * 1622377 * 2
def baseEnd_1622377 : Nat := 370248535022001856100591

theorem tailTrace_1622377 : CollatzResearch.WordTrace tailWord_1622377 prefixEnd_1622377 370248535022001856100591 := by
  unfold tailWord_1622377
  simp only [CollatzResearch.WordTrace]
  refine ⟨59172950443412683777249385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39448633628941789184832923 59172950443412683777249385)
  ·
    refine ⟨44379712832559512832937039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59172950443412683777249385 44379712832559512832937039)
    ·
      refine ⟨66569569248839269249405559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44379712832559512832937039 66569569248839269249405559)
      ·
        refine ⟨99854353873258903874108339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66569569248839269249405559 99854353873258903874108339)
        ·
          refine ⟨149781530809888355811162509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99854353873258903874108339 149781530809888355811162509)
          ·
            refine ⟨56168074053708133429185941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149781530809888355811162509 56168074053708133429185941)
            ·
              refine ⟨2632878471267568754493091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56168074053708133429185941 2632878471267568754493091)
              ·
                refine ⟨3949317706901353131739637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632878471267568754493091 3949317706901353131739637)
                ·
                  refine ⟨370248535022001856100591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3949317706901353131739637 370248535022001856100591)
                  ·
                    rfl

theorem cell21_1622377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_1622377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622377 prefixEnd_1622377 := by exact prefixLift 1622377
  have htrace : WordTrace (prefixWord ++ tailWord_1622377) baseStart_1622377 baseEnd_1622377 := by
    simpa [prefixWord, tailWord_1622377, baseEnd_1622377] using wordTrace_append hprefix tailTrace_1622377
  have hstable : (prefixWord ++ tailWord_1622377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622377).length < 2 ^ (prefixWord ++ tailWord_1622377).sum := by decide
  have hdescent : baseEnd_1622377 < baseStart_1622377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622411 : List Nat := [1, 1, 1, 1, 4, 6, 1, 3, 3]
def baseStart_1622411 : Nat := 118140960795 + 1622411 * 2 ^ 59
def prefixEnd_1622411 : Nat := 4983230072969 + 3 ^ 40 * 1622411 * 2
def baseEnd_1622411 : Nat := 370256294285225352533855

theorem tailTrace_1622411 : CollatzResearch.WordTrace tailWord_1622411 prefixEnd_1622411 370256294285225352533855 := by
  unfold tailWord_1622411
  simp only [CollatzResearch.WordTrace]
  refine ⟨59174190525289507583987087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39449460350193005055991391 59174190525289507583987087)
  ·
    refine ⟨88761285787934261375980631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59174190525289507583987087 88761285787934261375980631)
    ·
      refine ⟨133141928681901392063970947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88761285787934261375980631 133141928681901392063970947)
      ·
        refine ⟨199712893022852088095956421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133141928681901392063970947 199712893022852088095956421)
        ·
          refine ⟨37446167441784766517991829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199712893022852088095956421 37446167441784766517991829)
          ·
            refine ⟨1755289098833660930530867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37446167441784766517991829 1755289098833660930530867)
            ·
              refine ⟨2632933648250491395796301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755289098833660930530867 2632933648250491395796301)
              ·
                refine ⟨987350118093934273423613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2632933648250491395796301 987350118093934273423613)
                ·
                  refine ⟨370256294285225352533855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987350118093934273423613 370256294285225352533855)
                  ·
                    rfl

theorem cell21_1622411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 3].length) (baseStart_1622411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622411 prefixEnd_1622411 := by exact prefixLift 1622411
  have htrace : WordTrace (prefixWord ++ tailWord_1622411) baseStart_1622411 baseEnd_1622411 := by
    simpa [prefixWord, tailWord_1622411, baseEnd_1622411] using wordTrace_append hprefix tailTrace_1622411
  have hstable : (prefixWord ++ tailWord_1622411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622411).length < 2 ^ (prefixWord ++ tailWord_1622411).sum := by decide
  have hdescent : baseEnd_1622411 < baseStart_1622411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622439 : List Nat := [1, 1, 6, 1, 1, 3, 2, 6]
def baseStart_1622439 : Nat := 118140960795 + 1622439 * 2 ^ 59
def prefixEnd_1622439 : Nat := 4983230072969 + 3 ^ 40 * 1622439 * 2
def baseEnd_1622439 : Nat := 123420894755567842022377

theorem tailTrace_1622439 : CollatzResearch.WordTrace tailWord_1622439 prefixEnd_1622439 123420894755567842022377 := by
  unfold tailWord_1622439
  simp only [CollatzResearch.WordTrace]
  refine ⟨59175211769188068366006371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39450141179458712244004247 59175211769188068366006371)
  ·
    refine ⟨88762817653782102549009557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59175211769188068366006371 88762817653782102549009557)
    ·
      refine ⟨4160757077521036056984823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88762817653782102549009557 4160757077521036056984823)
      ·
        refine ⟨6241135616281554085477235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4160757077521036056984823 6241135616281554085477235)
        ·
          refine ⟨9361703424422331128215853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6241135616281554085477235 9361703424422331128215853)
          ·
            refine ⟨3510638784158374173080945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9361703424422331128215853 3510638784158374173080945)
            ·
              refine ⟨2632979088118780629810709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3510638784158374173080945 2632979088118780629810709)
              ·
                refine ⟨123420894755567842022377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2632979088118780629810709 123420894755567842022377)
                ·
                  rfl

theorem cell21_1622439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 6].length) (baseStart_1622439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622439 prefixEnd_1622439 := by exact prefixLift 1622439
  have htrace : WordTrace (prefixWord ++ tailWord_1622439) baseStart_1622439 baseEnd_1622439 := by
    simpa [prefixWord, tailWord_1622439, baseEnd_1622439] using wordTrace_append hprefix tailTrace_1622439
  have hstable : (prefixWord ++ tailWord_1622439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622439).length < 2 ^ (prefixWord ++ tailWord_1622439).sum := by decide
  have hdescent : baseEnd_1622439 < baseStart_1622439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622653 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 4]
def baseStart_1622653 : Nat := 118140960795 + 1622653 * 2 ^ 59
def prefixEnd_1622653 : Nat := 4983230072969 + 3 ^ 40 * 1622653 * 2
def baseEnd_1622653 : Nat := 370311521982286709500027

theorem tailTrace_1622653 : CollatzResearch.WordTrace tailWord_1622653 prefixEnd_1622653 370311521982286709500027 := by
  unfold tailWord_1622653
  simp only [CollatzResearch.WordTrace]
  refine ⟨59183016990412782914296613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39455344660275188609531075 59183016990412782914296613)
  ·
    refine ⟨11096815685702396796430615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59183016990412782914296613 11096815685702396796430615)
    ·
      refine ⟨16645223528553595194645923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11096815685702396796430615 16645223528553595194645923)
      ·
        refine ⟨24967835292830392791968885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16645223528553595194645923 24967835292830392791968885)
        ·
          refine ⟨2340734558702849324247083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24967835292830392791968885 2340734558702849324247083)
          ·
            refine ⟨3511101838054273986370625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340734558702849324247083 3511101838054273986370625)
            ·
              refine ⟨2633326378540705489777969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511101838054273986370625 2633326378540705489777969)
              ·
                refine ⟨1974994783905529117333477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633326378540705489777969 1974994783905529117333477)
                ·
                  refine ⟨370311521982286709500027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1974994783905529117333477 370311521982286709500027)
                  ·
                    rfl

theorem cell21_1622653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_1622653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622653 prefixEnd_1622653 := by exact prefixLift 1622653
  have htrace : WordTrace (prefixWord ++ tailWord_1622653) baseStart_1622653 baseEnd_1622653 := by
    simpa [prefixWord, tailWord_1622653, baseEnd_1622653] using wordTrace_append hprefix tailTrace_1622653
  have hstable : (prefixWord ++ tailWord_1622653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622653).length < 2 ^ (prefixWord ++ tailWord_1622653).sum := by decide
  have hdescent : baseEnd_1622653 < baseStart_1622653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622743 : List Nat := [1, 1, 3, 2, 1, 6, 2, 5]
def baseStart_1622743 : Nat := 118140960795 + 1622743 * 2 ^ 59
def prefixEnd_1622743 : Nat := 4983230072969 + 3 ^ 40 * 1622743 * 2
def baseEnd_1622743 : Nat := 123444020402822184333281

theorem tailTrace_1622743 : CollatzResearch.WordTrace tailWord_1622743 prefixEnd_1622743 123444020402822184333281 := by
  unfold tailWord_1622743
  simp only [CollatzResearch.WordTrace]
  refine ⟨59186299560086728285072883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39457533040057818856715255 59186299560086728285072883)
  ·
    refine ⟨88779449340130092427609325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59186299560086728285072883 88779449340130092427609325)
    ·
      refine ⟨33292293502548784660353497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88779449340130092427609325 33292293502548784660353497)
      ·
        refine ⟨24969220126911588495265123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33292293502548784660353497 24969220126911588495265123)
        ·
          refine ⟨37453830190367382742897685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24969220126911588495265123 37453830190367382742897685)
          ·
            refine ⟨1755648290173471066073329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37453830190367382742897685 1755648290173471066073329)
            ·
              refine ⟨1316736217630103299554997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1755648290173471066073329 1316736217630103299554997)
              ·
                refine ⟨123444020402822184333281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1316736217630103299554997 123444020402822184333281)
                ·
                  rfl

theorem cell21_1622743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 5].length) (baseStart_1622743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622743 prefixEnd_1622743 := by exact prefixLift 1622743
  have htrace : WordTrace (prefixWord ++ tailWord_1622743) baseStart_1622743 baseEnd_1622743 := by
    simpa [prefixWord, tailWord_1622743, baseEnd_1622743] using wordTrace_append hprefix tailTrace_1622743
  have hstable : (prefixWord ++ tailWord_1622743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622743).length < 2 ^ (prefixWord ++ tailWord_1622743).sum := by decide
  have hdescent : baseEnd_1622743 < baseStart_1622743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622771 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 4]
def baseStart_1622771 : Nat := 118140960795 + 1622771 * 2 ^ 59
def prefixEnd_1622771 : Nat := 4983230072969 + 3 ^ 40 * 1622771 * 2
def baseEnd_1622771 : Nat := 370338451189944726533119

theorem tailTrace_1622771 : CollatzResearch.WordTrace tailWord_1622771 prefixEnd_1622771 370338451189944726533119 := by
  unfold tailWord_1622771
  simp only [CollatzResearch.WordTrace]
  refine ⟨59187320803985289067092167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39458213869323526044728111 59187320803985289067092167)
  ·
    refine ⟨88780981205977933600638251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59187320803985289067092167 88780981205977933600638251)
    ·
      refine ⟨133171471808966900400957377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88780981205977933600638251 133171471808966900400957377)
      ·
        refine ⟨99878603856725175300718033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133171471808966900400957377 99878603856725175300718033)
        ·
          refine ⟨74908952892543881475538525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99878603856725175300718033 74908952892543881475538525)
          ·
            refine ⟨28090857334703955553326947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74908952892543881475538525 28090857334703955553326947)
            ·
              refine ⟨42136286002055933329990421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28090857334703955553326947 42136286002055933329990421)
              ·
                refine ⟨1975138406346371874843301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42136286002055933329990421 1975138406346371874843301)
                ·
                  refine ⟨370338451189944726533119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975138406346371874843301 370338451189944726533119)
                  ·
                    rfl

theorem cell21_1622771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 4].length) (baseStart_1622771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622771 prefixEnd_1622771 := by exact prefixLift 1622771
  have htrace : WordTrace (prefixWord ++ tailWord_1622771) baseStart_1622771 baseEnd_1622771 := by
    simpa [prefixWord, tailWord_1622771, baseEnd_1622771] using wordTrace_append hprefix tailTrace_1622771
  have hstable : (prefixWord ++ tailWord_1622771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622771).length < 2 ^ (prefixWord ++ tailWord_1622771).sum := by decide
  have hdescent : baseEnd_1622771 < baseStart_1622771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622788 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 4]
def baseStart_1622788 : Nat := 118140960795 + 1622788 * 2 ^ 59
def prefixEnd_1622788 : Nat := 4983230072969 + 3 ^ 40 * 1622788 * 2
def baseEnd_1622788 : Nat := 370342330821556474749751

theorem tailTrace_1622788 : CollatzResearch.WordTrace tailWord_1622788 prefixEnd_1622788 370342330821556474749751 := by
  unfold tailWord_1622788
  simp only [CollatzResearch.WordTrace]
  refine ⟨29593970422461850485230509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39458627229949133980307345 29593970422461850485230509)
  ·
    refine ⟨11097738908423193931961441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29593970422461850485230509 11097738908423193931961441)
    ·
      refine ⟨8323304181317395448971081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11097738908423193931961441 8323304181317395448971081)
      ·
        refine ⟨6242478135988046586728311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8323304181317395448971081 6242478135988046586728311)
        ·
          refine ⟨9363717203982069880092467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6242478135988046586728311 9363717203982069880092467)
          ·
            refine ⟨14045575805973104820138701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9363717203982069880092467 14045575805973104820138701)
            ·
              refine ⟨5267090927239914307552013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14045575805973104820138701 5267090927239914307552013)
              ·
                refine ⟨1975159097714967865332005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5267090927239914307552013 1975159097714967865332005)
                ·
                  refine ⟨370342330821556474749751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975159097714967865332005 370342330821556474749751)
                  ·
                    rfl

theorem cell21_1622788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_1622788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622788 prefixEnd_1622788 := by exact prefixLift 1622788
  have htrace : WordTrace (prefixWord ++ tailWord_1622788) baseStart_1622788 baseEnd_1622788 := by
    simpa [prefixWord, tailWord_1622788, baseEnd_1622788] using wordTrace_append hprefix tailTrace_1622788
  have hstable : (prefixWord ++ tailWord_1622788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622788).length < 2 ^ (prefixWord ++ tailWord_1622788).sum := by decide
  have hdescent : baseEnd_1622788 < baseStart_1622788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622836 : List Nat := [2, 5, 1, 1, 3, 2, 1, 6]
def baseStart_1622836 : Nat := 118140960795 + 1622836 * 2 ^ 59
def prefixEnd_1622836 : Nat := 4983230072969 + 3 ^ 40 * 1622836 * 2
def baseEnd_1622836 : Nat := 123451095025173019316551

theorem tailTrace_1622836 : CollatzResearch.WordTrace tailWord_1622836 prefixEnd_1622836 123451095025173019316551 := by
  unfold tailWord_1622836
  simp only [CollatzResearch.WordTrace]
  refine ⟨29594845774374902584104181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39459794365833203445472241 29594845774374902584104181)
  ·
    refine ⟨2774516791347647117259767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29594845774374902584104181 2774516791347647117259767)
    ·
      refine ⟨4161775187021470675889651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2774516791347647117259767 4161775187021470675889651)
      ·
        refine ⟨6242662780532206013834477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4161775187021470675889651 6242662780532206013834477)
        ·
          refine ⟨2340998542699577255187929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6242662780532206013834477 2340998542699577255187929)
          ·
            refine ⟨1755748907024682941390947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2340998542699577255187929 1755748907024682941390947)
            ·
              refine ⟨2633623360537024412086421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755748907024682941390947 2633623360537024412086421)
              ·
                refine ⟨123451095025173019316551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2633623360537024412086421 123451095025173019316551)
                ·
                  rfl

theorem cell21_1622836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_1622836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622836 prefixEnd_1622836 := by exact prefixLift 1622836
  have htrace : WordTrace (prefixWord ++ tailWord_1622836) baseStart_1622836 baseEnd_1622836 := by
    simpa [prefixWord, tailWord_1622836, baseEnd_1622836] using wordTrace_append hprefix tailTrace_1622836
  have hstable : (prefixWord ++ tailWord_1622836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622836).length < 2 ^ (prefixWord ++ tailWord_1622836).sum := by decide
  have hdescent : baseEnd_1622836 < baseStart_1622836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622943 : List Nat := [1, 1, 2, 5, 2, 2, 3, 2, 3]
def baseStart_1622943 : Nat := 118140960795 + 1622943 * 2 ^ 59
def prefixEnd_1622943 : Nat := 4983230072969 + 3 ^ 40 * 1622943 * 2
def baseEnd_1622943 : Nat := 370377703933310649666101

theorem tailTrace_1622943 : CollatzResearch.WordTrace tailWord_1622943 prefixEnd_1622943 370377703933310649666101 := by
  unfold tailWord_1622943
  simp only [CollatzResearch.WordTrace]
  refine ⟨59193594159362162442353483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39462396106241441628235655 59193594159362162442353483)
  ·
    refine ⟨88790391239043243663530225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59193594159362162442353483 88790391239043243663530225)
    ·
      refine ⟨66592793429282432747647669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88790391239043243663530225 66592793429282432747647669)
      ·
        refine ⟨6243074383995228070091969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66592793429282432747647669 6243074383995228070091969)
        ·
          refine ⟨4682305787996421052568977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6243074383995228070091969 4682305787996421052568977)
          ·
            refine ⟨3511729340997315789426733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4682305787996421052568977 3511729340997315789426733)
            ·
              refine ⟨1316898502873993421035025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3511729340997315789426733 1316898502873993421035025)
              ·
                refine ⟨987673877155495065776269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316898502873993421035025 987673877155495065776269)
                ·
                  refine ⟨370377703933310649666101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987673877155495065776269 370377703933310649666101)
                  ·
                    rfl

theorem cell21_1622943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 3].length) (baseStart_1622943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1622943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1622943 prefixEnd_1622943 := by exact prefixLift 1622943
  have htrace : WordTrace (prefixWord ++ tailWord_1622943) baseStart_1622943 baseEnd_1622943 := by
    simpa [prefixWord, tailWord_1622943, baseEnd_1622943] using wordTrace_append hprefix tailTrace_1622943
  have hstable : (prefixWord ++ tailWord_1622943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622943).length < 2 ^ (prefixWord ++ tailWord_1622943).sum := by decide
  have hdescent : baseEnd_1622943 < baseStart_1622943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623002 : List Nat := [3, 1, 1, 2, 4, 2, 1, 4, 3]
def baseStart_1623002 : Nat := 118140960795 + 1623002 * 2 ^ 59
def prefixEnd_1623002 : Nat := 4983230072969 + 3 ^ 40 * 1623002 * 2
def baseEnd_1623002 : Nat := 370391168537139658182647

theorem tailTrace_1623002 : CollatzResearch.WordTrace tailWord_1623002 prefixEnd_1623002 370391168537139658182647 := by
  unfold tailWord_1623002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14798936516537103879687815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39463830710765610345834173 14798936516537103879687815)
  ·
    refine ⟨22198404774805655819531723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14798936516537103879687815 22198404774805655819531723)
    ·
      refine ⟨33297607162208483729297585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22198404774805655819531723 33297607162208483729297585)
      ·
        refine ⟨24973205371656362796973189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33297607162208483729297585 24973205371656362796973189)
        ·
          refine ⟨4682476007185568024432473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24973205371656362796973189 4682476007185568024432473)
          ·
            refine ⟨3511857005389176018324355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4682476007185568024432473 3511857005389176018324355)
            ·
              refine ⟨5267785508083764027486533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3511857005389176018324355 5267785508083764027486533)
              ·
                refine ⟨987709782765705755153725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5267785508083764027486533 987709782765705755153725)
                ·
                  refine ⟨370391168537139658182647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987709782765705755153725 370391168537139658182647)
                  ·
                    rfl

theorem cell21_1623002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_1623002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623002 prefixEnd_1623002 := by exact prefixLift 1623002
  have htrace : WordTrace (prefixWord ++ tailWord_1623002) baseStart_1623002 baseEnd_1623002 := by
    simpa [prefixWord, tailWord_1623002, baseEnd_1623002] using wordTrace_append hprefix tailTrace_1623002
  have hstable : (prefixWord ++ tailWord_1623002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623002).length < 2 ^ (prefixWord ++ tailWord_1623002).sum := by decide
  have hdescent : baseEnd_1623002 < baseStart_1623002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623061 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 5]
def baseStart_1623061 : Nat := 118140960795 + 1623061 * 2 ^ 59
def prefixEnd_1623061 : Nat := 4983230072969 + 3 ^ 40 * 1623061 * 2
def baseEnd_1623061 : Nat := 370404633140968666699193

theorem tailTrace_1623061 : CollatzResearch.WordTrace tailWord_1623061 prefixEnd_1623061 370404633140968666699193 := by
  unfold tailWord_1623061
  simp only [CollatzResearch.WordTrace]
  refine ⟨59197897972934668595149037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39465265315289779063432691 59197897972934668595149037)
  ·
    refine ⟨22199211739850500723180889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59197897972934668595149037 22199211739850500723180889)
    ·
      refine ⟨16649408804887875542385667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22199211739850500723180889 16649408804887875542385667)
      ·
        refine ⟨24974113207331813313578501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16649408804887875542385667 24974113207331813313578501)
        ·
          refine ⟨4682646226374714996295969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24974113207331813313578501 4682646226374714996295969)
          ·
            refine ⟨3511984669781036247221977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4682646226374714996295969 3511984669781036247221977)
            ·
              refine ⟨2633988502335777185416483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511984669781036247221977 2633988502335777185416483)
              ·
                refine ⟨3950982753503665778124725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633988502335777185416483 3950982753503665778124725)
                ·
                  refine ⟨370404633140968666699193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3950982753503665778124725 370404633140968666699193)
                  ·
                    rfl

theorem cell21_1623061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_1623061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623061 prefixEnd_1623061 := by exact prefixLift 1623061
  have htrace : WordTrace (prefixWord ++ tailWord_1623061) baseStart_1623061 baseEnd_1623061 := by
    simpa [prefixWord, tailWord_1623061, baseEnd_1623061] using wordTrace_append hprefix tailTrace_1623061
  have hstable : (prefixWord ++ tailWord_1623061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623061).length < 2 ^ (prefixWord ++ tailWord_1623061).sum := by decide
  have hdescent : baseEnd_1623061 < baseStart_1623061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623089 : List Nat := [1, 2, 2, 3, 1, 2, 3, 7]
def baseStart_1623089 : Nat := 118140960795 + 1623089 * 2 ^ 59
def prefixEnd_1623089 : Nat := 4983230072969 + 3 ^ 40 * 1623089 * 2
def baseEnd_1623089 : Nat := 123470341040815613410823

theorem tailTrace_1623089 : CollatzResearch.WordTrace tailWord_1623089 prefixEnd_1623089 123470341040815613410823 := by
  unfold tailWord_1623089
  simp only [CollatzResearch.WordTrace]
  refine ⟨59198919216833229377168321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39465946144555486251445547 59198919216833229377168321)
  ·
    refine ⟨44399189412624922032876241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59198919216833229377168321 44399189412624922032876241)
    ·
      refine ⟨33299392059468691524657181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44399189412624922032876241 33299392059468691524657181)
      ·
        refine ⟨12487272022300759321746443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33299392059468691524657181 12487272022300759321746443)
        ·
          refine ⟨18730908033451138982619665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12487272022300759321746443 18730908033451138982619665)
          ·
            refine ⟨14048181025088354236964749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18730908033451138982619665 14048181025088354236964749)
            ·
              refine ⟨5268067884408132838861781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14048181025088354236964749 5268067884408132838861781)
              ·
                refine ⟨123470341040815613410823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5268067884408132838861781 123470341040815613410823)
                ·
                  rfl

theorem cell21_1623089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 7].length) (baseStart_1623089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623089 prefixEnd_1623089 := by exact prefixLift 1623089
  have htrace : WordTrace (prefixWord ++ tailWord_1623089) baseStart_1623089 baseEnd_1623089 := by
    simpa [prefixWord, tailWord_1623089, baseEnd_1623089] using wordTrace_append hprefix tailTrace_1623089
  have hstable : (prefixWord ++ tailWord_1623089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623089).length < 2 ^ (prefixWord ++ tailWord_1623089).sum := by decide
  have hdescent : baseEnd_1623089 < baseStart_1623089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623092 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1623092 : Nat := 118140960795 + 1623092 * 2 ^ 59
def prefixEnd_1623092 : Nat := 4983230072969 + 3 ^ 40 * 1623092 * 2
def baseEnd_1623092 : Nat := 370411707763319501682463

theorem tailTrace_1623092 : CollatzResearch.WordTrace tailWord_1623092 prefixEnd_1623092 370411707763319501682463 := by
  unfold tailWord_1623092
  simp only [CollatzResearch.WordTrace]
  refine ⟨29599514317911180444763765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39466019090548240593018353 29599514317911180444763765)
  ·
    refine ⟨2774954467304173166696603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29599514317911180444763765 2774954467304173166696603)
    ·
      refine ⟨4162431700956259750044905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2774954467304173166696603 4162431700956259750044905)
      ·
        refine ⟨3121823775717194812533679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4162431700956259750044905 3121823775717194812533679)
        ·
          refine ⟨4682735663575792218800519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3121823775717194812533679 4682735663575792218800519)
          ·
            refine ⟨7024103495363688328200779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682735663575792218800519 7024103495363688328200779)
            ·
              refine ⟨10536155243045532492301169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024103495363688328200779 10536155243045532492301169)
              ·
                refine ⟨7902116432284149369225877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10536155243045532492301169 7902116432284149369225877)
                ·
                  refine ⟨370411707763319501682463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7902116432284149369225877 370411707763319501682463)
                  ·
                    rfl

theorem cell21_1623092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1623092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623092 prefixEnd_1623092 := by exact prefixLift 1623092
  have htrace : WordTrace (prefixWord ++ tailWord_1623092) baseStart_1623092 baseEnd_1623092 := by
    simpa [prefixWord, tailWord_1623092, baseEnd_1623092] using wordTrace_append hprefix tailTrace_1623092
  have hstable : (prefixWord ++ tailWord_1623092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623092).length < 2 ^ (prefixWord ++ tailWord_1623092).sum := by decide
  have hdescent : baseEnd_1623092 < baseStart_1623092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623126 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_1623126 : Nat := 118140960795 + 1623126 * 2 ^ 59
def prefixEnd_1623126 : Nat := 4983230072969 + 3 ^ 40 * 1623126 * 2
def baseEnd_1623126 : Nat := 370419467026542998115727

theorem tailTrace_1623126 : CollatzResearch.WordTrace tailWord_1623126 prefixEnd_1623126 370419467026542998115727 := by
  unfold tailWord_1623126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3700016794856199043516577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39466845811799456464176821 3700016794856199043516577)
  ·
    refine ⟨2775012596142149282637433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3700016794856199043516577 2775012596142149282637433)
    ·
      refine ⟨2081259447106611961978075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2775012596142149282637433 2081259447106611961978075)
      ·
        refine ⟨3121889170659917942967113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081259447106611961978075 3121889170659917942967113)
        ·
          refine ⟨2341416877994938457225335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3121889170659917942967113 2341416877994938457225335)
          ·
            refine ⟨3512125316992407685838003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341416877994938457225335 3512125316992407685838003)
            ·
              refine ⟨5268187975488611528757005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512125316992407685838003 5268187975488611528757005)
              ·
                refine ⟨1975570490808229323283877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5268187975488611528757005 1975570490808229323283877)
                ·
                  refine ⟨370419467026542998115727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975570490808229323283877 370419467026542998115727)
                  ·
                    rfl

theorem cell21_1623126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_1623126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623126 prefixEnd_1623126 := by exact prefixLift 1623126
  have htrace : WordTrace (prefixWord ++ tailWord_1623126) baseStart_1623126 baseEnd_1623126 := by
    simpa [prefixWord, tailWord_1623126, baseEnd_1623126] using wordTrace_append hprefix tailTrace_1623126
  have hstable : (prefixWord ++ tailWord_1623126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623126).length < 2 ^ (prefixWord ++ tailWord_1623126).sum := by decide
  have hdescent : baseEnd_1623126 < baseStart_1623126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623179 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 9]
def baseStart_1623179 : Nat := 118140960795 + 1623179 * 2 ^ 59
def prefixEnd_1623179 : Nat := 4983230072969 + 3 ^ 40 * 1623179 * 2
def baseEnd_1623179 : Nat := 370431562348626683732285

theorem tailTrace_1623179 : CollatzResearch.WordTrace tailWord_1623179 prefixEnd_1623179 370431562348626683732285 := by
  unfold tailWord_1623179
  simp only [CollatzResearch.WordTrace]
  refine ⟨59202201786507174747944591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39468134524338116498629727 59202201786507174747944591)
  ·
    refine ⟨88803302679760762121916887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59202201786507174747944591 88803302679760762121916887)
    ·
      refine ⟨133204954019641143182875331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88803302679760762121916887 133204954019641143182875331)
      ·
        refine ⟨199807431029461714774312997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133204954019641143182875331 199807431029461714774312997)
        ·
          refine ⟨37463893318024071520183687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199807431029461714774312997 37463893318024071520183687)
          ·
            refine ⟨56195839977036107280275531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37463893318024071520183687 56195839977036107280275531)
            ·
              refine ⟨84293759965554160920413297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56195839977036107280275531 84293759965554160920413297)
              ·
                refine ⟨63220319974165620690309973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84293759965554160920413297 63220319974165620690309973)
                ·
                  refine ⟨370431562348626683732285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63220319974165620690309973 370431562348626683732285)
                  ·
                    rfl

theorem cell21_1623179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_1623179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623179 prefixEnd_1623179 := by exact prefixLift 1623179
  have htrace : WordTrace (prefixWord ++ tailWord_1623179) baseStart_1623179 baseEnd_1623179 := by
    simpa [prefixWord, tailWord_1623179, baseEnd_1623179] using wordTrace_append hprefix tailTrace_1623179
  have hstable : (prefixWord ++ tailWord_1623179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623179).length < 2 ^ (prefixWord ++ tailWord_1623179).sum := by decide
  have hdescent : baseEnd_1623179 < baseStart_1623179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623182 : List Nat := [4, 1, 1, 3, 2, 1, 3, 6]
def baseStart_1623182 : Nat := 118140960795 + 1623182 * 2 ^ 59
def prefixEnd_1623182 : Nat := 4983230072969 + 3 ^ 40 * 1623182 * 2
def baseEnd_1623182 : Nat := 123477415663166448394093

theorem tailTrace_1623182 : CollatzResearch.WordTrace tailWord_1623182 prefixEnd_1623182 123477415663166448394093 := by
  unfold tailWord_1623182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7400288900687038282537975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39468207470330870840202533 7400288900687038282537975)
  ·
    refine ⟨11100433351030557423806963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7400288900687038282537975 11100433351030557423806963)
    ·
      refine ⟨16650650026545836135710445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11100433351030557423806963 16650650026545836135710445)
      ·
        refine ⟨6243993759954688550891417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16650650026545836135710445 6243993759954688550891417)
        ·
          refine ⟨4682995319966016413168563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6243993759954688550891417 4682995319966016413168563)
          ·
            refine ⟨7024492979949024619752845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682995319966016413168563 7024492979949024619752845)
            ·
              refine ⟨2634184867480884232407317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7024492979949024619752845 2634184867480884232407317)
              ·
                refine ⟨123477415663166448394093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2634184867480884232407317 123477415663166448394093)
                ·
                  rfl

theorem cell21_1623182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_1623182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623182 prefixEnd_1623182 := by exact prefixLift 1623182
  have htrace : WordTrace (prefixWord ++ tailWord_1623182) baseStart_1623182 baseEnd_1623182 := by
    simpa [prefixWord, tailWord_1623182, baseEnd_1623182] using wordTrace_append hprefix tailTrace_1623182
  have hstable : (prefixWord ++ tailWord_1623182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623182).length < 2 ^ (prefixWord ++ tailWord_1623182).sum := by decide
  have hdescent : baseEnd_1623182 < baseStart_1623182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623196 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_1623196 : Nat := 118140960795 + 1623196 * 2 ^ 59
def prefixEnd_1623196 : Nat := 4983230072969 + 3 ^ 40 * 1623196 * 2
def baseEnd_1623196 : Nat := 370435441980238431948917

theorem tailTrace_1623196 : CollatzResearch.WordTrace tailWord_1623196 prefixEnd_1623196 370435441980238431948917 := by
  unfold tailWord_1623196
  simp only [CollatzResearch.WordTrace]
  refine ⟨29601410913722793325656721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39468547884963724434208961 29601410913722793325656721)
  ·
    refine ⟨22201058185292094994242541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29601410913722793325656721 22201058185292094994242541)
    ·
      refine ⟨8325396819484535622840953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22201058185292094994242541 8325396819484535622840953)
      ·
        refine ⟨6244047614613401717130715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8325396819484535622840953 6244047614613401717130715)
        ·
          refine ⟨9366071421920102575696073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6244047614613401717130715 9366071421920102575696073)
          ·
            refine ⟨7024553566440076931772055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9366071421920102575696073 7024553566440076931772055)
            ·
              refine ⟨10536830349660115397658083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024553566440076931772055 10536830349660115397658083)
              ·
                refine ⟨15805245524490173096487125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10536830349660115397658083 15805245524490173096487125)
                ·
                  refine ⟨370435441980238431948917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15805245524490173096487125 370435441980238431948917)
                  ·
                    rfl

theorem cell21_1623196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_1623196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623196 prefixEnd_1623196 := by exact prefixLift 1623196
  have htrace : WordTrace (prefixWord ++ tailWord_1623196) baseStart_1623196 baseEnd_1623196 := by
    simpa [prefixWord, tailWord_1623196, baseEnd_1623196] using wordTrace_append hprefix tailTrace_1623196
  have hstable : (prefixWord ++ tailWord_1623196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623196).length < 2 ^ (prefixWord ++ tailWord_1623196).sum := by decide
  have hdescent : baseEnd_1623196 < baseStart_1623196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623199 : List Nat := [1, 1, 2, 6, 2, 1, 3, 5]
def baseStart_1623199 : Nat := 118140960795 + 1623199 * 2 ^ 59
def prefixEnd_1623199 : Nat := 4983230072969 + 3 ^ 40 * 1623199 * 2
def baseEnd_1623199 : Nat := 123478708873703697799637

theorem tailTrace_1623199 : CollatzResearch.WordTrace tailWord_1623199 prefixEnd_1623199 123478708873703697799637 := by
  unfold tailWord_1623199
  simp only [CollatzResearch.WordTrace]
  refine ⟨59202931246434718163672651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39468620830956478775781767 59202931246434718163672651)
  ·
    refine ⟨88804396869652077245508977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59202931246434718163672651 88804396869652077245508977)
    ·
      refine ⟨66603297652239057934131733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88804396869652077245508977 66603297652239057934131733)
      ·
        refine ⟨3122029577448705840662425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66603297652239057934131733 3122029577448705840662425)
        ·
          refine ⟨2341522183086529380496819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3122029577448705840662425 2341522183086529380496819)
          ·
            refine ⟨3512283274629794070745229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341522183086529380496819 3512283274629794070745229)
            ·
              refine ⟨1317106227986172776529461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3512283274629794070745229 1317106227986172776529461)
              ·
                refine ⟨123478708873703697799637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1317106227986172776529461 123478708873703697799637)
                ·
                  rfl

theorem cell21_1623199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 5].length) (baseStart_1623199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623199 prefixEnd_1623199 := by exact prefixLift 1623199
  have htrace : WordTrace (prefixWord ++ tailWord_1623199) baseStart_1623199 baseEnd_1623199 := by
    simpa [prefixWord, tailWord_1623199, baseEnd_1623199] using wordTrace_append hprefix tailTrace_1623199
  have hstable : (prefixWord ++ tailWord_1623199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623199).length < 2 ^ (prefixWord ++ tailWord_1623199).sum := by decide
  have hdescent : baseEnd_1623199 < baseStart_1623199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623230 : List Nat := [4, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_1623230 : Nat := 118140960795 + 1623230 * 2 ^ 59
def prefixEnd_1623230 : Nat := 4983230072969 + 3 ^ 40 * 1623230 * 2
def baseEnd_1623230 : Nat := 370443201243461928382181

theorem tailTrace_1623230 : CollatzResearch.WordTrace tailWord_1623230 prefixEnd_1623230 370443201243461928382181 := by
  unfold tailWord_1623230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7400507738665301307256393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39469374606214940305367429 7400507738665301307256393)
  ·
    refine ⟨5550380803998975980442295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7400507738665301307256393 5550380803998975980442295)
    ·
      refine ⟨8325571205998463970663443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5550380803998975980442295 8325571205998463970663443)
      ·
        refine ⟨12488356808997695955995165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8325571205998463970663443 12488356808997695955995165)
        ·
          refine ⟨4683133803374135983498187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12488356808997695955995165 4683133803374135983498187)
          ·
            refine ⟨7024700705061203975247281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4683133803374135983498187 7024700705061203975247281)
            ·
              refine ⟨5268525528795902981435461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7024700705061203975247281 5268525528795902981435461)
              ·
                refine ⟨987848536649231809019149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5268525528795902981435461 987848536649231809019149)
                ·
                  refine ⟨370443201243461928382181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987848536649231809019149 370443201243461928382181)
                  ·
                    rfl

theorem cell21_1623230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_1623230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623230 prefixEnd_1623230 := by exact prefixLift 1623230
  have htrace : WordTrace (prefixWord ++ tailWord_1623230) baseStart_1623230 baseEnd_1623230 := by
    simpa [prefixWord, tailWord_1623230, baseEnd_1623230] using wordTrace_append hprefix tailTrace_1623230
  have hstable : (prefixWord ++ tailWord_1623230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623230).length < 2 ^ (prefixWord ++ tailWord_1623230).sum := by decide
  have hdescent : baseEnd_1623230 < baseStart_1623230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623396 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1623396 : Nat := 118140960795 + 1623396 * 2 ^ 59
def prefixEnd_1623396 : Nat := 4983230072969 + 3 ^ 40 * 1623396 * 2
def baseEnd_1623396 : Nat := 370481084705082528615175

theorem tailTrace_1623396 : CollatzResearch.WordTrace tailWord_1623396 prefixEnd_1623396 370481084705082528615175 := by
  unfold tailWord_1623396
  simp only [CollatzResearch.WordTrace]
  refine ⟨29605058213360510404297021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39473410951147347205729361 29605058213360510404297021)
  ·
    refine ⟨11101896830010191401611383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29605058213360510404297021 11101896830010191401611383)
    ·
      refine ⟨16652845245015287102417075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11101896830010191401611383 16652845245015287102417075)
      ·
        refine ⟨24979267867522930653625613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16652845245015287102417075 24979267867522930653625613)
        ·
          refine ⟨9367225450321098995109605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24979267867522930653625613 9367225450321098995109605)
          ·
            refine ⟨1756354771935206061583051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9367225450321098995109605 1756354771935206061583051)
            ·
              refine ⟨2634532157902809092374577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756354771935206061583051 2634532157902809092374577)
              ·
                refine ⟨1975899118427106819280933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2634532157902809092374577 1975899118427106819280933)
                ·
                  refine ⟨370481084705082528615175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975899118427106819280933 370481084705082528615175)
                  ·
                    rfl

theorem cell21_1623396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1623396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623396 prefixEnd_1623396 := by exact prefixLift 1623396
  have htrace : WordTrace (prefixWord ++ tailWord_1623396) baseStart_1623396 baseEnd_1623396 := by
    simpa [prefixWord, tailWord_1623396, baseEnd_1623396] using wordTrace_append hprefix tailTrace_1623396
  have hstable : (prefixWord ++ tailWord_1623396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623396).length < 2 ^ (prefixWord ++ tailWord_1623396).sum := by decide
  have hdescent : baseEnd_1623396 < baseStart_1623396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623413 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 4]
def baseStart_1623413 : Nat := 118140960795 + 1623413 * 2 ^ 59
def prefixEnd_1623413 : Nat := 4983230072969 + 3 ^ 40 * 1623413 * 2
def baseEnd_1623413 : Nat := 370484964336694276831807

theorem tailTrace_1623413 : CollatzResearch.WordTrace tailWord_1623413 prefixEnd_1623413 370484964336694276831807 := by
  unfold tailWord_1623413
  simp only [CollatzResearch.WordTrace]
  refine ⟨59210736467659432711962893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39473824311772955141308595 59210736467659432711962893)
  ·
    refine ⟨22204026175372287266986085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59210736467659432711962893 22204026175372287266986085)
    ·
      refine ⟨4163254907882303862559891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22204026175372287266986085 4163254907882303862559891)
      ·
        refine ⟨6244882361823455793839837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4163254907882303862559891 6244882361823455793839837)
        ·
          refine ⟨2341830885683795922689939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6244882361823455793839837 2341830885683795922689939)
          ·
            refine ⟨3512746328525693884034909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341830885683795922689939 3512746328525693884034909)
            ·
              refine ⟨1317279873197135206513091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3512746328525693884034909 1317279873197135206513091)
              ·
                refine ⟨1975919809795702809769637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1317279873197135206513091 1975919809795702809769637)
                ·
                  refine ⟨370484964336694276831807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975919809795702809769637 370484964336694276831807)
                  ·
                    rfl

theorem cell21_1623413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_1623413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623413 prefixEnd_1623413 := by exact prefixLift 1623413
  have htrace : WordTrace (prefixWord ++ tailWord_1623413) baseStart_1623413 baseEnd_1623413 := by
    simpa [prefixWord, tailWord_1623413, baseEnd_1623413] using wordTrace_append hprefix tailTrace_1623413
  have hstable : (prefixWord ++ tailWord_1623413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623413).length < 2 ^ (prefixWord ++ tailWord_1623413).sum := by decide
  have hdescent : baseEnd_1623413 < baseStart_1623413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623565 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1623565 : Nat := 118140960795 + 1623565 * 2 ^ 59
def prefixEnd_1623565 : Nat := 4983230072969 + 3 ^ 40 * 1623565 * 2
def baseEnd_1623565 : Nat := 370519652807575790298163

theorem tailTrace_1623565 : CollatzResearch.WordTrace tailWord_1623565 prefixEnd_1623565 370519652807575790298163 := by
  unfold tailWord_1623565
  simp only [CollatzResearch.WordTrace]
  refine ⟨59216280363108762671496149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39477520242072508447664099 59216280363108762671496149)
  ·
    refine ⟨1387881571010361625113191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 59216280363108762671496149 1387881571010361625113191)
    ·
      refine ⟨2081822356515542437669787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387881571010361625113191 2081822356515542437669787)
      ·
        refine ⟨3122733534773313656504681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081822356515542437669787 3122733534773313656504681)
        ·
          refine ⟨2342050151079985242378511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3122733534773313656504681 2342050151079985242378511)
          ·
            refine ⟨3513075226619977863567767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342050151079985242378511 3513075226619977863567767)
            ·
              refine ⟨5269612839929966795351651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3513075226619977863567767 5269612839929966795351651)
              ·
                refine ⟨7904419259894950193027477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5269612839929966795351651 7904419259894950193027477)
                ·
                  refine ⟨370519652807575790298163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7904419259894950193027477 370519652807575790298163)
                  ·
                    rfl

theorem cell21_1623565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1623565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623565 prefixEnd_1623565 := by exact prefixLift 1623565
  have htrace : WordTrace (prefixWord ++ tailWord_1623565) baseStart_1623565 baseEnd_1623565 := by
    simpa [prefixWord, tailWord_1623565, baseEnd_1623565] using wordTrace_append hprefix tailTrace_1623565
  have hstable : (prefixWord ++ tailWord_1623565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623565).length < 2 ^ (prefixWord ++ tailWord_1623565).sum := by decide
  have hdescent : baseEnd_1623565 < baseStart_1623565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623720 : List Nat := [2, 1, 7, 1, 1, 1, 2, 3, 3]
def baseStart_1623720 : Nat := 118140960795 + 1623720 * 2 ^ 59
def prefixEnd_1623720 : Nat := 4983230072969 + 3 ^ 40 * 1623720 * 2
def baseEnd_1623720 : Nat := 370555025919329965214513

theorem tailTrace_1623720 : CollatzResearch.WordTrace tailWord_1623720 prefixEnd_1623720 370555025919329965214513 := by
  unfold tailWord_1623720
  simp only [CollatzResearch.WordTrace]
  refine ⟨29610966838773612071694307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39481289118364816095592409 29610966838773612071694307)
  ·
    refine ⟨44416450258160418107541461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29610966838773612071694307 44416450258160418107541461)
    ·
      refine ⟨1041010552925634799395503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 44416450258160418107541461 1041010552925634799395503)
      ·
        refine ⟨1561515829388452199093255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041010552925634799395503 1561515829388452199093255)
        ·
          refine ⟨2342273744082678298639883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1561515829388452199093255 2342273744082678298639883)
          ·
            refine ⟨3513410616124017447959825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342273744082678298639883 3513410616124017447959825)
            ·
              refine ⟨2635057962093013085969869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3513410616124017447959825 2635057962093013085969869)
              ·
                refine ⟨988146735784879907238701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2635057962093013085969869 988146735784879907238701)
                ·
                  refine ⟨370555025919329965214513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988146735784879907238701 370555025919329965214513)
                  ·
                    rfl

theorem cell21_1623720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 3].length) (baseStart_1623720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623720 prefixEnd_1623720 := by exact prefixLift 1623720
  have htrace : WordTrace (prefixWord ++ tailWord_1623720) baseStart_1623720 baseEnd_1623720 := by
    simpa [prefixWord, tailWord_1623720, baseEnd_1623720] using wordTrace_append hprefix tailTrace_1623720
  have hstable : (prefixWord ++ tailWord_1623720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623720).length < 2 ^ (prefixWord ++ tailWord_1623720).sum := by decide
  have hdescent : baseEnd_1623720 < baseStart_1623720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623728 : List Nat := [2, 1, 1, 1, 2, 1, 5, 5, 3]
def baseStart_1623728 : Nat := 118140960795 + 1623728 * 2 ^ 59
def prefixEnd_1623728 : Nat := 4983230072969 + 3 ^ 40 * 1623728 * 2
def baseEnd_1623728 : Nat := 370556851628323729081163

theorem tailTrace_1623728 : CollatzResearch.WordTrace tailWord_1623728 prefixEnd_1623728 370556851628323729081163 := by
  unfold tailWord_1623728
  simp only [CollatzResearch.WordTrace]
  refine ⟨29611112730759120754839919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39481483641012161006453225 29611112730759120754839919)
  ·
    refine ⟨44416669096138681132259879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29611112730759120754839919 44416669096138681132259879)
    ·
      refine ⟨66625003644208021698389819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44416669096138681132259879 66625003644208021698389819)
      ·
        refine ⟨99937505466312032547584729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66625003644208021698389819 99937505466312032547584729)
        ·
          refine ⟨74953129099734024410688547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99937505466312032547584729 74953129099734024410688547)
          ·
            refine ⟨112429693649601036616032821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74953129099734024410688547 112429693649601036616032821)
            ·
              refine ⟨10540283779650097182753077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112429693649601036616032821 10540283779650097182753077)
              ·
                refine ⟨988151604342196610883101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10540283779650097182753077 988151604342196610883101)
                ·
                  refine ⟨370556851628323729081163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988151604342196610883101 370556851628323729081163)
                  ·
                    rfl

theorem cell21_1623728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 3].length) (baseStart_1623728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623728 prefixEnd_1623728 := by exact prefixLift 1623728
  have htrace : WordTrace (prefixWord ++ tailWord_1623728) baseStart_1623728 baseEnd_1623728 := by
    simpa [prefixWord, tailWord_1623728, baseEnd_1623728] using wordTrace_append hprefix tailTrace_1623728
  have hstable : (prefixWord ++ tailWord_1623728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623728).length < 2 ^ (prefixWord ++ tailWord_1623728).sum := by decide
  have hdescent : baseEnd_1623728 < baseStart_1623728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623779 : List Nat := [1, 1, 1, 7, 3, 1, 1, 3, 3]
def baseStart_1623779 : Nat := 118140960795 + 1623779 * 2 ^ 59
def prefixEnd_1623779 : Nat := 4983230072969 + 3 ^ 40 * 1623779 * 2
def baseEnd_1623779 : Nat := 370568490523158973731059

theorem tailTrace_1623779 : CollatzResearch.WordTrace tailWord_1623779 prefixEnd_1623779 370568490523158973731059 := by
  unfold tailWord_1623779
  simp only [CollatzResearch.WordTrace]
  refine ⟨59224085584333477219786391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39482723722888984813190927 59224085584333477219786391)
  ·
    refine ⟨88836128376500215829679587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59224085584333477219786391 88836128376500215829679587)
    ·
      refine ⟨133254192564750323744519381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88836128376500215829679587 133254192564750323744519381)
      ·
        refine ⟨3123145138236335712762173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 133254192564750323744519381 3123145138236335712762173)
        ·
          refine ⟨1171179426838625892285815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3123145138236335712762173 1171179426838625892285815)
          ·
            refine ⟨1756769140257938838428723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171179426838625892285815 1756769140257938838428723)
            ·
              refine ⟨2635153710386908257643085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1756769140257938838428723 2635153710386908257643085)
              ·
                refine ⟨988182641395090596616157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2635153710386908257643085 988182641395090596616157)
                ·
                  refine ⟨370568490523158973731059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988182641395090596616157 370568490523158973731059)
                  ·
                    rfl

theorem cell21_1623779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 3].length) (baseStart_1623779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623779 prefixEnd_1623779 := by exact prefixLift 1623779
  have htrace : WordTrace (prefixWord ++ tailWord_1623779) baseStart_1623779 baseEnd_1623779 := by
    simpa [prefixWord, tailWord_1623779, baseEnd_1623779] using wordTrace_append hprefix tailTrace_1623779
  have hstable : (prefixWord ++ tailWord_1623779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623779).length < 2 ^ (prefixWord ++ tailWord_1623779).sum := by decide
  have hdescent : baseEnd_1623779 < baseStart_1623779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623796 : List Nat := [2, 6, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1623796 : Nat := 118140960795 + 1623796 * 2 ^ 59
def prefixEnd_1623796 : Nat := 4983230072969 + 3 ^ 40 * 1623796 * 2
def baseEnd_1623796 : Nat := 370572370154770721947691

theorem tailTrace_1623796 : CollatzResearch.WordTrace tailWord_1623796 prefixEnd_1623796 370572370154770721947691 := by
  unfold tailWord_1623796
  simp only [CollatzResearch.WordTrace]
  refine ⟨29612352812635944561577621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39483137083514592748770161 29612352812635944561577621)
  ·
    refine ⟨1388079038092309901323951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29612352812635944561577621 1388079038092309901323951)
    ·
      refine ⟨2082118557138464851985927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1388079038092309901323951 2082118557138464851985927)
      ·
        refine ⟨3123177835707697277978891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082118557138464851985927 3123177835707697277978891)
        ·
          refine ⟨4684766753561545916968337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3123177835707697277978891 4684766753561545916968337)
          ·
            refine ⟨3513575065171159437726253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4684766753561545916968337 3513575065171159437726253)
            ·
              refine ⟨1317590649439184789147345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3513575065171159437726253 1317590649439184789147345)
              ·
                refine ⟨988192987079388591860509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317590649439184789147345 988192987079388591860509)
                ·
                  refine ⟨370572370154770721947691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988192987079388591860509 370572370154770721947691)
                  ·
                    rfl

theorem cell21_1623796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1623796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623796 prefixEnd_1623796 := by exact prefixLift 1623796
  have htrace : WordTrace (prefixWord ++ tailWord_1623796) baseStart_1623796 baseEnd_1623796 := by
    simpa [prefixWord, tailWord_1623796, baseEnd_1623796] using wordTrace_append hprefix tailTrace_1623796
  have hstable : (prefixWord ++ tailWord_1623796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623796).length < 2 ^ (prefixWord ++ tailWord_1623796).sum := by decide
  have hdescent : baseEnd_1623796 < baseStart_1623796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623832 : List Nat := [2, 1, 2, 3, 1, 1, 4, 7]
def baseStart_1623832 : Nat := 118140960795 + 1623832 * 2 ^ 59
def prefixEnd_1623832 : Nat := 4983230072969 + 3 ^ 40 * 1623832 * 2
def baseEnd_1623832 : Nat := 123526861948414219782539

theorem tailTrace_1623832 : CollatzResearch.WordTrace tailWord_1623832 prefixEnd_1623832 123526861948414219782539 := by
  unfold tailWord_1623832
  simp only [CollatzResearch.WordTrace]
  refine ⟨29613009326570733635732875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39484012435427644847643833 29613009326570733635732875)
  ·
    refine ⟨44419513989856100453599313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29613009326570733635732875 44419513989856100453599313)
    ·
      refine ⟨33314635492392075340199485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44419513989856100453599313 33314635492392075340199485)
      ·
        refine ⟨12492988309647028252574807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33314635492392075340199485 12492988309647028252574807)
        ·
          refine ⟨18739482464470542378862211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12492988309647028252574807 18739482464470542378862211)
          ·
            refine ⟨28109223696705813568293317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18739482464470542378862211 28109223696705813568293317)
            ·
              refine ⟨5270479443132340044054997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28109223696705813568293317 5270479443132340044054997)
              ·
                refine ⟨123526861948414219782539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5270479443132340044054997 123526861948414219782539)
                ·
                  rfl

theorem cell21_1623832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_1623832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623832 prefixEnd_1623832 := by exact prefixLift 1623832
  have htrace : WordTrace (prefixWord ++ tailWord_1623832) baseStart_1623832 baseEnd_1623832 := by
    simpa [prefixWord, tailWord_1623832, baseEnd_1623832] using wordTrace_append hprefix tailTrace_1623832
  have hstable : (prefixWord ++ tailWord_1623832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623832).length < 2 ^ (prefixWord ++ tailWord_1623832).sum := by decide
  have hdescent : baseEnd_1623832 < baseStart_1623832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623939 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 5]
def baseStart_1623939 : Nat := 118140960795 + 1623939 * 2 ^ 59
def prefixEnd_1623939 : Nat := 4983230072969 + 3 ^ 40 * 1623939 * 2
def baseEnd_1623939 : Nat := 370605004703034251064065

theorem tailTrace_1623939 : CollatzResearch.WordTrace tailWord_1623939 prefixEnd_1623939 370605004703034251064065 := by
  unfold tailWord_1623939
  simp only [CollatzResearch.WordTrace]
  refine ⟨59229921263753824545610871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39486614175835883030407247 59229921263753824545610871)
  ·
    refine ⟨88844881895630736818416307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59229921263753824545610871 88844881895630736818416307)
    ·
      refine ⟨133267322843446105227624461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88844881895630736818416307 133267322843446105227624461)
      ·
        refine ⟨49975246066292289460359173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133267322843446105227624461 49975246066292289460359173)
        ·
          refine ⟨9370358637429804273817345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49975246066292289460359173 9370358637429804273817345)
          ·
            refine ⟨7027768978072353205363009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9370358637429804273817345 7027768978072353205363009)
            ·
              refine ⟨5270826733554264904022257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7027768978072353205363009 5270826733554264904022257)
              ·
                refine ⟨3953120050165698678016693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5270826733554264904022257 3953120050165698678016693)
                ·
                  refine ⟨370605004703034251064065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3953120050165698678016693 370605004703034251064065)
                  ·
                    rfl

theorem cell21_1623939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_1623939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623939 prefixEnd_1623939 := by exact prefixLift 1623939
  have htrace : WordTrace (prefixWord ++ tailWord_1623939) baseStart_1623939 baseEnd_1623939 := by
    simpa [prefixWord, tailWord_1623939, baseEnd_1623939] using wordTrace_append hprefix tailTrace_1623939
  have hstable : (prefixWord ++ tailWord_1623939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623939).length < 2 ^ (prefixWord ++ tailWord_1623939).sum := by decide
  have hdescent : baseEnd_1623939 < baseStart_1623939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623953 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 6]
def baseStart_1623953 : Nat := 118140960795 + 1623953 * 2 ^ 59
def prefixEnd_1623953 : Nat := 4983230072969 + 3 ^ 40 * 1623953 * 2
def baseEnd_1623953 : Nat := 370608199693773337830703

theorem tailTrace_1623953 : CollatzResearch.WordTrace tailWord_1623953 prefixEnd_1623953 370608199693773337830703 := by
  unfold tailWord_1623953
  simp only [CollatzResearch.WordTrace]
  refine ⟨59230431885703104936620513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39486954590468736624413675 59230431885703104936620513)
  ·
    refine ⟨44422823914277328702465385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59230431885703104936620513 44422823914277328702465385)
    ·
      refine ⟨33317117935707996526849039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44422823914277328702465385 33317117935707996526849039)
      ·
        refine ⟨49975676903561994790273559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33317117935707996526849039 49975676903561994790273559)
        ·
          refine ⟨74963515355342992185410339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49975676903561994790273559 74963515355342992185410339)
          ·
            refine ⟨112445273033014488278115509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74963515355342992185410339 112445273033014488278115509)
            ·
              refine ⟨10541744346845108276073329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112445273033014488278115509 10541744346845108276073329)
              ·
                refine ⟨7906308260133831207054997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10541744346845108276073329 7906308260133831207054997)
                ·
                  refine ⟨370608199693773337830703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7906308260133831207054997 370608199693773337830703)
                  ·
                    rfl

theorem cell21_1623953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_1623953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1623953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1623953 prefixEnd_1623953 := by exact prefixLift 1623953
  have htrace : WordTrace (prefixWord ++ tailWord_1623953) baseStart_1623953 baseEnd_1623953 := by
    simpa [prefixWord, tailWord_1623953, baseEnd_1623953] using wordTrace_append hprefix tailTrace_1623953
  have hstable : (prefixWord ++ tailWord_1623953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623953).length < 2 ^ (prefixWord ++ tailWord_1623953).sum := by decide
  have hdescent : baseEnd_1623953 < baseStart_1623953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624156 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 4]
def baseStart_1624156 : Nat := 118140960795 + 1624156 * 2 ^ 59
def prefixEnd_1624156 : Nat := 4983230072969 + 3 ^ 40 * 1624156 * 2
def baseEnd_1624156 : Nat := 370654527059490095946955

theorem tailTrace_1624156 : CollatzResearch.WordTrace tailWord_1624156 prefixEnd_1624156 370654527059490095946955 := by
  unfold tailWord_1624156
  simp only [CollatzResearch.WordTrace]
  refine ⟨29618917951983835303130161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39491890602645113737506881 29618917951983835303130161)
  ·
    refine ⟨22214188463987876477347621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29618917951983835303130161 22214188463987876477347621)
    ·
      refine ⟨4165160336997726839502679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22214188463987876477347621 4165160336997726839502679)
      ·
        refine ⟨6247740505496590259254019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4165160336997726839502679 6247740505496590259254019)
        ·
          refine ⟨9371610758244885388881029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247740505496590259254019 9371610758244885388881029)
          ·
            refine ⟨1757177017170916010415193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9371610758244885388881029 1757177017170916010415193)
            ·
              refine ⟨1317882762878187007811395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757177017170916010415193 1317882762878187007811395)
              ·
                refine ⟨1976824144317280511717093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1317882762878187007811395 1976824144317280511717093)
                ·
                  refine ⟨370654527059490095946955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1976824144317280511717093 370654527059490095946955)
                  ·
                    rfl

theorem cell21_1624156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_1624156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624156 prefixEnd_1624156 := by exact prefixLift 1624156
  have htrace : WordTrace (prefixWord ++ tailWord_1624156) baseStart_1624156 baseEnd_1624156 := by
    simpa [prefixWord, tailWord_1624156, baseEnd_1624156] using wordTrace_append hprefix tailTrace_1624156
  have hstable : (prefixWord ++ tailWord_1624156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624156).length < 2 ^ (prefixWord ++ tailWord_1624156).sum := by decide
  have hdescent : baseEnd_1624156 < baseStart_1624156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624195 : List Nat := [1, 1, 1, 3, 3, 12]
def baseStart_1624195 : Nat := 118140960795 + 1624195 * 2 ^ 59
def prefixEnd_1624195 : Nat := 4983230072969 + 3 ^ 40 * 1624195 * 2
def baseEnd_1624195 : Nat := 13728275088549433140625

theorem tailTrace_1624195 : CollatzResearch.WordTrace tailWord_1624195 prefixEnd_1624195 13728275088549433140625 := by
  unfold tailWord_1624195
  simp only [CollatzResearch.WordTrace]
  refine ⟨59239258350826380266930039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39492838900550920177953359 59239258350826380266930039)
  ·
    refine ⟨88858887526239570400395059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59239258350826380266930039 88858887526239570400395059)
    ·
      refine ⟨133288331289359355600592589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88858887526239570400395059 133288331289359355600592589)
      ·
        refine ⟨49983124233509758350222221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133288331289359355600592589 49983124233509758350222221)
        ·
          refine ⟨18743671587566159381333333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49983124233509758350222221 18743671587566159381333333)
          ·
            refine ⟨13728275088549433140625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18743671587566159381333333 13728275088549433140625)
            ·
              rfl

theorem cell21_1624195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 12].length) (baseStart_1624195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624195 prefixEnd_1624195 := by exact prefixLift 1624195
  have htrace : WordTrace (prefixWord ++ tailWord_1624195) baseStart_1624195 baseEnd_1624195 := by
    simpa [prefixWord, tailWord_1624195, baseEnd_1624195] using wordTrace_append hprefix tailTrace_1624195
  have hstable : (prefixWord ++ tailWord_1624195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624195).length < 2 ^ (prefixWord ++ tailWord_1624195).sum := by decide
  have hdescent : baseEnd_1624195 < baseStart_1624195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624260 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 5]
def baseStart_1624260 : Nat := 118140960795 + 1624260 * 2 ^ 59
def prefixEnd_1624260 : Nat := 4983230072969 + 3 ^ 40 * 1624260 * 2
def baseEnd_1624260 : Nat := 370678261276409026213409

theorem tailTrace_1624260 : CollatzResearch.WordTrace tailWord_1624260 prefixEnd_1624260 370678261276409026213409 := by
  unfold tailWord_1624260
  simp only [CollatzResearch.WordTrace]
  refine ⟨29620814547795448184023117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39494419397060597578697489 29620814547795448184023117)
  ·
    refine ⟨11107805455423293069008669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29620814547795448184023117 11107805455423293069008669)
    ·
      refine ⟨4165427045783734900878251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11107805455423293069008669 4165427045783734900878251)
      ·
        refine ⟨6248140568675602351317377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4165427045783734900878251 6248140568675602351317377)
        ·
          refine ⟨4686105426506701763488033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6248140568675602351317377 4686105426506701763488033)
          ·
            refine ⟨3514579069880026322616025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4686105426506701763488033 3514579069880026322616025)
            ·
              refine ⟨2635934302410019741962019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3514579069880026322616025 2635934302410019741962019)
              ·
                refine ⟨3953901453615029612943029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635934302410019741962019 3953901453615029612943029)
                ·
                  refine ⟨370678261276409026213409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3953901453615029612943029 370678261276409026213409)
                  ·
                    rfl

theorem cell21_1624260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_1624260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624260 prefixEnd_1624260 := by exact prefixLift 1624260
  have htrace : WordTrace (prefixWord ++ tailWord_1624260) baseStart_1624260 baseEnd_1624260 := by
    simpa [prefixWord, tailWord_1624260, baseEnd_1624260] using wordTrace_append hprefix tailTrace_1624260
  have hstable : (prefixWord ++ tailWord_1624260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624260).length < 2 ^ (prefixWord ++ tailWord_1624260).sum := by decide
  have hdescent : baseEnd_1624260 < baseStart_1624260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624271 : List Nat := [1, 1, 2, 1, 1, 3, 4, 8]
def baseStart_1624271 : Nat := 118140960795 + 1624271 * 2 ^ 59
def prefixEnd_1624271 : Nat := 4983230072969 + 3 ^ 40 * 1624271 * 2
def baseEnd_1624271 : Nat := 123560257208758483843351

theorem tailTrace_1624271 : CollatzResearch.WordTrace tailWord_1624271 prefixEnd_1624271 123560257208758483843351 := by
  unfold tailWord_1624271
  simp only [CollatzResearch.WordTrace]
  refine ⟨59242030298551045246696667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39494686865700696831131111 59242030298551045246696667)
  ·
    refine ⟨88863045447826567870045001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59242030298551045246696667 88863045447826567870045001)
    ·
      refine ⟨66647284085869925902533751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88863045447826567870045001 66647284085869925902533751)
      ·
        refine ⟨99970926128804888853800627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66647284085869925902533751 99970926128804888853800627)
        ·
          refine ⟨149956389193207333280700941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99970926128804888853800627 149956389193207333280700941)
          ·
            refine ⟨56233645947452749980262853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149956389193207333280700941 56233645947452749980262853)
            ·
              refine ⟨10543808615147390621299285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56233645947452749980262853 10543808615147390621299285)
              ·
                refine ⟨123560257208758483843351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10543808615147390621299285 123560257208758483843351)
                ·
                  rfl

theorem cell21_1624271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 8].length) (baseStart_1624271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624271 prefixEnd_1624271 := by exact prefixLift 1624271
  have htrace : WordTrace (prefixWord ++ tailWord_1624271) baseStart_1624271 baseEnd_1624271 := by
    simpa [prefixWord, tailWord_1624271, baseEnd_1624271] using wordTrace_append hprefix tailTrace_1624271
  have hstable : (prefixWord ++ tailWord_1624271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624271).length < 2 ^ (prefixWord ++ tailWord_1624271).sum := by decide
  have hdescent : baseEnd_1624271 < baseStart_1624271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624347 : List Nat := [1, 1, 1, 1, 1, 1, 8, 7]
def baseStart_1624347 : Nat := 118140960795 + 1624347 * 2 ^ 59
def prefixEnd_1624347 : Nat := 4983230072969 + 3 ^ 40 * 1624347 * 2
def baseEnd_1624347 : Nat := 123566038620572069421077

theorem tailTrace_1624347 : CollatzResearch.WordTrace tailWord_1624347 prefixEnd_1624347 123566038620572069421077 := by
  unfold tailWord_1624347
  simp only [CollatzResearch.WordTrace]
  refine ⟨59244802246275710226463295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39496534830850473484308863 59244802246275710226463295)
  ·
    refine ⟨88867203369413565339694943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59244802246275710226463295 88867203369413565339694943)
    ·
      refine ⟨133300805054120348009542415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88867203369413565339694943 133300805054120348009542415)
      ·
        refine ⟨199951207581180522014313623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133300805054120348009542415 199951207581180522014313623)
        ·
          refine ⟨299926811371770783021470435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199951207581180522014313623 299926811371770783021470435)
          ·
            refine ⟨449890217057656174532205653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299926811371770783021470435 449890217057656174532205653)
            ·
              refine ⟨5272150981144408295299285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 449890217057656174532205653 5272150981144408295299285)
              ·
                refine ⟨123566038620572069421077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5272150981144408295299285 123566038620572069421077)
                ·
                  rfl

theorem cell21_1624347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 7].length) (baseStart_1624347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624347 prefixEnd_1624347 := by exact prefixLift 1624347
  have htrace : WordTrace (prefixWord ++ tailWord_1624347) baseStart_1624347 baseEnd_1624347 := by
    simpa [prefixWord, tailWord_1624347, baseEnd_1624347] using wordTrace_append hprefix tailTrace_1624347
  have hstable : (prefixWord ++ tailWord_1624347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624347).length < 2 ^ (prefixWord ++ tailWord_1624347).sum := by decide
  have hdescent : baseEnd_1624347 < baseStart_1624347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624370 : List Nat := [3, 2, 1, 1, 5, 2, 2, 2, 3]
def baseStart_1624370 : Nat := 118140960795 + 1624370 * 2 ^ 59
def prefixEnd_1624370 : Nat := 4983230072969 + 3 ^ 40 * 1624370 * 2
def baseEnd_1624370 : Nat := 370703364775073279379851

theorem tailTrace_1624370 : CollatzResearch.WordTrace tailWord_1624370 prefixEnd_1624370 370703364775073279379851 := by
  unfold tailWord_1624370
  simp only [CollatzResearch.WordTrace]
  refine ⟨14811410281298096288637641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39497094083461590103033709 14811410281298096288637641)
  ·
    refine ⟨11108557710973572216478231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14811410281298096288637641 11108557710973572216478231)
    ·
      refine ⟨16662836566460358324717347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11108557710973572216478231 16662836566460358324717347)
      ·
        refine ⟨24994254849690537487076021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16662836566460358324717347 24994254849690537487076021)
        ·
          refine ⟨2343211392158487889413377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24994254849690537487076021 2343211392158487889413377)
          ·
            refine ⟨1757408544118865917060033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2343211392158487889413377 1757408544118865917060033)
            ·
              refine ⟨1318056408089149437795025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757408544118865917060033 1318056408089149437795025)
              ·
                refine ⟨988542306066862078346269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318056408089149437795025 988542306066862078346269)
                ·
                  refine ⟨370703364775073279379851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988542306066862078346269 370703364775073279379851)
                  ·
                    rfl

theorem cell21_1624370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_1624370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624370 prefixEnd_1624370 := by exact prefixLift 1624370
  have htrace : WordTrace (prefixWord ++ tailWord_1624370) baseStart_1624370 baseEnd_1624370 := by
    simpa [prefixWord, tailWord_1624370, baseEnd_1624370] using wordTrace_append hprefix tailTrace_1624370
  have hstable : (prefixWord ++ tailWord_1624370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624370).length < 2 ^ (prefixWord ++ tailWord_1624370).sum := by decide
  have hdescent : baseEnd_1624370 < baseStart_1624370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624426 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_1624426 : Nat := 118140960795 + 1624426 * 2 ^ 59
def prefixEnd_1624426 : Nat := 4983230072969 + 3 ^ 40 * 1624426 * 2
def baseEnd_1624426 : Nat := 370716144738029626446403

theorem tailTrace_1624426 : CollatzResearch.WordTrace tailWord_1624426 prefixEnd_1624426 370716144738029626446403 := by
  unfold tailWord_1624426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14811920903247376679647283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39498455741993004479059421 14811920903247376679647283)
  ·
    refine ⟨22217881354871065019470925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14811920903247376679647283 22217881354871065019470925)
    ·
      refine ⟨8331705508076649382301597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22217881354871065019470925 8331705508076649382301597)
      ·
        refine ⟨3124389565528743518363099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8331705508076649382301597 3124389565528743518363099)
        ·
          refine ⟨4686584348293115277544649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3124389565528743518363099 4686584348293115277544649)
          ·
            refine ⟨3514938261219836458158487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4686584348293115277544649 3514938261219836458158487)
            ·
              refine ⟨5272407391829754687237731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514938261219836458158487 5272407391829754687237731)
              ·
                refine ⟨7908611087744632030856597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5272407391829754687237731 7908611087744632030856597)
                ·
                  refine ⟨370716144738029626446403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7908611087744632030856597 370716144738029626446403)
                  ·
                    rfl

theorem cell21_1624426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_1624426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624426 prefixEnd_1624426 := by exact prefixLift 1624426
  have htrace : WordTrace (prefixWord ++ tailWord_1624426) baseStart_1624426 baseEnd_1624426 := by
    simpa [prefixWord, tailWord_1624426, baseEnd_1624426] using wordTrace_append hprefix tailTrace_1624426
  have hstable : (prefixWord ++ tailWord_1624426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624426).length < 2 ^ (prefixWord ++ tailWord_1624426).sum := by decide
  have hdescent : baseEnd_1624426 < baseStart_1624426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624457 : List Nat := [1, 2, 1, 1, 6, 3, 2, 5]
def baseStart_1624457 : Nat := 118140960795 + 1624457 * 2 ^ 59
def prefixEnd_1624457 : Nat := 4983230072969 + 3 ^ 40 * 1624457 * 2
def baseEnd_1624457 : Nat := 123574406453460153809891

theorem tailTrace_1624457 : CollatzResearch.WordTrace tailWord_1624457 prefixEnd_1624457 123574406453460153809891 := by
  unfold tailWord_1624457
  simp only [CollatzResearch.WordTrace]
  refine ⟨59248814275877199012967625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39499209517251466008645083 59248814275877199012967625)
  ·
    refine ⟨44436610706907899259725719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59248814275877199012967625 44436610706907899259725719)
    ·
      refine ⟨66654916060361848889588579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44436610706907899259725719 66654916060361848889588579)
      ·
        refine ⟨99982374090542773334382869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66654916060361848889588579 99982374090542773334382869)
        ·
          refine ⟨4686673785494192500049197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99982374090542773334382869 4686673785494192500049197)
          ·
            refine ⟨1757502669560322187518449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4686673785494192500049197 1757502669560322187518449)
            ·
              refine ⟨1318127002170241640638837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757502669560322187518449 1318127002170241640638837)
              ·
                refine ⟨123574406453460153809891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1318127002170241640638837 123574406453460153809891)
                ·
                  rfl

theorem cell21_1624457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 5].length) (baseStart_1624457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624457 prefixEnd_1624457 := by exact prefixLift 1624457
  have htrace : WordTrace (prefixWord ++ tailWord_1624457) baseStart_1624457 baseEnd_1624457 := by
    simpa [prefixWord, tailWord_1624457, baseEnd_1624457] using wordTrace_append hprefix tailTrace_1624457
  have hstable : (prefixWord ++ tailWord_1624457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624457).length < 2 ^ (prefixWord ++ tailWord_1624457).sum := by decide
  have hdescent : baseEnd_1624457 < baseStart_1624457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624485 : List Nat := [1, 3, 1, 2, 1, 1, 4, 4, 4]
def baseStart_1624485 : Nat := 118140960795 + 1624485 * 2 ^ 59
def prefixEnd_1624485 : Nat := 4983230072969 + 3 ^ 40 * 1624485 * 2
def baseEnd_1624485 : Nat := 370729609341858634962949

theorem tailTrace_1624485 : CollatzResearch.WordTrace tailWord_1624485 prefixEnd_1624485 370729609341858634962949 := by
  unfold tailWord_1624485
  simp only [CollatzResearch.WordTrace]
  refine ⟨59249835519775759794986909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39499890346517173196657939 59249835519775759794986909)
  ·
    refine ⟨22218688319915909923120091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59249835519775759794986909 22218688319915909923120091)
    ·
      refine ⟨33328032479873864884680137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22218688319915909923120091 33328032479873864884680137)
      ·
        refine ⟨24996024359905398663510103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33328032479873864884680137 24996024359905398663510103)
        ·
          refine ⟨37494036539858097995265155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24996024359905398663510103 37494036539858097995265155)
          ·
            refine ⟨56241054809787146992897733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37494036539858097995265155 56241054809787146992897733)
            ·
              refine ⟨10545197776835090061168325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56241054809787146992897733 10545197776835090061168325)
              ·
                refine ⟨1977224583156579386469061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10545197776835090061168325 1977224583156579386469061)
                ·
                  refine ⟨370729609341858634962949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1977224583156579386469061 370729609341858634962949)
                  ·
                    rfl

theorem cell21_1624485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_1624485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624485 prefixEnd_1624485 := by exact prefixLift 1624485
  have htrace : WordTrace (prefixWord ++ tailWord_1624485) baseStart_1624485 baseEnd_1624485 := by
    simpa [prefixWord, tailWord_1624485, baseEnd_1624485] using wordTrace_append hprefix tailTrace_1624485
  have hstable : (prefixWord ++ tailWord_1624485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624485).length < 2 ^ (prefixWord ++ tailWord_1624485).sum := by decide
  have hdescent : baseEnd_1624485 < baseStart_1624485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624488 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 5]
def baseStart_1624488 : Nat := 118140960795 + 1624488 * 2 ^ 59
def prefixEnd_1624488 : Nat := 4983230072969 + 3 ^ 40 * 1624488 * 2
def baseEnd_1624488 : Nat := 370730293982731296412943

theorem tailTrace_1624488 : CollatzResearch.WordTrace tailWord_1624488 prefixEnd_1624488 370730293982731296412943 := by
  unfold tailWord_1624488
  simp only [CollatzResearch.WordTrace]
  refine ⟨29624972469382445653673059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39499963292509927538230745 29624972469382445653673059)
  ·
    refine ⟨44437458704073668480509589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29624972469382445653673059 44437458704073668480509589)
    ·
      refine ⟨2083005876753453210023887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44437458704073668480509589 2083005876753453210023887)
      ·
        refine ⟨3124508815130179815035831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083005876753453210023887 3124508815130179815035831)
        ·
          refine ⟨4686763222695269722553747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3124508815130179815035831 4686763222695269722553747)
          ·
            refine ⟨7030144834042904583830621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4686763222695269722553747 7030144834042904583830621)
            ·
              refine ⟨2636304312766089218936483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7030144834042904583830621 2636304312766089218936483)
              ·
                refine ⟨3954456469149133828404725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636304312766089218936483 3954456469149133828404725)
                ·
                  refine ⟨370730293982731296412943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3954456469149133828404725 370730293982731296412943)
                  ·
                    rfl

theorem cell21_1624488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_1624488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624488 prefixEnd_1624488 := by exact prefixLift 1624488
  have htrace : WordTrace (prefixWord ++ tailWord_1624488) baseStart_1624488 baseEnd_1624488 := by
    simpa [prefixWord, tailWord_1624488, baseEnd_1624488] using wordTrace_append hprefix tailTrace_1624488
  have hstable : (prefixWord ++ tailWord_1624488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624488).length < 2 ^ (prefixWord ++ tailWord_1624488).sum := by decide
  have hdescent : baseEnd_1624488 < baseStart_1624488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624561 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 4]
def baseStart_1624561 : Nat := 118140960795 + 1624561 * 2 ^ 59
def prefixEnd_1624561 : Nat := 4983230072969 + 3 ^ 40 * 1624561 * 2
def baseEnd_1624561 : Nat := 370746953577299391696127

theorem tailTrace_1624561 : CollatzResearch.WordTrace tailWord_1624561 prefixEnd_1624561 370746953577299391696127 := by
  unfold tailWord_1624561
  simp only [CollatzResearch.WordTrace]
  refine ⟨59252607467500424774753537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39501738311666949849835691 59252607467500424774753537)
  ·
    refine ⟨44439455600625318581065153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59252607467500424774753537 44439455600625318581065153)
    ·
      refine ⟨33329591700468988935798865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44439455600625318581065153 33329591700468988935798865)
      ·
        refine ⟨24997193775351741701849149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33329591700468988935798865 24997193775351741701849149)
        ·
          refine ⟨9373947665756903138193431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24997193775351741701849149 9373947665756903138193431)
          ·
            refine ⟨14060921498635354707290147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9373947665756903138193431 14060921498635354707290147)
            ·
              refine ⟨21091382247953032060935221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14060921498635354707290147 21091382247953032060935221)
              ·
                refine ⟨1977317085745596755712677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21091382247953032060935221 1977317085745596755712677)
                ·
                  refine ⟨370746953577299391696127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1977317085745596755712677 370746953577299391696127)
                  ·
                    rfl

theorem cell21_1624561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_1624561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624561 prefixEnd_1624561 := by exact prefixLift 1624561
  have htrace : WordTrace (prefixWord ++ tailWord_1624561) baseStart_1624561 baseEnd_1624561 := by
    simpa [prefixWord, tailWord_1624561, baseEnd_1624561] using wordTrace_append hprefix tailTrace_1624561
  have hstable : (prefixWord ++ tailWord_1624561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624561).length < 2 ^ (prefixWord ++ tailWord_1624561).sum := by decide
  have hdescent : baseEnd_1624561 < baseStart_1624561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624612 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 4]
def baseStart_1624612 : Nat := 118140960795 + 1624612 * 2 ^ 59
def prefixEnd_1624612 : Nat := 4983230072969 + 3 ^ 40 * 1624612 * 2
def baseEnd_1624612 : Nat := 370758592472134636346023

theorem tailTrace_1624612 : CollatzResearch.WordTrace tailWord_1624612 prefixEnd_1624612 370758592472134636346023 := by
  unfold tailWord_1624612
  simp only [CollatzResearch.WordTrace]
  refine ⟨29627233795157830242430045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39502978393543773656573393 29627233795157830242430045)
  ·
    refine ⟨11110212673184186340911267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29627233795157830242430045 11110212673184186340911267)
    ·
      refine ⟨16665319009776279511366901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11110212673184186340911267 16665319009776279511366901)
      ·
        refine ⟨1562373657166526204190647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16665319009776279511366901 1562373657166526204190647)
        ·
          refine ⟨2343560485749789306285971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562373657166526204190647 2343560485749789306285971)
          ·
            refine ⟨3515340728624683959428957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343560485749789306285971 3515340728624683959428957)
            ·
              refine ⟨1318252773234256484785859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3515340728624683959428957 1318252773234256484785859)
              ·
                refine ⟨1977379159851384727178789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318252773234256484785859 1977379159851384727178789)
                ·
                  refine ⟨370758592472134636346023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1977379159851384727178789 370758592472134636346023)
                  ·
                    rfl

theorem cell21_1624612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_1624612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624612 prefixEnd_1624612 := by exact prefixLift 1624612
  have htrace : WordTrace (prefixWord ++ tailWord_1624612) baseStart_1624612 baseEnd_1624612 := by
    simpa [prefixWord, tailWord_1624612, baseEnd_1624612] using wordTrace_append hprefix tailTrace_1624612
  have hstable : (prefixWord ++ tailWord_1624612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624612).length < 2 ^ (prefixWord ++ tailWord_1624612).sum := by decide
  have hdescent : baseEnd_1624612 < baseStart_1624612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624637 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 6]
def baseStart_1624637 : Nat := 118140960795 + 1624637 * 2 ^ 59
def prefixEnd_1624637 : Nat := 4983230072969 + 3 ^ 40 * 1624637 * 2
def baseEnd_1624637 : Nat := 370764297812740148429305

theorem tailTrace_1624637 : CollatzResearch.WordTrace tailWord_1624637 prefixEnd_1624637 370764297812740148429305 := by
  unfold tailWord_1624637
  simp only [CollatzResearch.WordTrace]
  refine ⟨59255379415225089754520165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39503586276816726503013443 59255379415225089754520165)
  ·
    refine ⟨11110383640354704328972531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59255379415225089754520165 11110383640354704328972531)
    ·
      refine ⟨16665575460532056493458797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11110383640354704328972531 16665575460532056493458797)
      ·
        refine ⟨6249590797699521185047049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16665575460532056493458797 6249590797699521185047049)
        ·
          refine ⟨4687193098274640888785287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6249590797699521185047049 4687193098274640888785287)
          ·
            refine ⟨7030789647411961333177931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4687193098274640888785287 7030789647411961333177931)
            ·
              refine ⟨10546184471117941999766897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030789647411961333177931 10546184471117941999766897)
              ·
                refine ⟨7909638353338456499825173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10546184471117941999766897 7909638353338456499825173)
                ·
                  refine ⟨370764297812740148429305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7909638353338456499825173 370764297812740148429305)
                  ·
                    rfl

theorem cell21_1624637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_1624637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624637 prefixEnd_1624637 := by exact prefixLift 1624637
  have htrace : WordTrace (prefixWord ++ tailWord_1624637) baseStart_1624637 baseEnd_1624637 := by
    simpa [prefixWord, tailWord_1624637, baseEnd_1624637] using wordTrace_append hprefix tailTrace_1624637
  have hstable : (prefixWord ++ tailWord_1624637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624637).length < 2 ^ (prefixWord ++ tailWord_1624637).sum := by decide
  have hdescent : baseEnd_1624637 < baseStart_1624637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624682 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_1624682 : Nat := 118140960795 + 1624682 * 2 ^ 59
def prefixEnd_1624682 : Nat := 4983230072969 + 3 ^ 40 * 1624682 * 2
def baseEnd_1624682 : Nat := 370774567425830070179213

theorem tailTrace_1624682 : CollatzResearch.WordTrace tailWord_1624682 prefixEnd_1624682 370774567425830070179213 := by
  unfold tailWord_1624682
  simp only [CollatzResearch.WordTrace]
  refine ⟨14814255175015515609977075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39504680466708041626605533 14814255175015515609977075)
  ·
    refine ⟨22221382762523273414965613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14814255175015515609977075 22221382762523273414965613)
    ·
      refine ⟨8333018535946227530612105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22221382762523273414965613 8333018535946227530612105)
      ·
        refine ⟨6249763901959670647959079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8333018535946227530612105 6249763901959670647959079)
        ·
          refine ⟨9374645852939505971938619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6249763901959670647959079 9374645852939505971938619)
          ·
            refine ⟨14061968779409258957907929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9374645852939505971938619 14061968779409258957907929)
            ·
              refine ⟨10546476584556944218430947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14061968779409258957907929 10546476584556944218430947)
              ·
                refine ⟨15819714876835416327646421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10546476584556944218430947 15819714876835416327646421)
                ·
                  refine ⟨370774567425830070179213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15819714876835416327646421 370774567425830070179213)
                  ·
                    rfl

theorem cell21_1624682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_1624682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624682 prefixEnd_1624682 := by exact prefixLift 1624682
  have htrace : WordTrace (prefixWord ++ tailWord_1624682) baseStart_1624682 baseEnd_1624682 := by
    simpa [prefixWord, tailWord_1624682, baseEnd_1624682] using wordTrace_append hprefix tailTrace_1624682
  have hstable : (prefixWord ++ tailWord_1624682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624682).length < 2 ^ (prefixWord ++ tailWord_1624682).sum := by decide
  have hdescent : baseEnd_1624682 < baseStart_1624682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624885 : List Nat := [1, 3, 3, 1, 3, 3, 2, 2, 3]
def baseStart_1624885 : Nat := 118140960795 + 1624885 * 2 ^ 59
def prefixEnd_1624885 : Nat := 4983230072969 + 3 ^ 40 * 1624885 * 2
def baseEnd_1624885 : Nat := 370820894791546828295465

theorem tailTrace_1624885 : CollatzResearch.WordTrace tailWord_1624885 prefixEnd_1624885 370820894791546828295465 := by
  unfold tailWord_1624885
  simp only [CollatzResearch.WordTrace]
  refine ⟨59264424718326628109548109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39509616478884418739698739 59264424718326628109548109)
  ·
    refine ⟨22224159269372485541080541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59264424718326628109548109 22224159269372485541080541)
    ·
      refine ⟨8334059726014682077905203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22224159269372485541080541 8334059726014682077905203)
      ·
        refine ⟨12501089589022023116857805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8334059726014682077905203 12501089589022023116857805)
        ·
          refine ⟨4687908595883258668821677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12501089589022023116857805 4687908595883258668821677)
          ·
            refine ⟨1757965723456222000808129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4687908595883258668821677 1757965723456222000808129)
            ·
              refine ⟨1318474292592166500606097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1757965723456222000808129 1318474292592166500606097)
              ·
                refine ⟨988855719444124875454573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1318474292592166500606097 988855719444124875454573)
                ·
                  refine ⟨370820894791546828295465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988855719444124875454573 370820894791546828295465)
                  ·
                    rfl

theorem cell21_1624885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_1624885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624885 prefixEnd_1624885 := by exact prefixLift 1624885
  have htrace : WordTrace (prefixWord ++ tailWord_1624885) baseStart_1624885 baseEnd_1624885 := by
    simpa [prefixWord, tailWord_1624885, baseEnd_1624885] using wordTrace_append hprefix tailTrace_1624885
  have hstable : (prefixWord ++ tailWord_1624885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624885).length < 2 ^ (prefixWord ++ tailWord_1624885).sum := by decide
  have hdescent : baseEnd_1624885 < baseStart_1624885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624927 : List Nat := [1, 1, 2, 3, 1, 3, 4, 3, 3]
def baseStart_1624927 : Nat := 118140960795 + 1624927 * 2 ^ 59
def prefixEnd_1624927 : Nat := 4983230072969 + 3 ^ 40 * 1624927 * 2
def baseEnd_1624927 : Nat := 370830479763764088595379

theorem tailTrace_1624927 : CollatzResearch.WordTrace tailWord_1624927 prefixEnd_1624927 370830479763764088595379 := by
  unfold tailWord_1624927
  simp only [CollatzResearch.WordTrace]
  refine ⟨59265956584174469282577035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39510637722782979521718023 59265956584174469282577035)
  ·
    refine ⟨88898934876261703923865553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59265956584174469282577035 88898934876261703923865553)
    ·
      refine ⟨66674201157196277942899165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88898934876261703923865553 66674201157196277942899165)
      ·
        refine ⟨25002825433948604228587187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66674201157196277942899165 25002825433948604228587187)
        ·
          refine ⟨37504238150922906342880781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25002825433948604228587187 37504238150922906342880781)
          ·
            refine ⟨14064089306596089878580293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37504238150922906342880781 14064089306596089878580293)
            ·
              refine ⟨2637016744986766852233805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14064089306596089878580293 2637016744986766852233805)
              ·
                refine ⟨988881279370037569587677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2637016744986766852233805 988881279370037569587677)
                ·
                  refine ⟨370830479763764088595379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988881279370037569587677 370830479763764088595379)
                  ·
                    rfl

theorem cell21_1624927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 3].length) (baseStart_1624927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624927 prefixEnd_1624927 := by exact prefixLift 1624927
  have htrace : WordTrace (prefixWord ++ tailWord_1624927) baseStart_1624927 baseEnd_1624927 := by
    simpa [prefixWord, tailWord_1624927, baseEnd_1624927] using wordTrace_append hprefix tailTrace_1624927
  have hstable : (prefixWord ++ tailWord_1624927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624927).length < 2 ^ (prefixWord ++ tailWord_1624927).sum := by decide
  have hdescent : baseEnd_1624927 < baseStart_1624927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1624978 : List Nat := [3, 2, 3, 2, 3, 1, 1, 3, 3]
def baseStart_1624978 : Nat := 118140960795 + 1624978 * 2 ^ 59
def prefixEnd_1624978 : Nat := 4983230072969 + 3 ^ 40 * 1624978 * 2
def baseEnd_1624978 : Nat := 370842118658599333245275

theorem tailTrace_1624978 : CollatzResearch.WordTrace tailWord_1624978 prefixEnd_1624978 370842118658599333245275 := by
  unfold tailWord_1624978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14816954176747426248170897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39511877804659803328455725 14816954176747426248170897)
  ·
    refine ⟨11112715632560569686128173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14816954176747426248170897 11112715632560569686128173)
    ·
      refine ⟨4167268362210213632298065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11112715632560569686128173 4167268362210213632298065)
      ·
        refine ⟨3125451271657660224223549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4167268362210213632298065 3125451271657660224223549)
        ·
          refine ⟨1172044226871622584083831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3125451271657660224223549 1172044226871622584083831)
          ·
            refine ⟨1758066340307433876125747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172044226871622584083831 1758066340307433876125747)
            ·
              refine ⟨2637099510461150814188621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1758066340307433876125747 2637099510461150814188621)
              ·
                refine ⟨988912316422931555320733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2637099510461150814188621 988912316422931555320733)
                ·
                  refine ⟨370842118658599333245275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 988912316422931555320733 370842118658599333245275)
                  ·
                    rfl

theorem cell21_1624978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_1624978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1624978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1624978 prefixEnd_1624978 := by exact prefixLift 1624978
  have htrace : WordTrace (prefixWord ++ tailWord_1624978) baseStart_1624978 baseEnd_1624978 := by
    simpa [prefixWord, tailWord_1624978, baseEnd_1624978] using wordTrace_append hprefix tailTrace_1624978
  have hstable : (prefixWord ++ tailWord_1624978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1624978).length < 2 ^ (prefixWord ++ tailWord_1624978).sum := by decide
  have hdescent : baseEnd_1624978 < baseStart_1624978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1624978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625017 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 4]
def baseStart_1625017 : Nat := 118140960795 + 1625017 * 2 ^ 59
def prefixEnd_1625017 : Nat := 4983230072969 + 3 ^ 40 * 1625017 * 2
def baseEnd_1625017 : Nat := 370851018989943932095195

theorem tailTrace_1625017 : CollatzResearch.WordTrace tailWord_1625017 prefixEnd_1625017 370851018989943932095195 := by
  unfold tailWord_1625017
  simp only [CollatzResearch.WordTrace]
  refine ⟨59269239153848414653353305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39512826102565609768902203 59269239153848414653353305)
  ·
    refine ⟨44451929365386310990014979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59269239153848414653353305 44451929365386310990014979)
    ·
      refine ⟨66677894048079466485022469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44451929365386310990014979 66677894048079466485022469)
      ·
        refine ⟨12502105134014899965941713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66677894048079466485022469 12502105134014899965941713)
        ·
          refine ⟨9376578850511174974456285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12502105134014899965941713 9376578850511174974456285)
          ·
            refine ⟨3516217068941690615421107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9376578850511174974456285 3516217068941690615421107)
            ·
              refine ⟨5274325603412535923131661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3516217068941690615421107 5274325603412535923131661)
              ·
                refine ⟨1977872101279700971174373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5274325603412535923131661 1977872101279700971174373)
                ·
                  refine ⟨370851018989943932095195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1977872101279700971174373 370851018989943932095195)
                  ·
                    rfl

theorem cell21_1625017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_1625017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625017 prefixEnd_1625017 := by exact prefixLift 1625017
  have htrace : WordTrace (prefixWord ++ tailWord_1625017) baseStart_1625017 baseEnd_1625017 := by
    simpa [prefixWord, tailWord_1625017, baseEnd_1625017] using wordTrace_append hprefix tailTrace_1625017
  have hstable : (prefixWord ++ tailWord_1625017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625017).length < 2 ^ (prefixWord ++ tailWord_1625017).sum := by decide
  have hdescent : baseEnd_1625017 < baseStart_1625017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625127 : List Nat := [1, 1, 7, 1, 1, 2, 3, 1, 4]
def baseStart_1625127 : Nat := 118140960795 + 1625127 * 2 ^ 59
def prefixEnd_1625127 : Nat := 4983230072969 + 3 ^ 40 * 1625127 * 2
def baseEnd_1625127 : Nat := 370876122488608185261637

theorem tailTrace_1625127 : CollatzResearch.WordTrace tailWord_1625127 prefixEnd_1625127 370876122488608185261637 := by
  unfold tailWord_1625127
  simp only [CollatzResearch.WordTrace]
  refine ⟨59273251183449903439857635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39515500788966602293238423 59273251183449903439857635)
  ·
    refine ⟨88909876775174855159786453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59273251183449903439857635 88909876775174855159786453)
    ·
      refine ⟨2083825236918160667807495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 88909876775174855159786453 2083825236918160667807495)
      ·
        refine ⟨3125737855377241001711243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083825236918160667807495 3125737855377241001711243)
        ·
          refine ⟨4688606783065861502566865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125737855377241001711243 4688606783065861502566865)
          ·
            refine ⟨3516455087299396126925149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4688606783065861502566865 3516455087299396126925149)
            ·
              refine ⟨1318670657737273547596931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3516455087299396126925149 1318670657737273547596931)
              ·
                refine ⟨1978005986605910321395397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1318670657737273547596931 1978005986605910321395397)
                ·
                  refine ⟨370876122488608185261637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978005986605910321395397 370876122488608185261637)
                  ·
                    rfl

theorem cell21_1625127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 4].length) (baseStart_1625127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625127 prefixEnd_1625127 := by exact prefixLift 1625127
  have htrace : WordTrace (prefixWord ++ tailWord_1625127) baseStart_1625127 baseEnd_1625127 := by
    simpa [prefixWord, tailWord_1625127, baseEnd_1625127] using wordTrace_append hprefix tailTrace_1625127
  have hstable : (prefixWord ++ tailWord_1625127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625127).length < 2 ^ (prefixWord ++ tailWord_1625127).sum := by decide
  have hdescent : baseEnd_1625127 < baseStart_1625127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625186 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1625186 : Nat := 118140960795 + 1625186 * 2 ^ 59
def prefixEnd_1625186 : Nat := 4983230072969 + 3 ^ 40 * 1625186 * 2
def baseEnd_1625186 : Nat := 370889587092437193778183

theorem tailTrace_1625186 : CollatzResearch.WordTrace tailWord_1625186 prefixEnd_1625186 370889587092437193778183 := by
  unfold tailWord_1625186
  simp only [CollatzResearch.WordTrace]
  refine ⟨14818850772559039129063853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39516935393490771010836941 14818850772559039129063853)
  ·
    refine ⟨5557069039709639673398945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14818850772559039129063853 5557069039709639673398945)
    ·
      refine ⟨4167801779782229755049209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5557069039709639673398945 4167801779782229755049209)
      ·
        refine ⟨3125851334836672316286907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4167801779782229755049209 3125851334836672316286907)
        ·
          refine ⟨4688777002255008474430361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125851334836672316286907 4688777002255008474430361)
          ·
            refine ⟨3516582751691256355822771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4688777002255008474430361 3516582751691256355822771)
            ·
              refine ⟨5274874127536884533734157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3516582751691256355822771 5274874127536884533734157)
              ·
                refine ⟨1978077797826331700150309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5274874127536884533734157 1978077797826331700150309)
                ·
                  refine ⟨370889587092437193778183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978077797826331700150309 370889587092437193778183)
                  ·
                    rfl

theorem cell21_1625186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1625186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625186 prefixEnd_1625186 := by exact prefixLift 1625186
  have htrace : WordTrace (prefixWord ++ tailWord_1625186) baseStart_1625186 baseEnd_1625186 := by
    simpa [prefixWord, tailWord_1625186, baseEnd_1625186] using wordTrace_append hprefix tailTrace_1625186
  have hstable : (prefixWord ++ tailWord_1625186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625186).length < 2 ^ (prefixWord ++ tailWord_1625186).sum := by decide
  have hdescent : baseEnd_1625186 < baseStart_1625186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625211 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 8]
def baseStart_1625211 : Nat := 118140960795 + 1625211 * 2 ^ 59
def prefixEnd_1625211 : Nat := 4983230072969 + 3 ^ 40 * 1625211 * 2
def baseEnd_1625211 : Nat := 370895292433042705861465

theorem tailTrace_1625211 : CollatzResearch.WordTrace tailWord_1625211 prefixEnd_1625211 370895292433042705861465 := by
  unfold tailWord_1625211
  simp only [CollatzResearch.WordTrace]
  refine ⟨59276314915145585785915487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39517543276763723857276991 59276314915145585785915487)
  ·
    refine ⟨88914472372718378678873231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59276314915145585785915487 88914472372718378678873231)
    ·
      refine ⟨133371708559077568018309847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88914472372718378678873231 133371708559077568018309847)
      ·
        refine ⟨200057562838616352027464771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133371708559077568018309847 200057562838616352027464771)
        ·
          refine ⟨300086344257924528041197157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200057562838616352027464771 300086344257924528041197157)
          ·
            refine ⟨56266189548360849007724467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300086344257924528041197157 56266189548360849007724467)
            ·
              refine ⟨84399284322541273511586701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56266189548360849007724467 84399284322541273511586701)
              ·
                refine ⟨31649731620952977566845013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84399284322541273511586701 31649731620952977566845013)
                ·
                  refine ⟨370895292433042705861465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31649731620952977566845013 370895292433042705861465)
                  ·
                    rfl

theorem cell21_1625211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_1625211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625211 prefixEnd_1625211 := by exact prefixLift 1625211
  have htrace : WordTrace (prefixWord ++ tailWord_1625211) baseStart_1625211 baseEnd_1625211 := by
    simpa [prefixWord, tailWord_1625211, baseEnd_1625211] using wordTrace_append hprefix tailTrace_1625211
  have hstable : (prefixWord ++ tailWord_1625211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625211).length < 2 ^ (prefixWord ++ tailWord_1625211).sum := by decide
  have hdescent : baseEnd_1625211 < baseStart_1625211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625290 : List Nat := [3, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_1625290 : Nat := 118140960795 + 1625290 * 2 ^ 59
def prefixEnd_1625290 : Nat := 4983230072969 + 3 ^ 40 * 1625290 * 2
def baseEnd_1625290 : Nat := 370913321309356124044637

theorem tailTrace_1625290 : CollatzResearch.WordTrace tailWord_1625290 prefixEnd_1625290 370913321309356124044637 := by
  unfold tailWord_1625290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14819799070464845569510331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39519464187906254852027549 14819799070464845569510331)
  ·
    refine ⟨22229698605697268354265497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14819799070464845569510331 22229698605697268354265497)
    ·
      refine ⟨16672273954272951265699123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22229698605697268354265497 16672273954272951265699123)
      ·
        refine ⟨25008410931409426898548685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16672273954272951265699123 25008410931409426898548685)
        ·
          refine ⟨9378154099278535086955757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25008410931409426898548685 9378154099278535086955757)
          ·
            refine ⟨3516807787229450657608409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9378154099278535086955757 3516807787229450657608409)
            ·
              refine ⟨2637605840422087993206307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3516807787229450657608409 2637605840422087993206307)
              ·
                refine ⟨3956408760633131989809461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637605840422087993206307 3956408760633131989809461)
                ·
                  refine ⟨370913321309356124044637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3956408760633131989809461 370913321309356124044637)
                  ·
                    rfl

theorem cell21_1625290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_1625290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625290 prefixEnd_1625290 := by exact prefixLift 1625290
  have htrace : WordTrace (prefixWord ++ tailWord_1625290) baseStart_1625290 baseEnd_1625290 := by
    simpa [prefixWord, tailWord_1625290, baseEnd_1625290] using wordTrace_append hprefix tailTrace_1625290
  have hstable : (prefixWord ++ tailWord_1625290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625290).length < 2 ^ (prefixWord ++ tailWord_1625290).sum := by decide
  have hdescent : baseEnd_1625290 < baseStart_1625290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625394 : List Nat := [3, 2, 1, 1, 4, 10]
def baseStart_1625394 : Nat := 118140960795 + 1625394 * 2 ^ 59
def prefixEnd_1625394 : Nat := 4983230072969 + 3 ^ 40 * 1625394 * 2
def baseEnd_1625394 : Nat := 13738409463936113122633

theorem tailTrace_1625394 : CollatzResearch.WordTrace tailWord_1625394 prefixEnd_1625394 13738409463936113122633 := by
  unfold tailWord_1625394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14820747368370652009956809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39521992982321738693218157 14820747368370652009956809)
  ·
    refine ⟨11115560526277989007467607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14820747368370652009956809 11115560526277989007467607)
    ·
      refine ⟨16673340789416983511201411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11115560526277989007467607 16673340789416983511201411)
      ·
        refine ⟨25010011184125475266802117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16673340789416983511201411 25010011184125475266802117)
        ·
          refine ⟨4689377097023526612525397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25010011184125475266802117 4689377097023526612525397)
          ·
            refine ⟨13738409463936113122633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4689377097023526612525397 13738409463936113122633)
            ·
              rfl

theorem cell21_1625394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 10].length) (baseStart_1625394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625394 prefixEnd_1625394 := by exact prefixLift 1625394
  have htrace : WordTrace (prefixWord ++ tailWord_1625394) baseStart_1625394 baseEnd_1625394 := by
    simpa [prefixWord, tailWord_1625394, baseEnd_1625394] using wordTrace_append hprefix tailTrace_1625394
  have hstable : (prefixWord ++ tailWord_1625394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625394).length < 2 ^ (prefixWord ++ tailWord_1625394).sum := by decide
  have hdescent : baseEnd_1625394 < baseStart_1625394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625397 : List Nat := [1, 3, 3, 1, 2, 3, 2, 2, 4]
def baseStart_1625397 : Nat := 118140960795 + 1625397 * 2 ^ 59
def prefixEnd_1625397 : Nat := 4983230072969 + 3 ^ 40 * 1625397 * 2
def baseEnd_1625397 : Nat := 370937740167147715761085

theorem tailTrace_1625397 : CollatzResearch.WordTrace tailWord_1625397 prefixEnd_1625397 370937740167147715761085 := by
  unfold tailWord_1625397
  simp only [CollatzResearch.WordTrace]
  refine ⟨59283098892471739552186445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39522065928314493034790963 59283098892471739552186445)
  ·
    refine ⟨22231162084676902332069917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59283098892471739552186445 22231162084676902332069917)
    ·
      refine ⟨8336685781753838374526219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22231162084676902332069917 8336685781753838374526219)
      ·
        refine ⟨12505028672630757561789329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8336685781753838374526219 12505028672630757561789329)
        ·
          refine ⟨9378771504473068171341997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12505028672630757561789329 9378771504473068171341997)
          ·
            refine ⟨3517039314177400564253249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9378771504473068171341997 3517039314177400564253249)
            ·
              refine ⟨2637779485633050423189937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3517039314177400564253249 2637779485633050423189937)
              ·
                refine ⟨1978334614224787817392453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2637779485633050423189937 1978334614224787817392453)
                ·
                  refine ⟨370937740167147715761085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978334614224787817392453 370937740167147715761085)
                  ·
                    rfl

theorem cell21_1625397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_1625397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625397 prefixEnd_1625397 := by exact prefixLift 1625397
  have htrace : WordTrace (prefixWord ++ tailWord_1625397) baseStart_1625397 baseEnd_1625397 := by
    simpa [prefixWord, tailWord_1625397, baseEnd_1625397] using wordTrace_append hprefix tailTrace_1625397
  have hstable : (prefixWord ++ tailWord_1625397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625397).length < 2 ^ (prefixWord ++ tailWord_1625397).sum := by decide
  have hdescent : baseEnd_1625397 < baseStart_1625397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625425 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 5]
def baseStart_1625425 : Nat := 118140960795 + 1625425 * 2 ^ 59
def prefixEnd_1625425 : Nat := 4983230072969 + 3 ^ 40 * 1625425 * 2
def baseEnd_1625425 : Nat := 370944130148625889294361

theorem tailTrace_1625425 : CollatzResearch.WordTrace tailWord_1625425 prefixEnd_1625425 370944130148625889294361 := by
  unfold tailWord_1625425
  simp only [CollatzResearch.WordTrace]
  refine ⟨59284120136370300334205729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39522746757580200222803819 59284120136370300334205729)
  ·
    refine ⟨44463090102277725250654297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59284120136370300334205729 44463090102277725250654297)
    ·
      refine ⟨33347317576708293937990723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44463090102277725250654297 33347317576708293937990723)
      ·
        refine ⟨50020976365062440906986085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33347317576708293937990723 50020976365062440906986085)
        ·
          refine ⟨9378933068449207670059891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50020976365062440906986085 9378933068449207670059891)
          ·
            refine ⟨14068399602673811505089837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9378933068449207670059891 14068399602673811505089837)
            ·
              refine ⟨5275649851002679314408689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14068399602673811505089837 5275649851002679314408689)
              ·
                refine ⟨3956737388252009485806517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5275649851002679314408689 3956737388252009485806517)
                ·
                  refine ⟨370944130148625889294361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3956737388252009485806517 370944130148625889294361)
                  ·
                    rfl

theorem cell21_1625425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_1625425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625425 prefixEnd_1625425 := by exact prefixLift 1625425
  have htrace : WordTrace (prefixWord ++ tailWord_1625425) baseStart_1625425 baseEnd_1625425 := by
    simpa [prefixWord, tailWord_1625425, baseEnd_1625425] using wordTrace_append hprefix tailTrace_1625425
  have hstable : (prefixWord ++ tailWord_1625425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625425).length < 2 ^ (prefixWord ++ tailWord_1625425).sum := by decide
  have hdescent : baseEnd_1625425 < baseStart_1625425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625439 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 6]
def baseStart_1625439 : Nat := 118140960795 + 1625439 * 2 ^ 59
def prefixEnd_1625439 : Nat := 4983230072969 + 3 ^ 40 * 1625439 * 2
def baseEnd_1625439 : Nat := 370947325139364976060999

theorem tailTrace_1625439 : CollatzResearch.WordTrace tailWord_1625439 prefixEnd_1625439 370947325139364976060999 := by
  unfold tailWord_1625439
  simp only [CollatzResearch.WordTrace]
  refine ⟨59284630758319580725215371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39523087172213053816810247 59284630758319580725215371)
  ·
    refine ⟨88926946137479371087823057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59284630758319580725215371 88926946137479371087823057)
    ·
      refine ⟨66695209603109528315867293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88926946137479371087823057 66695209603109528315867293)
      ·
        refine ⟨25010703601166073118450235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66695209603109528315867293 25010703601166073118450235)
        ·
          refine ⟨37516055401749109677675353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25010703601166073118450235 37516055401749109677675353)
          ·
            refine ⟨28137041551311832258256515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37516055401749109677675353 28137041551311832258256515)
            ·
              refine ⟨42205562326967748387384773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28137041551311832258256515 42205562326967748387384773)
              ·
                refine ⟨7913542936306452822634645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42205562326967748387384773 7913542936306452822634645)
                ·
                  refine ⟨370947325139364976060999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7913542936306452822634645 370947325139364976060999)
                  ·
                    rfl

theorem cell21_1625439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 6].length) (baseStart_1625439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625439 prefixEnd_1625439 := by exact prefixLift 1625439
  have htrace : WordTrace (prefixWord ++ tailWord_1625439) baseStart_1625439 baseEnd_1625439 := by
    simpa [prefixWord, tailWord_1625439, baseEnd_1625439] using wordTrace_append hprefix tailTrace_1625439
  have hstable : (prefixWord ++ tailWord_1625439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625439).length < 2 ^ (prefixWord ++ tailWord_1625439).sum := by decide
  have hdescent : baseEnd_1625439 < baseStart_1625439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625546 : List Nat := [3, 1, 2, 1, 2, 3, 2, 7]
def baseStart_1625546 : Nat := 118140960795 + 1625546 * 2 ^ 59
def prefixEnd_1625546 : Nat := 4983230072969 + 3 ^ 40 * 1625546 * 2
def baseEnd_1625546 : Nat := 123657247999052189259149

theorem tailTrace_1625546 : CollatzResearch.WordTrace tailWord_1625546 prefixEnd_1625546 123657247999052189259149 := by
  unfold tailWord_1625546
  simp only [CollatzResearch.WordTrace]
  refine ⟨14822133342232984499840123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39525688912621291999573661 14822133342232984499840123)
  ·
    refine ⟨22233200013349476749760185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14822133342232984499840123 22233200013349476749760185)
    ·
      refine ⟨16674900010012107562320139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22233200013349476749760185 16674900010012107562320139)
      ·
        refine ⟨25012350015018161343480209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16674900010012107562320139 25012350015018161343480209)
        ·
          refine ⟨18759262511263621007610157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25012350015018161343480209 18759262511263621007610157)
          ·
            refine ⟨7034723441723857877853809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18759262511263621007610157 7034723441723857877853809)
            ·
              refine ⟨5276042581292893408390357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7034723441723857877853809 5276042581292893408390357)
              ·
                refine ⟨123657247999052189259149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5276042581292893408390357 123657247999052189259149)
                ·
                  rfl

theorem cell21_1625546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_1625546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625546 prefixEnd_1625546 := by exact prefixLift 1625546
  have htrace : WordTrace (prefixWord ++ tailWord_1625546) baseStart_1625546 baseEnd_1625546 := by
    simpa [prefixWord, tailWord_1625546, baseEnd_1625546] using wordTrace_append hprefix tailTrace_1625546
  have hstable : (prefixWord ++ tailWord_1625546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625546).length < 2 ^ (prefixWord ++ tailWord_1625546).sum := by decide
  have hdescent : baseEnd_1625546 < baseStart_1625546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625611 : List Nat := [1, 1, 1, 1, 8, 1, 2, 3, 3]
def baseStart_1625611 : Nat := 118140960795 + 1625611 * 2 ^ 59
def prefixEnd_1625611 : Nat := 4983230072969 + 3 ^ 40 * 1625611 * 2
def baseEnd_1625611 : Nat := 370986577882730899193981

theorem tailTrace_1625611 : CollatzResearch.WordTrace tailWord_1625611 prefixEnd_1625611 370986577882730899193981 := by
  unfold tailWord_1625611
  simp only [CollatzResearch.WordTrace]
  refine ⟨59290904113696454100476687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39527269409130969400317791 59290904113696454100476687)
  ·
    refine ⟨88936356170544681150715031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59290904113696454100476687 88936356170544681150715031)
    ·
      refine ⟨133404534255817021726072547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88936356170544681150715031 133404534255817021726072547)
      ·
        refine ⟨200106801383725532589108821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133404534255817021726072547 200106801383725532589108821)
        ·
          refine ⟨2345001578715533585028619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 200106801383725532589108821 2345001578715533585028619)
          ·
            refine ⟨3517502368073300377542929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345001578715533585028619 3517502368073300377542929)
            ·
              refine ⟨2638126776054975283157197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3517502368073300377542929 2638126776054975283157197)
              ·
                refine ⟨989297541020615731183949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2638126776054975283157197 989297541020615731183949)
                ·
                  refine ⟨370986577882730899193981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989297541020615731183949 370986577882730899193981)
                  ·
                    rfl

theorem cell21_1625611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 3].length) (baseStart_1625611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625611 prefixEnd_1625611 := by exact prefixLift 1625611
  have htrace : WordTrace (prefixWord ++ tailWord_1625611) baseStart_1625611 baseEnd_1625611 := by
    simpa [prefixWord, tailWord_1625611, baseEnd_1625611] using wordTrace_append hprefix tailTrace_1625611
  have hstable : (prefixWord ++ tailWord_1625611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625611).length < 2 ^ (prefixWord ++ tailWord_1625611).sum := by decide
  have hdescent : baseEnd_1625611 < baseStart_1625611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625653 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 5]
def baseStart_1625653 : Nat := 118140960795 + 1625653 * 2 ^ 59
def prefixEnd_1625653 : Nat := 4983230072969 + 3 ^ 40 * 1625653 * 2
def baseEnd_1625653 : Nat := 370996162854948159493895

theorem tailTrace_1625653 : CollatzResearch.WordTrace tailWord_1625653 prefixEnd_1625653 370996162854948159493895 := by
  unfold tailWord_1625653
  simp only [CollatzResearch.WordTrace]
  refine ⟨59292435979544295273505613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39528290653029530182337075 59292435979544295273505613)
  ·
    refine ⟨22234663492329110727564605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59292435979544295273505613 22234663492329110727564605)
    ·
      refine ⟨8337998809623416522836727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22234663492329110727564605 8337998809623416522836727)
      ·
        refine ⟨12506998214435124784255091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8337998809623416522836727 12506998214435124784255091)
        ·
          refine ⟨18760497321652687176382637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12506998214435124784255091 18760497321652687176382637)
          ·
            refine ⟨7035186495619757691143489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18760497321652687176382637 7035186495619757691143489)
            ·
              refine ⟨5276389871714818268357617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7035186495619757691143489 5276389871714818268357617)
              ·
                refine ⟨3957292403786113701268213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5276389871714818268357617 3957292403786113701268213)
                ·
                  refine ⟨370996162854948159493895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3957292403786113701268213 370996162854948159493895)
                  ·
                    rfl

theorem cell21_1625653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_1625653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625653 prefixEnd_1625653 := by exact prefixLift 1625653
  have htrace : WordTrace (prefixWord ++ tailWord_1625653) baseStart_1625653 baseEnd_1625653 := by
    simpa [prefixWord, tailWord_1625653, baseEnd_1625653] using wordTrace_append hprefix tailTrace_1625653
  have hstable : (prefixWord ++ tailWord_1625653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625653).length < 2 ^ (prefixWord ++ tailWord_1625653).sum := by decide
  have hdescent : baseEnd_1625653 < baseStart_1625653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625684 : List Nat := [2, 4, 1, 1, 1, 2, 2, 4, 4]
def baseStart_1625684 : Nat := 118140960795 + 1625684 * 2 ^ 59
def prefixEnd_1625684 : Nat := 4983230072969 + 3 ^ 40 * 1625684 * 2
def baseEnd_1625684 : Nat := 371003237477298994477165

theorem tailTrace_1625684 : CollatzResearch.WordTrace tailWord_1625684 prefixEnd_1625684 371003237477298994477165 := by
  unfold tailWord_1625684
  simp only [CollatzResearch.WordTrace]
  refine ⟨29646783321215993783942053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39529044428287991711922737 29646783321215993783942053)
  ·
    refine ⟨5558771872727998834489135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29646783321215993783942053 5558771872727998834489135)
    ·
      refine ⟨8338157809091998251733703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5558771872727998834489135 8338157809091998251733703)
      ·
        refine ⟨12507236713637997377600555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8338157809091998251733703 12507236713637997377600555)
        ·
          refine ⟨18760855070456996066400833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12507236713637997377600555 18760855070456996066400833)
          ·
            refine ⟨14070641302842747049800625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18760855070456996066400833 14070641302842747049800625)
            ·
              refine ⟨10552980977132060287350469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14070641302842747049800625 10552980977132060287350469)
              ·
                refine ⟨1978683933212261303878213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10552980977132060287350469 1978683933212261303878213)
                ·
                  refine ⟨371003237477298994477165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978683933212261303878213 371003237477298994477165)
                  ·
                    rfl

theorem cell21_1625684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_1625684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625684 prefixEnd_1625684 := by exact prefixLift 1625684
  have htrace : WordTrace (prefixWord ++ tailWord_1625684) baseStart_1625684 baseEnd_1625684 := by
    simpa [prefixWord, tailWord_1625684, baseEnd_1625684] using wordTrace_append hprefix tailTrace_1625684
  have hstable : (prefixWord ++ tailWord_1625684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625684).length < 2 ^ (prefixWord ++ tailWord_1625684).sum := by decide
  have hdescent : baseEnd_1625684 < baseStart_1625684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625687 : List Nat := [1, 1, 3, 2, 2, 4, 3, 2, 3]
def baseStart_1625687 : Nat := 118140960795 + 1625687 * 2 ^ 59
def prefixEnd_1625687 : Nat := 4983230072969 + 3 ^ 40 * 1625687 * 2
def baseEnd_1625687 : Nat := 371003922118171655927159

theorem tailTrace_1625687 : CollatzResearch.WordTrace tailWord_1625687 prefixEnd_1625687 371003922118171655927159 := by
  unfold tailWord_1625687
  simp only [CollatzResearch.WordTrace]
  refine ⟨59293676061421119080243315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39529117374280746053495543 59293676061421119080243315)
  ·
    refine ⟨88940514092131678620364973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59293676061421119080243315 88940514092131678620364973)
    ·
      refine ⟨33352692784549379482636865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88940514092131678620364973 33352692784549379482636865)
      ·
        refine ⟨25014519588412034611977649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33352692784549379482636865 25014519588412034611977649)
        ·
          refine ⟨18760889691309025958983237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25014519588412034611977649 18760889691309025958983237)
          ·
            refine ⟨3517666817120442367309357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18760889691309025958983237 3517666817120442367309357)
            ·
              refine ⟨1319125056420165887741009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3517666817120442367309357 1319125056420165887741009)
              ·
                refine ⟨989343792315124415805757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319125056420165887741009 989343792315124415805757)
                ·
                  refine ⟨371003922118171655927159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989343792315124415805757 371003922118171655927159)
                  ·
                    rfl

theorem cell21_1625687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 2, 3].length) (baseStart_1625687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625687 prefixEnd_1625687 := by exact prefixLift 1625687
  have htrace : WordTrace (prefixWord ++ tailWord_1625687) baseStart_1625687 baseEnd_1625687 := by
    simpa [prefixWord, tailWord_1625687, baseEnd_1625687] using wordTrace_append hprefix tailTrace_1625687
  have hstable : (prefixWord ++ tailWord_1625687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625687).length < 2 ^ (prefixWord ++ tailWord_1625687).sum := by decide
  have hdescent : baseEnd_1625687 < baseStart_1625687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625701 : List Nat := [1, 3, 1, 3, 3, 1, 4, 1, 4]
def baseStart_1625701 : Nat := 118140960795 + 1625701 * 2 ^ 59
def prefixEnd_1625701 : Nat := 4983230072969 + 3 ^ 40 * 1625701 * 2
def baseEnd_1625701 : Nat := 371007117108910742693797

theorem tailTrace_1625701 : CollatzResearch.WordTrace tailWord_1625701 prefixEnd_1625701 371007117108910742693797 := by
  unfold tailWord_1625701
  simp only [CollatzResearch.WordTrace]
  refine ⟨59294186683370399471252957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39529457788913599647501971 59294186683370399471252957)
  ·
    refine ⟨22235320006263899801719859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59294186683370399471252957 22235320006263899801719859)
    ·
      refine ⟨33352980009395849702579789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22235320006263899801719859 33352980009395849702579789)
      ·
        refine ⟨12507367503523443638467421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33352980009395849702579789 12507367503523443638467421)
        ·
          refine ⟨4690262813821291364425283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12507367503523443638467421 4690262813821291364425283)
          ·
            refine ⟨7035394220731937046637925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690262813821291364425283 7035394220731937046637925)
            ·
              refine ⟨1319136416387238196244611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7035394220731937046637925 1319136416387238196244611)
              ·
                refine ⟨1978704624580857294366917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319136416387238196244611 1978704624580857294366917)
                ·
                  refine ⟨371007117108910742693797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978704624580857294366917 371007117108910742693797)
                  ·
                    rfl

theorem cell21_1625701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_1625701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625701 prefixEnd_1625701 := by exact prefixLift 1625701
  have htrace : WordTrace (prefixWord ++ tailWord_1625701) baseStart_1625701 baseEnd_1625701 := by
    simpa [prefixWord, tailWord_1625701, baseEnd_1625701] using wordTrace_append hprefix tailTrace_1625701
  have hstable : (prefixWord ++ tailWord_1625701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625701).length < 2 ^ (prefixWord ++ tailWord_1625701).sum := by decide
  have hdescent : baseEnd_1625701 < baseStart_1625701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625760 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 4]
def baseStart_1625760 : Nat := 118140960795 + 1625760 * 2 ^ 59
def prefixEnd_1625760 : Nat := 4983230072969 + 3 ^ 40 * 1625760 * 2
def baseEnd_1625760 : Nat := 371020581712739751210343

theorem tailTrace_1625760 : CollatzResearch.WordTrace tailWord_1625760 prefixEnd_1625760 371020581712739751210343 := by
  unfold tailWord_1625760
  simp only [CollatzResearch.WordTrace]
  refine ⟨29648169295078326273825367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39530892393437768365100489 29648169295078326273825367)
  ·
    refine ⟨44472253942617489410738051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29648169295078326273825367 44472253942617489410738051)
    ·
      refine ⟨66708380913926234116107077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44472253942617489410738051 66708380913926234116107077)
      ·
        refine ⟨12507821421361168896770077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66708380913926234116107077 12507821421361168896770077)
        ·
          refine ⟨4690433033010438336288779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12507821421361168896770077 4690433033010438336288779)
          ·
            refine ⟨7035649549515657504433169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4690433033010438336288779 7035649549515657504433169)
            ·
              refine ⟨5276737162136743128324877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7035649549515657504433169 5276737162136743128324877)
              ·
                refine ⟨1978776435801278673121829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5276737162136743128324877 1978776435801278673121829)
                ·
                  refine ⟨371020581712739751210343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978776435801278673121829 371020581712739751210343)
                  ·
                    rfl

theorem cell21_1625760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_1625760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625760 prefixEnd_1625760 := by exact prefixLift 1625760
  have htrace : WordTrace (prefixWord ++ tailWord_1625760) baseStart_1625760 baseEnd_1625760 := by
    simpa [prefixWord, tailWord_1625760, baseEnd_1625760] using wordTrace_append hprefix tailTrace_1625760
  have hstable : (prefixWord ++ tailWord_1625760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625760).length < 2 ^ (prefixWord ++ tailWord_1625760).sum := by decide
  have hdescent : baseEnd_1625760 < baseStart_1625760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625862 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1625862 : Nat := 118140960795 + 1625862 * 2 ^ 59
def prefixEnd_1625862 : Nat := 4983230072969 + 3 ^ 40 * 1625862 * 2
def baseEnd_1625862 : Nat := 371043859502410240510135

theorem tailTrace_1625862 : CollatzResearch.WordTrace tailWord_1625862 prefixEnd_1625862 371043859502410240510135 := by
  unfold tailWord_1625862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853126838618347623995745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39533372557191415978575893 1853126838618347623995745)
  ·
    refine ⟨1389845128963760717996809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1853126838618347623995745 1389845128963760717996809)
    ·
      refine ⟨1042383846722820538497607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1389845128963760717996809 1042383846722820538497607)
      ·
        refine ⟨1563575770084230807746411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042383846722820538497607 1563575770084230807746411)
        ·
          refine ⟨2345363655126346211619617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1563575770084230807746411 2345363655126346211619617)
          ·
            refine ⟨1759022741344759658714713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2345363655126346211619617 1759022741344759658714713)
            ·
              refine ⟨1319267056008569744036035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1759022741344759658714713 1319267056008569744036035)
              ·
                refine ⟨1978900584012854616054053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319267056008569744036035 1978900584012854616054053)
                ·
                  refine ⟨371043859502410240510135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978900584012854616054053 371043859502410240510135)
                  ·
                    rfl

theorem cell21_1625862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1625862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625862 prefixEnd_1625862 := by exact prefixLift 1625862
  have htrace : WordTrace (prefixWord ++ tailWord_1625862) baseStart_1625862 baseEnd_1625862 := by
    simpa [prefixWord, tailWord_1625862, baseEnd_1625862] using wordTrace_append hprefix tailTrace_1625862
  have hstable : (prefixWord ++ tailWord_1625862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625862).length < 2 ^ (prefixWord ++ tailWord_1625862).sum := by decide
  have hdescent : baseEnd_1625862 < baseStart_1625862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625909 : List Nat := [1, 3, 3, 1, 13]
def baseStart_1625909 : Nat := 118140960795 + 1625909 * 2 ^ 59
def prefixEnd_1625909 : Nat := 4983230072969 + 3 ^ 40 * 1625909 * 2
def baseEnd_1625909 : Nat := 4580920809169735842305

theorem tailTrace_1625909 : CollatzResearch.WordTrace tailWord_1625909 prefixEnd_1625909 4580920809169735842305 := by
  unfold tailWord_1625909
  simp only [CollatzResearch.WordTrace]
  refine ⟨59301773066616850994824781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39534515377744567329883187 59301773066616850994824781)
  ·
    refine ⟨22238164899981319123059293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59301773066616850994824781 22238164899981319123059293)
    ·
      refine ⟨8339311837492994671147235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22238164899981319123059293 8339311837492994671147235)
      ·
        refine ⟨12508967756239492006720853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8339311837492994671147235 12508967756239492006720853)
        ·
          refine ⟨4580920809169735842305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 12508967756239492006720853 4580920809169735842305)
          ·
            rfl

theorem cell21_1625909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 13].length) (baseStart_1625909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625909 prefixEnd_1625909 := by exact prefixLift 1625909
  have htrace : WordTrace (prefixWord ++ tailWord_1625909) baseStart_1625909 baseEnd_1625909 := by
    simpa [prefixWord, tailWord_1625909, baseEnd_1625909] using wordTrace_append hprefix tailTrace_1625909
  have hstable : (prefixWord ++ tailWord_1625909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625909).length < 2 ^ (prefixWord ++ tailWord_1625909).sum := by decide
  have hdescent : baseEnd_1625909 < baseStart_1625909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625912 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 4]
def baseStart_1625912 : Nat := 118140960795 + 1625912 * 2 ^ 59
def prefixEnd_1625912 : Nat := 4983230072969 + 3 ^ 40 * 1625912 * 2
def baseEnd_1625912 : Nat := 371055270183621264676699

theorem tailTrace_1625912 : CollatzResearch.WordTrace tailWord_1625912 prefixEnd_1625912 371055270183621264676699 := by
  unfold tailWord_1625912
  simp only [CollatzResearch.WordTrace]
  refine ⟨29650941242802991253591995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39534588323737321671455993 29650941242802991253591995)
  ·
    refine ⟨44476411864204486880387993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29650941242802991253591995 44476411864204486880387993)
    ·
      refine ⟨33357308898153365160290995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44476411864204486880387993 33357308898153365160290995)
      ·
        refine ⟨50035963347230047740436493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33357308898153365160290995 50035963347230047740436493)
        ·
          refine ⟨18763486255211267902663685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50035963347230047740436493 18763486255211267902663685)
          ·
            refine ⟨3518153672852112731749441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18763486255211267902663685 3518153672852112731749441)
            ·
              refine ⟨2638615254639084548812081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3518153672852112731749441 2638615254639084548812081)
              ·
                refine ⟨1978961440979313411609061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638615254639084548812081 1978961440979313411609061)
                ·
                  refine ⟨371055270183621264676699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1978961440979313411609061 371055270183621264676699)
                  ·
                    rfl

theorem cell21_1625912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_1625912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625912 prefixEnd_1625912 := by exact prefixLift 1625912
  have htrace : WordTrace (prefixWord ++ tailWord_1625912) baseStart_1625912 baseEnd_1625912 := by
    simpa [prefixWord, tailWord_1625912, baseEnd_1625912] using wordTrace_append hprefix tailTrace_1625912
  have hstable : (prefixWord ++ tailWord_1625912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625912).length < 2 ^ (prefixWord ++ tailWord_1625912).sum := by decide
  have hdescent : baseEnd_1625912 < baseStart_1625912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1625943 : List Nat := [1, 1, 3, 2, 5, 1, 3, 5]
def baseStart_1625943 : Nat := 118140960795 + 1625943 * 2 ^ 59
def prefixEnd_1625943 : Nat := 4983230072969 + 3 ^ 40 * 1625943 * 2
def baseEnd_1625943 : Nat := 123687448268657366553323

theorem tailTrace_1625943 : CollatzResearch.WordTrace tailWord_1625943 prefixEnd_1625943 123687448268657366553323 := by
  unfold tailWord_1625943
  simp only [CollatzResearch.WordTrace]
  refine ⟨59303013148493674801562483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39535342098995783201041655 59303013148493674801562483)
  ·
    refine ⟨88954519722740512202343725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59303013148493674801562483 88954519722740512202343725)
    ·
      refine ⟨33357944896027692075878897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88954519722740512202343725 33357944896027692075878897)
      ·
        refine ⟨25018458672020769056909173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33357944896027692075878897 25018458672020769056909173)
        ·
          refine ⟨2345480500501947099085235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25018458672020769056909173 2345480500501947099085235)
          ·
            refine ⟨3518220750752920648627853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345480500501947099085235 3518220750752920648627853)
            ·
              refine ⟨1319332781532345243235445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3518220750752920648627853 1319332781532345243235445)
              ·
                refine ⟨123687448268657366553323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1319332781532345243235445 123687448268657366553323)
                ·
                  rfl

theorem cell21_1625943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 5].length) (baseStart_1625943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1625943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1625943 prefixEnd_1625943 := by exact prefixLift 1625943
  have htrace : WordTrace (prefixWord ++ tailWord_1625943) baseStart_1625943 baseEnd_1625943 := by
    simpa [prefixWord, tailWord_1625943, baseEnd_1625943] using wordTrace_append hprefix tailTrace_1625943
  have hstable : (prefixWord ++ tailWord_1625943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1625943).length < 2 ^ (prefixWord ++ tailWord_1625943).sum := by decide
  have hdescent : baseEnd_1625943 < baseStart_1625943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1625943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626008 : List Nat := [2, 1, 2, 6, 1, 2, 1, 3, 3]
def baseStart_1626008 : Nat := 118140960795 + 1626008 * 2 ^ 59
def prefixEnd_1626008 : Nat := 4983230072969 + 3 ^ 40 * 1626008 * 2
def baseEnd_1626008 : Nat := 371077178691546431076503

theorem tailTrace_1626008 : CollatzResearch.WordTrace tailWord_1626008 prefixEnd_1626008 371077178691546431076503 := by
  unfold tailWord_1626008
  simp only [CollatzResearch.WordTrace]
  refine ⟨29652691946629095451339339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39536922595505460601785785 29652691946629095451339339)
  ·
    refine ⟨44479037919943643177009009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29652691946629095451339339 44479037919943643177009009)
    ·
      refine ⟨33359278439957732382756757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44479037919943643177009009 33359278439957732382756757)
      ·
        refine ⟨1563716176873018705441723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33359278439957732382756757 1563716176873018705441723)
        ·
          refine ⟨2345574265309528058162585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1563716176873018705441723 2345574265309528058162585)
          ·
            refine ⟨1759180698982146043621939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2345574265309528058162585 1759180698982146043621939)
            ·
              refine ⟨2638771048473219065432909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759180698982146043621939 2638771048473219065432909)
              ·
                refine ⟨989539143177457149537341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2638771048473219065432909 989539143177457149537341)
                ·
                  refine ⟨371077178691546431076503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989539143177457149537341 371077178691546431076503)
                  ·
                    rfl

theorem cell21_1626008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 3, 3].length) (baseStart_1626008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626008 prefixEnd_1626008 := by exact prefixLift 1626008
  have htrace : WordTrace (prefixWord ++ tailWord_1626008) baseStart_1626008 baseEnd_1626008 := by
    simpa [prefixWord, tailWord_1626008, baseEnd_1626008] using wordTrace_append hprefix tailTrace_1626008
  have hstable : (prefixWord ++ tailWord_1626008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626008).length < 2 ^ (prefixWord ++ tailWord_1626008).sum := by decide
  have hdescent : baseEnd_1626008 < baseStart_1626008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626033 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 5]
def baseStart_1626033 : Nat := 118140960795 + 1626033 * 2 ^ 59
def prefixEnd_1626033 : Nat := 4983230072969 + 3 ^ 40 * 1626033 * 2
def baseEnd_1626033 : Nat := 371082884032151943159785

theorem tailTrace_1626033 : CollatzResearch.WordTrace tailWord_1626033 prefixEnd_1626033 371082884032151943159785 := by
  unfold tailWord_1626033
  simp only [CollatzResearch.WordTrace]
  refine ⟨59306295718167620172338753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39537530478778413448225835 59306295718167620172338753)
  ·
    refine ⟨44479721788625715129254065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59306295718167620172338753 44479721788625715129254065)
    ·
      refine ⟨33359791341469286346940549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44479721788625715129254065 33359791341469286346940549)
      ·
        refine ⟨6254960876525491190051353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33359791341469286346940549 6254960876525491190051353)
        ·
          refine ⟨4691220657394118392538515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6254960876525491190051353 4691220657394118392538515)
          ·
            refine ⟨7036830986091177588807773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4691220657394118392538515 7036830986091177588807773)
            ·
              refine ⟨2638811619784191595802915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7036830986091177588807773 2638811619784191595802915)
              ·
                refine ⟨3958217429676287393704373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638811619784191595802915 3958217429676287393704373)
                ·
                  refine ⟨371082884032151943159785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3958217429676287393704373 371082884032151943159785)
                  ·
                    rfl

theorem cell21_1626033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 5].length) (baseStart_1626033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626033 prefixEnd_1626033 := by exact prefixLift 1626033
  have htrace : WordTrace (prefixWord ++ tailWord_1626033) baseStart_1626033 baseEnd_1626033 := by
    simpa [prefixWord, tailWord_1626033, baseEnd_1626033] using wordTrace_append hprefix tailTrace_1626033
  have hstable : (prefixWord ++ tailWord_1626033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626033).length < 2 ^ (prefixWord ++ tailWord_1626033).sum := by decide
  have hdescent : baseEnd_1626033 < baseStart_1626033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626036 : List Nat := [2, 5, 2, 1, 2, 1, 2, 6]
def baseStart_1626036 : Nat := 118140960795 + 1626036 * 2 ^ 59
def prefixEnd_1626036 : Nat := 4983230072969 + 3 ^ 40 * 1626036 * 2
def baseEnd_1626036 : Nat := 123694522891008201536593

theorem tailTrace_1626036 : CollatzResearch.WordTrace tailWord_1626036 prefixEnd_1626036 123694522891008201536593 := by
  unfold tailWord_1626036
  simp only [CollatzResearch.WordTrace]
  refine ⟨29653202568578375842348981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39537603424771167789798641 29653202568578375842348981)
  ·
    refine ⟨2779987740804222735220217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29653202568578375842348981 2779987740804222735220217)
    ·
      refine ⟨2084990805603167051415163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2779987740804222735220217 2084990805603167051415163)
      ·
        refine ⟨3127486208404750577122745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2084990805603167051415163 3127486208404750577122745)
        ·
          refine ⟨2345614656303562932842059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3127486208404750577122745 2345614656303562932842059)
          ·
            refine ⟨3518421984455344399263089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345614656303562932842059 3518421984455344399263089)
            ·
              refine ⟨2638816488341508299447317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3518421984455344399263089 2638816488341508299447317)
              ·
                refine ⟨123694522891008201536593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2638816488341508299447317 123694522891008201536593)
                ·
                  rfl

theorem cell21_1626036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_1626036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626036 prefixEnd_1626036 := by exact prefixLift 1626036
  have htrace : WordTrace (prefixWord ++ tailWord_1626036) baseStart_1626036 baseEnd_1626036 := by
    simpa [prefixWord, tailWord_1626036, baseEnd_1626036] using wordTrace_append hprefix tailTrace_1626036
  have hstable : (prefixWord ++ tailWord_1626036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626036).length < 2 ^ (prefixWord ++ tailWord_1626036).sum := by decide
  have hdescent : baseEnd_1626036 < baseStart_1626036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626047 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 4]
def baseStart_1626047 : Nat := 118140960795 + 1626047 * 2 ^ 59
def prefixEnd_1626047 : Nat := 4983230072969 + 3 ^ 40 * 1626047 * 2
def baseEnd_1626047 : Nat := 371086079022891029926423

theorem tailTrace_1626047 : CollatzResearch.WordTrace tailWord_1626047 prefixEnd_1626047 371086079022891029926423 := by
  unfold tailWord_1626047
  simp only [CollatzResearch.WordTrace]
  refine ⟨59306806340116900563348395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39537870893411267042232263 59306806340116900563348395)
  ·
    refine ⟨88960209510175350845022593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59306806340116900563348395 88960209510175350845022593)
    ·
      refine ⟨66720157132631513133766945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88960209510175350845022593 66720157132631513133766945)
      ·
        refine ⟨50040117849473634850325209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66720157132631513133766945 50040117849473634850325209)
        ·
          refine ⟨37530088387105226137743907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50040117849473634850325209 37530088387105226137743907)
          ·
            refine ⟨56295132580657839206615861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37530088387105226137743907 56295132580657839206615861)
            ·
              refine ⟨5277668679436672425620237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56295132580657839206615861 5277668679436672425620237)
              ·
                refine ⟨1979125754788752159607589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5277668679436672425620237 1979125754788752159607589)
                ·
                  refine ⟨371086079022891029926423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1979125754788752159607589 371086079022891029926423)
                  ·
                    rfl

theorem cell21_1626047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 4].length) (baseStart_1626047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626047 prefixEnd_1626047 := by exact prefixLift 1626047
  have htrace : WordTrace (prefixWord ++ tailWord_1626047) baseStart_1626047 baseEnd_1626047 := by
    simpa [prefixWord, tailWord_1626047, baseEnd_1626047] using wordTrace_append hprefix tailTrace_1626047
  have hstable : (prefixWord ++ tailWord_1626047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626047).length < 2 ^ (prefixWord ++ tailWord_1626047).sum := by decide
  have hdescent : baseEnd_1626047 < baseStart_1626047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626106 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_1626106 : Nat := 118140960795 + 1626106 * 2 ^ 59
def prefixEnd_1626106 : Nat := 4983230072969 + 3 ^ 40 * 1626106 * 2
def baseEnd_1626106 : Nat := 371099543626720038442969

theorem tailTrace_1626106 : CollatzResearch.WordTrace tailWord_1626106 prefixEnd_1626106 371099543626720038442969 := by
  unfold tailWord_1626106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14827239561725788409936543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39539305497935435759830781 14827239561725788409936543)
  ·
    refine ⟨22240859342588682614904815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14827239561725788409936543 22240859342588682614904815)
    ·
      refine ⟨33361289013883023922357223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22240859342588682614904815 33361289013883023922357223)
      ·
        refine ⟨50041933520824535883535835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33361289013883023922357223 50041933520824535883535835)
        ·
          refine ⟨75062900281236803825303753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50041933520824535883535835 75062900281236803825303753)
          ·
            refine ⟨56297175210927602868977815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75062900281236803825303753 56297175210927602868977815)
            ·
              refine ⟨84445762816391404303466723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56297175210927602868977815 84445762816391404303466723)
              ·
                refine ⟨126668644224587106455200085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84445762816391404303466723 126668644224587106455200085)
                ·
                  refine ⟨371099543626720038442969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 126668644224587106455200085 371099543626720038442969)
                  ·
                    rfl

theorem cell21_1626106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_1626106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626106 prefixEnd_1626106 := by exact prefixLift 1626106
  have htrace : WordTrace (prefixWord ++ tailWord_1626106) baseStart_1626106 baseEnd_1626106 := by
    simpa [prefixWord, tailWord_1626106, baseEnd_1626106] using wordTrace_append hprefix tailTrace_1626106
  have hstable : (prefixWord ++ tailWord_1626106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626106).length < 2 ^ (prefixWord ++ tailWord_1626106).sum := by decide
  have hdescent : baseEnd_1626106 < baseStart_1626106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626118 : List Nat := [6, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1626118 : Nat := 118140960795 + 1626118 * 2 ^ 59
def prefixEnd_1626118 : Nat := 4983230072969 + 3 ^ 40 * 1626118 * 2
def baseEnd_1626118 : Nat := 371102282190210684242945

theorem tailTrace_1626118 : CollatzResearch.WordTrace tailWord_1626118 prefixEnd_1626118 371102282190210684242945 := by
  unfold tailWord_1626118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853418622589364990286969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39539597281906453126122005 1853418622589364990286969)
  ·
    refine ⟨1390063966942023742715227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1853418622589364990286969 1390063966942023742715227)
    ·
      refine ⟨2085095950413035614072841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390063966942023742715227 2085095950413035614072841)
      ·
        refine ⟨1563821962809776710554631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2085095950413035614072841 1563821962809776710554631)
        ·
          refine ⟨2345732944214665065831947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1563821962809776710554631 2345732944214665065831947)
          ·
            refine ⟨3518599416321997598747921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345732944214665065831947 3518599416321997598747921)
            ·
              refine ⟨2638949562241498199060941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3518599416321997598747921 2638949562241498199060941)
              ·
                refine ⟨989606085840561824647853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2638949562241498199060941 989606085840561824647853)
                ·
                  refine ⟨371102282190210684242945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989606085840561824647853 371102282190210684242945)
                  ·
                    rfl

theorem cell21_1626118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1626118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626118 prefixEnd_1626118 := by exact prefixLift 1626118
  have htrace : WordTrace (prefixWord ++ tailWord_1626118) baseStart_1626118 baseEnd_1626118 := by
    simpa [prefixWord, tailWord_1626118, baseEnd_1626118] using wordTrace_append hprefix tailTrace_1626118
  have hstable : (prefixWord ++ tailWord_1626118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626118).length < 2 ^ (prefixWord ++ tailWord_1626118).sum := by decide
  have hdescent : baseEnd_1626118 < baseStart_1626118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626126 : List Nat := [4, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_1626126 : Nat := 118140960795 + 1626126 * 2 ^ 59
def prefixEnd_1626126 : Nat := 4983230072969 + 3 ^ 40 * 1626126 * 2
def baseEnd_1626126 : Nat := 371104107899204448109595

theorem tailTrace_1626126 : CollatzResearch.WordTrace tailWord_1626126 prefixEnd_1626126 371104107899204448109595 := by
  unfold tailWord_1626126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7413710963353837131934279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39539791804553798036982821 7413710963353837131934279)
  ·
    refine ⟨11120566445030755697901419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7413710963353837131934279 11120566445030755697901419)
    ·
      refine ⟨16680849667546133546852129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11120566445030755697901419 16680849667546133546852129)
      ·
        refine ⟨12510637250659600160139097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16680849667546133546852129 12510637250659600160139097)
        ·
          refine ⟨9382977937994700120104323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12510637250659600160139097 9382977937994700120104323)
          ·
            refine ⟨14074466906992050180156485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9382977937994700120104323 14074466906992050180156485)
            ·
              refine ⟨2638962545061009408779341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14074466906992050180156485 2638962545061009408779341)
              ·
                refine ⟨989610954397878528292253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2638962545061009408779341 989610954397878528292253)
                ·
                  refine ⟨371104107899204448109595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989610954397878528292253 371104107899204448109595)
                  ·
                    rfl

theorem cell21_1626126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_1626126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626126 prefixEnd_1626126 := by exact prefixLift 1626126
  have htrace : WordTrace (prefixWord ++ tailWord_1626126) baseStart_1626126 baseEnd_1626126 := by
    simpa [prefixWord, tailWord_1626126, baseEnd_1626126] using wordTrace_append hprefix tailTrace_1626126
  have hstable : (prefixWord ++ tailWord_1626126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626126).length < 2 ^ (prefixWord ++ tailWord_1626126).sum := by decide
  have hdescent : baseEnd_1626126 < baseStart_1626126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626140 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 4]
def baseStart_1626140 : Nat := 118140960795 + 1626140 * 2 ^ 59
def prefixEnd_1626140 : Nat := 4983230072969 + 3 ^ 40 * 1626140 * 2
def baseEnd_1626140 : Nat := 371107302889943534876233

theorem tailTrace_1626140 : CollatzResearch.WordTrace tailWord_1626140 prefixEnd_1626140 371107302889943534876233 := by
  unfold tailWord_1626140
  simp only [CollatzResearch.WordTrace]
  refine ⟨29655099164389988723241937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39540132219186651630989249 29655099164389988723241937)
  ·
    refine ⟨22241324373292491542431453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29655099164389988723241937 22241324373292491542431453)
    ·
      refine ⟨8340496639984684328411795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22241324373292491542431453 8340496639984684328411795)
      ·
        refine ⟨12510744959977026492617693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8340496639984684328411795 12510744959977026492617693)
        ·
          refine ⟨4691529359991384934731635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12510744959977026492617693 4691529359991384934731635)
          ·
            refine ⟨7037294039987077402097453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4691529359991384934731635 7037294039987077402097453)
            ·
              refine ⟨2638985264995154025786545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7037294039987077402097453 2638985264995154025786545)
              ·
                refine ⟨1979238948746365519339909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638985264995154025786545 1979238948746365519339909)
                ·
                  refine ⟨371107302889943534876233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1979238948746365519339909 371107302889943534876233)
                  ·
                    rfl

theorem cell21_1626140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_1626140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626140 prefixEnd_1626140 := by exact prefixLift 1626140
  have htrace : WordTrace (prefixWord ++ tailWord_1626140) baseStart_1626140 baseEnd_1626140 := by
    simpa [prefixWord, tailWord_1626140, baseEnd_1626140] using wordTrace_append hprefix tailTrace_1626140
  have hstable : (prefixWord ++ tailWord_1626140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626140).length < 2 ^ (prefixWord ++ tailWord_1626140).sum := by decide
  have hdescent : baseEnd_1626140 < baseStart_1626140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626202 : List Nat := [3, 1, 1, 2, 1, 1, 7, 2, 3]
def baseStart_1626202 : Nat := 118140960795 + 1626202 * 2 ^ 59
def prefixEnd_1626202 : Nat := 4983230072969 + 3 ^ 40 * 1626202 * 2
def baseEnd_1626202 : Nat := 371121452134645204842773

theorem tailTrace_1626202 : CollatzResearch.WordTrace tailWord_1626202 prefixEnd_1626202 371121452134645204842773 := by
  unfold tailWord_1626202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14828114913638840508810215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39541639769703574690160573 14828114913638840508810215)
  ·
    refine ⟨22242172370458260763215323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14828114913638840508810215 22242172370458260763215323)
    ·
      refine ⟨33363258555687391144822985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22242172370458260763215323 33363258555687391144822985)
      ·
        refine ⟨25022443916765543358617239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33363258555687391144822985 25022443916765543358617239)
        ·
          refine ⟨37533665875148315037925859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25022443916765543358617239 37533665875148315037925859)
          ·
            refine ⟨56300498812722472556888789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37533665875148315037925859 56300498812722472556888789)
            ·
              refine ⟨1319542940923182950552081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56300498812722472556888789 1319542940923182950552081)
              ·
                refine ⟨989657205692387212914061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319542940923182950552081 989657205692387212914061)
                ·
                  refine ⟨371121452134645204842773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989657205692387212914061 371121452134645204842773)
                  ·
                    rfl

theorem cell21_1626202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_1626202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626202 prefixEnd_1626202 := by exact prefixLift 1626202
  have htrace : WordTrace (prefixWord ++ tailWord_1626202) baseStart_1626202 baseEnd_1626202 := by
    simpa [prefixWord, tailWord_1626202, baseEnd_1626202] using wordTrace_append hprefix tailTrace_1626202
  have hstable : (prefixWord ++ tailWord_1626202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626202).length < 2 ^ (prefixWord ++ tailWord_1626202).sum := by decide
  have hdescent : baseEnd_1626202 < baseStart_1626202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626213 : List Nat := [1, 3, 1, 3, 2, 2, 1, 8]
def baseStart_1626213 : Nat := 118140960795 + 1626213 * 2 ^ 59
def prefixEnd_1626213 : Nat := 4983230072969 + 3 ^ 40 * 1626213 * 2
def baseEnd_1626213 : Nat := 123707987494837210053139

theorem tailTrace_1626213 : CollatzResearch.WordTrace tailWord_1626213 prefixEnd_1626213 123707987494837210053139 := by
  unfold tailWord_1626213
  simp only [CollatzResearch.WordTrace]
  refine ⟨59312860857515510913891293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39541907238343673942594195 59312860857515510913891293)
  ·
    refine ⟨22242322821568316592709235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59312860857515510913891293 22242322821568316592709235)
    ·
      refine ⟨33363484232352474889063853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22242322821568316592709235 33363484232352474889063853)
      ·
        refine ⟨12511306587132178083398945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33363484232352474889063853 12511306587132178083398945)
        ·
          refine ⟨9383479940349133562549209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12511306587132178083398945 9383479940349133562549209)
          ·
            refine ⟨7037609955261850171911907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9383479940349133562549209 7037609955261850171911907)
            ·
              refine ⟨10556414932892775257867861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7037609955261850171911907 10556414932892775257867861)
              ·
                refine ⟨123707987494837210053139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10556414932892775257867861 123707987494837210053139)
                ·
                  rfl

theorem cell21_1626213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 8].length) (baseStart_1626213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626213 prefixEnd_1626213 := by exact prefixLift 1626213
  have htrace : WordTrace (prefixWord ++ tailWord_1626213) baseStart_1626213 baseEnd_1626213 := by
    simpa [prefixWord, tailWord_1626213, baseEnd_1626213] using wordTrace_append hprefix tailTrace_1626213
  have hstable : (prefixWord ++ tailWord_1626213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626213).length < 2 ^ (prefixWord ++ tailWord_1626213).sum := by decide
  have hdescent : baseEnd_1626213 < baseStart_1626213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626230 : List Nat := [5, 1, 1, 2, 1, 2, 2, 7]
def baseStart_1626230 : Nat := 118140960795 + 1626230 * 2 ^ 59
def prefixEnd_1626230 : Nat := 4983230072969 + 3 ^ 40 * 1626230 * 2
def baseEnd_1626230 : Nat := 123709280705374459458683

theorem tailTrace_1626230 : CollatzResearch.WordTrace tailWord_1626230 prefixEnd_1626230 123709280705374459458683 := by
  unfold tailWord_1626230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707092556153370176078759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39542320598969281878173429 3707092556153370176078759)
  ·
    refine ⟨5560638834230055264118139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3707092556153370176078759 5560638834230055264118139)
    ·
      refine ⟨8340958251345082896177209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5560638834230055264118139 8340958251345082896177209)
      ·
        refine ⟨6255718688508812172132907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8340958251345082896177209 6255718688508812172132907)
        ·
          refine ⟨9383578032763218258199361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6255718688508812172132907 9383578032763218258199361)
          ·
            refine ⟨7037683524572413693649521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9383578032763218258199361 7037683524572413693649521)
            ·
              refine ⟨5278262643429310270237141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7037683524572413693649521 5278262643429310270237141)
              ·
                refine ⟨123709280705374459458683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5278262643429310270237141 123709280705374459458683)
                ·
                  rfl

theorem cell21_1626230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_1626230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626230 prefixEnd_1626230 := by exact prefixLift 1626230
  have htrace : WordTrace (prefixWord ++ tailWord_1626230) baseStart_1626230 baseEnd_1626230 := by
    simpa [prefixWord, tailWord_1626230, baseEnd_1626230] using wordTrace_append hprefix tailTrace_1626230
  have hstable : (prefixWord ++ tailWord_1626230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626230).length < 2 ^ (prefixWord ++ tailWord_1626230).sum := by decide
  have hdescent : baseEnd_1626230 < baseStart_1626230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626261 : List Nat := [1, 3, 2, 1, 1, 1, 5, 4, 3]
def baseStart_1626261 : Nat := 118140960795 + 1626261 * 2 ^ 59
def prefixEnd_1626261 : Nat := 4983230072969 + 3 ^ 40 * 1626261 * 2
def baseEnd_1626261 : Nat := 371134916738474213359319

theorem tailTrace_1626261 : CollatzResearch.WordTrace tailWord_1626261 prefixEnd_1626261 371134916738474213359319 := by
  unfold tailWord_1626261
  simp only [CollatzResearch.WordTrace]
  refine ⟨59314611561341615111638637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39543074374227743407759091 59314611561341615111638637)
  ·
    refine ⟨22242979335503105666864489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59314611561341615111638637 22242979335503105666864489)
    ·
      refine ⟨16682234501627329250148367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22242979335503105666864489 16682234501627329250148367)
      ·
        refine ⟨25023351752440993875222551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16682234501627329250148367 25023351752440993875222551)
        ·
          refine ⟨37535027628661490812833827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25023351752440993875222551 37535027628661490812833827)
          ·
            refine ⟨56302541442992236219250741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37535027628661490812833827 56302541442992236219250741)
            ·
              refine ⟨5278363260280522145554757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56302541442992236219250741 5278363260280522145554757)
              ·
                refine ⟨989693111302597902291517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5278363260280522145554757 989693111302597902291517)
                ·
                  refine ⟨371134916738474213359319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989693111302597902291517 371134916738474213359319)
                  ·
                    rfl

theorem cell21_1626261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_1626261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626261 prefixEnd_1626261 := by exact prefixLift 1626261
  have htrace : WordTrace (prefixWord ++ tailWord_1626261) baseStart_1626261 baseEnd_1626261 := by
    simpa [prefixWord, tailWord_1626261, baseEnd_1626261] using wordTrace_append hprefix tailTrace_1626261
  have hstable : (prefixWord ++ tailWord_1626261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626261).length < 2 ^ (prefixWord ++ tailWord_1626261).sum := by decide
  have hdescent : baseEnd_1626261 < baseStart_1626261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626303 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 9]
def baseStart_1626303 : Nat := 118140960795 + 1626303 * 2 ^ 59
def prefixEnd_1626303 : Nat := 4983230072969 + 3 ^ 40 * 1626303 * 2
def baseEnd_1626303 : Nat := 371144501710691473659233

theorem tailTrace_1626303 : CollatzResearch.WordTrace tailWord_1626303 prefixEnd_1626303 371144501710691473659233 := by
  unfold tailWord_1626303
  simp only [CollatzResearch.WordTrace]
  refine ⟨59316143427189456284667563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39544095618126304189778375 59316143427189456284667563)
  ·
    refine ⟨88974215140784184427001345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59316143427189456284667563 88974215140784184427001345)
    ·
      refine ⟨66730661355588138320251009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88974215140784184427001345 66730661355588138320251009)
      ·
        refine ⟨50047996016691103740188257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66730661355588138320251009 50047996016691103740188257)
        ·
          refine ⟨37535997012518327805141193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50047996016691103740188257 37535997012518327805141193)
          ·
            refine ⟨28151997759388745853855895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37535997012518327805141193 28151997759388745853855895)
            ·
              refine ⟨42227996639083118780783843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28151997759388745853855895 42227996639083118780783843)
              ·
                refine ⟨63341994958624678171175765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42227996639083118780783843 63341994958624678171175765)
                ·
                  refine ⟨371144501710691473659233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63341994958624678171175765 371144501710691473659233)
                  ·
                    rfl

theorem cell21_1626303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_1626303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626303 prefixEnd_1626303 := by exact prefixLift 1626303
  have htrace : WordTrace (prefixWord ++ tailWord_1626303) baseStart_1626303 baseEnd_1626303 := by
    simpa [prefixWord, tailWord_1626303, baseEnd_1626303] using wordTrace_append hprefix tailTrace_1626303
  have hstable : (prefixWord ++ tailWord_1626303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626303).length < 2 ^ (prefixWord ++ tailWord_1626303).sum := by decide
  have hdescent : baseEnd_1626303 < baseStart_1626303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626326 : List Nat := [5, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1626326 : Nat := 118140960795 + 1626326 * 2 ^ 59
def prefixEnd_1626326 : Nat := 4983230072969 + 3 ^ 40 * 1626326 * 2
def baseEnd_1626326 : Nat := 371149750624048544775853

theorem tailTrace_1626326 : CollatzResearch.WordTrace tailWord_1626326 prefixEnd_1626326 371149750624048544775853 := by
  unfold tailWord_1626326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707311394131633200797177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39544654870737420808503221 3707311394131633200797177)
  ·
    refine ⟨2780483545598724900597883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3707311394131633200797177 2780483545598724900597883)
    ·
      refine ⟨4170725318398087350896825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2780483545598724900597883 4170725318398087350896825)
      ·
        refine ⟨3128043988798565513172619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4170725318398087350896825 3128043988798565513172619)
        ·
          refine ⟨4692065983197848269758929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3128043988798565513172619 4692065983197848269758929)
          ·
            refine ⟨3519049487398386202319197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4692065983197848269758929 3519049487398386202319197)
            ·
              refine ⟨1319643557774394825869699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3519049487398386202319197 1319643557774394825869699)
              ·
                refine ⟨1979465336661592238804549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319643557774394825869699 1979465336661592238804549)
                ·
                  refine ⟨371149750624048544775853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1979465336661592238804549 371149750624048544775853)
                  ·
                    rfl

theorem cell21_1626326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1626326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626326 prefixEnd_1626326 := by exact prefixLift 1626326
  have htrace : WordTrace (prefixWord ++ tailWord_1626326) baseStart_1626326 baseEnd_1626326 := by
    simpa [prefixWord, tailWord_1626326, baseEnd_1626326] using wordTrace_append hprefix tailTrace_1626326
  have hstable : (prefixWord ++ tailWord_1626326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626326).length < 2 ^ (prefixWord ++ tailWord_1626326).sum := by decide
  have hdescent : baseEnd_1626326 < baseStart_1626326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626354 : List Nat := [3, 2, 1, 3, 2, 1, 3, 3, 3]
def baseStart_1626354 : Nat := 118140960795 + 1626354 * 2 ^ 59
def prefixEnd_1626354 : Nat := 4983230072969 + 3 ^ 40 * 1626354 * 2
def baseEnd_1626354 : Nat := 371156140605526718309129

theorem tailTrace_1626354 : CollatzResearch.WordTrace tailWord_1626354 prefixEnd_1626354 371156140605526718309129 := by
  unfold tailWord_1626354
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829500887501172998693529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39545335700003127996516077 14829500887501172998693529)
  ·
    refine ⟨11122125665625879749020147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14829500887501172998693529 11122125665625879749020147)
    ·
      refine ⟨16683188498438819623530221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11122125665625879749020147 16683188498438819623530221)
      ·
        refine ⟨6256195686914557358823833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16683188498438819623530221 6256195686914557358823833)
        ·
          refine ⟨4692146765185918019117875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6256195686914557358823833 4692146765185918019117875)
          ·
            refine ⟨7038220147778877028676813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692146765185918019117875 7038220147778877028676813)
            ·
              refine ⟨2639332555417078885753805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7038220147778877028676813 2639332555417078885753805)
              ·
                refine ⟨989749708281404582157677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2639332555417078885753805 989749708281404582157677)
                ·
                  refine ⟨371156140605526718309129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989749708281404582157677 371156140605526718309129)
                  ·
                    rfl

theorem cell21_1626354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_1626354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626354 prefixEnd_1626354 := by exact prefixLift 1626354
  have htrace : WordTrace (prefixWord ++ tailWord_1626354) baseStart_1626354 baseEnd_1626354 := by
    simpa [prefixWord, tailWord_1626354, baseEnd_1626354] using wordTrace_append hprefix tailTrace_1626354
  have hstable : (prefixWord ++ tailWord_1626354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626354).length < 2 ^ (prefixWord ++ tailWord_1626354).sum := by decide
  have hdescent : baseEnd_1626354 < baseStart_1626354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626430 : List Nat := [4, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_1626430 : Nat := 118140960795 + 1626430 * 2 ^ 59
def prefixEnd_1626430 : Nat := 4983230072969 + 3 ^ 40 * 1626430 * 2
def baseEnd_1626430 : Nat := 371173484840967475042307

theorem tailTrace_1626430 : CollatzResearch.WordTrace tailWord_1626430 prefixEnd_1626430 371173484840967475042307 := by
  unfold tailWord_1626430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7415096937216169621817593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39547183665152904649693829 7415096937216169621817593)
  ·
    refine ⟨5561322702912127216363195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7415096937216169621817593 5561322702912127216363195)
    ·
      refine ⟨8341984054368190824544793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5561322702912127216363195 8341984054368190824544793)
      ·
        refine ⟨6256488040776143118408595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8341984054368190824544793 6256488040776143118408595)
        ·
          refine ⟨9384732061164214677612893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6256488040776143118408595 9384732061164214677612893)
          ·
            refine ⟨3519274522936580504104835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9384732061164214677612893 3519274522936580504104835)
            ·
              refine ⟨5278911784404870756157253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519274522936580504104835 5278911784404870756157253)
              ·
                refine ⟨989795959575913266779485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5278911784404870756157253 989795959575913266779485)
                ·
                  refine ⟨371173484840967475042307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989795959575913266779485 371173484840967475042307)
                  ·
                    rfl

theorem cell21_1626430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_1626430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626430 prefixEnd_1626430 := by exact prefixLift 1626430
  have htrace : WordTrace (prefixWord ++ tailWord_1626430) baseStart_1626430 baseEnd_1626430 := by
    simpa [prefixWord, tailWord_1626430, baseEnd_1626430] using wordTrace_append hprefix tailTrace_1626430
  have hstable : (prefixWord ++ tailWord_1626430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626430).length < 2 ^ (prefixWord ++ tailWord_1626430).sum := by decide
  have hdescent : baseEnd_1626430 < baseStart_1626430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626582 : List Nat := [5, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_1626582 : Nat := 118140960795 + 1626582 * 2 ^ 59
def prefixEnd_1626582 : Nat := 4983230072969 + 3 ^ 40 * 1626582 * 2
def baseEnd_1626582 : Nat := 371208173311848988508663

theorem tailTrace_1626582 : CollatzResearch.WordTrace tailWord_1626582 prefixEnd_1626582 371208173311848988508663 := by
  unfold tailWord_1626582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707894962073667933379625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39550879595452457956049333 3707894962073667933379625)
  ·
    refine ⟨2780921221555250950034719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3707894962073667933379625 2780921221555250950034719)
    ·
      refine ⟨4171381832332876425052079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2780921221555250950034719 4171381832332876425052079)
      ·
        refine ⟨6257072748499314637578119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4171381832332876425052079 6257072748499314637578119)
        ·
          refine ⟨9385609122748971956367179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6257072748499314637578119 9385609122748971956367179)
          ·
            refine ⟨14078413684123457934550769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9385609122748971956367179 14078413684123457934550769)
            ·
              refine ⟨10558810263092593450913077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14078413684123457934550769 10558810263092593450913077)
              ·
                refine ⟨989888462164930636023101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10558810263092593450913077 989888462164930636023101)
                ·
                  refine ⟨371208173311848988508663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989888462164930636023101 371208173311848988508663)
                  ·
                    rfl

theorem cell21_1626582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_1626582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626582 prefixEnd_1626582 := by exact prefixLift 1626582
  have htrace : WordTrace (prefixWord ++ tailWord_1626582) baseStart_1626582 baseEnd_1626582 := by
    simpa [prefixWord, tailWord_1626582, baseEnd_1626582] using wordTrace_append hprefix tailTrace_1626582
  have hstable : (prefixWord ++ tailWord_1626582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626582).length < 2 ^ (prefixWord ++ tailWord_1626582).sum := by decide
  have hdescent : baseEnd_1626582 < baseStart_1626582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626607 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 5]
def baseStart_1626607 : Nat := 118140960795 + 1626607 * 2 ^ 59
def prefixEnd_1626607 : Nat := 4983230072969 + 3 ^ 40 * 1626607 * 2
def baseEnd_1626607 : Nat := 371213878652454500591945

theorem tailTrace_1626607 : CollatzResearch.WordTrace tailWord_1626607 prefixEnd_1626607 371213878652454500591945 := by
  unfold tailWord_1626607
  simp only [CollatzResearch.WordTrace]
  refine ⟨59327231218088116203734075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39551487478725410802489383 59327231218088116203734075)
  ·
    refine ⟨88990846827132174305601113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59327231218088116203734075 88990846827132174305601113)
    ·
      refine ⟨66743135120349130729200835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88990846827132174305601113 66743135120349130729200835)
      ·
        refine ⟨100114702680523696093801253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66743135120349130729200835 100114702680523696093801253)
        ·
          refine ⟨18771506752598193017587735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100114702680523696093801253 18771506752598193017587735)
          ·
            refine ⟨28157260128897289526381603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18771506752598193017587735 28157260128897289526381603)
            ·
              refine ⟨42235890193345934289572405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28157260128897289526381603 42235890193345934289572405)
              ·
                refine ⟨3959614705626181339647413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42235890193345934289572405 3959614705626181339647413)
                ·
                  refine ⟨371213878652454500591945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3959614705626181339647413 371213878652454500591945)
                  ·
                    rfl

theorem cell21_1626607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_1626607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626607 prefixEnd_1626607 := by exact prefixLift 1626607
  have htrace : WordTrace (prefixWord ++ tailWord_1626607) baseStart_1626607 baseEnd_1626607 := by
    simpa [prefixWord, tailWord_1626607, baseEnd_1626607] using wordTrace_append hprefix tailTrace_1626607
  have hstable : (prefixWord ++ tailWord_1626607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626607).length < 2 ^ (prefixWord ++ tailWord_1626607).sum := by decide
  have hdescent : baseEnd_1626607 < baseStart_1626607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626866 : List Nat := [3, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_1626866 : Nat := 118140960795 + 1626866 * 2 ^ 59
def prefixEnd_1626866 : Nat := 4983230072969 + 3 ^ 40 * 1626866 * 2
def baseEnd_1626866 : Nat := 371272985981127605774749

theorem tailTrace_1626866 : CollatzResearch.WordTrace tailWord_1626866 prefixEnd_1626866 371272985981127605774749 := by
  unfold tailWord_1626866
  simp only [CollatzResearch.WordTrace]
  refine ⟨14834169431037450859353113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39557785149433202291608301 14834169431037450859353113)
  ·
    refine ⟨11125627073278088144514835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14834169431037450859353113 11125627073278088144514835)
    ·
      refine ⟨16688440609917132216772253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11125627073278088144514835 16688440609917132216772253)
      ·
        refine ⟨6258165228718924581289595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16688440609917132216772253 6258165228718924581289595)
        ·
          refine ⟨9387247843078386871934393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6258165228718924581289595 9387247843078386871934393)
          ·
            refine ⟨7040435882308790153950795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9387247843078386871934393 7040435882308790153950795)
            ·
              refine ⟨10560653823463185230926193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7040435882308790153950795 10560653823463185230926193)
              ·
                refine ⟨7920490367597388923194645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10560653823463185230926193 7920490367597388923194645)
                ·
                  refine ⟨371272985981127605774749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7920490367597388923194645 371272985981127605774749)
                  ·
                    rfl

theorem cell21_1626866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_1626866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626866 prefixEnd_1626866 := by exact prefixLift 1626866
  have htrace : WordTrace (prefixWord ++ tailWord_1626866) baseStart_1626866 baseEnd_1626866 := by
    simpa [prefixWord, tailWord_1626866, baseEnd_1626866] using wordTrace_append hprefix tailTrace_1626866
  have hstable : (prefixWord ++ tailWord_1626866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626866).length < 2 ^ (prefixWord ++ tailWord_1626866).sum := by decide
  have hdescent : baseEnd_1626866 < baseStart_1626866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1626948 : List Nat := [2, 3, 4, 2, 2, 1, 1, 6]
def baseStart_1626948 : Nat := 118140960795 + 1626948 * 2 ^ 59
def prefixEnd_1626948 : Nat := 4983230072969 + 3 ^ 40 * 1626948 * 2
def baseEnd_1626948 : Nat := 123763899832771228469305

theorem tailTrace_1626948 : CollatzResearch.WordTrace tailWord_1626948 prefixEnd_1626948 123763899832771228469305 := by
  unfold tailWord_1626948
  simp only [CollatzResearch.WordTrace]
  refine ⟨29669834254926365720948749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39559779006568487627931665 29669834254926365720948749)
  ·
    refine ⟨11126187845597387145355781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29669834254926365720948749 11126187845597387145355781)
    ·
      refine ⟨2086160221049510089754209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11126187845597387145355781 2086160221049510089754209)
      ·
        refine ⟨1564620165787132567315657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2086160221049510089754209 1564620165787132567315657)
        ·
          refine ⟨1173465124340349425486743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1564620165787132567315657 1173465124340349425486743)
          ·
            refine ⟨1760197686510524138230115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173465124340349425486743 1760197686510524138230115)
            ·
              refine ⟨2640296529765786207345173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760197686510524138230115 2640296529765786207345173)
              ·
                refine ⟨123763899832771228469305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2640296529765786207345173 123763899832771228469305)
                ·
                  rfl

theorem cell21_1626948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 6].length) (baseStart_1626948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1626948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1626948 prefixEnd_1626948 := by exact prefixLift 1626948
  have htrace : WordTrace (prefixWord ++ tailWord_1626948) baseStart_1626948 baseEnd_1626948 := by
    simpa [prefixWord, tailWord_1626948, baseEnd_1626948] using wordTrace_append hprefix tailTrace_1626948
  have hstable : (prefixWord ++ tailWord_1626948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1626948).length < 2 ^ (prefixWord ++ tailWord_1626948).sum := by decide
  have hdescent : baseEnd_1626948 < baseStart_1626948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1626948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627010 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1627010 : Nat := 118140960795 + 1627010 * 2 ^ 59
def prefixEnd_1627010 : Nat := 4983230072969 + 3 ^ 40 * 1627010 * 2
def baseEnd_1627010 : Nat := 371305848743015355374455

theorem tailTrace_1627010 : CollatzResearch.WordTrace tailWord_1627010 prefixEnd_1627010 371305848743015355374455 := by
  unfold tailWord_1627010
  simp only [CollatzResearch.WordTrace]
  refine ⟨14835482458907029007663621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39561286557085410687102989 14835482458907029007663621)
  ·
    refine ⟨2781652961045067938936929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14835482458907029007663621 2781652961045067938936929)
    ·
      refine ⟨2086239720783800954202697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2781652961045067938936929 2086239720783800954202697)
      ·
        refine ⟨1564679790587850715652023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2086239720783800954202697 1564679790587850715652023)
        ·
          refine ⟨2347019685881776073478035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564679790587850715652023 2347019685881776073478035)
          ·
            refine ⟨3520529528822664110217053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347019685881776073478035 3520529528822664110217053)
            ·
              refine ⟨1320198573308499041331395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3520529528822664110217053 1320198573308499041331395)
              ·
                refine ⟨1980297859962748561997093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320198573308499041331395 1980297859962748561997093)
                ·
                  refine ⟨371305848743015355374455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1980297859962748561997093 371305848743015355374455)
                  ·
                    rfl

theorem cell21_1627010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1627010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627010 prefixEnd_1627010 := by exact prefixLift 1627010
  have htrace : WordTrace (prefixWord ++ tailWord_1627010) baseStart_1627010 baseEnd_1627010 := by
    simpa [prefixWord, tailWord_1627010, baseEnd_1627010] using wordTrace_append hprefix tailTrace_1627010
  have hstable : (prefixWord ++ tailWord_1627010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627010).length < 2 ^ (prefixWord ++ tailWord_1627010).sum := by decide
  have hdescent : baseEnd_1627010 < baseStart_1627010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627063 : List Nat := [1, 1, 3, 1, 3, 1, 5, 1, 5]
def baseStart_1627063 : Nat := 118140960795 + 1627063 * 2 ^ 59
def prefixEnd_1627063 : Nat := 4983230072969 + 3 ^ 40 * 1627063 * 2
def baseEnd_1627063 : Nat := 371317944065099040991013

theorem tailTrace_1627063 : CollatzResearch.WordTrace tailWord_1627063 prefixEnd_1627063 371317944065099040991013 := by
  unfold tailWord_1627063
  simp only [CollatzResearch.WordTrace]
  refine ⟨59343862904436106082333843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39562575269624070721555895 59343862904436106082333843)
  ·
    refine ⟨89015794356654159123500765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59343862904436106082333843 89015794356654159123500765)
    ·
      refine ⟨33380922883745309671312787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89015794356654159123500765 33380922883745309671312787)
      ·
        refine ⟨50071384325617964506969181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33380922883745309671312787 50071384325617964506969181)
        ·
          refine ⟨18776769122106736690113443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50071384325617964506969181 18776769122106736690113443)
          ·
            refine ⟨28165153683160105035170165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18776769122106736690113443 28165153683160105035170165)
            ·
              refine ⟨2640483157796259847047203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28165153683160105035170165 2640483157796259847047203)
              ·
                refine ⟨3960724736694389770570805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2640483157796259847047203 3960724736694389770570805)
                ·
                  refine ⟨371317944065099040991013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3960724736694389770570805 371317944065099040991013)
                  ·
                    rfl

theorem cell21_1627063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 5].length) (baseStart_1627063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627063 prefixEnd_1627063 := by exact prefixLift 1627063
  have htrace : WordTrace (prefixWord ++ tailWord_1627063) baseStart_1627063 baseEnd_1627063 := by
    simpa [prefixWord, tailWord_1627063, baseEnd_1627063] using wordTrace_append hprefix tailTrace_1627063
  have hstable : (prefixWord ++ tailWord_1627063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627063).length < 2 ^ (prefixWord ++ tailWord_1627063).sum := by decide
  have hdescent : baseEnd_1627063 < baseStart_1627063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627069 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 4]
def baseStart_1627069 : Nat := 118140960795 + 1627069 * 2 ^ 59
def prefixEnd_1627069 : Nat := 4983230072969 + 3 ^ 40 * 1627069 * 2
def baseEnd_1627069 : Nat := 371319313346844363891001

theorem tailTrace_1627069 : CollatzResearch.WordTrace tailWord_1627069 prefixEnd_1627069 371319313346844363891001 := by
  unfold tailWord_1627069
  simp only [CollatzResearch.WordTrace]
  refine ⟨59344081742414369107052261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39562721161609579404701507 59344081742414369107052261)
  ·
    refine ⟨11127015326702694207572299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59344081742414369107052261 11127015326702694207572299)
    ·
      refine ⟨16690522990054041311358449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11127015326702694207572299 16690522990054041311358449)
      ·
        refine ⟨12517892242540530983518837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16690522990054041311358449 12517892242540530983518837)
        ·
          refine ⟨1173552397738174779704891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12517892242540530983518837 1173552397738174779704891)
          ·
            refine ⟨1760328596607262169557337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173552397738174779704891 1760328596607262169557337)
            ·
              refine ⟨1320246447455446627168003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760328596607262169557337 1320246447455446627168003)
              ·
                refine ⟨1980369671183169940752005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320246447455446627168003 1980369671183169940752005)
                ·
                  refine ⟨371319313346844363891001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1980369671183169940752005 371319313346844363891001)
                  ·
                    rfl

theorem cell21_1627069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_1627069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627069 prefixEnd_1627069 := by exact prefixLift 1627069
  have htrace : WordTrace (prefixWord ++ tailWord_1627069) baseStart_1627069 baseEnd_1627069 := by
    simpa [prefixWord, tailWord_1627069, baseEnd_1627069] using wordTrace_append hprefix tailTrace_1627069
  have hstable : (prefixWord ++ tailWord_1627069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627069).length < 2 ^ (prefixWord ++ tailWord_1627069).sum := by decide
  have hdescent : baseEnd_1627069 < baseStart_1627069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627111 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 4]
def baseStart_1627111 : Nat := 118140960795 + 1627111 * 2 ^ 59
def prefixEnd_1627111 : Nat := 4983230072969 + 3 ^ 40 * 1627111 * 2
def baseEnd_1627111 : Nat := 371328898319061624190915

theorem tailTrace_1627111 : CollatzResearch.WordTrace tailWord_1627111 prefixEnd_1627111 371328898319061624190915 := by
  unfold tailWord_1627111
  simp only [CollatzResearch.WordTrace]
  refine ⟨59345613608262210280081187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39563742405508140186720791 59345613608262210280081187)
  ·
    refine ⟨89018420412393315420121781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59345613608262210280081187 89018420412393315420121781)
    ·
      refine ⟨8345476913661873320636417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89018420412393315420121781 8345476913661873320636417)
      ·
        refine ⟨6259107685246404990477313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8345476913661873320636417 6259107685246404990477313)
        ·
          refine ⟨4694330763934803742857985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6259107685246404990477313 4694330763934803742857985)
          ·
            refine ⟨3520748072951102807143489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4694330763934803742857985 3520748072951102807143489)
            ·
              refine ⟨2640561054713327105357617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3520748072951102807143489 2640561054713327105357617)
              ·
                refine ⟨1980420791034995329018213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2640561054713327105357617 1980420791034995329018213)
                ·
                  refine ⟨371328898319061624190915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1980420791034995329018213 371328898319061624190915)
                  ·
                    rfl

theorem cell21_1627111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 4].length) (baseStart_1627111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627111 prefixEnd_1627111 := by exact prefixLift 1627111
  have htrace : WordTrace (prefixWord ++ tailWord_1627111) baseStart_1627111 baseEnd_1627111 := by
    simpa [prefixWord, tailWord_1627111, baseEnd_1627111] using wordTrace_append hprefix tailTrace_1627111
  have hstable : (prefixWord ++ tailWord_1627111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627111).length < 2 ^ (prefixWord ++ tailWord_1627111).sum := by decide
  have hdescent : baseEnd_1627111 < baseStart_1627111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627114 : List Nat := [3, 1, 3, 1, 2, 4, 2, 2, 3]
def baseStart_1627114 : Nat := 118140960795 + 1627114 * 2 ^ 59
def prefixEnd_1627114 : Nat := 4983230072969 + 3 ^ 40 * 1627114 * 2
def baseEnd_1627114 : Nat := 371329582959934285640909

theorem tailTrace_1627114 : CollatzResearch.WordTrace tailWord_1627114 prefixEnd_1627114 371329582959934285640909 := by
  unfold tailWord_1627114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14836430756812835448110099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39563815351500894528293597 14836430756812835448110099)
  ·
    refine ⟨22254646135219253172165149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14836430756812835448110099 22254646135219253172165149)
    ·
      refine ⟨8345492300707219939561931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22254646135219253172165149 8345492300707219939561931)
      ·
        refine ⟨12518238451060829909342897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8345492300707219939561931 12518238451060829909342897)
        ·
          refine ⟨9388678838295622432007173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12518238451060829909342897 9388678838295622432007173)
          ·
            refine ⟨1760377282180429206001345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9388678838295622432007173 1760377282180429206001345)
            ·
              refine ⟨1320282961635321904501009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760377282180429206001345 1320282961635321904501009)
              ·
                refine ⟨990212221226491428375757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320282961635321904501009 990212221226491428375757)
                ·
                  refine ⟨371329582959934285640909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990212221226491428375757 371329582959934285640909)
                  ·
                    rfl

theorem cell21_1627114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_1627114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627114 prefixEnd_1627114 := by exact prefixLift 1627114
  have htrace : WordTrace (prefixWord ++ tailWord_1627114) baseStart_1627114 baseEnd_1627114 := by
    simpa [prefixWord, tailWord_1627114, baseEnd_1627114] using wordTrace_append hprefix tailTrace_1627114
  have hstable : (prefixWord ++ tailWord_1627114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627114).length < 2 ^ (prefixWord ++ tailWord_1627114).sum := by decide
  have hdescent : baseEnd_1627114 < baseStart_1627114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627170 : List Nat := [3, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1627170 : Nat := 118140960795 + 1627170 * 2 ^ 59
def prefixEnd_1627170 : Nat := 4983230072969 + 3 ^ 40 * 1627170 * 2
def baseEnd_1627170 : Nat := 371342362922890632707461

theorem tailTrace_1627170 : CollatzResearch.WordTrace tailWord_1627170 prefixEnd_1627170 371342362922890632707461 := by
  unfold tailWord_1627170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14836941378762115839119741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39565177010032308904319309 14836941378762115839119741)
  ·
    refine ⟨5563853017035793439669903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14836941378762115839119741 5563853017035793439669903)
    ·
      refine ⟨8345779525553690159504855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5563853017035793439669903 8345779525553690159504855)
      ·
        refine ⟨12518669288330535239257283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8345779525553690159504855 12518669288330535239257283)
        ·
          refine ⟨18778003932495802858885925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12518669288330535239257283 18778003932495802858885925)
          ·
            refine ⟨3520875737342963036041111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18778003932495802858885925 3520875737342963036041111)
            ·
              refine ⟨5281313606014444554061667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520875737342963036041111 5281313606014444554061667)
              ·
                refine ⟨7921970409021666831092501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5281313606014444554061667 7921970409021666831092501)
                ·
                  refine ⟨371342362922890632707461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7921970409021666831092501 371342362922890632707461)
                  ·
                    rfl

theorem cell21_1627170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1627170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627170 prefixEnd_1627170 := by exact prefixLift 1627170
  have htrace : WordTrace (prefixWord ++ tailWord_1627170) baseStart_1627170 baseEnd_1627170 := by
    simpa [prefixWord, tailWord_1627170, baseEnd_1627170] using wordTrace_append hprefix tailTrace_1627170
  have hstable : (prefixWord ++ tailWord_1627170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627170).length < 2 ^ (prefixWord ++ tailWord_1627170).sum := by decide
  have hdescent : baseEnd_1627170 < baseStart_1627170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627201 : List Nat := [1, 2, 5, 1, 3, 1, 1, 7]
def baseStart_1627201 : Nat := 118140960795 + 1627201 * 2 ^ 59
def prefixEnd_1627201 : Nat := 4983230072969 + 3 ^ 40 * 1627201 * 2
def baseEnd_1627201 : Nat := 123783145848413822563577

theorem tailTrace_1627201 : CollatzResearch.WordTrace tailWord_1627201 prefixEnd_1627201 123783145848413822563577 := by
  unfold tailWord_1627201
  simp only [CollatzResearch.WordTrace]
  refine ⟨59348896177936155650857457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39565930785290770433904971 59348896177936155650857457)
  ·
    refine ⟨44511672133452116738143093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59348896177936155650857457 44511672133452116738143093)
    ·
      refine ⟨4172969262511135944200915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44511672133452116738143093 4172969262511135944200915)
      ·
        refine ⟨6259453893766703916301373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4172969262511135944200915 6259453893766703916301373)
        ·
          refine ⟨2347295210162513968613015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6259453893766703916301373 2347295210162513968613015)
          ·
            refine ⟨3520942815243770952919523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347295210162513968613015 3520942815243770952919523)
            ·
              refine ⟨5281414222865656429379285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520942815243770952919523 5281414222865656429379285)
              ·
                refine ⟨123783145848413822563577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5281414222865656429379285 123783145848413822563577)
                ·
                  rfl

theorem cell21_1627201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 7].length) (baseStart_1627201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627201 prefixEnd_1627201 := by exact prefixLift 1627201
  have htrace : WordTrace (prefixWord ++ tailWord_1627201) baseStart_1627201 baseEnd_1627201 := by
    simpa [prefixWord, tailWord_1627201, baseEnd_1627201] using wordTrace_append hprefix tailTrace_1627201
  have hstable : (prefixWord ++ tailWord_1627201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627201).length < 2 ^ (prefixWord ++ tailWord_1627201).sum := by decide
  have hdescent : baseEnd_1627201 < baseStart_1627201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627294 : List Nat := [4, 3, 1, 1, 2, 3, 1, 6]
def baseStart_1627294 : Nat := 118140960795 + 1627294 * 2 ^ 59
def prefixEnd_1627294 : Nat := 4983230072969 + 3 ^ 40 * 1627294 * 2
def baseEnd_1627294 : Nat := 123790220470764657546847

theorem tailTrace_1627294 : CollatzResearch.WordTrace tailWord_1627294 prefixEnd_1627294 123790220470764657546847 := by
  unfold tailWord_1627294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7419036020824904066749117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39568192111066155022661957 7419036020824904066749117)
  ·
    refine ⟨2782138507809339025030919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7419036020824904066749117 2782138507809339025030919)
    ·
      refine ⟨4173207761714008537546379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2782138507809339025030919 4173207761714008537546379)
      ·
        refine ⟨6259811642571012806319569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4173207761714008537546379 6259811642571012806319569)
        ·
          refine ⟨4694858731928259604739677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6259811642571012806319569 4694858731928259604739677)
          ·
            refine ⟨1760572024473097351777379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4694858731928259604739677 1760572024473097351777379)
            ·
              refine ⟨2640858036709646027666069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760572024473097351777379 2640858036709646027666069)
              ·
                refine ⟨123790220470764657546847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2640858036709646027666069 123790220470764657546847)
                ·
                  rfl

theorem cell21_1627294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_1627294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627294 prefixEnd_1627294 := by exact prefixLift 1627294
  have htrace : WordTrace (prefixWord ++ tailWord_1627294) baseStart_1627294 baseEnd_1627294 := by
    simpa [prefixWord, tailWord_1627294, baseEnd_1627294] using wordTrace_append hprefix tailTrace_1627294
  have hstable : (prefixWord ++ tailWord_1627294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627294).length < 2 ^ (prefixWord ++ tailWord_1627294).sum := by decide
  have hdescent : baseEnd_1627294 < baseStart_1627294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627395 : List Nat := [1, 1, 1, 3, 2, 4, 9]
def baseStart_1627395 : Nat := 118140960795 + 1627395 * 2 ^ 59
def prefixEnd_1627395 : Nat := 4983230072969 + 3 ^ 40 * 1627395 * 2
def baseEnd_1627395 : Nat := 41265967887593360161889

theorem tailTrace_1627395 : CollatzResearch.WordTrace tailWord_1627395 prefixEnd_1627395 41265967887593360161889 := by
  unfold tailWord_1627395
  simp only [CollatzResearch.WordTrace]
  refine ⟨59355971939233326783419639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39570647959488884522279759 59355971939233326783419639)
  ·
    refine ⟨89033957908849990175129459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59355971939233326783419639 89033957908849990175129459)
    ·
      refine ⟨133550936863274985262694189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89033957908849990175129459 133550936863274985262694189)
      ·
        refine ⟨50081601323728119473510321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133550936863274985262694189 50081601323728119473510321)
        ·
          refine ⟨37561200992796089605132741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50081601323728119473510321 37561200992796089605132741)
          ·
            refine ⟨7042725186149266800962389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37561200992796089605132741 7042725186149266800962389)
            ·
              refine ⟨41265967887593360161889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7042725186149266800962389 41265967887593360161889)
              ·
                rfl

theorem cell21_1627395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 9].length) (baseStart_1627395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627395 prefixEnd_1627395 := by exact prefixLift 1627395
  have htrace : WordTrace (prefixWord ++ tailWord_1627395) baseStart_1627395 baseEnd_1627395 := by
    simpa [prefixWord, tailWord_1627395, baseEnd_1627395] using wordTrace_append hprefix tailTrace_1627395
  have hstable : (prefixWord ++ tailWord_1627395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627395).length < 2 ^ (prefixWord ++ tailWord_1627395).sum := by decide
  have hdescent : baseEnd_1627395 < baseStart_1627395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627446 : List Nat := [5, 1, 2, 3, 2, 8]
def baseStart_1627446 : Nat := 118140960795 + 1627446 * 2 ^ 59
def prefixEnd_1627446 : Nat := 4983230072969 + 3 ^ 40 * 1627446 * 2
def baseEnd_1627446 : Nat := 13755753699376869855811

theorem tailTrace_1627446 : CollatzResearch.WordTrace tailWord_1627446 prefixEnd_1627446 13755753699376869855811 := by
  unfold tailWord_1627446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709864503878035155845387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39571888041365708329017461 3709864503878035155845387)
  ·
    refine ⟨5564796755817052733768081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3709864503878035155845387 5564796755817052733768081)
    ·
      refine ⟨4173597566862789550326061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5564796755817052733768081 4173597566862789550326061)
      ·
        refine ⟨1565099087573546081372273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4173597566862789550326061 1565099087573546081372273)
        ·
          refine ⟨1173824315680159561029205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1565099087573546081372273 1173824315680159561029205)
          ·
            refine ⟨13755753699376869855811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1173824315680159561029205 13755753699376869855811)
            ·
              rfl

theorem cell21_1627446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 8].length) (baseStart_1627446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627446 prefixEnd_1627446 := by exact prefixLift 1627446
  have htrace : WordTrace (prefixWord ++ tailWord_1627446) baseStart_1627446 baseEnd_1627446 := by
    simpa [prefixWord, tailWord_1627446, baseEnd_1627446] using wordTrace_append hprefix tailTrace_1627446
  have hstable : (prefixWord ++ tailWord_1627446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627446).length < 2 ^ (prefixWord ++ tailWord_1627446).sum := by decide
  have hdescent : baseEnd_1627446 < baseStart_1627446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627623 : List Nat := [1, 1, 5, 2, 1, 11]
def baseStart_1627623 : Nat := 118140960795 + 1627623 * 2 ^ 59
def prefixEnd_1627623 : Nat := 4983230072969 + 3 ^ 40 * 1627623 * 2
def baseEnd_1627623 : Nat := 13757249766468981913205

theorem tailTrace_1627623 : CollatzResearch.WordTrace tailWord_1627623 prefixEnd_1627623 13757249766468981913205 := by
  unfold tailWord_1627623
  simp only [CollatzResearch.WordTrace]
  refine ⟨59364287782407321722719523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39576191854938214481813015 59364287782407321722719523)
  ·
    refine ⟨89046431673610982584079285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59364287782407321722719523 89046431673610982584079285)
    ·
      refine ⟨8348102969401029617257433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89046431673610982584079285 8348102969401029617257433)
      ·
        refine ⟨6261077227050772212943075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8348102969401029617257433 6261077227050772212943075)
        ·
          refine ⟨9391615840576158319414613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6261077227050772212943075 9391615840576158319414613)
          ·
            refine ⟨13757249766468981913205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9391615840576158319414613 13757249766468981913205)
            ·
              rfl

theorem cell21_1627623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 11].length) (baseStart_1627623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627623 prefixEnd_1627623 := by exact prefixLift 1627623
  have htrace : WordTrace (prefixWord ++ tailWord_1627623) baseStart_1627623 baseEnd_1627623 := by
    simpa [prefixWord, tailWord_1627623, baseEnd_1627623] using wordTrace_append hprefix tailTrace_1627623
  have hstable : (prefixWord ++ tailWord_1627623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627623).length < 2 ^ (prefixWord ++ tailWord_1627623).sum := by decide
  have hdescent : baseEnd_1627623 < baseStart_1627623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627629 : List Nat := [1, 5, 1, 3, 2, 1, 1, 4, 3]
def baseStart_1627629 : Nat := 118140960795 + 1627629 * 2 ^ 59
def prefixEnd_1627629 : Nat := 4983230072969 + 3 ^ 40 * 1627629 * 2
def baseEnd_1627629 : Nat := 371447112976407834556523

theorem tailTrace_1627629 : CollatzResearch.WordTrace tailWord_1627629 prefixEnd_1627629 371447112976407834556523 := by
  unfold tailWord_1627629
  simp only [CollatzResearch.WordTrace]
  refine ⟨59364506620385584747437941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39576337746923723164958627 59364506620385584747437941)
  ·
    refine ⟨5565422495661148570072307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59364506620385584747437941 5565422495661148570072307)
    ·
      refine ⟨8348133743491722855108461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5565422495661148570072307 8348133743491722855108461)
      ·
        refine ⟨3130550153809396070665673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8348133743491722855108461 3130550153809396070665673)
        ·
          refine ⟨2347912615357047052999255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3130550153809396070665673 2347912615357047052999255)
          ·
            refine ⟨3521868923035570579498883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347912615357047052999255 3521868923035570579498883)
            ·
              refine ⟨5282803384553355869248325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3521868923035570579498883 5282803384553355869248325)
              ·
                refine ⟨990525634603754225484061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5282803384553355869248325 990525634603754225484061)
                ·
                  refine ⟨371447112976407834556523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990525634603754225484061 371447112976407834556523)
                  ·
                    rfl

theorem cell21_1627629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_1627629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627629 prefixEnd_1627629 := by exact prefixLift 1627629
  have htrace : WordTrace (prefixWord ++ tailWord_1627629) baseStart_1627629 baseEnd_1627629 := by
    simpa [prefixWord, tailWord_1627629, baseEnd_1627629] using wordTrace_append hprefix tailTrace_1627629
  have hstable : (prefixWord ++ tailWord_1627629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627629).length < 2 ^ (prefixWord ++ tailWord_1627629).sum := by decide
  have hdescent : baseEnd_1627629 < baseStart_1627629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627640 : List Nat := [2, 1, 2, 1, 1, 7, 1, 6]
def baseStart_1627640 : Nat := 118140960795 + 1627640 * 2 ^ 59
def prefixEnd_1627640 : Nat := 4983230072969 + 3 ^ 40 * 1627640 * 2
def baseEnd_1627640 : Nat := 123816541108758086624389

theorem tailTrace_1627640 : CollatzResearch.WordTrace tailWord_1627640 prefixEnd_1627640 123816541108758086624389 := by
  unfold tailWord_1627640
  simp only [CollatzResearch.WordTrace]
  refine ⟨29682453911672866813044187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39576605215563822417392249 29682453911672866813044187)
  ·
    refine ⟨44523680867509300219566281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29682453911672866813044187 44523680867509300219566281)
    ·
      refine ⟨33392760650631975164674711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44523680867509300219566281 33392760650631975164674711)
      ·
        refine ⟨50089140975947962747012067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33392760650631975164674711 50089140975947962747012067)
        ·
          refine ⟨75133711463921944120518101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50089140975947962747012067 75133711463921944120518101)
          ·
            refine ⟨1760946362435670565324643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 75133711463921944120518101 1760946362435670565324643)
            ·
              refine ⟨2641419543653505847986965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760946362435670565324643 2641419543653505847986965)
              ·
                refine ⟨123816541108758086624389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2641419543653505847986965 123816541108758086624389)
                ·
                  rfl

theorem cell21_1627640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 6].length) (baseStart_1627640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627640 prefixEnd_1627640 := by exact prefixLift 1627640
  have htrace : WordTrace (prefixWord ++ tailWord_1627640) baseStart_1627640 baseEnd_1627640 := by
    simpa [prefixWord, tailWord_1627640, baseEnd_1627640] using wordTrace_append hprefix tailTrace_1627640
  have hstable : (prefixWord ++ tailWord_1627640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627640).length < 2 ^ (prefixWord ++ tailWord_1627640).sum := by decide
  have hdescent : baseEnd_1627640 < baseStart_1627640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627688 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 5]
def baseStart_1627688 : Nat := 118140960795 + 1627688 * 2 ^ 59
def prefixEnd_1627688 : Nat := 4983230072969 + 3 ^ 40 * 1627688 * 2
def baseEnd_1627688 : Nat := 371460577580236843073069

theorem tailTrace_1627688 : CollatzResearch.WordTrace tailWord_1627688 prefixEnd_1627688 371460577580236843073069 := by
  unfold tailWord_1627688
  simp only [CollatzResearch.WordTrace]
  refine ⟨29683329263585918911917859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39577772351447891882557145 29683329263585918911917859)
  ·
    refine ⟨44524993895378878367876789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29683329263585918911917859 44524993895378878367876789)
    ·
      refine ⟨4174218177691769846988449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44524993895378878367876789 4174218177691769846988449)
      ·
        refine ⟨3130663633268827385241337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4174218177691769846988449 3130663633268827385241337)
        ·
          refine ⟨2347997724951620538931003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3130663633268827385241337 2347997724951620538931003)
          ·
            refine ⟨3521996587427430808396505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2347997724951620538931003 3521996587427430808396505)
            ·
              refine ⟨2641497440570573106297379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3521996587427430808396505 2641497440570573106297379)
              ·
                refine ⟨3962246160855859659446069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641497440570573106297379 3962246160855859659446069)
                ·
                  refine ⟨371460577580236843073069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3962246160855859659446069 371460577580236843073069)
                  ·
                    rfl

theorem cell21_1627688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_1627688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627688 prefixEnd_1627688 := by exact prefixLift 1627688
  have htrace : WordTrace (prefixWord ++ tailWord_1627688) baseStart_1627688 baseEnd_1627688 := by
    simpa [prefixWord, tailWord_1627688, baseEnd_1627688] using wordTrace_append hprefix tailTrace_1627688
  have hstable : (prefixWord ++ tailWord_1627688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627688).length < 2 ^ (prefixWord ++ tailWord_1627688).sum := by decide
  have hdescent : baseEnd_1627688 < baseStart_1627688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627747 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 5]
def baseStart_1627747 : Nat := 118140960795 + 1627747 * 2 ^ 59
def prefixEnd_1627747 : Nat := 4983230072969 + 3 ^ 40 * 1627747 * 2
def baseEnd_1627747 : Nat := 371474042184065851589615

theorem tailTrace_1627747 : CollatzResearch.WordTrace tailWord_1627747 prefixEnd_1627747 371474042184065851589615 := by
  unfold tailWord_1627747
  simp only [CollatzResearch.WordTrace]
  refine ⟨59368810433958090900233495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39579206955972060600155663 59368810433958090900233495)
  ·
    refine ⟨89053215650937136350350243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59368810433958090900233495 89053215650937136350350243)
    ·
      refine ⟨133579823476405704525525365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89053215650937136350350243 133579823476405704525525365)
      ·
        refine ⟨12523108450913034799268003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133579823476405704525525365 12523108450913034799268003)
        ·
          refine ⟨18784662676369552198902005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12523108450913034799268003 18784662676369552198902005)
          ·
            refine ⟨1761062125909645518647063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18784662676369552198902005 1761062125909645518647063)
            ·
              refine ⟨2641593188864468277970595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761062125909645518647063 2641593188864468277970595)
              ·
                refine ⟨3962389783296702416955893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2641593188864468277970595 3962389783296702416955893)
                ·
                  refine ⟨371474042184065851589615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3962389783296702416955893 371474042184065851589615)
                  ·
                    rfl

theorem cell21_1627747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 5].length) (baseStart_1627747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627747 prefixEnd_1627747 := by exact prefixLift 1627747
  have htrace : WordTrace (prefixWord ++ tailWord_1627747) baseStart_1627747 baseEnd_1627747 := by
    simpa [prefixWord, tailWord_1627747, baseEnd_1627747] using wordTrace_append hprefix tailTrace_1627747
  have hstable : (prefixWord ++ tailWord_1627747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627747).length < 2 ^ (prefixWord ++ tailWord_1627747).sum := by decide
  have hdescent : baseEnd_1627747 < baseStart_1627747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627882 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_1627882 : Nat := 118140960795 + 1627882 * 2 ^ 59
def prefixEnd_1627882 : Nat := 4983230072969 + 3 ^ 40 * 1627882 * 2
def baseEnd_1627882 : Nat := 371504851023335616839339

theorem tailTrace_1627882 : CollatzResearch.WordTrace tailWord_1627882 prefixEnd_1627882 371504851023335616839339 := by
  unfold tailWord_1627882
  simp only [CollatzResearch.WordTrace]
  refine ⟨14843433572117252239099475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39582489525646005970931933 14843433572117252239099475)
  ·
    refine ⟨22265150358175878358649213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14843433572117252239099475 22265150358175878358649213)
    ·
      refine ⟨8349431384315954384493455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22265150358175878358649213 8349431384315954384493455)
      ·
        refine ⟨12524147076473931576740183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8349431384315954384493455 12524147076473931576740183)
        ·
          refine ⟨18786220614710897365110275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12524147076473931576740183 18786220614710897365110275)
          ·
            refine ⟨28179330922066346047665413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18786220614710897365110275 28179330922066346047665413)
            ·
              refine ⟨5283624547887439883937265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28179330922066346047665413 5283624547887439883937265)
              ·
                refine ⟨3962718410915579912952949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5283624547887439883937265 3962718410915579912952949)
                ·
                  refine ⟨371504851023335616839339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3962718410915579912952949 371504851023335616839339)
                  ·
                    rfl

theorem cell21_1627882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_1627882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627882 prefixEnd_1627882 := by exact prefixLift 1627882
  have htrace : WordTrace (prefixWord ++ tailWord_1627882) baseStart_1627882 baseEnd_1627882 := by
    simpa [prefixWord, tailWord_1627882, baseEnd_1627882] using wordTrace_append hprefix tailTrace_1627882
  have hstable : (prefixWord ++ tailWord_1627882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627882).length < 2 ^ (prefixWord ++ tailWord_1627882).sum := by decide
  have hdescent : baseEnd_1627882 < baseStart_1627882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627885 : List Nat := [1, 5, 1, 2, 1, 4, 2, 5]
def baseStart_1627885 : Nat := 118140960795 + 1627885 * 2 ^ 59
def prefixEnd_1627885 : Nat := 4983230072969 + 3 ^ 40 * 1627885 * 2
def baseEnd_1627885 : Nat := 123835178554736092763111

theorem tailTrace_1627885 : CollatzResearch.WordTrace tailWord_1627885 prefixEnd_1627885 123835178554736092763111 := by
  unfold tailWord_1627885
  simp only [CollatzResearch.WordTrace]
  refine ⟨59373843707458140468757109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39582562471638760312504739 59373843707458140468757109)
  ·
    refine ⟨5566297847574200668945979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59373843707458140468757109 5566297847574200668945979)
    ·
      refine ⟨8349446771361301003418969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5566297847574200668945979 8349446771361301003418969)
      ·
        refine ⟨6262085078520975752564227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8349446771361301003418969 6262085078520975752564227)
        ·
          refine ⟨9393127617781463628846341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6262085078520975752564227 9393127617781463628846341)
          ·
            refine ⟨1761211428334024430408689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9393127617781463628846341 1761211428334024430408689)
            ·
              refine ⟨1320908571250518322806517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1761211428334024430408689 1320908571250518322806517)
              ·
                refine ⟨123835178554736092763111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1320908571250518322806517 123835178554736092763111)
                ·
                  rfl

theorem cell21_1627885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 5].length) (baseStart_1627885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627885 prefixEnd_1627885 := by exact prefixLift 1627885
  have htrace : WordTrace (prefixWord ++ tailWord_1627885) baseStart_1627885 baseEnd_1627885 := by
    simpa [prefixWord, tailWord_1627885, baseEnd_1627885] using wordTrace_append hprefix tailTrace_1627885
  have hstable : (prefixWord ++ tailWord_1627885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627885).length < 2 ^ (prefixWord ++ tailWord_1627885).sum := by decide
  have hdescent : baseEnd_1627885 < baseStart_1627885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627927 : List Nat := [1, 1, 3, 4, 2, 1, 1, 8]
def baseStart_1627927 : Nat := 118140960795 + 1627927 * 2 ^ 59
def prefixEnd_1627927 : Nat := 4983230072969 + 3 ^ 40 * 1627927 * 2
def baseEnd_1627927 : Nat := 123838373545475179529749

theorem tailTrace_1627927 : CollatzResearch.WordTrace tailWord_1627927 prefixEnd_1627927 123838373545475179529749 := by
  unfold tailWord_1627927
  simp only [CollatzResearch.WordTrace]
  refine ⟨59375375573305981641786035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39583583715537321094524023 59375375573305981641786035)
  ·
    refine ⟨89063063359958972462679053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59375375573305981641786035 89063063359958972462679053)
    ·
      refine ⟨33398648759984614673504645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89063063359958972462679053 33398648759984614673504645)
      ·
        refine ⟨6262246642497115251282121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33398648759984614673504645 6262246642497115251282121)
        ·
          refine ⟨4696684981872836438461591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6262246642497115251282121 4696684981872836438461591)
          ·
            refine ⟨7045027472809254657692387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696684981872836438461591 7045027472809254657692387)
            ·
              refine ⟨10567541209213881986538581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7045027472809254657692387 10567541209213881986538581)
              ·
                refine ⟨123838373545475179529749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10567541209213881986538581 123838373545475179529749)
                ·
                  rfl

theorem cell21_1627927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 8].length) (baseStart_1627927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627927 prefixEnd_1627927 := by exact prefixLift 1627927
  have htrace : WordTrace (prefixWord ++ tailWord_1627927) baseStart_1627927 baseEnd_1627927 := by
    simpa [prefixWord, tailWord_1627927, baseEnd_1627927] using wordTrace_append hprefix tailTrace_1627927
  have hstable : (prefixWord ++ tailWord_1627927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627927).length < 2 ^ (prefixWord ++ tailWord_1627927).sum := by decide
  have hdescent : baseEnd_1627927 < baseStart_1627927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627930 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_1627930 : Nat := 118140960795 + 1627930 * 2 ^ 59
def prefixEnd_1627930 : Nat := 4983230072969 + 3 ^ 40 * 1627930 * 2
def baseEnd_1627930 : Nat := 371515805277298200039241

theorem tailTrace_1627930 : CollatzResearch.WordTrace tailWord_1627930 prefixEnd_1627930 371515805277298200039241 := by
  unfold tailWord_1627930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14843871248073778288536311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39583656661530075436096829 14843871248073778288536311)
  ·
    refine ⟨22265806872110667432804467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14843871248073778288536311 22265806872110667432804467)
    ·
      refine ⟨33398710308166001149206701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22265806872110667432804467 33398710308166001149206701)
      ·
        refine ⟨12524516365562250430952513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33398710308166001149206701 12524516365562250430952513)
        ·
          refine ⟨9393387274171687823214385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12524516365562250430952513 9393387274171687823214385)
          ·
            refine ⟨7045040455628765867410789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9393387274171687823214385 7045040455628765867410789)
            ·
              refine ⟨1320945085430393600139523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7045040455628765867410789 1320945085430393600139523)
              ·
                refine ⟨1981417628145590400209285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320945085430393600139523 1981417628145590400209285)
                ·
                  refine ⟨371515805277298200039241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1981417628145590400209285 371515805277298200039241)
                  ·
                    rfl

theorem cell21_1627930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_1627930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627930 prefixEnd_1627930 := by exact prefixLift 1627930
  have htrace : WordTrace (prefixWord ++ tailWord_1627930) baseStart_1627930 baseEnd_1627930 := by
    simpa [prefixWord, tailWord_1627930, baseEnd_1627930] using wordTrace_append hprefix tailTrace_1627930
  have hstable : (prefixWord ++ tailWord_1627930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627930).length < 2 ^ (prefixWord ++ tailWord_1627930).sum := by decide
  have hdescent : baseEnd_1627930 < baseStart_1627930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1627989 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 4]
def baseStart_1627989 : Nat := 118140960795 + 1627989 * 2 ^ 59
def prefixEnd_1627989 : Nat := 4983230072969 + 3 ^ 40 * 1627989 * 2
def baseEnd_1627989 : Nat := 371529269881127208555787

theorem tailTrace_1627989 : CollatzResearch.WordTrace tailWord_1627989 prefixEnd_1627989 371529269881127208555787 := by
  unfold tailWord_1627989
  simp only [CollatzResearch.WordTrace]
  refine ⟨59377636899081366230543021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39585091266054244153695347 59377636899081366230543021)
  ·
    refine ⟨22266613837155512336453633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59377636899081366230543021 22266613837155512336453633)
    ·
      refine ⟨16699960377866634252340225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22266613837155512336453633 16699960377866634252340225)
      ·
        refine ⟨12524970283399975689255169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16699960377866634252340225 12524970283399975689255169)
        ·
          refine ⟨9393727712549981766941377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12524970283399975689255169 9393727712549981766941377)
          ·
            refine ⟨7045295784412486325206033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9393727712549981766941377 7045295784412486325206033)
            ·
              refine ⟨5283971838309364743904525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7045295784412486325206033 5283971838309364743904525)
              ·
                refine ⟨1981489439366011778964197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5283971838309364743904525 1981489439366011778964197)
                ·
                  refine ⟨371529269881127208555787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1981489439366011778964197 371529269881127208555787)
                  ·
                    rfl

theorem cell21_1627989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_1627989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1627989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1627989 prefixEnd_1627989 := by exact prefixLift 1627989
  have htrace : WordTrace (prefixWord ++ tailWord_1627989) baseStart_1627989 baseEnd_1627989 := by
    simpa [prefixWord, tailWord_1627989, baseEnd_1627989] using wordTrace_append hprefix tailTrace_1627989
  have hstable : (prefixWord ++ tailWord_1627989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1627989).length < 2 ^ (prefixWord ++ tailWord_1627989).sum := by decide
  have hdescent : baseEnd_1627989 < baseStart_1627989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1627989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628017 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 7]
def baseStart_1628017 : Nat := 118140960795 + 1628017 * 2 ^ 59
def prefixEnd_1628017 : Nat := 4983230072969 + 3 ^ 40 * 1628017 * 2
def baseEnd_1628017 : Nat := 371535659862605382089063

theorem tailTrace_1628017 : CollatzResearch.WordTrace tailWord_1628017 prefixEnd_1628017 371535659862605382089063 := by
  unfold tailWord_1628017
  simp only [CollatzResearch.WordTrace]
  refine ⟨59378658142979927012562305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39585772095319951341708203 59378658142979927012562305)
  ·
    refine ⟨44533993607234945259421729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59378658142979927012562305 44533993607234945259421729)
    ·
      refine ⟨33400495205426208944566297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44533993607234945259421729 33400495205426208944566297)
      ·
        refine ⟨25050371404069656708424723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33400495205426208944566297 25050371404069656708424723)
        ·
          refine ⟨37575557106104485062637085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25050371404069656708424723 37575557106104485062637085)
          ·
            refine ⟨14090833914789181898488907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37575557106104485062637085 14090833914789181898488907)
            ·
              refine ⟨21136250872183772847733361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14090833914789181898488907 21136250872183772847733361)
              ·
                refine ⟨15852188154137829635800021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21136250872183772847733361 15852188154137829635800021)
                ·
                  refine ⟨371535659862605382089063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15852188154137829635800021 371535659862605382089063)
                  ·
                    rfl

theorem cell21_1628017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_1628017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628017 prefixEnd_1628017 := by exact prefixLift 1628017
  have htrace : WordTrace (prefixWord ++ tailWord_1628017) baseStart_1628017 baseEnd_1628017 := by
    simpa [prefixWord, tailWord_1628017, baseEnd_1628017] using wordTrace_append hprefix tailTrace_1628017
  have hstable : (prefixWord ++ tailWord_1628017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628017).length < 2 ^ (prefixWord ++ tailWord_1628017).sum := by decide
  have hdescent : baseEnd_1628017 < baseStart_1628017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628054 : List Nat := [5, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1628054 : Nat := 118140960795 + 1628054 * 2 ^ 59
def prefixEnd_1628054 : Nat := 4983230072969 + 3 ^ 40 * 1628054 * 2
def baseEnd_1628054 : Nat := 123848034588900513324107

theorem tailTrace_1628054 : CollatzResearch.WordTrace tailWord_1628054 prefixEnd_1628054 123848034588900513324107 := by
  unfold tailWord_1628054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3711250477740367645728701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39586671762563921554439477 3711250477740367645728701)
  ·
    refine ⟨1391718929152637867148263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3711250477740367645728701 1391718929152637867148263)
    ·
      refine ⟨2087578393728956800722395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391718929152637867148263 2087578393728956800722395)
      ·
        refine ⟨3131367590593435201083593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087578393728956800722395 3131367590593435201083593)
        ·
          refine ⟨2348525692945076400812695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3131367590593435201083593 2348525692945076400812695)
          ·
            refine ⟨3522788539417614601219043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348525692945076400812695 3522788539417614601219043)
            ·
              refine ⟨5284182809126421901828565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3522788539417614601219043 5284182809126421901828565)
              ·
                refine ⟨123848034588900513324107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5284182809126421901828565 123848034588900513324107)
                ·
                  rfl

theorem cell21_1628054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1628054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628054 prefixEnd_1628054 := by exact prefixLift 1628054
  have htrace : WordTrace (prefixWord ++ tailWord_1628054) baseStart_1628054 baseEnd_1628054 := by
    simpa [prefixWord, tailWord_1628054, baseEnd_1628054] using wordTrace_append hprefix tailTrace_1628054
  have hstable : (prefixWord ++ tailWord_1628054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628054).length < 2 ^ (prefixWord ++ tailWord_1628054).sum := by decide
  have hdescent : baseEnd_1628054 < baseStart_1628054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628068 : List Nat := [2, 3, 1, 2, 1, 5, 1, 3, 3]
def baseStart_1628068 : Nat := 118140960795 + 1628068 * 2 ^ 59
def prefixEnd_1628068 : Nat := 4983230072969 + 3 ^ 40 * 1628068 * 2
def baseEnd_1628068 : Nat := 371547298757440626738959

theorem tailTrace_1628068 : CollatzResearch.WordTrace tailWord_1628068 prefixEnd_1628068 371547298757440626738959 := by
  unfold tailWord_1628068
  simp only [CollatzResearch.WordTrace]
  refine ⟨29690259132897581361334429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39587012177196775148445905 29690259132897581361334429)
  ·
    refine ⟨11133847174836593010500411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29690259132897581361334429 11133847174836593010500411)
    ·
      refine ⟨16700770762254889515750617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11133847174836593010500411 16700770762254889515750617)
      ·
        refine ⟨12525578071691167136812963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16700770762254889515750617 12525578071691167136812963)
        ·
          refine ⟨18788367107536750705219445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12525578071691167136812963 18788367107536750705219445)
          ·
            refine ⟨1761409416331570378614323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18788367107536750705219445 1761409416331570378614323)
            ·
              refine ⟨2642114124497355567921485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761409416331570378614323 2642114124497355567921485)
              ·
                refine ⟨990792796686508337970557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2642114124497355567921485 990792796686508337970557)
                ·
                  refine ⟨371547298757440626738959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990792796686508337970557 371547298757440626738959)
                  ·
                    rfl

theorem cell21_1628068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_1628068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628068 prefixEnd_1628068 := by exact prefixLift 1628068
  have htrace : WordTrace (prefixWord ++ tailWord_1628068) baseStart_1628068 baseEnd_1628068 := by
    simpa [prefixWord, tailWord_1628068, baseEnd_1628068] using wordTrace_append hprefix tailTrace_1628068
  have hstable : (prefixWord ++ tailWord_1628068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628068).length < 2 ^ (prefixWord ++ tailWord_1628068).sum := by decide
  have hdescent : baseEnd_1628068 < baseStart_1628068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628158 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1628158 : Nat := 118140960795 + 1628158 * 2 ^ 59
def prefixEnd_1628158 : Nat := 4983230072969 + 3 ^ 40 * 1628158 * 2
def baseEnd_1628158 : Nat := 371567837983620470238775

theorem tailTrace_1628158 : CollatzResearch.WordTrace tailWord_1628158 prefixEnd_1628158 371567837983620470238775 := by
  unfold tailWord_1628158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7422975104433638511680641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39589200556979405395630085 7422975104433638511680641)
  ·
    refine ⟨5567231328325228883760481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7422975104433638511680641 5567231328325228883760481)
    ·
      refine ⟨4175423496243921662820361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5567231328325228883760481 4175423496243921662820361)
      ·
        refine ⟨3131567622182941247115271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4175423496243921662820361 3131567622182941247115271)
        ·
          refine ⟨4697351433274411870672907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3131567622182941247115271 4697351433274411870672907)
          ·
            refine ⟨7046027149911617806009361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4697351433274411870672907 7046027149911617806009361)
            ·
              refine ⟨5284520362433713354507021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7046027149911617806009361 5284520362433713354507021)
              ·
                refine ⟨1981695135912642507940133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5284520362433713354507021 1981695135912642507940133)
                ·
                  refine ⟨371567837983620470238775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1981695135912642507940133 371567837983620470238775)
                  ·
                    rfl

theorem cell21_1628158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1628158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628158 prefixEnd_1628158 := by exact prefixLift 1628158
  have htrace : WordTrace (prefixWord ++ tailWord_1628158) baseStart_1628158 baseEnd_1628158 := by
    simpa [prefixWord, tailWord_1628158, baseEnd_1628158] using wordTrace_append hprefix tailTrace_1628158
  have hstable : (prefixWord ++ tailWord_1628158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628158).length < 2 ^ (prefixWord ++ tailWord_1628158).sum := by decide
  have hdescent : baseEnd_1628158 < baseStart_1628158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628254 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1628254 : Nat := 118140960795 + 1628254 * 2 ^ 59
def prefixEnd_1628254 : Nat := 4983230072969 + 3 ^ 40 * 1628254 * 2
def baseEnd_1628254 : Nat := 371589746491545636638579

theorem tailTrace_1628254 : CollatzResearch.WordTrace tailWord_1628254 prefixEnd_1628254 371589746491545636638579 := by
  unfold tailWord_1628254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7423412780390164561117477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39591534828747544325959877 7423412780390164561117477)
  ·
    refine ⟨1391889896323155855209527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7423412780390164561117477 1391889896323155855209527)
    ·
      refine ⟨2087834844484733782814291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391889896323155855209527 2087834844484733782814291)
      ·
        refine ⟨3131752266727100674221437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2087834844484733782814291 3131752266727100674221437)
        ·
          refine ⟨1174407100022662752833039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3131752266727100674221437 1174407100022662752833039)
          ·
            refine ⟨1761610650033994129249559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174407100022662752833039 1761610650033994129249559)
            ·
              refine ⟨2642415975050991193874339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761610650033994129249559 2642415975050991193874339)
              ·
                refine ⟨3963623962576486790811509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2642415975050991193874339 3963623962576486790811509)
                ·
                  refine ⟨371589746491545636638579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3963623962576486790811509 371589746491545636638579)
                  ·
                    rfl

theorem cell21_1628254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1628254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628254 prefixEnd_1628254 := by exact prefixLift 1628254
  have htrace : WordTrace (prefixWord ++ tailWord_1628254) baseStart_1628254 baseEnd_1628254 := by
    simpa [prefixWord, tailWord_1628254, baseEnd_1628254] using wordTrace_append hprefix tailTrace_1628254
  have hstable : (prefixWord ++ tailWord_1628254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628254).length < 2 ^ (prefixWord ++ tailWord_1628254).sum := by decide
  have hdescent : baseEnd_1628254 < baseStart_1628254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628324 : List Nat := [2, 3, 1, 2, 4, 2, 1, 6]
def baseStart_1628324 : Nat := 118140960795 + 1628324 * 2 ^ 59
def prefixEnd_1628324 : Nat := 4983230072969 + 3 ^ 40 * 1628324 * 2
def baseEnd_1628324 : Nat := 123868573815080356823923

theorem tailTrace_1628324 : CollatzResearch.WordTrace tailWord_1628324 prefixEnd_1628324 123868573815080356823923 := by
  unfold tailWord_1628324
  simp only [CollatzResearch.WordTrace]
  refine ⟨29694927676433859221994013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39593236901911812295992017 29694927676433859221994013)
  ·
    refine ⟨11135597878662697208247755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29694927676433859221994013 11135597878662697208247755)
    ·
      refine ⟨16703396817994045812371633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11135597878662697208247755 16703396817994045812371633)
      ·
        refine ⟨12527547613495534359278725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16703396817994045812371633 12527547613495534359278725)
        ·
          refine ⟨2348915177530412692364761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12527547613495534359278725 2348915177530412692364761)
          ·
            refine ⟨1761686383147809519273571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2348915177530412692364761 1761686383147809519273571)
            ·
              refine ⟨2642529574721714278910357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761686383147809519273571 2642529574721714278910357)
              ·
                refine ⟨123868573815080356823923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2642529574721714278910357 123868573815080356823923)
                ·
                  rfl

theorem cell21_1628324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 6].length) (baseStart_1628324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628324 prefixEnd_1628324 := by exact prefixLift 1628324
  have htrace : WordTrace (prefixWord ++ tailWord_1628324) baseStart_1628324 baseEnd_1628324 := by
    simpa [prefixWord, tailWord_1628324, baseEnd_1628324] using wordTrace_append hprefix tailTrace_1628324
  have hstable : (prefixWord ++ tailWord_1628324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628324).length < 2 ^ (prefixWord ++ tailWord_1628324).sum := by decide
  have hdescent : baseEnd_1628324 < baseStart_1628324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628335 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 8]
def baseStart_1628335 : Nat := 118140960795 + 1628335 * 2 ^ 59
def prefixEnd_1628335 : Nat := 4983230072969 + 3 ^ 40 * 1628335 * 2
def baseEnd_1628335 : Nat := 371608231795107495788413

theorem tailTrace_1628335 : CollatzResearch.WordTrace tailWord_1628335 prefixEnd_1628335 371608231795107495788413 := by
  unfold tailWord_1628335
  simp only [CollatzResearch.WordTrace]
  refine ⟨59390256555827867322638459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39593504370551911548425639 59390256555827867322638459)
  ·
    refine ⟨89085384833741800983957689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59390256555827867322638459 89085384833741800983957689)
    ·
      refine ⟨66814038625306350737968267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89085384833741800983957689 66814038625306350737968267)
      ·
        refine ⟨100221057937959526106952401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66814038625306350737968267 100221057937959526106952401)
        ·
          refine ⟨75165793453469644580214301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100221057937959526106952401 75165793453469644580214301)
          ·
            refine ⟨28187172545051116717580363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75165793453469644580214301 28187172545051116717580363)
            ·
              refine ⟨42280758817576675076370545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28187172545051116717580363 42280758817576675076370545)
              ·
                refine ⟨31710569113182506307277909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42280758817576675076370545 31710569113182506307277909)
                ·
                  refine ⟨371608231795107495788413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31710569113182506307277909 371608231795107495788413)
                  ·
                    rfl

theorem cell21_1628335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_1628335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628335 prefixEnd_1628335 := by exact prefixLift 1628335
  have htrace : WordTrace (prefixWord ++ tailWord_1628335) baseStart_1628335 baseEnd_1628335 := by
    simpa [prefixWord, tailWord_1628335, baseEnd_1628335] using wordTrace_append hprefix tailTrace_1628335
  have hstable : (prefixWord ++ tailWord_1628335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628335).length < 2 ^ (prefixWord ++ tailWord_1628335).sum := by decide
  have hdescent : baseEnd_1628335 < baseStart_1628335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628341 : List Nat := [1, 3, 3, 4, 1, 1, 3, 5]
def baseStart_1628341 : Nat := 118140960795 + 1628341 * 2 ^ 59
def prefixEnd_1628341 : Nat := 4983230072969 + 3 ^ 40 * 1628341 * 2
def baseEnd_1628341 : Nat := 123869867025617606229467

theorem tailTrace_1628341 : CollatzResearch.WordTrace tailWord_1628341 prefixEnd_1628341 123869867025617606229467 := by
  unfold tailWord_1628341
  simp only [CollatzResearch.WordTrace]
  refine ⟨59390475393806130347356877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39593650262537420231571251 59390475393806130347356877)
  ·
    refine ⟨22271428272677298880258829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59390475393806130347356877 22271428272677298880258829)
    ·
      refine ⟨8351785602253987080097061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22271428272677298880258829 8351785602253987080097061)
      ·
        refine ⟨1565959800422622577518199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8351785602253987080097061 1565959800422622577518199)
        ·
          refine ⟨2348939700633933866277299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1565959800422622577518199 2348939700633933866277299)
          ·
            refine ⟨3523409550950900799415949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2348939700633933866277299 3523409550950900799415949)
            ·
              refine ⟨1321278581606587799780981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3523409550950900799415949 1321278581606587799780981)
              ·
                refine ⟨123869867025617606229467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1321278581606587799780981 123869867025617606229467)
                ·
                  rfl

theorem cell21_1628341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 5].length) (baseStart_1628341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628341 prefixEnd_1628341 := by exact prefixLift 1628341
  have htrace : WordTrace (prefixWord ++ tailWord_1628341) baseStart_1628341 baseEnd_1628341 := by
    simpa [prefixWord, tailWord_1628341, baseEnd_1628341] using wordTrace_append hprefix tailTrace_1628341
  have hstable : (prefixWord ++ tailWord_1628341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628341).length < 2 ^ (prefixWord ++ tailWord_1628341).sum := by decide
  have hdescent : baseEnd_1628341 < baseStart_1628341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628428 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 4]
def baseStart_1628428 : Nat := 118140960795 + 1628428 * 2 ^ 59
def prefixEnd_1628428 : Nat := 4983230072969 + 3 ^ 40 * 1628428 * 2
def baseEnd_1628428 : Nat := 371629455662160000738223

theorem tailTrace_1628428 : CollatzResearch.WordTrace tailWord_1628428 prefixEnd_1628428 371629455662160000738223 := by
  unfold tailWord_1628428
  simp only [CollatzResearch.WordTrace]
  refine ⟨29696824272245472102886969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39595765696327296137182625 29696824272245472102886969)
  ·
    refine ⟨22272618204184104077165227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29696824272245472102886969 22272618204184104077165227)
    ·
      refine ⟨33408927306276156115747841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22272618204184104077165227 33408927306276156115747841)
      ·
        refine ⟨25056695479707117086810881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33408927306276156115747841 25056695479707117086810881)
        ·
          refine ⟨18792521609780337815108161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25056695479707117086810881 18792521609780337815108161)
          ·
            refine ⟨14094391207335253361331121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18792521609780337815108161 14094391207335253361331121)
            ·
              refine ⟨10570793405501440020998341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14094391207335253361331121 10570793405501440020998341)
              ·
                refine ⟨1982023763531520003937189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10570793405501440020998341 1982023763531520003937189)
                ·
                  refine ⟨371629455662160000738223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982023763531520003937189 371629455662160000738223)
                  ·
                    rfl

theorem cell21_1628428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_1628428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628428 prefixEnd_1628428 := by exact prefixLift 1628428
  have htrace : WordTrace (prefixWord ++ tailWord_1628428) baseStart_1628428 baseEnd_1628428 := by
    simpa [prefixWord, tailWord_1628428, baseEnd_1628428] using wordTrace_append hprefix tailTrace_1628428
  have hstable : (prefixWord ++ tailWord_1628428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628428).length < 2 ^ (prefixWord ++ tailWord_1628428).sum := by decide
  have hdescent : baseEnd_1628428 < baseStart_1628428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628583 : List Nat := [1, 1, 6, 1, 1, 2, 3, 3, 3]
def baseStart_1628583 : Nat := 118140960795 + 1628583 * 2 ^ 59
def prefixEnd_1628583 : Nat := 4983230072969 + 3 ^ 40 * 1628583 * 2
def baseEnd_1628583 : Nat := 371664828773914175654573

theorem tailTrace_1628583 : CollatzResearch.WordTrace tailWord_1628583 prefixEnd_1628583 371664828773914175654573 := by
  unfold tailWord_1628583
  simp only [CollatzResearch.WordTrace]
  refine ⟨59399301858929405677666403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39599534572619603785110935 59399301858929405677666403)
  ·
    refine ⟨89098952788394108516499605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59399301858929405677666403 89098952788394108516499605)
    ·
      refine ⟨4176513411955973836710919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89098952788394108516499605 4176513411955973836710919)
      ·
        refine ⟨6264770117933960755066379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4176513411955973836710919 6264770117933960755066379)
        ·
          refine ⟨9397155176900941132599569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6264770117933960755066379 9397155176900941132599569)
          ·
            refine ⟨7047866382675705849449677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9397155176900941132599569 7047866382675705849449677)
            ·
              refine ⟨2642949893503389693543629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7047866382675705849449677 2642949893503389693543629)
              ·
                refine ⟨991106210063771135078861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2642949893503389693543629 991106210063771135078861)
                ·
                  refine ⟨371664828773914175654573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 991106210063771135078861 371664828773914175654573)
                  ·
                    rfl

theorem cell21_1628583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 3].length) (baseStart_1628583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628583 prefixEnd_1628583 := by exact prefixLift 1628583
  have htrace : WordTrace (prefixWord ++ tailWord_1628583) baseStart_1628583 baseEnd_1628583 := by
    simpa [prefixWord, tailWord_1628583, baseEnd_1628583] using wordTrace_append hprefix tailTrace_1628583
  have hstable : (prefixWord ++ tailWord_1628583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628583).length < 2 ^ (prefixWord ++ tailWord_1628583).sum := by decide
  have hdescent : baseEnd_1628583 < baseStart_1628583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628586 : List Nat := [3, 1, 6, 1, 2, 1, 7]
def baseStart_1628586 : Nat := 118140960795 + 1628586 * 2 ^ 59
def prefixEnd_1628586 : Nat := 4983230072969 + 3 ^ 40 * 1628586 * 2
def baseEnd_1628586 : Nat := 41296168157198537456063

theorem tailTrace_1628586 : CollatzResearch.WordTrace tailWord_1628586 prefixEnd_1628586 41296168157198537456063 := by
  unfold tailWord_1628586
  simp only [CollatzResearch.WordTrace]
  refine ⟨14849852819479634297506403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39599607518612358126683741 14849852819479634297506403)
  ·
    refine ⟨22274779229219451446259605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14849852819479634297506403 22274779229219451446259605)
    ·
      refine ⟨1044130276369661786543419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22274779229219451446259605 1044130276369661786543419)
      ·
        refine ⟨1566195414554492679815129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044130276369661786543419 1566195414554492679815129)
        ·
          refine ⟨1174646560915869509861347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1566195414554492679815129 1174646560915869509861347)
          ·
            refine ⟨1761969841373804264792021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174646560915869509861347 1761969841373804264792021)
            ·
              refine ⟨41296168157198537456063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1761969841373804264792021 41296168157198537456063)
              ·
                rfl

theorem cell21_1628586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 7].length) (baseStart_1628586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628586 prefixEnd_1628586 := by exact prefixLift 1628586
  have htrace : WordTrace (prefixWord ++ tailWord_1628586) baseStart_1628586 baseEnd_1628586 := by
    simpa [prefixWord, tailWord_1628586, baseEnd_1628586] using wordTrace_append hprefix tailTrace_1628586
  have hstable : (prefixWord ++ tailWord_1628586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628586).length < 2 ^ (prefixWord ++ tailWord_1628586).sum := by decide
  have hdescent : baseEnd_1628586 < baseStart_1628586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628656 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 4]
def baseStart_1628656 : Nat := 118140960795 + 1628656 * 2 ^ 59
def prefixEnd_1628656 : Nat := 4983230072969 + 3 ^ 40 * 1628656 * 2
def baseEnd_1628656 : Nat := 371681488368482270937757

theorem tailTrace_1628656 : CollatzResearch.WordTrace tailWord_1628656 prefixEnd_1628656 371681488368482270937757 := by
  unfold tailWord_1628656
  simp only [CollatzResearch.WordTrace]
  refine ⟨29700982193832469572536911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39601309591776626096715881 29700982193832469572536911)
  ·
    refine ⟨44551473290748704358805367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29700982193832469572536911 44551473290748704358805367)
    ·
      refine ⟨66827209936123056538208051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44551473290748704358805367 66827209936123056538208051)
      ·
        refine ⟨100240814904184584807312077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66827209936123056538208051 100240814904184584807312077)
        ·
          refine ⟨37590305589069219302742029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100240814904184584807312077 37590305589069219302742029)
          ·
            refine ⟨14096364595900957238528261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37590305589069219302742029 14096364595900957238528261)
            ·
              refine ⟨2643068361731429482224049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14096364595900957238528261 2643068361731429482224049)
              ·
                refine ⟨1982301271298572111668037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2643068361731429482224049 1982301271298572111668037)
                ·
                  refine ⟨371681488368482270937757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982301271298572111668037 371681488368482270937757)
                  ·
                    rfl

theorem cell21_1628656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_1628656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628656 prefixEnd_1628656 := by exact prefixLift 1628656
  have htrace : WordTrace (prefixWord ++ tailWord_1628656) baseStart_1628656 baseEnd_1628656 := by
    simpa [prefixWord, tailWord_1628656, baseEnd_1628656] using wordTrace_append hprefix tailTrace_1628656
  have hstable : (prefixWord ++ tailWord_1628656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628656).length < 2 ^ (prefixWord ++ tailWord_1628656).sum := by decide
  have hdescent : baseEnd_1628656 < baseStart_1628656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628746 : List Nat := [3, 1, 2, 1, 1, 5, 1, 7]
def baseStart_1628746 : Nat := 118140960795 + 1628746 * 2 ^ 59
def prefixEnd_1628746 : Nat := 4983230072969 + 3 ^ 40 * 1628746 * 2
def baseEnd_1628746 : Nat := 123900675864887371479191

theorem tailTrace_1628746 : CollatzResearch.WordTrace tailWord_1628746 prefixEnd_1628746 123900675864887371479191 := by
  unfold tailWord_1628746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14851311739334721128962523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39603497971559256343900061 14851311739334721128962523)
  ·
    refine ⟨22276967609002081693443785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14851311739334721128962523 22276967609002081693443785)
    ·
      refine ⟨16707725706751561270082839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22276967609002081693443785 16707725706751561270082839)
      ·
        refine ⟨25061588560127341905124259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16707725706751561270082839 25061588560127341905124259)
        ·
          refine ⟨37592382840191012857686389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25061588560127341905124259 37592382840191012857686389)
          ·
            refine ⟨3524285891267907455408099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37592382840191012857686389 3524285891267907455408099)
            ·
              refine ⟨5286428836901861183112149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3524285891267907455408099 5286428836901861183112149)
              ·
                refine ⟨123900675864887371479191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5286428836901861183112149 123900675864887371479191)
                ·
                  rfl

theorem cell21_1628746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_1628746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628746 prefixEnd_1628746 := by exact prefixLift 1628746
  have htrace : WordTrace (prefixWord ++ tailWord_1628746) baseStart_1628746 baseEnd_1628746 := by
    simpa [prefixWord, tailWord_1628746, baseEnd_1628746] using wordTrace_append hprefix tailTrace_1628746
  have hstable : (prefixWord ++ tailWord_1628746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628746).length < 2 ^ (prefixWord ++ tailWord_1628746).sum := by decide
  have hdescent : baseEnd_1628746 < baseStart_1628746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628760 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_1628760 : Nat := 118140960795 + 1628760 * 2 ^ 59
def prefixEnd_1628760 : Nat := 4983230072969 + 3 ^ 40 * 1628760 * 2
def baseEnd_1628760 : Nat := 371705222585401201204211

theorem tailTrace_1628760 : CollatzResearch.WordTrace tailWord_1628760 prefixEnd_1628760 371705222585401201204211 := by
  unfold tailWord_1628760
  simp only [CollatzResearch.WordTrace]
  refine ⟨29702878789644082453429867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39603838386192109937906489 29702878789644082453429867)
  ·
    refine ⟨44554318184466123680144801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29702878789644082453429867 44554318184466123680144801)
    ·
      refine ⟨33415738638349592760108601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44554318184466123680144801 33415738638349592760108601)
      ·
        refine ⟨25061803978762194570081451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33415738638349592760108601 25061803978762194570081451)
        ·
          refine ⟨37592705968143291855122177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25061803978762194570081451 37592705968143291855122177)
          ·
            refine ⟨28194529476107468891341633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37592705968143291855122177 28194529476107468891341633)
            ·
              refine ⟨21145897107080601668506225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28194529476107468891341633 21145897107080601668506225)
              ·
                refine ⟨15859422830310451251379669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21145897107080601668506225 15859422830310451251379669)
                ·
                  refine ⟨371705222585401201204211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15859422830310451251379669 371705222585401201204211)
                  ·
                    rfl

theorem cell21_1628760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_1628760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628760 prefixEnd_1628760 := by exact prefixLift 1628760
  have htrace : WordTrace (prefixWord ++ tailWord_1628760) baseStart_1628760 baseEnd_1628760 := by
    simpa [prefixWord, tailWord_1628760, baseEnd_1628760] using wordTrace_append hprefix tailTrace_1628760
  have hstable : (prefixWord ++ tailWord_1628760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628760).length < 2 ^ (prefixWord ++ tailWord_1628760).sum := by decide
  have hdescent : baseEnd_1628760 < baseStart_1628760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628828 : List Nat := [2, 2, 3, 2, 2, 3, 2, 2, 3]
def baseStart_1628828 : Nat := 118140960795 + 1628828 * 2 ^ 59
def prefixEnd_1628828 : Nat := 4983230072969 + 3 ^ 40 * 1628828 * 2
def baseEnd_1628828 : Nat := 371720741111848194070739

theorem tailTrace_1628828 : CollatzResearch.WordTrace tailWord_1628828 prefixEnd_1628828 371720741111848194070739 := by
  unfold tailWord_1628828
  simp only [CollatzResearch.WordTrace]
  refine ⟨29704118871520906260167569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39605491828694541680223425 29704118871520906260167569)
  ·
    refine ⟨22278089153640679695125677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29704118871520906260167569 22278089153640679695125677)
    ·
      refine ⟨8354283432615254885672129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22278089153640679695125677 8354283432615254885672129)
      ·
        refine ⟨6265712574461441164254097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8354283432615254885672129 6265712574461441164254097)
        ·
          refine ⟨4699284430846080873190573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6265712574461441164254097 4699284430846080873190573)
          ·
            refine ⟨1762231661567280327446465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4699284430846080873190573 1762231661567280327446465)
            ·
              refine ⟨1321673746175460245584849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762231661567280327446465 1321673746175460245584849)
              ·
                refine ⟨991255309631595184188637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1321673746175460245584849 991255309631595184188637)
                ·
                  refine ⟨371720741111848194070739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 991255309631595184188637 371720741111848194070739)
                  ·
                    rfl

theorem cell21_1628828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 3].length) (baseStart_1628828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628828 prefixEnd_1628828 := by exact prefixLift 1628828
  have htrace : WordTrace (prefixWord ++ tailWord_1628828) baseStart_1628828 baseEnd_1628828 := by
    simpa [prefixWord, tailWord_1628828, baseEnd_1628828] using wordTrace_append hprefix tailTrace_1628828
  have hstable : (prefixWord ++ tailWord_1628828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628828).length < 2 ^ (prefixWord ++ tailWord_1628828).sum := by decide
  have hdescent : baseEnd_1628828 < baseStart_1628828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628853 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 7]
def baseStart_1628853 : Nat := 118140960795 + 1628853 * 2 ^ 59
def prefixEnd_1628853 : Nat := 4983230072969 + 3 ^ 40 * 1628853 * 2
def baseEnd_1628853 : Nat := 371726446452453706154021

theorem tailTrace_1628853 : CollatzResearch.WordTrace tailWord_1628853 prefixEnd_1628853 371726446452453706154021 := by
  unfold tailWord_1628853
  simp only [CollatzResearch.WordTrace]
  refine ⟨59409149567951241789995213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39606099711967494526663475 59409149567951241789995213)
  ·
    refine ⟨22278431087981715671248205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59409149567951241789995213 22278431087981715671248205)
    ·
      refine ⟨8354411657993143376718077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22278431087981715671248205 8354411657993143376718077)
      ·
        refine ⟨3132904371747428766269279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8354411657993143376718077 3132904371747428766269279)
        ·
          refine ⟨4699356557621143149403919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3132904371747428766269279 4699356557621143149403919)
          ·
            refine ⟨7049034836431714724105879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4699356557621143149403919 7049034836431714724105879)
            ·
              refine ⟨10573552254647572086158819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7049034836431714724105879 10573552254647572086158819)
              ·
                refine ⟨15860328381971358129238229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10573552254647572086158819 15860328381971358129238229)
                ·
                  refine ⟨371726446452453706154021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15860328381971358129238229 371726446452453706154021)
                  ·
                    rfl

theorem cell21_1628853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_1628853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628853 prefixEnd_1628853 := by exact prefixLift 1628853
  have htrace : WordTrace (prefixWord ++ tailWord_1628853) baseStart_1628853 baseEnd_1628853 := by
    simpa [prefixWord, tailWord_1628853, baseEnd_1628853] using wordTrace_append hprefix tailTrace_1628853
  have hstable : (prefixWord ++ tailWord_1628853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628853).length < 2 ^ (prefixWord ++ tailWord_1628853).sum := by decide
  have hdescent : baseEnd_1628853 < baseStart_1628853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628881 : List Nat := [1, 2, 2, 1, 2, 3, 10]
def baseStart_1628881 : Nat := 118140960795 + 1628881 * 2 ^ 59
def prefixEnd_1628881 : Nat := 4983230072969 + 3 ^ 40 * 1628881 * 2
def baseEnd_1628881 : Nat := 41303648492659097743033

theorem tailTrace_1628881 : CollatzResearch.WordTrace tailWord_1628881 prefixEnd_1628881 41303648492659097743033 := by
  unfold tailWord_1628881
  simp only [CollatzResearch.WordTrace]
  refine ⟨59410170811849802572014497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39606780541233201714676331 59410170811849802572014497)
  ·
    refine ⟨44557628108887351929010873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59410170811849802572014497 44557628108887351929010873)
    ·
      refine ⟨33418221081665513946758155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44557628108887351929010873 33418221081665513946758155)
      ·
        refine ⟨50127331622498270920137233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33418221081665513946758155 50127331622498270920137233)
        ·
          refine ⟨37595498716873703190102925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50127331622498270920137233 37595498716873703190102925)
          ·
            refine ⟨14098312018827638696288597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37595498716873703190102925 14098312018827638696288597)
            ·
              refine ⟨41303648492659097743033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14098312018827638696288597 41303648492659097743033)
              ·
                rfl

theorem cell21_1628881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 10].length) (baseStart_1628881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628881 prefixEnd_1628881 := by exact prefixLift 1628881
  have htrace : WordTrace (prefixWord ++ tailWord_1628881) baseStart_1628881 baseEnd_1628881 := by
    simpa [prefixWord, tailWord_1628881, baseEnd_1628881] using wordTrace_append hprefix tailTrace_1628881
  have hstable : (prefixWord ++ tailWord_1628881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628881).length < 2 ^ (prefixWord ++ tailWord_1628881).sum := by decide
  have hdescent : baseEnd_1628881 < baseStart_1628881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628901 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 4]
def baseStart_1628901 : Nat := 118140960795 + 1628901 * 2 ^ 59
def prefixEnd_1628901 : Nat := 4983230072969 + 3 ^ 40 * 1628901 * 2
def baseEnd_1628901 : Nat := 371737400706416289353923

theorem tailTrace_1628901 : CollatzResearch.WordTrace tailWord_1628901 prefixEnd_1628901 371737400706416289353923 := by
  unfold tailWord_1628901
  simp only [CollatzResearch.WordTrace]
  refine ⟨59410900271777345987742557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39607266847851563991828371 59410900271777345987742557)
  ·
    refine ⟨22279087601916504745403459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59410900271777345987742557 22279087601916504745403459)
    ·
      refine ⟨33418631402874757118105189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22279087601916504745403459 33418631402874757118105189)
      ·
        refine ⟨6265993388039016959644723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33418631402874757118105189 6265993388039016959644723)
        ·
          refine ⟨9398990082058525439467085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6265993388039016959644723 9398990082058525439467085)
          ·
            refine ⟨3524621280771947039800157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9398990082058525439467085 3524621280771947039800157)
            ·
              refine ⟨1321732980289480139925059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3524621280771947039800157 1321732980289480139925059)
              ·
                refine ⟨1982599470434220209887589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321732980289480139925059 1982599470434220209887589)
                ·
                  refine ⟨371737400706416289353923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982599470434220209887589 371737400706416289353923)
                  ·
                    rfl

theorem cell21_1628901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_1628901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628901 prefixEnd_1628901 := by exact prefixLift 1628901
  have htrace : WordTrace (prefixWord ++ tailWord_1628901) baseStart_1628901 baseEnd_1628901 := by
    simpa [prefixWord, tailWord_1628901, baseEnd_1628901] using wordTrace_append hprefix tailTrace_1628901
  have hstable : (prefixWord ++ tailWord_1628901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628901).length < 2 ^ (prefixWord ++ tailWord_1628901).sum := by decide
  have hdescent : baseEnd_1628901 < baseStart_1628901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628912 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_1628912 : Nat := 118140960795 + 1628912 * 2 ^ 59
def prefixEnd_1628912 : Nat := 4983230072969 + 3 ^ 40 * 1628912 * 2
def baseEnd_1628912 : Nat := 371739911056282714670567

theorem tailTrace_1628912 : CollatzResearch.WordTrace tailWord_1628912 prefixEnd_1628912 371739911056282714670567 := by
  unfold tailWord_1628912
  simp only [CollatzResearch.WordTrace]
  refine ⟨29705650737368747433196495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39607534316491663244261993 29705650737368747433196495)
  ·
    refine ⟨44558476106053121149794743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29705650737368747433196495 44558476106053121149794743)
    ·
      refine ⟨66837714159079681724692115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44558476106053121149794743 66837714159079681724692115)
      ·
        refine ⟨100256571238619522587038173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66837714159079681724692115 100256571238619522587038173)
        ·
          refine ⟨37596214214482320970139315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100256571238619522587038173 37596214214482320970139315)
          ·
            refine ⟨56394321321723481455208973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37596214214482320970139315 56394321321723481455208973)
            ·
              refine ⟨21147870495646305545703365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56394321321723481455208973 21147870495646305545703365)
              ·
                refine ⟨3965225717933682289819381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21147870495646305545703365 3965225717933682289819381)
                ·
                  refine ⟨371739911056282714670567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3965225717933682289819381 371739911056282714670567)
                  ·
                    rfl

theorem cell21_1628912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_1628912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628912 prefixEnd_1628912 := by exact prefixLift 1628912
  have htrace : WordTrace (prefixWord ++ tailWord_1628912) baseStart_1628912 baseEnd_1628912 := by
    simpa [prefixWord, tailWord_1628912, baseEnd_1628912] using wordTrace_append hprefix tailTrace_1628912
  have hstable : (prefixWord ++ tailWord_1628912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628912).length < 2 ^ (prefixWord ++ tailWord_1628912).sum := by decide
  have hdescent : baseEnd_1628912 < baseStart_1628912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628943 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 4]
def baseStart_1628943 : Nat := 118140960795 + 1628943 * 2 ^ 59
def prefixEnd_1628943 : Nat := 4983230072969 + 3 ^ 40 * 1628943 * 2
def baseEnd_1628943 : Nat := 371746985678633549653837

theorem tailTrace_1628943 : CollatzResearch.WordTrace tailWord_1628943 prefixEnd_1628943 371746985678633549653837 := by
  unfold tailWord_1628943
  simp only [CollatzResearch.WordTrace]
  refine ⟨59412432137625187160771483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39608288091750124773847655 59412432137625187160771483)
  ·
    refine ⟨89118648206437780741157225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59412432137625187160771483 89118648206437780741157225)
    ·
      refine ⟨66838986154828335555867919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89118648206437780741157225 66838986154828335555867919)
      ·
        refine ⟨100258479232242503333801879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66838986154828335555867919 100258479232242503333801879)
        ·
          refine ⟨150387718848363755000702819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100258479232242503333801879 150387718848363755000702819)
          ·
            refine ⟨225581578272545632501054229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150387718848363755000702819 225581578272545632501054229)
            ·
              refine ⟨10574136481525576523486917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 225581578272545632501054229 10574136481525576523486917)
              ·
                refine ⟨1982650590286045598153797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10574136481525576523486917 1982650590286045598153797)
                ·
                  refine ⟨371746985678633549653837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982650590286045598153797 371746985678633549653837)
                  ·
                    rfl

theorem cell21_1628943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 4].length) (baseStart_1628943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628943 prefixEnd_1628943 := by exact prefixLift 1628943
  have htrace : WordTrace (prefixWord ++ tailWord_1628943) baseStart_1628943 baseEnd_1628943 := by
    simpa [prefixWord, tailWord_1628943, baseEnd_1628943] using wordTrace_append hprefix tailTrace_1628943
  have hstable : (prefixWord ++ tailWord_1628943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628943).length < 2 ^ (prefixWord ++ tailWord_1628943).sum := by decide
  have hdescent : baseEnd_1628943 < baseStart_1628943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1628960 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 4]
def baseStart_1628960 : Nat := 118140960795 + 1628960 * 2 ^ 59
def prefixEnd_1628960 : Nat := 4983230072969 + 3 ^ 40 * 1628960 * 2
def baseEnd_1628960 : Nat := 371750865310245297870469

theorem tailTrace_1628960 : CollatzResearch.WordTrace tailWord_1628960 prefixEnd_1628960 371750865310245297870469 := by
  unfold tailWord_1628960
  simp only [CollatzResearch.WordTrace]
  refine ⟨29706526089281799532070167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39608701452375732709426889 29706526089281799532070167)
  ·
    refine ⟨44559789133922699298105251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29706526089281799532070167 44559789133922699298105251)
    ·
      refine ⟨66839683700884048947157877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44559789133922699298105251 66839683700884048947157877)
      ·
        refine ⟨6266220346957879588796051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66839683700884048947157877 6266220346957879588796051)
        ·
          refine ⟨9399330520436819383194077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6266220346957879588796051 9399330520436819383194077)
          ·
            refine ⟨3524748945163807268697779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9399330520436819383194077 3524748945163807268697779)
            ·
              refine ⟨5287123417745710903046669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3524748945163807268697779 5287123417745710903046669)
              ·
                refine ⟨1982671281654641588642501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5287123417745710903046669 1982671281654641588642501)
                ·
                  refine ⟨371750865310245297870469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982671281654641588642501 371750865310245297870469)
                  ·
                    rfl

theorem cell21_1628960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 4].length) (baseStart_1628960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1628960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1628960 prefixEnd_1628960 := by exact prefixLift 1628960
  have htrace : WordTrace (prefixWord ++ tailWord_1628960) baseStart_1628960 baseEnd_1628960 := by
    simpa [prefixWord, tailWord_1628960, baseEnd_1628960] using wordTrace_append hprefix tailTrace_1628960
  have hstable : (prefixWord ++ tailWord_1628960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1628960).length < 2 ^ (prefixWord ++ tailWord_1628960).sum := by decide
  have hdescent : baseEnd_1628960 < baseStart_1628960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1628960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629084 : List Nat := [2, 2, 3, 3, 2, 2, 2, 5]
def baseStart_1629084 : Nat := 118140960795 + 1629084 * 2 ^ 59
def prefixEnd_1629084 : Nat := 4983230072969 + 3 ^ 40 * 1629084 * 2
def baseEnd_1629084 : Nat := 123926387933216212601183

theorem tailTrace_1629084 : CollatzResearch.WordTrace tailWord_1629084 prefixEnd_1629084 123926387933216212601183 := by
  unfold tailWord_1629084
  simp only [CollatzResearch.WordTrace]
  refine ⟨29708787415057184120827153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39611716553409578827769537 29708787415057184120827153)
  ·
    refine ⟨22281590561292888090620365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29708787415057184120827153 22281590561292888090620365)
    ·
      refine ⟨8355596460484833033982637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22281590561292888090620365 8355596460484833033982637)
      ·
        refine ⟨3133348672681812387743489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8355596460484833033982637 3133348672681812387743489)
        ·
          refine ⟨2350011504511359290807617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3133348672681812387743489 2350011504511359290807617)
          ·
            refine ⟨1762508628383519468105713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2350011504511359290807617 1762508628383519468105713)
            ·
              refine ⟨1321881471287639601079285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762508628383519468105713 1321881471287639601079285)
              ·
                refine ⟨123926387933216212601183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1321881471287639601079285 123926387933216212601183)
                ·
                  rfl

theorem cell21_1629084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_1629084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629084 prefixEnd_1629084 := by exact prefixLift 1629084
  have htrace : WordTrace (prefixWord ++ tailWord_1629084) baseStart_1629084 baseEnd_1629084 := by
    simpa [prefixWord, tailWord_1629084, baseEnd_1629084] using wordTrace_append hprefix tailTrace_1629084
  have hstable : (prefixWord ++ tailWord_1629084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629084).length < 2 ^ (prefixWord ++ tailWord_1629084).sum := by decide
  have hdescent : baseEnd_1629084 < baseStart_1629084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629233 : List Nat := [1, 2, 2, 3, 1, 2, 1, 6, 3]
def baseStart_1629233 : Nat := 118140960795 + 1629233 * 2 ^ 59
def prefixEnd_1629233 : Nat := 4983230072969 + 3 ^ 40 * 1629233 * 2
def baseEnd_1629233 : Nat := 371813167629657489819911

theorem tailTrace_1629233 : CollatzResearch.WordTrace tailWord_1629233 prefixEnd_1629233 371813167629657489819911 := by
  unfold tailWord_1629233
  simp only [CollatzResearch.WordTrace]
  refine ⟨59423009306574566688828353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39615339537716377792552235 59423009306574566688828353)
  ·
    refine ⟨44567256979930925016621265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59423009306574566688828353 44567256979930925016621265)
    ·
      refine ⟨33425442734948193762465949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44567256979930925016621265 33425442734948193762465949)
      ·
        refine ⟨12534541025605572660924731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33425442734948193762465949 12534541025605572660924731)
        ·
          refine ⟨18801811538408358991387097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12534541025605572660924731 18801811538408358991387097)
          ·
            refine ⟨14101358653806269243540323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18801811538408358991387097 14101358653806269243540323)
            ·
              refine ⟨21152037980709403865310485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14101358653806269243540323 21152037980709403865310485)
              ·
                refine ⟨991501780345753306186429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21152037980709403865310485 991501780345753306186429)
                ·
                  refine ⟨371813167629657489819911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 991501780345753306186429 371813167629657489819911)
                  ·
                    rfl

theorem cell21_1629233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 3].length) (baseStart_1629233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629233 prefixEnd_1629233 := by exact prefixLift 1629233
  have htrace : WordTrace (prefixWord ++ tailWord_1629233) baseStart_1629233 baseEnd_1629233 := by
    simpa [prefixWord, tailWord_1629233, baseEnd_1629233] using wordTrace_append hprefix tailTrace_1629233
  have hstable : (prefixWord ++ tailWord_1629233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629233).length < 2 ^ (prefixWord ++ tailWord_1629233).sum := by decide
  have hdescent : baseEnd_1629233 < baseStart_1629233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629340 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 4]
def baseStart_1629340 : Nat := 118140960795 + 1629340 * 2 ^ 59
def prefixEnd_1629340 : Nat := 4983230072969 + 3 ^ 40 * 1629340 * 2
def baseEnd_1629340 : Nat := 371837586487449081536359

theorem tailTrace_1629340 : CollatzResearch.WordTrace tailWord_1629340 prefixEnd_1629340 371837586487449081536359 := by
  unfold tailWord_1629340
  simp only [CollatzResearch.WordTrace]
  refine ⟨29713455958593461981486737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39617941278124615975315649 29713455958593461981486737)
  ·
    refine ⟨22285091968945096486115053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29713455958593461981486737 22285091968945096486115053)
    ·
      refine ⟨8356909488354411182293145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22285091968945096486115053 8356909488354411182293145)
      ·
        refine ⟨6267682116265808386719859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8356909488354411182293145 6267682116265808386719859)
        ·
          refine ⟨9401523174398712580079789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6267682116265808386719859 9401523174398712580079789)
          ·
            refine ⟨3525571190399517217529921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9401523174398712580079789 3525571190399517217529921)
            ·
              refine ⟨2644178392799637913147441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3525571190399517217529921 2644178392799637913147441)
              ·
                refine ⟨1983133794599728434860581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2644178392799637913147441 1983133794599728434860581)
                ·
                  refine ⟨371837586487449081536359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983133794599728434860581 371837586487449081536359)
                  ·
                    rfl

theorem cell21_1629340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_1629340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629340 prefixEnd_1629340 := by exact prefixLift 1629340
  have htrace : WordTrace (prefixWord ++ tailWord_1629340) baseStart_1629340 baseEnd_1629340 := by
    simpa [prefixWord, tailWord_1629340, baseEnd_1629340] using wordTrace_append hprefix tailTrace_1629340
  have hstable : (prefixWord ++ tailWord_1629340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629340).length < 2 ^ (prefixWord ++ tailWord_1629340).sum := by decide
  have hdescent : baseEnd_1629340 < baseStart_1629340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629399 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 4]
def baseStart_1629399 : Nat := 118140960795 + 1629399 * 2 ^ 59
def prefixEnd_1629399 : Nat := 4983230072969 + 3 ^ 40 * 1629399 * 2
def baseEnd_1629399 : Nat := 371851051091278090052905

theorem tailTrace_1629399 : CollatzResearch.WordTrace tailWord_1629399 prefixEnd_1629399 371851051091278090052905 := by
  unfold tailWord_1629399
  simp only [CollatzResearch.WordTrace]
  refine ⟨59429063823973177039371251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39619375882648784692914167 59429063823973177039371251)
  ·
    refine ⟨89143595735959765559056877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59429063823973177039371251 89143595735959765559056877)
    ·
      refine ⟨33428848400984912084646329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89143595735959765559056877 33428848400984912084646329)
      ·
        refine ⟨25071636300738684063484747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33428848400984912084646329 25071636300738684063484747)
        ·
          refine ⟨37607454451108026095227121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25071636300738684063484747 37607454451108026095227121)
          ·
            refine ⟨28205590838331019571420341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37607454451108026095227121 28205590838331019571420341)
            ·
              refine ⟨2644274141093533084820657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28205590838331019571420341 2644274141093533084820657)
              ·
                refine ⟨1983205605820149813615493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2644274141093533084820657 1983205605820149813615493)
                ·
                  refine ⟨371851051091278090052905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983205605820149813615493 371851051091278090052905)
                  ·
                    rfl

theorem cell21_1629399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 4].length) (baseStart_1629399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629399 prefixEnd_1629399 := by exact prefixLift 1629399
  have htrace : WordTrace (prefixWord ++ tailWord_1629399) baseStart_1629399 baseEnd_1629399 := by
    simpa [prefixWord, tailWord_1629399, baseEnd_1629399] using wordTrace_append hprefix tailTrace_1629399
  have hstable : (prefixWord ++ tailWord_1629399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629399).length < 2 ^ (prefixWord ++ tailWord_1629399).sum := by decide
  have hdescent : baseEnd_1629399 < baseStart_1629399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629416 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 4]
def baseStart_1629416 : Nat := 118140960795 + 1629416 * 2 ^ 59
def prefixEnd_1629416 : Nat := 4983230072969 + 3 ^ 40 * 1629416 * 2
def baseEnd_1629416 : Nat := 371854930722889838269537

theorem tailTrace_1629416 : CollatzResearch.WordTrace tailWord_1629416 prefixEnd_1629416 371854930722889838269537 := by
  unfold tailWord_1629416
  simp only [CollatzResearch.WordTrace]
  refine ⟨29714841932455794471370051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39619789243274392628493401 29714841932455794471370051)
  ·
    refine ⟨44572262898683691707055077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29714841932455794471370051 44572262898683691707055077)
    ·
      refine ⟨8357299293503192195072827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44572262898683691707055077 8357299293503192195072827)
      ·
        refine ⟨12535948940254788292609241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8357299293503192195072827 12535948940254788292609241)
        ·
          refine ⟨9401961705191091219456931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12535948940254788292609241 9401961705191091219456931)
          ·
            refine ⟨14102942557786636829185397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9401961705191091219456931 14102942557786636829185397)
            ·
              refine ⟨1322150864792497202736131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14102942557786636829185397 1322150864792497202736131)
              ·
                refine ⟨1983226297188745804104197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322150864792497202736131 1983226297188745804104197)
                ·
                  refine ⟨371854930722889838269537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983226297188745804104197 371854930722889838269537)
                  ·
                    rfl

theorem cell21_1629416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_1629416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629416 prefixEnd_1629416 := by exact prefixLift 1629416
  have htrace : WordTrace (prefixWord ++ tailWord_1629416) baseStart_1629416 baseEnd_1629416 := by
    simpa [prefixWord, tailWord_1629416, baseEnd_1629416] using wordTrace_append hprefix tailTrace_1629416
  have hstable : (prefixWord ++ tailWord_1629416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629416).length < 2 ^ (prefixWord ++ tailWord_1629416).sum := by decide
  have hdescent : baseEnd_1629416 < baseStart_1629416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629475 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 4]
def baseStart_1629475 : Nat := 118140960795 + 1629475 * 2 ^ 59
def prefixEnd_1629475 : Nat := 4983230072969 + 3 ^ 40 * 1629475 * 2
def baseEnd_1629475 : Nat := 371868395326718846786083

theorem tailTrace_1629475 : CollatzResearch.WordTrace tailWord_1629475 prefixEnd_1629475 371868395326718846786083 := by
  unfold tailWord_1629475
  simp only [CollatzResearch.WordTrace]
  refine ⟨59431835771697842019137879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39621223847798561346091919 59431835771697842019137879)
  ·
    refine ⟨89147753657546763028706819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59431835771697842019137879 89147753657546763028706819)
    ·
      refine ⟨133721630486320144543060229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89147753657546763028706819 133721630486320144543060229)
      ·
        refine ⟨25072805716185027101823793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133721630486320144543060229 25072805716185027101823793)
        ·
          refine ⟨18804604287138770326367845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25072805716185027101823793 18804604287138770326367845)
          ·
            refine ⟨3525863303838519436193971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18804604287138770326367845 3525863303838519436193971)
            ·
              refine ⟨5288794955757779154290957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3525863303838519436193971 5288794955757779154290957)
              ·
                refine ⟨1983298108409167182859109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5288794955757779154290957 1983298108409167182859109)
                ·
                  refine ⟨371868395326718846786083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983298108409167182859109 371868395326718846786083)
                  ·
                    rfl

theorem cell21_1629475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 4].length) (baseStart_1629475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629475 prefixEnd_1629475 := by exact prefixLift 1629475
  have htrace : WordTrace (prefixWord ++ tailWord_1629475) baseStart_1629475 baseEnd_1629475 := by
    simpa [prefixWord, tailWord_1629475, baseEnd_1629475] using wordTrace_append hprefix tailTrace_1629475
  have hstable : (prefixWord ++ tailWord_1629475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629475).length < 2 ^ (prefixWord ++ tailWord_1629475).sum := by decide
  have hdescent : baseEnd_1629475 < baseStart_1629475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629489 : List Nat := [1, 2, 2, 3, 3, 1, 2, 7]
def baseStart_1629489 : Nat := 118140960795 + 1629489 * 2 ^ 59
def prefixEnd_1629489 : Nat := 4983230072969 + 3 ^ 40 * 1629489 * 2
def baseEnd_1629489 : Nat := 123957196772485977850907

theorem tailTrace_1629489 : CollatzResearch.WordTrace tailWord_1629489 prefixEnd_1629489 123957196772485977850907 := by
  unfold tailWord_1629489
  simp only [CollatzResearch.WordTrace]
  refine ⟨59432346393647122410147521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39621564262431414940098347 59432346393647122410147521)
  ·
    refine ⟨44574259795235341807610641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59432346393647122410147521 44574259795235341807610641)
    ·
      refine ⟨33430694846426506355707981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44574259795235341807610641 33430694846426506355707981)
      ·
        refine ⟨12536510567409939883390493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33430694846426506355707981 12536510567409939883390493)
        ·
          refine ⟨4701191462778727456271435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12536510567409939883390493 4701191462778727456271435)
          ·
            refine ⟨7051787194168091184407153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701191462778727456271435 7051787194168091184407153)
            ·
              refine ⟨5288840395626068388305365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7051787194168091184407153 5288840395626068388305365)
              ·
                refine ⟨123957196772485977850907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5288840395626068388305365 123957196772485977850907)
                ·
                  rfl

theorem cell21_1629489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 7].length) (baseStart_1629489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629489 prefixEnd_1629489 := by exact prefixLift 1629489
  have htrace : WordTrace (prefixWord ++ tailWord_1629489) baseStart_1629489 baseEnd_1629489 := by
    simpa [prefixWord, tailWord_1629489, baseEnd_1629489] using wordTrace_append hprefix tailTrace_1629489
  have hstable : (prefixWord ++ tailWord_1629489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629489).length < 2 ^ (prefixWord ++ tailWord_1629489).sum := by decide
  have hdescent : baseEnd_1629489 < baseStart_1629489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629624 : List Nat := [2, 1, 2, 1, 2, 2, 11]
def baseStart_1629624 : Nat := 118140960795 + 1629624 * 2 ^ 59
def prefixEnd_1629624 : Nat := 4983230072969 + 3 ^ 40 * 1629624 * 2
def baseEnd_1629624 : Nat := 41322488795191966533605

theorem tailTrace_1629624 : CollatzResearch.WordTrace tailWord_1629624 prefixEnd_1629624 41322488795191966533605 := by
  unfold tailWord_1629624
  simp only [CollatzResearch.WordTrace]
  refine ⟨29718635124079020233155963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39624846832105360310874617 29718635124079020233155963)
  ·
    refine ⟨44577952686118530349733945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29718635124079020233155963 44577952686118530349733945)
    ·
      refine ⟨33433464514588897762300459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44577952686118530349733945 33433464514588897762300459)
      ·
        refine ⟨50150196771883346643450689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33433464514588897762300459 50150196771883346643450689)
        ·
          refine ⟨37612647578912509982588017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50150196771883346643450689 37612647578912509982588017)
          ·
            refine ⟨28209485684184382486941013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37612647578912509982588017 28209485684184382486941013)
            ·
              refine ⟨41322488795191966533605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28209485684184382486941013 41322488795191966533605)
              ·
                rfl

theorem cell21_1629624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 11].length) (baseStart_1629624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629624 prefixEnd_1629624 := by exact prefixLift 1629624
  have htrace : WordTrace (prefixWord ++ tailWord_1629624) baseStart_1629624 baseEnd_1629624 := by
    simpa [prefixWord, tailWord_1629624, baseEnd_1629624] using wordTrace_append hprefix tailTrace_1629624
  have hstable : (prefixWord ++ tailWord_1629624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629624).length < 2 ^ (prefixWord ++ tailWord_1629624).sum := by decide
  have hdescent : baseEnd_1629624 < baseStart_1629624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629644 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 4]
def baseStart_1629644 : Nat := 118140960795 + 1629644 * 2 ^ 59
def prefixEnd_1629644 : Nat := 4983230072969 + 3 ^ 40 * 1629644 * 2
def baseEnd_1629644 : Nat := 371906963429212108469071

theorem tailTrace_1629644 : CollatzResearch.WordTrace tailWord_1629644 prefixEnd_1629644 371906963429212108469071 := by
  unfold tailWord_1629644
  simp only [CollatzResearch.WordTrace]
  refine ⟨29718999854042791941019993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39625333138723722588026657 29718999854042791941019993)
  ·
    refine ⟨22289249890532093955764995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29718999854042791941019993 22289249890532093955764995)
    ·
      refine ⟨33433874835798140933647493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22289249890532093955764995 33433874835798140933647493)
      ·
        refine ⟨6268851531712151425058905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33433874835798140933647493 6268851531712151425058905)
        ·
          refine ⟨4701638648784113568794179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6268851531712151425058905 4701638648784113568794179)
          ·
            refine ⟨7052457973176170353191269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701638648784113568794179 7052457973176170353191269)
            ·
              refine ⟨1322335869970531941223363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7052457973176170353191269 1322335869970531941223363)
              ·
                refine ⟨1983503804955797911835045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322335869970531941223363 1983503804955797911835045)
                ·
                  refine ⟨371906963429212108469071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983503804955797911835045 371906963429212108469071)
                  ·
                    rfl

theorem cell21_1629644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_1629644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629644 prefixEnd_1629644 := by exact prefixLift 1629644
  have htrace : WordTrace (prefixWord ++ tailWord_1629644) baseStart_1629644 baseEnd_1629644 := by
    simpa [prefixWord, tailWord_1629644, baseEnd_1629644] using wordTrace_append hprefix tailTrace_1629644
  have hstable : (prefixWord ++ tailWord_1629644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629644).length < 2 ^ (prefixWord ++ tailWord_1629644).sum := by decide
  have hdescent : baseEnd_1629644 < baseStart_1629644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629655 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 5]
def baseStart_1629655 : Nat := 118140960795 + 1629655 * 2 ^ 59
def prefixEnd_1629655 : Nat := 4983230072969 + 3 ^ 40 * 1629655 * 2
def baseEnd_1629655 : Nat := 371909473779078533785715

theorem tailTrace_1629655 : CollatzResearch.WordTrace tailWord_1629655 prefixEnd_1629655 371909473779078533785715 := by
  unfold tailWord_1629655
  simp only [CollatzResearch.WordTrace]
  refine ⟨59438400911045732760690419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39625600607363821840460279 59438400911045732760690419)
  ·
    refine ⟨89157601366568599141035629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59438400911045732760690419 89157601366568599141035629)
    ·
      refine ⟨33434100512463224677888361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89157601366568599141035629 33434100512463224677888361)
      ·
        refine ⟨25075575384347418508416271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33434100512463224677888361 25075575384347418508416271)
        ·
          refine ⟨37613363076521127762624407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25075575384347418508416271 37613363076521127762624407)
          ·
            refine ⟨56420044614781691643936611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37613363076521127762624407 56420044614781691643936611)
            ·
              refine ⟨84630066922172537465904917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56420044614781691643936611 84630066922172537465904917)
              ·
                refine ⟨3967034386976837693714293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84630066922172537465904917 3967034386976837693714293)
                ·
                  refine ⟨371909473779078533785715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3967034386976837693714293 371909473779078533785715)
                  ·
                    rfl

theorem cell21_1629655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_1629655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629655 prefixEnd_1629655 := by exact prefixLift 1629655
  have htrace : WordTrace (prefixWord ++ tailWord_1629655) baseStart_1629655 baseEnd_1629655 := by
    simpa [prefixWord, tailWord_1629655, baseEnd_1629655] using wordTrace_append hprefix tailTrace_1629655
  have hstable : (prefixWord ++ tailWord_1629655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629655).length < 2 ^ (prefixWord ++ tailWord_1629655).sum := by decide
  have hdescent : baseEnd_1629655 < baseStart_1629655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629703 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 4]
def baseStart_1629703 : Nat := 118140960795 + 1629703 * 2 ^ 59
def prefixEnd_1629703 : Nat := 4983230072969 + 3 ^ 40 * 1629703 * 2
def baseEnd_1629703 : Nat := 371920428033041116985617

theorem tailTrace_1629703 : CollatzResearch.WordTrace tailWord_1629703 prefixEnd_1629703 371920428033041116985617 := by
  unfold tailWord_1629703
  simp only [CollatzResearch.WordTrace]
  refine ⟨59440151614871836958437763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39626767743247891305625175 59440151614871836958437763)
  ·
    refine ⟨89160227422307755437656645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59440151614871836958437763 89160227422307755437656645)
    ·
      refine ⟨16717542641682704144560621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89160227422307755437656645 16717542641682704144560621)
      ·
        refine ⟨6269078490631014054210233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16717542641682704144560621 6269078490631014054210233)
        ·
          refine ⟨4701808867973260540657675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6269078490631014054210233 4701808867973260540657675)
          ·
            refine ⟨7052713301959890810986513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701808867973260540657675 7052713301959890810986513)
            ·
              refine ⟨5289534976469918108239885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7052713301959890810986513 5289534976469918108239885)
              ·
                refine ⟨1983575616176219290589957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5289534976469918108239885 1983575616176219290589957)
                ·
                  refine ⟨371920428033041116985617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983575616176219290589957 371920428033041116985617)
                  ·
                    rfl

theorem cell21_1629703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 4].length) (baseStart_1629703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629703 prefixEnd_1629703 := by exact prefixLift 1629703
  have htrace : WordTrace (prefixWord ++ tailWord_1629703) baseStart_1629703 baseEnd_1629703 := by
    simpa [prefixWord, tailWord_1629703, baseEnd_1629703] using wordTrace_append hprefix tailTrace_1629703
  have hstable : (prefixWord ++ tailWord_1629703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629703).length < 2 ^ (prefixWord ++ tailWord_1629703).sum := by decide
  have hdescent : baseEnd_1629703 < baseStart_1629703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629776 : List Nat := [2, 1, 1, 1, 1, 3, 5, 7]
def baseStart_1629776 : Nat := 118140960795 + 1629776 * 2 ^ 59
def prefixEnd_1629776 : Nat := 4983230072969 + 3 ^ 40 * 1629776 * 2
def baseEnd_1629776 : Nat := 123979029209203070756267

theorem tailTrace_1629776 : CollatzResearch.WordTrace tailWord_1629776 prefixEnd_1629776 123979029209203070756267 := by
  unfold tailWord_1629776
  simp only [CollatzResearch.WordTrace]
  refine ⟨29721407071803685212922591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39628542762404913617230121 29721407071803685212922591)
  ·
    refine ⟨44582110607705527819383887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29721407071803685212922591 44582110607705527819383887)
    ·
      refine ⟨66873165911558291729075831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44582110607705527819383887 66873165911558291729075831)
      ·
        refine ⟨100309748867337437593613747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66873165911558291729075831 100309748867337437593613747)
        ·
          refine ⟨150464623301006156390420621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100309748867337437593613747 150464623301006156390420621)
          ·
            refine ⟨56424233737877308646407733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150464623301006156390420621 56424233737877308646407733)
            ·
              refine ⟨5289771912925997685600725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56424233737877308646407733 5289771912925997685600725)
              ·
                refine ⟨123979029209203070756267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5289771912925997685600725 123979029209203070756267)
                ·
                  rfl

theorem cell21_1629776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_1629776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629776 prefixEnd_1629776 := by exact prefixLift 1629776
  have htrace : WordTrace (prefixWord ++ tailWord_1629776) baseStart_1629776 baseEnd_1629776 := by
    simpa [prefixWord, tailWord_1629776, baseEnd_1629776] using wordTrace_append hprefix tailTrace_1629776
  have hstable : (prefixWord ++ tailWord_1629776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629776).length < 2 ^ (prefixWord ++ tailWord_1629776).sum := by decide
  have hdescent : baseEnd_1629776 < baseStart_1629776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629813 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 4]
def baseStart_1629813 : Nat := 118140960795 + 1629813 * 2 ^ 59
def prefixEnd_1629813 : Nat := 4983230072969 + 3 ^ 40 * 1629813 * 2
def baseEnd_1629813 : Nat := 371945531531705370152059

theorem tailTrace_1629813 : CollatzResearch.WordTrace tailWord_1629813 prefixEnd_1629813 371945531531705370152059 := by
  unfold tailWord_1629813
  simp only [CollatzResearch.WordTrace]
  refine ⟨59444163644473325744942093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39629442429648883829961395 59444163644473325744942093)
  ·
    refine ⟨22291561366677497154353285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59444163644473325744942093 22291561366677497154353285)
    ·
      refine ⟨4179667756252030716441241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22291561366677497154353285 4179667756252030716441241)
      ·
        refine ⟨3134750817189023037330931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4179667756252030716441241 3134750817189023037330931)
        ·
          refine ⟨4702126225783534555996397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3134750817189023037330931 4702126225783534555996397)
          ·
            refine ⟨1763297334668825458498649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4702126225783534555996397 1763297334668825458498649)
            ·
              refine ⟨1322473001001619093873987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1763297334668825458498649 1322473001001619093873987)
              ·
                refine ⟨1983709501502428640810981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322473001001619093873987 1983709501502428640810981)
                ·
                  refine ⟨371945531531705370152059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1983709501502428640810981 371945531531705370152059)
                  ·
                    rfl

theorem cell21_1629813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 4].length) (baseStart_1629813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629813 prefixEnd_1629813 := by exact prefixLift 1629813
  have htrace : WordTrace (prefixWord ++ tailWord_1629813) baseStart_1629813 baseEnd_1629813 := by
    simpa [prefixWord, tailWord_1629813, baseEnd_1629813] using wordTrace_append hprefix tailTrace_1629813
  have hstable : (prefixWord ++ tailWord_1629813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629813).length < 2 ^ (prefixWord ++ tailWord_1629813).sum := by decide
  have hdescent : baseEnd_1629813 < baseStart_1629813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629852 : List Nat := [2, 2, 3, 2, 12]
def baseStart_1629852 : Nat := 118140960795 + 1629852 * 2 ^ 59
def prefixEnd_1629852 : Nat := 4983230072969 + 3 ^ 40 * 1629852 * 2
def baseEnd_1629852 : Nat := 4592030023000616901259

theorem tailTrace_1629852 : CollatzResearch.WordTrace tailWord_1629852 prefixEnd_1629852 4592030023000616901259 := by
  unfold tailWord_1629852
  simp only [CollatzResearch.WordTrace]
  refine ⟨29722793045666017702805905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39630390727554690270407873 29722793045666017702805905)
  ·
    refine ⟨22292094784249513277104429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29722793045666017702805905 22292094784249513277104429)
    ·
      refine ⟨8359535544093567478914161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22292094784249513277104429 8359535544093567478914161)
      ·
        refine ⟨6269651658070175609185621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8359535544093567478914161 6269651658070175609185621)
        ·
          refine ⟨4592030023000616901259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6269651658070175609185621 4592030023000616901259)
          ·
            rfl

theorem cell21_1629852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 12].length) (baseStart_1629852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629852 prefixEnd_1629852 := by exact prefixLift 1629852
  have htrace : WordTrace (prefixWord ++ tailWord_1629852) baseStart_1629852 baseEnd_1629852 := by
    simpa [prefixWord, tailWord_1629852, baseEnd_1629852] using wordTrace_append hprefix tailTrace_1629852
  have hstable : (prefixWord ++ tailWord_1629852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629852).length < 2 ^ (prefixWord ++ tailWord_1629852).sum := by decide
  have hdescent : baseEnd_1629852 < baseStart_1629852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629886 : List Nat := [4, 2, 1, 1, 2, 3, 3, 5]
def baseStart_1629886 : Nat := 118140960795 + 1629886 * 2 ^ 59
def prefixEnd_1629886 : Nat := 4983230072969 + 3 ^ 40 * 1629886 * 2
def baseEnd_1629886 : Nat := 123987397042091155145081

theorem tailTrace_1629886 : CollatzResearch.WordTrace tailWord_1629886 prefixEnd_1629886 123987397042091155145081 := by
  unfold tailWord_1629886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7430853271651107401543689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39631217448805906141566341 7430853271651107401543689)
  ·
    refine ⟨5573139953738330551157767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7430853271651107401543689 5573139953738330551157767)
    ·
      refine ⟨8359709930607495826736651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5573139953738330551157767 8359709930607495826736651)
      ·
        refine ⟨12539564895911243740104977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8359709930607495826736651 12539564895911243740104977)
        ·
          refine ⟨9404673671933432805078733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12539564895911243740104977 9404673671933432805078733)
          ·
            refine ⟨3526752626975037301904525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9404673671933432805078733 3526752626975037301904525)
            ·
              refine ⟨1322532235115638988214197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3526752626975037301904525 1322532235115638988214197)
              ·
                refine ⟨123987397042091155145081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1322532235115638988214197 123987397042091155145081)
                ·
                  rfl

theorem cell21_1629886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_1629886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629886 prefixEnd_1629886 := by exact prefixLift 1629886
  have htrace : WordTrace (prefixWord ++ tailWord_1629886) baseStart_1629886 baseEnd_1629886 := by
    simpa [prefixWord, tailWord_1629886, baseEnd_1629886] using wordTrace_append hprefix tailTrace_1629886
  have hstable : (prefixWord ++ tailWord_1629886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629886).length < 2 ^ (prefixWord ++ tailWord_1629886).sum := by decide
  have hdescent : baseEnd_1629886 < baseStart_1629886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629914 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 6]
def baseStart_1629914 : Nat := 118140960795 + 1629914 * 2 ^ 59
def prefixEnd_1629914 : Nat := 4983230072969 + 3 ^ 40 * 1629914 * 2
def baseEnd_1629914 : Nat := 371968581107751638968519

theorem tailTrace_1629914 : CollatzResearch.WordTrace tailWord_1629914 prefixEnd_1629914 371968581107751638968519 := by
  unfold tailWord_1629914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14861961854276854998592199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39631898278071613329579197 14861961854276854998592199)
  ·
    refine ⟨22292942781415282497888299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14861961854276854998592199 22292942781415282497888299)
    ·
      refine ⟨33439414172122923746832449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22292942781415282497888299 33439414172122923746832449)
      ·
        refine ⟨25079560629092192810124337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33439414172122923746832449 25079560629092192810124337)
        ·
          refine ⟨18809670471819144607593253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25079560629092192810124337 18809670471819144607593253)
          ·
            refine ⟨3526813213466089613923735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18809670471819144607593253 3526813213466089613923735)
            ·
              refine ⟨5290219820199134420885603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3526813213466089613923735 5290219820199134420885603)
              ·
                refine ⟨7935329730298701631328405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290219820199134420885603 7935329730298701631328405)
                ·
                  refine ⟨371968581107751638968519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7935329730298701631328405 371968581107751638968519)
                  ·
                    rfl

theorem cell21_1629914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_1629914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629914 prefixEnd_1629914 := by exact prefixLift 1629914
  have htrace : WordTrace (prefixWord ++ tailWord_1629914) baseStart_1629914 baseEnd_1629914 := by
    simpa [prefixWord, tailWord_1629914, baseEnd_1629914] using wordTrace_append hprefix tailTrace_1629914
  have hstable : (prefixWord ++ tailWord_1629914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629914).length < 2 ^ (prefixWord ++ tailWord_1629914).sum := by decide
  have hdescent : baseEnd_1629914 < baseStart_1629914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1629976 : List Nat := [2, 1, 2, 3, 1, 1, 2, 6, 3]
def baseStart_1629976 : Nat := 118140960795 + 1629976 * 2 ^ 59
def prefixEnd_1629976 : Nat := 4983230072969 + 3 ^ 40 * 1629976 * 2
def baseEnd_1629976 : Nat := 371982730352453308935059

theorem tailTrace_1629976 : CollatzResearch.WordTrace tailWord_1629976 prefixEnd_1629976 371982730352453308935059 := by
  unfold tailWord_1629976
  simp only [CollatzResearch.WordTrace]
  refine ⟨29725054371441402291562891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39633405828588536388750521 29725054371441402291562891)
  ·
    refine ⟨44587581557162103437344337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29725054371441402291562891 44587581557162103437344337)
    ·
      refine ⟨33440686167871577578008253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44587581557162103437344337 33440686167871577578008253)
      ·
        refine ⟨12540257312951841591753095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33440686167871577578008253 12540257312951841591753095)
        ·
          refine ⟨18810385969427762387629643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12540257312951841591753095 18810385969427762387629643)
          ·
            refine ⟨28215578954141643581444465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18810385969427762387629643 28215578954141643581444465)
            ·
              refine ⟨21161684215606232686083349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28215578954141643581444465 21161684215606232686083349)
              ·
                refine ⟨991953947606542157160157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21161684215606232686083349 991953947606542157160157)
                ·
                  refine ⟨371982730352453308935059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 991953947606542157160157 371982730352453308935059)
                  ·
                    rfl

theorem cell21_1629976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 3].length) (baseStart_1629976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1629976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1629976 prefixEnd_1629976 := by exact prefixLift 1629976
  have htrace : WordTrace (prefixWord ++ tailWord_1629976) baseStart_1629976 baseEnd_1629976 := by
    simpa [prefixWord, tailWord_1629976, baseEnd_1629976] using wordTrace_append hprefix tailTrace_1629976
  have hstable : (prefixWord ++ tailWord_1629976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1629976).length < 2 ^ (prefixWord ++ tailWord_1629976).sum := by decide
  have hdescent : baseEnd_1629976 < baseStart_1629976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1629976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630052 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 5]
def baseStart_1630052 : Nat := 118140960795 + 1630052 * 2 ^ 59
def prefixEnd_1630052 : Nat := 4983230072969 + 3 ^ 40 * 1630052 * 2
def baseEnd_1630052 : Nat := 372000074587894065668237

theorem tailTrace_1630052 : CollatzResearch.WordTrace tailWord_1630052 prefixEnd_1630052 372000074587894065668237 := by
  unfold tailWord_1630052
  simp only [CollatzResearch.WordTrace]
  refine ⟨29726440345303734781446205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39635253793738313041928273 29726440345303734781446205)
  ·
    refine ⟨11147415129488900543042327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29726440345303734781446205 11147415129488900543042327)
    ·
      refine ⟨16721122694233350814563491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11147415129488900543042327 16721122694233350814563491)
      ·
        refine ⟨25081684041350026221845237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16721122694233350814563491 25081684041350026221845237)
        ·
          refine ⟨2351407878876564958297991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25081684041350026221845237 2351407878876564958297991)
          ·
            refine ⟨3527111818314847437446987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351407878876564958297991 3527111818314847437446987)
            ·
              refine ⟨5290667727472271156170481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527111818314847437446987 5290667727472271156170481)
              ·
                refine ⟨3968000795604203367127861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5290667727472271156170481 3968000795604203367127861)
                ·
                  refine ⟨372000074587894065668237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3968000795604203367127861 372000074587894065668237)
                  ·
                    rfl

theorem cell21_1630052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_1630052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630052 prefixEnd_1630052 := by exact prefixLift 1630052
  have htrace : WordTrace (prefixWord ++ tailWord_1630052) baseStart_1630052 baseEnd_1630052 := by
    simpa [prefixWord, tailWord_1630052, baseEnd_1630052] using wordTrace_append hprefix tailTrace_1630052
  have hstable : (prefixWord ++ tailWord_1630052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630052).length < 2 ^ (prefixWord ++ tailWord_1630052).sum := by decide
  have hdescent : baseEnd_1630052 < baseStart_1630052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630069 : List Nat := [1, 3, 4, 1, 1, 1, 4, 3, 3]
def baseStart_1630069 : Nat := 118140960795 + 1630069 * 2 ^ 59
def prefixEnd_1630069 : Nat := 4983230072969 + 3 ^ 40 * 1630069 * 2
def baseEnd_1630069 : Nat := 372003954219505813884869

theorem tailTrace_1630069 : CollatzResearch.WordTrace tailWord_1630069 prefixEnd_1630069 372003954219505813884869 := by
  unfold tailWord_1630069
  simp only [CollatzResearch.WordTrace]
  refine ⟨59453500731545881466261261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39635667154363920977507507 59453500731545881466261261)
  ·
    refine ⟨22295062774329705549847973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59453500731545881466261261 22295062774329705549847973)
    ·
      refine ⟨4180324270186819790596495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22295062774329705549847973 4180324270186819790596495)
      ·
        refine ⟨6270486405280229685894743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4180324270186819790596495 6270486405280229685894743)
        ·
          refine ⟨9405729607920344528842115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6270486405280229685894743 9405729607920344528842115)
          ·
            refine ⟨14108594411880516793263173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9405729607920344528842115 14108594411880516793263173)
            ·
              refine ⟨2645361452227596898736845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14108594411880516793263173 2645361452227596898736845)
              ·
                refine ⟨992010544585348837026317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2645361452227596898736845 992010544585348837026317)
                ·
                  refine ⟨372003954219505813884869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992010544585348837026317 372003954219505813884869)
                  ·
                    rfl

theorem cell21_1630069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_1630069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630069 prefixEnd_1630069 := by exact prefixLift 1630069
  have htrace : WordTrace (prefixWord ++ tailWord_1630069) baseStart_1630069 baseEnd_1630069 := by
    simpa [prefixWord, tailWord_1630069, baseEnd_1630069] using wordTrace_append hprefix tailTrace_1630069
  have hstable : (prefixWord ++ tailWord_1630069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630069).length < 2 ^ (prefixWord ++ tailWord_1630069).sum := by decide
  have hdescent : baseEnd_1630069 < baseStart_1630069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630083 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 4]
def baseStart_1630083 : Nat := 118140960795 + 1630083 * 2 ^ 59
def prefixEnd_1630083 : Nat := 4983230072969 + 3 ^ 40 * 1630083 * 2
def baseEnd_1630083 : Nat := 372007149210244900651507

theorem tailTrace_1630083 : CollatzResearch.WordTrace tailWord_1630083 prefixEnd_1630083 372007149210244900651507 := by
  unfold tailWord_1630083
  simp only [CollatzResearch.WordTrace]
  refine ⟨59454011353495161857270903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39636007568996774571513935 59454011353495161857270903)
  ·
    refine ⟨89181017030242742785906355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59454011353495161857270903 89181017030242742785906355)
    ·
      refine ⟨133771525545364114178859533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89181017030242742785906355 133771525545364114178859533)
      ·
        refine ⟨50164322079511542817072325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133771525545364114178859533 50164322079511542817072325)
        ·
          refine ⟨9405810389908414278201061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50164322079511542817072325 9405810389908414278201061)
          ·
            refine ⟨1763589448107827677162699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9405810389908414278201061 1763589448107827677162699)
            ·
              refine ⟨2645384172161741515744049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763589448107827677162699 2645384172161741515744049)
              ·
                refine ⟨1984038129121306136808037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2645384172161741515744049 1984038129121306136808037)
                ·
                  refine ⟨372007149210244900651507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1984038129121306136808037 372007149210244900651507)
                  ·
                    rfl

theorem cell21_1630083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 4].length) (baseStart_1630083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630083 prefixEnd_1630083 := by exact prefixLift 1630083
  have htrace : WordTrace (prefixWord ++ tailWord_1630083) baseStart_1630083 baseEnd_1630083 := by
    simpa [prefixWord, tailWord_1630083, baseEnd_1630083] using wordTrace_append hprefix tailTrace_1630083
  have hstable : (prefixWord ++ tailWord_1630083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630083).length < 2 ^ (prefixWord ++ tailWord_1630083).sum := by decide
  have hdescent : baseEnd_1630083 < baseStart_1630083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630100 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 4]
def baseStart_1630100 : Nat := 118140960795 + 1630100 * 2 ^ 59
def prefixEnd_1630100 : Nat := 4983230072969 + 3 ^ 40 * 1630100 * 2
def baseEnd_1630100 : Nat := 372011028841856648868139

theorem tailTrace_1630100 : CollatzResearch.WordTrace tailWord_1630100 prefixEnd_1630100 372011028841856648868139 := by
  unfold tailWord_1630100
  simp only [CollatzResearch.WordTrace]
  refine ⟨29727315697216786880319877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39636420929622382507093169 29727315697216786880319877)
  ·
    refine ⟨5573871693228147540059977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29727315697216786880319877 5573871693228147540059977)
    ·
      refine ⟨4180403769921110655044983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5573871693228147540059977 4180403769921110655044983)
      ·
        refine ⟨6270605654881665982567475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4180403769921110655044983 6270605654881665982567475)
        ·
          refine ⟨9405908482322498973851213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6270605654881665982567475 9405908482322498973851213)
          ·
            refine ⟨3527215680870937115194205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9405908482322498973851213 3527215680870937115194205)
            ·
              refine ⟨1322705880326601418197827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3527215680870937115194205 1322705880326601418197827)
              ·
                refine ⟨1984058820489902127296741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322705880326601418197827 1984058820489902127296741)
                ·
                  refine ⟨372011028841856648868139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1984058820489902127296741 372011028841856648868139)
                  ·
                    rfl

theorem cell21_1630100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_1630100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630100 prefixEnd_1630100 := by exact prefixLift 1630100
  have htrace : WordTrace (prefixWord ++ tailWord_1630100) baseStart_1630100 baseEnd_1630100 := by
    simpa [prefixWord, tailWord_1630100, baseEnd_1630100] using wordTrace_append hprefix tailTrace_1630100
  have hstable : (prefixWord ++ tailWord_1630100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630100).length < 2 ^ (prefixWord ++ tailWord_1630100).sum := by decide
  have hdescent : baseEnd_1630100 < baseStart_1630100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630120 : List Nat := [2, 1, 6, 2, 2, 1, 1, 3, 3]
def baseStart_1630120 : Nat := 118140960795 + 1630120 * 2 ^ 59
def prefixEnd_1630120 : Nat := 4983230072969 + 3 ^ 40 * 1630120 * 2
def baseEnd_1630120 : Nat := 372015593114341058534765

theorem tailTrace_1630120 : CollatzResearch.WordTrace tailWord_1630120 prefixEnd_1630120 372015593114341058534765 := by
  unfold tailWord_1630120
  simp only [CollatzResearch.WordTrace]
  refine ⟨29727680427180558588183907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39636907236240744784245209 29727680427180558588183907)
  ·
    refine ⟨44591520640770837882275861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29727680427180558588183907 44591520640770837882275861)
    ·
      refine ⟨2090227530036133025731681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44591520640770837882275861 2090227530036133025731681)
      ·
        refine ⟨1567670647527099769298761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2090227530036133025731681 1567670647527099769298761)
        ·
          refine ⟨1175752985645324826974071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1567670647527099769298761 1175752985645324826974071)
          ·
            refine ⟨1763629478467987240461107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175752985645324826974071 1763629478467987240461107)
            ·
              refine ⟨2645444217701980860691661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1763629478467987240461107 2645444217701980860691661)
              ·
                refine ⟨992041581638242822759373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2645444217701980860691661 992041581638242822759373)
                ·
                  refine ⟨372015593114341058534765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992041581638242822759373 372015593114341058534765)
                  ·
                    rfl

theorem cell21_1630120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 3].length) (baseStart_1630120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630120 prefixEnd_1630120 := by exact prefixLift 1630120
  have htrace : WordTrace (prefixWord ++ tailWord_1630120) baseStart_1630120 baseEnd_1630120 := by
    simpa [prefixWord, tailWord_1630120, baseEnd_1630120] using wordTrace_append hprefix tailTrace_1630120
  have hstable : (prefixWord ++ tailWord_1630120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630120).length < 2 ^ (prefixWord ++ tailWord_1630120).sum := by decide
  have hdescent : baseEnd_1630120 < baseStart_1630120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630142 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1630142 : Nat := 118140960795 + 1630142 * 2 ^ 59
def prefixEnd_1630142 : Nat := 4983230072969 + 3 ^ 40 * 1630142 * 2
def baseEnd_1630142 : Nat := 372020613814073909168053

theorem tailTrace_1630142 : CollatzResearch.WordTrace tailWord_1630142 prefixEnd_1630142 372020613814073909168053 := by
  unfold tailWord_1630142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7432020407535176866708585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39637442173520943289112453 7432020407535176866708585)
  ·
    refine ⟨5574015305651382650031439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7432020407535176866708585 5574015305651382650031439)
    ·
      refine ⟨8361022958477073975047159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5574015305651382650031439 8361022958477073975047159)
      ·
        refine ⟨12541534437715610962570739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8361022958477073975047159 12541534437715610962570739)
        ·
          refine ⟨18812301656573416443856109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12541534437715610962570739 18812301656573416443856109)
          ·
            refine ⟨7054613121215031166446041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18812301656573416443856109 7054613121215031166446041)
            ·
              refine ⟨5290959840911273374834531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7054613121215031166446041 5290959840911273374834531)
              ·
                refine ⟨7936439761366910062251797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290959840911273374834531 7936439761366910062251797)
                ·
                  refine ⟨372020613814073909168053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7936439761366910062251797 372020613814073909168053)
                  ·
                    rfl

theorem cell21_1630142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1630142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630142 prefixEnd_1630142 := by exact prefixLift 1630142
  have htrace : WordTrace (prefixWord ++ tailWord_1630142) baseStart_1630142 baseEnd_1630142 := by
    simpa [prefixWord, tailWord_1630142, baseEnd_1630142] using wordTrace_append hprefix tailTrace_1630142
  have hstable : (prefixWord ++ tailWord_1630142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630142).length < 2 ^ (prefixWord ++ tailWord_1630142).sum := by decide
  have hdescent : baseEnd_1630142 < baseStart_1630142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630156 : List Nat := [2, 2, 1, 4, 1, 2, 1, 8]
def baseStart_1630156 : Nat := 118140960795 + 1630156 * 2 ^ 59
def prefixEnd_1630156 : Nat := 4983230072969 + 3 ^ 40 * 1630156 * 2
def baseEnd_1630156 : Nat := 124007936268270998644897

theorem tailTrace_1630156 : CollatzResearch.WordTrace tailWord_1630156 prefixEnd_1630156 124007936268270998644897 := by
  unfold tailWord_1630156
  simp only [CollatzResearch.WordTrace]
  refine ⟨29728336941115347662339161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39637782588153796883118881 29728336941115347662339161)
  ·
    refine ⟨22296252705836510746754371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29728336941115347662339161 22296252705836510746754371)
    ·
      refine ⟨33444379058754766120131557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22296252705836510746754371 33444379058754766120131557)
      ·
        refine ⟨6270821073516518647524667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33444379058754766120131557 6270821073516518647524667)
        ·
          refine ⟨9406231610274777971287001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6270821073516518647524667 9406231610274777971287001)
          ·
            refine ⟨7054673707706083478465251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9406231610274777971287001 7054673707706083478465251)
            ·
              refine ⟨10582010561559125217697877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7054673707706083478465251 10582010561559125217697877)
              ·
                refine ⟨124007936268270998644897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10582010561559125217697877 124007936268270998644897)
                ·
                  rfl

theorem cell21_1630156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_1630156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630156 prefixEnd_1630156 := by exact prefixLift 1630156
  have htrace : WordTrace (prefixWord ++ tailWord_1630156) baseStart_1630156 baseEnd_1630156 := by
    simpa [prefixWord, tailWord_1630156, baseEnd_1630156] using wordTrace_append hprefix tailTrace_1630156
  have hstable : (prefixWord ++ tailWord_1630156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630156).length < 2 ^ (prefixWord ++ tailWord_1630156).sum := by decide
  have hdescent : baseEnd_1630156 < baseStart_1630156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630204 : List Nat := [2, 2, 2, 1, 2, 2, 3, 4, 3]
def baseStart_1630204 : Nat := 118140960795 + 1630204 * 2 ^ 59
def prefixEnd_1630204 : Nat := 4983230072969 + 3 ^ 40 * 1630204 * 2
def baseEnd_1630204 : Nat := 372034763058775579134593

theorem tailTrace_1630204 : CollatzResearch.WordTrace tailWord_1630204 prefixEnd_1630204 372034763058775579134593 := by
  unfold tailWord_1630204
  simp only [CollatzResearch.WordTrace]
  refine ⟨29729212293028399761212833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39638949724037866348283777 29729212293028399761212833)
  ·
    refine ⟨22296909219771299820909625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29729212293028399761212833 22296909219771299820909625)
    ·
      refine ⟨16722681914828474865682219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22296909219771299820909625 16722681914828474865682219)
      ·
        refine ⟨25084022872242712298523329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16722681914828474865682219 25084022872242712298523329)
        ·
          refine ⟨18813017154182034223892497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25084022872242712298523329 18813017154182034223892497)
          ·
            refine ⟨14109762865636525667919373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18813017154182034223892497 14109762865636525667919373)
            ·
              refine ⟨5291161074613697125469765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14109762865636525667919373 5291161074613697125469765)
              ·
                refine ⟨992092701490068211025581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5291161074613697125469765 992092701490068211025581)
                ·
                  refine ⟨372034763058775579134593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992092701490068211025581 372034763058775579134593)
                  ·
                    rfl

theorem cell21_1630204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_1630204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630204 prefixEnd_1630204 := by exact prefixLift 1630204
  have htrace : WordTrace (prefixWord ++ tailWord_1630204) baseStart_1630204 baseEnd_1630204 := by
    simpa [prefixWord, tailWord_1630204, baseEnd_1630204] using wordTrace_append hprefix tailTrace_1630204
  have hstable : (prefixWord ++ tailWord_1630204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630204).length < 2 ^ (prefixWord ++ tailWord_1630204).sum := by decide
  have hdescent : baseEnd_1630204 < baseStart_1630204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630314 : List Nat := [3, 1, 3, 2, 3, 1, 3, 2, 3]
def baseStart_1630314 : Nat := 118140960795 + 1630314 * 2 ^ 59
def prefixEnd_1630314 : Nat := 4983230072969 + 3 ^ 40 * 1630314 * 2
def baseEnd_1630314 : Nat := 372059866557439832301035

theorem tailTrace_1630314 : CollatzResearch.WordTrace tailWord_1630314 prefixEnd_1630314 372059866557439832301035 := by
  unfold tailWord_1630314
  simp only [CollatzResearch.WordTrace]
  refine ⟨14865609153914572077232499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39641624410438858872619997 14865609153914572077232499)
  ·
    refine ⟨22298413730871858115848749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14865609153914572077232499 22298413730871858115848749)
    ·
      refine ⟨8361905149076946793443281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22298413730871858115848749 8361905149076946793443281)
      ·
        refine ⟨6271428861807710095082461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8361905149076946793443281 6271428861807710095082461)
        ·
          refine ⟨2351785823177891285655923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6271428861807710095082461 2351785823177891285655923)
          ·
            refine ⟨3527678734766836928483885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2351785823177891285655923 3527678734766836928483885)
            ·
              refine ⟨1322879525537563848181457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3527678734766836928483885 1322879525537563848181457)
              ·
                refine ⟨992159644153172886136093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322879525537563848181457 992159644153172886136093)
                ·
                  refine ⟨372059866557439832301035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992159644153172886136093 372059866557439832301035)
                  ·
                    rfl

theorem cell21_1630314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_1630314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630314 prefixEnd_1630314 := by exact prefixLift 1630314
  have htrace : WordTrace (prefixWord ++ tailWord_1630314) baseStart_1630314 baseEnd_1630314 := by
    simpa [prefixWord, tailWord_1630314, baseEnd_1630314] using wordTrace_append hprefix tailTrace_1630314
  have hstable : (prefixWord ++ tailWord_1630314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630314).length < 2 ^ (prefixWord ++ tailWord_1630314).sum := by decide
  have hdescent : baseEnd_1630314 < baseStart_1630314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630443 : List Nat := [1, 1, 1, 1, 2, 5, 2, 8]
def baseStart_1630443 : Nat := 118140960795 + 1630443 * 2 ^ 59
def prefixEnd_1630443 : Nat := 4983230072969 + 3 ^ 40 * 1630443 * 2
def baseEnd_1630443 : Nat := 124029768704988091550257

theorem tailTrace_1630443 : CollatzResearch.WordTrace tailWord_1630443 prefixEnd_1630443 124029768704988091550257 := by
  unfold tailWord_1630443
  simp only [CollatzResearch.WordTrace]
  refine ⟨59467141632190943340375983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39644761088127295560250655 59467141632190943340375983)
  ·
    refine ⟨89200712448286415010563975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59467141632190943340375983 89200712448286415010563975)
    ·
      refine ⟨133801068672429622515845963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89200712448286415010563975 133801068672429622515845963)
      ·
        refine ⟨200701603008644433773768945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133801068672429622515845963 200701603008644433773768945)
        ·
          refine ⟨150526202256483325330326709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200701603008644433773768945 150526202256483325330326709)
          ·
            refine ⟨14111831461545311749718129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150526202256483325330326709 14111831461545311749718129)
            ·
              refine ⟨10583873596158983812288597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14111831461545311749718129 10583873596158983812288597)
              ·
                refine ⟨124029768704988091550257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10583873596158983812288597 124029768704988091550257)
                ·
                  rfl

theorem cell21_1630443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 8].length) (baseStart_1630443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630443 prefixEnd_1630443 := by exact prefixLift 1630443
  have htrace : WordTrace (prefixWord ++ tailWord_1630443) baseStart_1630443 baseEnd_1630443 := by
    simpa [prefixWord, tailWord_1630443, baseEnd_1630443] using wordTrace_append hprefix tailTrace_1630443
  have hstable : (prefixWord ++ tailWord_1630443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630443).length < 2 ^ (prefixWord ++ tailWord_1630443).sum := by decide
  have hdescent : baseEnd_1630443 < baseStart_1630443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630460 : List Nat := [2, 2, 2, 1, 4, 2, 1, 7]
def baseStart_1630460 : Nat := 118140960795 + 1630460 * 2 ^ 59
def prefixEnd_1630460 : Nat := 4983230072969 + 3 ^ 40 * 1630460 * 2
def baseEnd_1630460 : Nat := 124031061915525340955801

theorem tailTrace_1630460 : CollatzResearch.WordTrace tailWord_1630460 prefixEnd_1630460 124031061915525340955801 := by
  unfold tailWord_1630460
  simp only [CollatzResearch.WordTrace]
  refine ⟨29733880836564677621872417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39645174448752903495829889 29733880836564677621872417)
  ·
    refine ⟨22300410627423508216404313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29733880836564677621872417 22300410627423508216404313)
    ·
      refine ⟨16725307970567631162303235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22300410627423508216404313 16725307970567631162303235)
      ·
        refine ⟨25087961955851446743454853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16725307970567631162303235 25087961955851446743454853)
        ·
          refine ⟨4703992866722146264397785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25087961955851446743454853 4703992866722146264397785)
          ·
            refine ⟨3527994650041609698298339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4703992866722146264397785 3527994650041609698298339)
            ·
              refine ⟨5291991975062414547447509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527994650041609698298339 5291991975062414547447509)
              ·
                refine ⟨124031061915525340955801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5291991975062414547447509 124031061915525340955801)
                ·
                  rfl

theorem cell21_1630460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_1630460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630460 prefixEnd_1630460 := by exact prefixLift 1630460
  have htrace : WordTrace (prefixWord ++ tailWord_1630460) baseStart_1630460 baseEnd_1630460 := by
    simpa [prefixWord, tailWord_1630460, baseEnd_1630460] using wordTrace_append hprefix tailTrace_1630460
  have hstable : (prefixWord ++ tailWord_1630460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630460).length < 2 ^ (prefixWord ++ tailWord_1630460).sum := by decide
  have hdescent : baseEnd_1630460 < baseStart_1630460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630466 : List Nat := [3, 4, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1630466 : Nat := 118140960795 + 1630466 * 2 ^ 59
def prefixEnd_1630466 : Nat := 4983230072969 + 3 ^ 40 * 1630466 * 2
def baseEnd_1630466 : Nat := 372094555028321345767391

theorem tailTrace_1630466 : CollatzResearch.WordTrace tailWord_1630466 prefixEnd_1630466 372094555028321345767391 := by
  unfold tailWord_1630466
  simp only [CollatzResearch.WordTrace]
  refine ⟨14866995127776904567115813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39645320340738412178975501 14866995127776904567115813)
  ·
    refine ⟨2787561586458169606334215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14866995127776904567115813 2787561586458169606334215)
    ·
      refine ⟨4181342379687254409501323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2787561586458169606334215 4181342379687254409501323)
      ·
        refine ⟨6272013569530881614251985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4181342379687254409501323 6272013569530881614251985)
        ·
          refine ⟨4704010177148161210688989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6272013569530881614251985 4704010177148161210688989)
          ·
            refine ⟨1764003816430560454008371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4704010177148161210688989 1764003816430560454008371)
            ·
              refine ⟨2646005724645840681012557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764003816430560454008371 2646005724645840681012557)
              ·
                refine ⟨992252146742190255379709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2646005724645840681012557 992252146742190255379709)
                ·
                  refine ⟨372094555028321345767391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992252146742190255379709 372094555028321345767391)
                  ·
                    rfl

theorem cell21_1630466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1630466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630466 prefixEnd_1630466 := by exact prefixLift 1630466
  have htrace : WordTrace (prefixWord ++ tailWord_1630466) baseStart_1630466 baseEnd_1630466 := by
    simpa [prefixWord, tailWord_1630466, baseEnd_1630466] using wordTrace_append hprefix tailTrace_1630466
  have hstable : (prefixWord ++ tailWord_1630466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630466).length < 2 ^ (prefixWord ++ tailWord_1630466).sum := by decide
  have hdescent : baseEnd_1630466 < baseStart_1630466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630474 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_1630474 : Nat := 118140960795 + 1630474 * 2 ^ 59
def prefixEnd_1630474 : Nat := 4983230072969 + 3 ^ 40 * 1630474 * 2
def baseEnd_1630474 : Nat := 372096380737315109634041

theorem tailTrace_1630474 : CollatzResearch.WordTrace tailWord_1630474 prefixEnd_1630474 372096380737315109634041 := by
  unfold tailWord_1630474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14867068073769658908688619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39645514863385757089836317 14867068073769658908688619)
  ·
    refine ⟨22300602110654488363032929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14867068073769658908688619 22300602110654488363032929)
    ·
      refine ⟨16725451582990866272274697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22300602110654488363032929 16725451582990866272274697)
      ·
        refine ⟨12544088687243149704206023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16725451582990866272274697 12544088687243149704206023)
        ·
          refine ⟨18816133030864724556309035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12544088687243149704206023 18816133030864724556309035)
          ·
            refine ⟨28224199546297086834463553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18816133030864724556309035 28224199546297086834463553)
            ·
              refine ⟨21168149659722815125847665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28224199546297086834463553 21168149659722815125847665)
              ·
                refine ⟨15876112244792111344385749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21168149659722815125847665 15876112244792111344385749)
                ·
                  refine ⟨372096380737315109634041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15876112244792111344385749 372096380737315109634041)
                  ·
                    rfl

theorem cell21_1630474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_1630474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630474 prefixEnd_1630474 := by exact prefixLift 1630474
  have htrace : WordTrace (prefixWord ++ tailWord_1630474) baseStart_1630474 baseEnd_1630474 := by
    simpa [prefixWord, tailWord_1630474, baseEnd_1630474] using wordTrace_append hprefix tailTrace_1630474
  have hstable : (prefixWord ++ tailWord_1630474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630474).length < 2 ^ (prefixWord ++ tailWord_1630474).sum := by decide
  have hdescent : baseEnd_1630474 < baseStart_1630474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630491 : List Nat := [1, 1, 1, 1, 1, 1, 6, 6, 3]
def baseStart_1630491 : Nat := 118140960795 + 1630491 * 2 ^ 59
def prefixEnd_1630491 : Nat := 4983230072969 + 3 ^ 40 * 1630491 * 2
def baseEnd_1630491 : Nat := 372100260368926857850673

theorem tailTrace_1630491 : CollatzResearch.WordTrace tailWord_1630491 prefixEnd_1630491 372100260368926857850673 := by
  unfold tailWord_1630491
  simp only [CollatzResearch.WordTrace]
  refine ⟨59468892336017047538123327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39645928224011365025415551 59468892336017047538123327)
  ·
    refine ⟨89203338504025571307184991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59468892336017047538123327 89203338504025571307184991)
    ·
      refine ⟨133805007756038356960777487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89203338504025571307184991 133805007756038356960777487)
      ·
        refine ⟨200707511634057535441166231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133805007756038356960777487 200707511634057535441166231)
        ·
          refine ⟨301061267451086303161749347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200707511634057535441166231 301061267451086303161749347)
          ·
            refine ⟨451591901176629454742624021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301061267451086303161749347 451591901176629454742624021)
            ·
              refine ⟨21168370367654505691060501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 451591901176629454742624021 21168370367654505691060501)
              ·
                refine ⟨992267360983804954268461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21168370367654505691060501 992267360983804954268461)
                ·
                  refine ⟨372100260368926857850673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992267360983804954268461 372100260368926857850673)
                  ·
                    rfl

theorem cell21_1630491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 3].length) (baseStart_1630491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630491 prefixEnd_1630491 := by exact prefixLift 1630491
  have htrace : WordTrace (prefixWord ++ tailWord_1630491) baseStart_1630491 baseEnd_1630491 := by
    simpa [prefixWord, tailWord_1630491, baseEnd_1630491] using wordTrace_append hprefix tailTrace_1630491
  have hstable : (prefixWord ++ tailWord_1630491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630491).length < 2 ^ (prefixWord ++ tailWord_1630491).sum := by decide
  have hdescent : baseEnd_1630491 < baseStart_1630491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630494 : List Nat := [4, 3, 2, 1, 1, 2, 2, 6]
def baseStart_1630494 : Nat := 118140960795 + 1630494 * 2 ^ 59
def prefixEnd_1630494 : Nat := 4983230072969 + 3 ^ 40 * 1630494 * 2
def baseEnd_1630494 : Nat := 124033648336599839766889

theorem tailTrace_1630494 : CollatzResearch.WordTrace tailWord_1630494 prefixEnd_1630494 124033648336599839766889 := by
  unfold tailWord_1630494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7433625219375772381310317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39646001170004119366988357 7433625219375772381310317)
  ·
    refine ⟨2787609457265914642991369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7433625219375772381310317 2787609457265914642991369)
    ·
      refine ⟨2090707092949435982243527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2787609457265914642991369 2090707092949435982243527)
      ·
        refine ⟨3136060639424153973365291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090707092949435982243527 3136060639424153973365291)
        ·
          refine ⟨4704090959136230960047937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136060639424153973365291 4704090959136230960047937)
          ·
            refine ⟨3528068219352173220035953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4704090959136230960047937 3528068219352173220035953)
            ·
              refine ⟨2646051164514129915026965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3528068219352173220035953 2646051164514129915026965)
              ·
                refine ⟨124033648336599839766889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2646051164514129915026965 124033648336599839766889)
                ·
                  rfl

theorem cell21_1630494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_1630494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630494 prefixEnd_1630494 := by exact prefixLift 1630494
  have htrace : WordTrace (prefixWord ++ tailWord_1630494) baseStart_1630494 baseEnd_1630494 := by
    simpa [prefixWord, tailWord_1630494, baseEnd_1630494] using wordTrace_append hprefix tailTrace_1630494
  have hstable : (prefixWord ++ tailWord_1630494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630494).length < 2 ^ (prefixWord ++ tailWord_1630494).sum := by decide
  have hdescent : baseEnd_1630494 < baseStart_1630494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630567 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 5]
def baseStart_1630567 : Nat := 118140960795 + 1630567 * 2 ^ 59
def prefixEnd_1630567 : Nat := 4983230072969 + 3 ^ 40 * 1630567 * 2
def baseEnd_1630567 : Nat := 372117604604367614583851

theorem tailTrace_1630567 : CollatzResearch.WordTrace tailWord_1630567 prefixEnd_1630567 372117604604367614583851 := by
  unfold tailWord_1630567
  simp only [CollatzResearch.WordTrace]
  refine ⟨59471664283741712517889955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39647776189161141678593303 59471664283741712517889955)
  ·
    refine ⟨89207496425612568776834933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59471664283741712517889955 89207496425612568776834933)
    ·
      refine ⟨8363202789901178322828275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89207496425612568776834933 8363202789901178322828275)
      ·
        refine ⟨12544804184851767484242413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8363202789901178322828275 12544804184851767484242413)
        ·
          refine ⟨4704301569319412806590905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12544804184851767484242413 4704301569319412806590905)
          ·
            refine ⟨3528226176989559604943179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4704301569319412806590905 3528226176989559604943179)
            ·
              refine ⟨5292339265484339407414769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528226176989559604943179 5292339265484339407414769)
              ·
                refine ⟨3969254449113254555561077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5292339265484339407414769 3969254449113254555561077)
                ·
                  refine ⟨372117604604367614583851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3969254449113254555561077 372117604604367614583851)
                  ·
                    rfl

theorem cell21_1630567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 5].length) (baseStart_1630567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630567 prefixEnd_1630567 := by exact prefixLift 1630567
  have htrace : WordTrace (prefixWord ++ tailWord_1630567) baseStart_1630567 baseEnd_1630567 := by
    simpa [prefixWord, tailWord_1630567, baseEnd_1630567] using wordTrace_append hprefix tailTrace_1630567
  have hstable : (prefixWord ++ tailWord_1630567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630567).length < 2 ^ (prefixWord ++ tailWord_1630567).sum := by decide
  have hdescent : baseEnd_1630567 < baseStart_1630567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630719 : List Nat := [1, 1, 2, 2, 1, 2, 5, 4, 3]
def baseStart_1630719 : Nat := 118140960795 + 1630719 * 2 ^ 59
def prefixEnd_1630719 : Nat := 4983230072969 + 3 ^ 40 * 1630719 * 2
def baseEnd_1630719 : Nat := 372152293075249128050207

theorem tailTrace_1630719 : CollatzResearch.WordTrace tailWord_1630719 prefixEnd_1630719 372152293075249128050207 := by
  unfold tailWord_1630719
  simp only [CollatzResearch.WordTrace]
  refine ⟨59477208179191042477423211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39651472119460694984948807 59477208179191042477423211)
  ·
    refine ⟨89215812268786563716134817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59477208179191042477423211 89215812268786563716134817)
    ·
      refine ⟨66911859201589922787101113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89215812268786563716134817 66911859201589922787101113)
      ·
        refine ⟨50183894401192442090325835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66911859201589922787101113 50183894401192442090325835)
        ·
          refine ⟨75275841601788663135488753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50183894401192442090325835 75275841601788663135488753)
          ·
            refine ⟨56456881201341497351616565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75275841601788663135488753 56456881201341497351616565)
            ·
              refine ⟨5292832612625765376714053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56456881201341497351616565 5292832612625765376714053)
              ·
                refine ⟨992406114867331008133885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5292832612625765376714053 992406114867331008133885)
                ·
                  refine ⟨372152293075249128050207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992406114867331008133885 372152293075249128050207)
                  ·
                    rfl

theorem cell21_1630719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 3].length) (baseStart_1630719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630719 prefixEnd_1630719 := by exact prefixLift 1630719
  have htrace : WordTrace (prefixWord ++ tailWord_1630719) baseStart_1630719 baseEnd_1630719 := by
    simpa [prefixWord, tailWord_1630719, baseEnd_1630719] using wordTrace_append hprefix tailTrace_1630719
  have hstable : (prefixWord ++ tailWord_1630719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630719).length < 2 ^ (prefixWord ++ tailWord_1630719).sum := by decide
  have hdescent : baseEnd_1630719 < baseStart_1630719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630722 : List Nat := [3, 4, 1, 2, 2, 2, 1, 6]
def baseStart_1630722 : Nat := 118140960795 + 1630722 * 2 ^ 59
def prefixEnd_1630722 : Nat := 4983230072969 + 3 ^ 40 * 1630722 * 2
def baseEnd_1630722 : Nat := 124050992572040596500067

theorem tailTrace_1630722 : CollatzResearch.WordTrace tailWord_1630722 prefixEnd_1630722 124050992572040596500067 := by
  unfold tailWord_1630722
  simp only [CollatzResearch.WordTrace]
  refine ⟨14869329399545043497445605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39651545065453449326521613 14869329399545043497445605)
  ·
    refine ⟨2787999262414695655771051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14869329399545043497445605 2787999262414695655771051)
    ·
      refine ⟨4181998893622043483656577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2787999262414695655771051 4181998893622043483656577)
      ·
        refine ⟨3136499170216532612742433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4181998893622043483656577 3136499170216532612742433)
        ·
          refine ⟨2352374377662399459556825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3136499170216532612742433 2352374377662399459556825)
          ·
            refine ⟨1764280783246799594667619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2352374377662399459556825 1764280783246799594667619)
            ·
              refine ⟨2646421174870199392001429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764280783246799594667619 2646421174870199392001429)
              ·
                refine ⟨124050992572040596500067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2646421174870199392001429 124050992572040596500067)
                ·
                  rfl

theorem cell21_1630722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_1630722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630722 prefixEnd_1630722 := by exact prefixLift 1630722
  have htrace : WordTrace (prefixWord ++ tailWord_1630722) baseStart_1630722 baseEnd_1630722 := by
    simpa [prefixWord, tailWord_1630722, baseEnd_1630722] using wordTrace_append hprefix tailTrace_1630722
  have hstable : (prefixWord ++ tailWord_1630722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630722).length < 2 ^ (prefixWord ++ tailWord_1630722).sum := by decide
  have hdescent : baseEnd_1630722 < baseStart_1630722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630778 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_1630778 : Nat := 118140960795 + 1630778 * 2 ^ 59
def prefixEnd_1630778 : Nat := 4983230072969 + 3 ^ 40 * 1630778 * 2
def baseEnd_1630778 : Nat := 372165757679078136566753

theorem tailTrace_1630778 : CollatzResearch.WordTrace tailWord_1630778 prefixEnd_1630778 372165757679078136566753 := by
  unfold tailWord_1630778
  simp only [CollatzResearch.WordTrace]
  refine ⟨14869840021494323888455247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39652906723984863702547325 14869840021494323888455247)
  ·
    refine ⟨22304760032241485832682871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14869840021494323888455247 22304760032241485832682871)
    ·
      refine ⟨33457140048362228749024307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22304760032241485832682871 33457140048362228749024307)
      ·
        refine ⟨50185710072543343123536461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33457140048362228749024307 50185710072543343123536461)
        ·
          refine ⟨18819641277203753671326173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50185710072543343123536461 18819641277203753671326173)
          ·
            refine ⟨7057365478951407626747315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18819641277203753671326173 7057365478951407626747315)
            ·
              refine ⟨10586048218427111440120973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7057365478951407626747315 10586048218427111440120973)
              ·
                refine ⟨3969768081910166790045365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10586048218427111440120973 3969768081910166790045365)
                ·
                  refine ⟨372165757679078136566753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3969768081910166790045365 372165757679078136566753)
                  ·
                    rfl

theorem cell21_1630778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_1630778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630778 prefixEnd_1630778 := by exact prefixLift 1630778
  have htrace : WordTrace (prefixWord ++ tailWord_1630778) baseStart_1630778 baseEnd_1630778 := by
    simpa [prefixWord, tailWord_1630778, baseEnd_1630778] using wordTrace_append hprefix tailTrace_1630778
  have hstable : (prefixWord ++ tailWord_1630778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630778).length < 2 ^ (prefixWord ++ tailWord_1630778).sum := by decide
  have hdescent : baseEnd_1630778 < baseStart_1630778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630829 : List Nat := [1, 5, 1, 1, 3, 2, 3, 2, 3]
def baseStart_1630829 : Nat := 118140960795 + 1630829 * 2 ^ 59
def prefixEnd_1630829 : Nat := 4983230072969 + 3 ^ 40 * 1630829 * 2
def baseEnd_1630829 : Nat := 372177396573913381216649

theorem tailTrace_1630829 : CollatzResearch.WordTrace tailWord_1630829 prefixEnd_1630829 372177396573913381216649 := by
  unfold tailWord_1630829
  simp only [CollatzResearch.WordTrace]
  refine ⟨59481220208792531263927541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39654146805861687509285027 59481220208792531263927541)
  ·
    refine ⟨5576364394574299805993207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59481220208792531263927541 5576364394574299805993207)
    ·
      refine ⟨8364546591861449708989811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5576364394574299805993207 8364546591861449708989811)
      ·
        refine ⟨12546819887792174563484717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8364546591861449708989811 12546819887792174563484717)
        ·
          refine ⟨4705057457922065461306769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12546819887792174563484717 4705057457922065461306769)
          ·
            refine ⟨3528793093441549095980077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4705057457922065461306769 3528793093441549095980077)
            ·
              refine ⟨1323297410040580910992529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3528793093441549095980077 1323297410040580910992529)
              ·
                refine ⟨992473057530435683244397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323297410040580910992529 992473057530435683244397)
                ·
                  refine ⟨372177396573913381216649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992473057530435683244397 372177396573913381216649)
                  ·
                    rfl

theorem cell21_1630829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_1630829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630829 prefixEnd_1630829 := by exact prefixLift 1630829
  have htrace : WordTrace (prefixWord ++ tailWord_1630829) baseStart_1630829 baseEnd_1630829 := by
    simpa [prefixWord, tailWord_1630829, baseEnd_1630829] using wordTrace_append hprefix tailTrace_1630829
  have hstable : (prefixWord ++ tailWord_1630829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630829).length < 2 ^ (prefixWord ++ tailWord_1630829).sum := by decide
  have hdescent : baseEnd_1630829 < baseStart_1630829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630871 : List Nat := [1, 1, 3, 3, 2, 1, 2, 5, 3]
def baseStart_1630871 : Nat := 118140960795 + 1630871 * 2 ^ 59
def prefixEnd_1630871 : Nat := 4983230072969 + 3 ^ 40 * 1630871 * 2
def baseEnd_1630871 : Nat := 372186981546130641516563

theorem tailTrace_1630871 : CollatzResearch.WordTrace tailWord_1630871 prefixEnd_1630871 372186981546130641516563 := by
  unfold tailWord_1630871
  simp only [CollatzResearch.WordTrace]
  refine ⟨59482752074640372436956467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39655168049760248291304311 59482752074640372436956467)
  ·
    refine ⟨89224128111960558655434701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59482752074640372436956467 89224128111960558655434701)
    ·
      refine ⟨33459048041985209495788013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89224128111960558655434701 33459048041985209495788013)
      ·
        refine ⟨12547143015744453560920505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33459048041985209495788013 12547143015744453560920505)
        ·
          refine ⟨9410357261808340170690379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12547143015744453560920505 9410357261808340170690379)
          ·
            refine ⟨14115535892712510256035569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9410357261808340170690379 14115535892712510256035569)
            ·
              refine ⟨10586651919534382692026677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14115535892712510256035569 10586651919534382692026677)
              ·
                refine ⟨992498617456348377377501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10586651919534382692026677 992498617456348377377501)
                ·
                  refine ⟨372186981546130641516563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992498617456348377377501 372186981546130641516563)
                  ·
                    rfl

theorem cell21_1630871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 3].length) (baseStart_1630871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630871 prefixEnd_1630871 := by exact prefixLift 1630871
  have htrace : WordTrace (prefixWord ++ tailWord_1630871) baseStart_1630871 baseEnd_1630871 := by
    simpa [prefixWord, tailWord_1630871, baseEnd_1630871] using wordTrace_append hprefix tailTrace_1630871
  have hstable : (prefixWord ++ tailWord_1630871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630871).length < 2 ^ (prefixWord ++ tailWord_1630871).sum := by decide
  have hdescent : baseEnd_1630871 < baseStart_1630871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630899 : List Nat := [1, 1, 1, 2, 3, 4, 3, 6]
def baseStart_1630899 : Nat := 118140960795 + 1630899 * 2 ^ 59
def prefixEnd_1630899 : Nat := 4983230072969 + 3 ^ 40 * 1630899 * 2
def baseEnd_1630899 : Nat := 124064457175869605016613

theorem tailTrace_1630899 : CollatzResearch.WordTrace tailWord_1630899 prefixEnd_1630899 124064457175869605016613 := by
  unfold tailWord_1630899
  simp only [CollatzResearch.WordTrace]
  refine ⟨59483773318538933218975751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39655848879025955479317167 59483773318538933218975751)
  ·
    refine ⟨89225659977808399828463627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59483773318538933218975751 89225659977808399828463627)
    ·
      refine ⟨133838489966712599742695441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89225659977808399828463627 133838489966712599742695441)
      ·
        refine ⟨100378867475034449807021581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133838489966712599742695441 100378867475034449807021581)
        ·
          refine ⟨37642075303137918677633093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100378867475034449807021581 37642075303137918677633093)
          ·
            refine ⟨7057889119338359752056205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37642075303137918677633093 7057889119338359752056205)
            ·
              refine ⟨2646708419751884907021077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7057889119338359752056205 2646708419751884907021077)
              ·
                refine ⟨124064457175869605016613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2646708419751884907021077 124064457175869605016613)
                ·
                  rfl

theorem cell21_1630899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 6].length) (baseStart_1630899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630899 prefixEnd_1630899 := by exact prefixLift 1630899
  have htrace : WordTrace (prefixWord ++ tailWord_1630899) baseStart_1630899 baseEnd_1630899 := by
    simpa [prefixWord, tailWord_1630899, baseEnd_1630899] using wordTrace_append hprefix tailTrace_1630899
  have hstable : (prefixWord ++ tailWord_1630899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630899).length < 2 ^ (prefixWord ++ tailWord_1630899).sum := by decide
  have hdescent : baseEnd_1630899 < baseStart_1630899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1630947 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 5]
def baseStart_1630947 : Nat := 118140960795 + 1630947 * 2 ^ 59
def prefixEnd_1630947 : Nat := 4983230072969 + 3 ^ 40 * 1630947 * 2
def baseEnd_1630947 : Nat := 372204325781571398249741

theorem tailTrace_1630947 : CollatzResearch.WordTrace tailWord_1630947 prefixEnd_1630947 372204325781571398249741 := by
  unfold tailWord_1630947
  simp only [CollatzResearch.WordTrace]
  refine ⟨59485524022365037416723095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39657016014910024944482063 59485524022365037416723095)
  ·
    refine ⟨89228286033547556125084643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59485524022365037416723095 89228286033547556125084643)
    ·
      refine ⟨133842429050321334187626965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89228286033547556125084643 133842429050321334187626965)
      ·
        refine ⟨3136931930866906270022507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 133842429050321334187626965 3136931930866906270022507)
        ·
          refine ⟨4705397896300359405033761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3136931930866906270022507 4705397896300359405033761)
          ·
            refine ⟨3529048422225269553775321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4705397896300359405033761 3529048422225269553775321)
            ·
              refine ⟨2646786316668952165331491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3529048422225269553775321 2646786316668952165331491)
              ·
                refine ⟨3970179475003428247997237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646786316668952165331491 3970179475003428247997237)
                ·
                  refine ⟨372204325781571398249741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3970179475003428247997237 372204325781571398249741)
                  ·
                    rfl

theorem cell21_1630947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 5].length) (baseStart_1630947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1630947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1630947 prefixEnd_1630947 := by exact prefixLift 1630947
  have htrace : WordTrace (prefixWord ++ tailWord_1630947) baseStart_1630947 baseEnd_1630947 := by
    simpa [prefixWord, tailWord_1630947, baseEnd_1630947] using wordTrace_append hprefix tailTrace_1630947
  have hstable : (prefixWord ++ tailWord_1630947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1630947).length < 2 ^ (prefixWord ++ tailWord_1630947).sum := by decide
  have hdescent : baseEnd_1630947 < baseStart_1630947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1630947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631012 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 4]
def baseStart_1631012 : Nat := 118140960795 + 1631012 * 2 ^ 59
def prefixEnd_1631012 : Nat := 4983230072969 + 3 ^ 40 * 1631012 * 2
def baseEnd_1631012 : Nat := 372219159667145729666275

theorem tailTrace_1631012 : CollatzResearch.WordTrace tailWord_1631012 prefixEnd_1631012 372219159667145729666275 := by
  unfold tailWord_1631012
  simp only [CollatzResearch.WordTrace]
  refine ⟨29743947383564776758919645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39658596511419702345226193 29743947383564776758919645)
  ·
    refine ⟨11153980268836791284594867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29743947383564776758919645 11153980268836791284594867)
    ·
      refine ⟨16730970403255186926892301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11153980268836791284594867 16730970403255186926892301)
      ·
        refine ⟨6274113901220695097584613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16730970403255186926892301 6274113901220695097584613)
        ·
          refine ⟨1176396356478880330797115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6274113901220695097584613 1176396356478880330797115)
          ·
            refine ⟨1764594534718320496195673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176396356478880330797115 1764594534718320496195673)
            ·
              refine ⟨1323445901038740372146755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1764594534718320496195673 1323445901038740372146755)
              ·
                refine ⟨1985168851558110558220133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323445901038740372146755 1985168851558110558220133)
                ·
                  refine ⟨372219159667145729666275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1985168851558110558220133 372219159667145729666275)
                  ·
                    rfl

theorem cell21_1631012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_1631012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631012 prefixEnd_1631012 := by exact prefixLift 1631012
  have htrace : WordTrace (prefixWord ++ tailWord_1631012) baseStart_1631012 baseEnd_1631012 := by
    simpa [prefixWord, tailWord_1631012, baseEnd_1631012] using wordTrace_append hprefix tailTrace_1631012
  have hstable : (prefixWord ++ tailWord_1631012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631012).length < 2 ^ (prefixWord ++ tailWord_1631012).sum := by decide
  have hdescent : baseEnd_1631012 < baseStart_1631012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631057 : List Nat := [1, 2, 2, 1, 6, 2, 2, 2, 3]
def baseStart_1631057 : Nat := 118140960795 + 1631057 * 2 ^ 59
def prefixEnd_1631057 : Nat := 4983230072969 + 3 ^ 40 * 1631057 * 2
def baseEnd_1631057 : Nat := 372229429280235651416183

theorem tailTrace_1631057 : CollatzResearch.WordTrace tailWord_1631057 prefixEnd_1631057 372229429280235651416183 := by
  unfold tailWord_1631057
  simp only [CollatzResearch.WordTrace]
  refine ⟨59489536051966526203227425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39659690701311017468818283 59489536051966526203227425)
  ·
    refine ⟨44617152038974894652420569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59489536051966526203227425 44617152038974894652420569)
    ·
      refine ⟨33462864029231170989315427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44617152038974894652420569 33462864029231170989315427)
      ·
        refine ⟨50194296043846756483973141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33462864029231170989315427 50194296043846756483973141)
        ·
          refine ⟨2352857627055316710186241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50194296043846756483973141 2352857627055316710186241)
          ·
            refine ⟨1764643220291487532639681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2352857627055316710186241 1764643220291487532639681)
            ·
              refine ⟨1323482415218615649479761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1764643220291487532639681 1323482415218615649479761)
              ·
                refine ⟨992611811413961737109821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1323482415218615649479761 992611811413961737109821)
                ·
                  refine ⟨372229429280235651416183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992611811413961737109821 372229429280235651416183)
                  ·
                    rfl

theorem cell21_1631057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 3].length) (baseStart_1631057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631057 prefixEnd_1631057 := by exact prefixLift 1631057
  have htrace : WordTrace (prefixWord ++ tailWord_1631057) baseStart_1631057 baseEnd_1631057 := by
    simpa [prefixWord, tailWord_1631057, baseEnd_1631057] using wordTrace_append hprefix tailTrace_1631057
  have hstable : (prefixWord ++ tailWord_1631057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631057).length < 2 ^ (prefixWord ++ tailWord_1631057).sum := by decide
  have hdescent : baseEnd_1631057 < baseStart_1631057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631068 : List Nat := [2, 2, 4, 2, 1, 1, 3, 6]
def baseStart_1631068 : Nat := 118140960795 + 1631068 * 2 ^ 59
def prefixEnd_1631068 : Nat := 4983230072969 + 3 ^ 40 * 1631068 * 2
def baseEnd_1631068 : Nat := 124077313210034025577609

theorem tailTrace_1631068 : CollatzResearch.WordTrace tailWord_1631068 prefixEnd_1631068 124077313210034025577609 := by
  unfold tailWord_1631068
  simp only [CollatzResearch.WordTrace]
  refine ⟨29744968627463337540938929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39659958169951116721251905 29744968627463337540938929)
  ·
    refine ⟨22308726470597503155704197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29744968627463337540938929 22308726470597503155704197)
    ·
      refine ⟨4182886213237031841694537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22308726470597503155704197 4182886213237031841694537)
      ·
        refine ⟨3137164659927773881270903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4182886213237031841694537 3137164659927773881270903)
        ·
          refine ⟨4705746989891660821906355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3137164659927773881270903 4705746989891660821906355)
          ·
            refine ⟨7058620484837491232859533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4705746989891660821906355 7058620484837491232859533)
            ·
              refine ⟨2646982681814059212322325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7058620484837491232859533 2646982681814059212322325)
              ·
                refine ⟨124077313210034025577609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2646982681814059212322325 124077313210034025577609)
                ·
                  rfl

theorem cell21_1631068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_1631068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631068 prefixEnd_1631068 := by exact prefixLift 1631068
  have htrace : WordTrace (prefixWord ++ tailWord_1631068) baseStart_1631068 baseEnd_1631068 := by
    simpa [prefixWord, tailWord_1631068, baseEnd_1631068] using wordTrace_append hprefix tailTrace_1631068
  have hstable : (prefixWord ++ tailWord_1631068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631068).length < 2 ^ (prefixWord ++ tailWord_1631068).sum := by decide
  have hdescent : baseEnd_1631068 < baseStart_1631068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631113 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 4]
def baseStart_1631113 : Nat := 118140960795 + 1631113 * 2 ^ 59
def prefixEnd_1631113 : Nat := 4983230072969 + 3 ^ 40 * 1631113 * 2
def baseEnd_1631113 : Nat := 372242209243191998482735

theorem tailTrace_1631113 : CollatzResearch.WordTrace tailWord_1631113 prefixEnd_1631113 372242209243191998482735 := by
  unfold tailWord_1631113
  simp only [CollatzResearch.WordTrace]
  refine ⟨59491578539763647767265993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39661052359842431844843995 59491578539763647767265993)
  ·
    refine ⟨44618683904822735825449495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59491578539763647767265993 44618683904822735825449495)
    ·
      refine ⟨66928025857234103738174243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44618683904822735825449495 66928025857234103738174243)
      ·
        refine ⟨100392038785851155607261365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66928025857234103738174243 100392038785851155607261365)
        ·
          refine ⟨9411753636173545838180753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100392038785851155607261365 9411753636173545838180753)
          ·
            refine ⟨7058815227130159378635565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9411753636173545838180753 7058815227130159378635565)
            ·
              refine ⟨2647055710173809766988337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7058815227130159378635565 2647055710173809766988337)
              ·
                refine ⟨1985291782630357325241253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2647055710173809766988337 1985291782630357325241253)
                ·
                  refine ⟨372242209243191998482735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1985291782630357325241253 372242209243191998482735)
                  ·
                    rfl

theorem cell21_1631113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_1631113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631113 prefixEnd_1631113 := by exact prefixLift 1631113
  have htrace : WordTrace (prefixWord ++ tailWord_1631113) baseStart_1631113 baseEnd_1631113 := by
    simpa [prefixWord, tailWord_1631113, baseEnd_1631113] using wordTrace_append hprefix tailTrace_1631113
  have hstable : (prefixWord ++ tailWord_1631113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631113).length < 2 ^ (prefixWord ++ tailWord_1631113).sum := by decide
  have hdescent : baseEnd_1631113 < baseStart_1631113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631268 : List Nat := [2, 3, 1, 4, 1, 2, 2, 3, 3]
def baseStart_1631268 : Nat := 118140960795 + 1631268 * 2 ^ 59
def prefixEnd_1631268 : Nat := 4983230072969 + 3 ^ 40 * 1631268 * 2
def baseEnd_1631268 : Nat := 372277582354946173399085

theorem tailTrace_1631268 : CollatzResearch.WordTrace tailWord_1631268 prefixEnd_1631268 372277582354946173399085 := by
  unfold tailWord_1631268
  simp only [CollatzResearch.WordTrace]
  refine ⟨29748615927101054619579229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39664821236134739492772305 29748615927101054619579229)
  ·
    refine ⟨11155730972662895482342211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29748615927101054619579229 11155730972662895482342211)
    ·
      refine ⟨16733596458994343223513317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11155730972662895482342211 16733596458994343223513317)
      ·
        refine ⟨3137549336061439354408747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16733596458994343223513317 3137549336061439354408747)
        ·
          refine ⟨4706324004092159031613121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3137549336061439354408747 4706324004092159031613121)
          ·
            refine ⟨3529743003069119273709841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4706324004092159031613121 3529743003069119273709841)
            ·
              refine ⟨2647307252301839455282381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3529743003069119273709841 2647307252301839455282381)
              ·
                refine ⟨992740219613189795730893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2647307252301839455282381 992740219613189795730893)
                ·
                  refine ⟨372277582354946173399085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992740219613189795730893 372277582354946173399085)
                  ·
                    rfl

theorem cell21_1631268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_1631268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631268 prefixEnd_1631268 := by exact prefixLift 1631268
  have htrace : WordTrace (prefixWord ++ tailWord_1631268) baseStart_1631268 baseEnd_1631268 := by
    simpa [prefixWord, tailWord_1631268, baseEnd_1631268] using wordTrace_append hprefix tailTrace_1631268
  have hstable : (prefixWord ++ tailWord_1631268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631268).length < 2 ^ (prefixWord ++ tailWord_1631268).sum := by decide
  have hdescent : baseEnd_1631268 < baseStart_1631268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631307 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 10]
def baseStart_1631307 : Nat := 118140960795 + 1631307 * 2 ^ 59
def prefixEnd_1631307 : Nat := 4983230072969 + 3 ^ 40 * 1631307 * 2
def baseEnd_1631307 : Nat := 372286482686290772249005

theorem tailTrace_1631307 : CollatzResearch.WordTrace tailWord_1631307 prefixEnd_1631307 372286482686290772249005 := by
  unfold tailWord_1631307
  simp only [CollatzResearch.WordTrace]
  refine ⟨59498654301060818899828175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39665769534040545933218783 59498654301060818899828175)
  ·
    refine ⟨89247981451591228349742263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59498654301060818899828175 89247981451591228349742263)
    ·
      refine ⟨133871972177386842524613395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89247981451591228349742263 133871972177386842524613395)
      ·
        refine ⟨200807958266080263786920093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133871972177386842524613395 200807958266080263786920093)
        ·
          refine ⟨75302984349780098920095035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200807958266080263786920093 75302984349780098920095035)
          ·
            refine ⟨112954476524670148380142553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75302984349780098920095035 112954476524670148380142553)
            ·
              refine ⟨84715857393502611285106915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112954476524670148380142553 84715857393502611285106915)
              ·
                refine ⟨127073786090253916927660373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84715857393502611285106915 127073786090253916927660373)
                ·
                  refine ⟨372286482686290772249005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 127073786090253916927660373 372286482686290772249005)
                  ·
                    rfl

theorem cell21_1631307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_1631307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631307 prefixEnd_1631307 := by exact prefixLift 1631307
  have htrace : WordTrace (prefixWord ++ tailWord_1631307) baseStart_1631307 baseEnd_1631307 := by
    simpa [prefixWord, tailWord_1631307, baseEnd_1631307] using wordTrace_append hprefix tailTrace_1631307
  have hstable : (prefixWord ++ tailWord_1631307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631307).length < 2 ^ (prefixWord ++ tailWord_1631307).sum := by decide
  have hdescent : baseEnd_1631307 < baseStart_1631307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631324 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_1631324 : Nat := 118140960795 + 1631324 * 2 ^ 59
def prefixEnd_1631324 : Nat := 4983230072969 + 3 ^ 40 * 1631324 * 2
def baseEnd_1631324 : Nat := 372290362317902520465637

theorem tailTrace_1631324 : CollatzResearch.WordTrace tailWord_1631324 prefixEnd_1631324 372290362317902520465637 := by
  unfold tailWord_1631324
  simp only [CollatzResearch.WordTrace]
  refine ⟨29749637170999615401598513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39666182894666153868798017 29749637170999615401598513)
  ·
    refine ⟨22312227878249711551198885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29749637170999615401598513 22312227878249711551198885)
    ·
      refine ⟨4183542727171820915849791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22312227878249711551198885 4183542727171820915849791)
      ·
        refine ⟨6275314090757731373774687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4183542727171820915849791 6275314090757731373774687)
        ·
          refine ⟨9412971136136597060662031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6275314090757731373774687 9412971136136597060662031)
          ·
            refine ⟨14119456704204895590993047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9412971136136597060662031 14119456704204895590993047)
            ·
              refine ⟨21179185056307343386489571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14119456704204895590993047 21179185056307343386489571)
              ·
                refine ⟨31768777584461015079734357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21179185056307343386489571 31768777584461015079734357)
                ·
                  refine ⟨372290362317902520465637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31768777584461015079734357 372290362317902520465637)
                  ·
                    rfl

theorem cell21_1631324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_1631324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631324 prefixEnd_1631324 := by exact prefixLift 1631324
  have htrace : WordTrace (prefixWord ++ tailWord_1631324) baseStart_1631324 baseEnd_1631324 := by
    simpa [prefixWord, tailWord_1631324, baseEnd_1631324] using wordTrace_append hprefix tailTrace_1631324
  have hstable : (prefixWord ++ tailWord_1631324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631324).length < 2 ^ (prefixWord ++ tailWord_1631324).sum := by decide
  have hdescent : baseEnd_1631324 < baseStart_1631324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631496 : List Nat := [2, 1, 3, 2, 4, 2, 1, 3, 3]
def baseStart_1631496 : Nat := 118140960795 + 1631496 * 2 ^ 59
def prefixEnd_1631496 : Nat := 4983230072969 + 3 ^ 40 * 1631496 * 2
def baseEnd_1631496 : Nat := 372329615061268443598619

theorem tailTrace_1631496 : CollatzResearch.WordTrace tailWord_1631496 prefixEnd_1631496 372329615061268443598619 := by
  unfold tailWord_1631496
  simp only [CollatzResearch.WordTrace]
  refine ⟨29752773848688052089229171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39670365131584069452305561 29752773848688052089229171)
  ·
    refine ⟨44629160773032078133843757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29752773848688052089229171 44629160773032078133843757)
    ·
      refine ⟨16735935289887029300191409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44629160773032078133843757 16735935289887029300191409)
      ·
        refine ⟨12551951467415271975143557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16735935289887029300191409 12551951467415271975143557)
        ·
          refine ⟨2353490900140363495339417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12551951467415271975143557 2353490900140363495339417)
          ·
            refine ⟨1765118175105272621504563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2353490900140363495339417 1765118175105272621504563)
            ·
              refine ⟨2647677262657908932256845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765118175105272621504563 2647677262657908932256845)
              ·
                refine ⟨992878973496715849596317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2647677262657908932256845 992878973496715849596317)
                ·
                  refine ⟨372329615061268443598619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992878973496715849596317 372329615061268443598619)
                  ·
                    rfl

theorem cell21_1631496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 3].length) (baseStart_1631496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631496 prefixEnd_1631496 := by exact prefixLift 1631496
  have htrace : WordTrace (prefixWord ++ tailWord_1631496) baseStart_1631496 baseEnd_1631496 := by
    simpa [prefixWord, tailWord_1631496, baseEnd_1631496] using wordTrace_append hprefix tailTrace_1631496
  have hstable : (prefixWord ++ tailWord_1631496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631496).length < 2 ^ (prefixWord ++ tailWord_1631496).sum := by decide
  have hdescent : baseEnd_1631496 < baseStart_1631496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631597 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1631597 : Nat := 118140960795 + 1631597 * 2 ^ 59
def prefixEnd_1631597 : Nat := 4983230072969 + 3 ^ 40 * 1631597 * 2
def baseEnd_1631597 : Nat := 372352664637314712415079

theorem tailTrace_1631597 : CollatzResearch.WordTrace tailWord_1631597 prefixEnd_1631597 372352664637314712415079 := by
  unfold tailWord_1631597
  simp only [CollatzResearch.WordTrace]
  refine ⟨59509231470010198427885045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39672820980006798951923363 59509231470010198427885045)
  ·
    refine ⟨5578990450313456102614223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59509231470010198427885045 5578990450313456102614223)
    ·
      refine ⟨8368485675470184153921335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5578990450313456102614223 8368485675470184153921335)
      ·
        refine ⟨12552728513205276230882003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8368485675470184153921335 12552728513205276230882003)
        ·
          refine ⟨18829092769807914346323005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12552728513205276230882003 18829092769807914346323005)
          ·
            refine ⟨7060909788677967879871127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18829092769807914346323005 7060909788677967879871127)
            ·
              refine ⟨10591364683016951819806691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7060909788677967879871127 10591364683016951819806691)
              ·
                refine ⟨15887047024525427729710037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10591364683016951819806691 15887047024525427729710037)
                ·
                  refine ⟨372352664637314712415079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15887047024525427729710037 372352664637314712415079)
                  ·
                    rfl

theorem cell21_1631597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1631597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631597 prefixEnd_1631597 := by exact prefixLift 1631597
  have htrace : WordTrace (prefixWord ++ tailWord_1631597) baseStart_1631597 baseEnd_1631597 := by
    simpa [prefixWord, tailWord_1631597, baseEnd_1631597] using wordTrace_append hprefix tailTrace_1631597
  have hstable : (prefixWord ++ tailWord_1631597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631597).length < 2 ^ (prefixWord ++ tailWord_1631597).sum := by decide
  have hdescent : baseEnd_1631597 < baseStart_1631597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631611 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 6]
def baseStart_1631611 : Nat := 118140960795 + 1631611 * 2 ^ 59
def prefixEnd_1631611 : Nat := 4983230072969 + 3 ^ 40 * 1631611 * 2
def baseEnd_1631611 : Nat := 372355859628053799181717

theorem tailTrace_1631611 : CollatzResearch.WordTrace tailWord_1631611 prefixEnd_1631611 372355859628053799181717 := by
  unfold tailWord_1631611
  simp only [CollatzResearch.WordTrace]
  refine ⟨59509742091959478818894687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39673161394639652545929791 59509742091959478818894687)
  ·
    refine ⟨89264613137939218228342031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59509742091959478818894687 89264613137939218228342031)
    ·
      refine ⟨133896919706908827342513047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89264613137939218228342031 133896919706908827342513047)
      ·
        refine ⟨200845379560363241013769571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133896919706908827342513047 200845379560363241013769571)
        ·
          refine ⟨301268069340544861520654357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200845379560363241013769571 301268069340544861520654357)
          ·
            refine ⟨14121940750338040383780673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 301268069340544861520654357 14121940750338040383780673)
            ·
              refine ⟨10591455562753530287835505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14121940750338040383780673 10591455562753530287835505)
              ·
                refine ⟨7943591672065147715876629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10591455562753530287835505 7943591672065147715876629)
                ·
                  refine ⟨372355859628053799181717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7943591672065147715876629 372355859628053799181717)
                  ·
                    rfl

theorem cell21_1631611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_1631611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631611 prefixEnd_1631611 := by exact prefixLift 1631611
  have htrace : WordTrace (prefixWord ++ tailWord_1631611) baseStart_1631611 baseEnd_1631611 := by
    simpa [prefixWord, tailWord_1631611, baseEnd_1631611] using wordTrace_append hprefix tailTrace_1631611
  have hstable : (prefixWord ++ tailWord_1631611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631611).length < 2 ^ (prefixWord ++ tailWord_1631611).sum := by decide
  have hdescent : baseEnd_1631611 < baseStart_1631611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631642 : List Nat := [3, 1, 1, 4, 1, 1, 2, 8]
def baseStart_1631642 : Nat := 118140960795 + 1631642 * 2 ^ 59
def prefixEnd_1631642 : Nat := 4983230072969 + 3 ^ 40 * 1631642 * 2
def baseEnd_1631642 : Nat := 124120978083468211388329

theorem tailTrace_1631642 : CollatzResearch.WordTrace tailWord_1631642 prefixEnd_1631642 124120978083468211388329 := by
  unfold tailWord_1631642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14877718188711792778318295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39673915169898114075515453 14877718188711792778318295)
  ·
    refine ⟨22316577283067689167477443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14877718188711792778318295 22316577283067689167477443)
    ·
      refine ⟨33474865924601533751216165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22316577283067689167477443 33474865924601533751216165)
      ·
        refine ⟨6276537360862787578353031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33474865924601533751216165 6276537360862787578353031)
        ·
          refine ⟨9414806041294181367529547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6276537360862787578353031 9414806041294181367529547)
          ·
            refine ⟨14122209061941272051294321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9414806041294181367529547 14122209061941272051294321)
            ·
              refine ⟨10591656796455954038470741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14122209061941272051294321 10591656796455954038470741)
              ·
                refine ⟨124120978083468211388329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10591656796455954038470741 124120978083468211388329)
                ·
                  rfl

theorem cell21_1631642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_1631642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631642 prefixEnd_1631642 := by exact prefixLift 1631642
  have htrace : WordTrace (prefixWord ++ tailWord_1631642) baseStart_1631642 baseEnd_1631642 := by
    simpa [prefixWord, tailWord_1631642, baseEnd_1631642] using wordTrace_append hprefix tailTrace_1631642
  have hstable : (prefixWord ++ tailWord_1631642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631642).length < 2 ^ (prefixWord ++ tailWord_1631642).sum := by decide
  have hdescent : baseEnd_1631642 < baseStart_1631642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631676 : List Nat := [2, 2, 2, 4, 3, 1, 7]
def baseStart_1631676 : Nat := 118140960795 + 1631676 * 2 ^ 59
def prefixEnd_1631676 : Nat := 4983230072969 + 3 ^ 40 * 1631676 * 2
def baseEnd_1631676 : Nat := 41374521501514236733139

theorem tailTrace_1631676 : CollatzResearch.WordTrace tailWord_1631676 prefixEnd_1631676 41374521501514236733139 := by
  unfold tailWord_1631676
  simp only [CollatzResearch.WordTrace]
  refine ⟨29756056418361997460005441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39674741891149329946673921 29756056418361997460005441)
  ·
    refine ⟨22317042313771498095004081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29756056418361997460005441 22317042313771498095004081)
    ·
      refine ⟨16737781735328623571253061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22317042313771498095004081 16737781735328623571253061)
      ·
        refine ⟨3138334075374116919609949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16737781735328623571253061 3138334075374116919609949)
        ·
          refine ⟨1176875278265293844853731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3138334075374116919609949 1176875278265293844853731)
          ·
            refine ⟨1765312917397940767280597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176875278265293844853731 1765312917397940767280597)
            ·
              refine ⟨41374521501514236733139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1765312917397940767280597 41374521501514236733139)
              ·
                rfl

theorem cell21_1631676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 7].length) (baseStart_1631676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631676 prefixEnd_1631676 := by exact prefixLift 1631676
  have htrace : WordTrace (prefixWord ++ tailWord_1631676) baseStart_1631676 baseEnd_1631676 := by
    simpa [prefixWord, tailWord_1631676, baseEnd_1631676] using wordTrace_append hprefix tailTrace_1631676
  have hstable : (prefixWord ++ tailWord_1631676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631676).length < 2 ^ (prefixWord ++ tailWord_1631676).sum := by decide
  have hdescent : baseEnd_1631676 < baseStart_1631676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631682 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1631682 : Nat := 118140960795 + 1631682 * 2 ^ 59
def prefixEnd_1631682 : Nat := 4983230072969 + 3 ^ 40 * 1631682 * 2
def baseEnd_1631682 : Nat := 372372062795373453498239

theorem tailTrace_1631682 : CollatzResearch.WordTrace tailWord_1631682 prefixEnd_1631682 372372062795373453498239 := by
  unfold tailWord_1631682
  simp only [CollatzResearch.WordTrace]
  refine ⟨14878082918675564486182325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39674887783134838629819533 14878082918675564486182325)
  ·
    refine ⟨1394820273625834170579593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14878082918675564486182325 1394820273625834170579593)
    ·
      refine ⟨1046115205219375627934695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1394820273625834170579593 1046115205219375627934695)
      ·
        refine ⟨1569172807829063441902043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046115205219375627934695 1569172807829063441902043)
        ·
          refine ⟨2353759211743595162853065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569172807829063441902043 2353759211743595162853065)
          ·
            refine ⟨1765319408807696372139799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2353759211743595162853065 1765319408807696372139799)
            ·
              refine ⟨2647979113211544558209699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765319408807696372139799 2647979113211544558209699)
              ·
                refine ⟨3971968669817316837314549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647979113211544558209699 3971968669817316837314549)
                ·
                  refine ⟨372372062795373453498239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3971968669817316837314549 372372062795373453498239)
                  ·
                    rfl

theorem cell21_1631682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1631682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631682 prefixEnd_1631682 := by exact prefixLift 1631682
  have htrace : WordTrace (prefixWord ++ tailWord_1631682) baseStart_1631682 baseEnd_1631682 := by
    simpa [prefixWord, tailWord_1631682, baseEnd_1631682] using wordTrace_append hprefix tailTrace_1631682
  have hstable : (prefixWord ++ tailWord_1631682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631682).length < 2 ^ (prefixWord ++ tailWord_1631682).sum := by decide
  have hdescent : baseEnd_1631682 < baseStart_1631682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631687 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 6]
def baseStart_1631687 : Nat := 118140960795 + 1631687 * 2 ^ 59
def prefixEnd_1631687 : Nat := 4983230072969 + 3 ^ 40 * 1631687 * 2
def baseEnd_1631687 : Nat := 372373203863494555914895

theorem tailTrace_1631687 : CollatzResearch.WordTrace tailWord_1631687 prefixEnd_1631687 372373203863494555914895 := by
  unfold tailWord_1631687
  simp only [CollatzResearch.WordTrace]
  refine ⟨59512514039684143798661315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39675009359789429199107543 59512514039684143798661315)
  ·
    refine ⟨89268771059526215697991973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59512514039684143798661315 89268771059526215697991973)
    ·
      refine ⟨16737894573661165443373495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89268771059526215697991973 16737894573661165443373495)
      ·
        refine ⟨25106841860491748165060243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16737894573661165443373495 25106841860491748165060243)
        ·
          refine ⟨37660262790737622247590365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25106841860491748165060243 37660262790737622247590365)
          ·
            refine ⟨14122598546526608342846387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37660262790737622247590365 14122598546526608342846387)
            ·
              refine ⟨21183897819789912514269581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14122598546526608342846387 21183897819789912514269581)
              ·
                refine ⟨7943961682421217192851093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21183897819789912514269581 7943961682421217192851093)
                ·
                  refine ⟨372373203863494555914895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7943961682421217192851093 372373203863494555914895)
                  ·
                    rfl

theorem cell21_1631687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_1631687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631687 prefixEnd_1631687 := by exact prefixLift 1631687
  have htrace : WordTrace (prefixWord ++ tailWord_1631687) baseStart_1631687 baseEnd_1631687 := by
    simpa [prefixWord, tailWord_1631687, baseEnd_1631687] using wordTrace_append hprefix tailTrace_1631687
  have hstable : (prefixWord ++ tailWord_1631687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631687).length < 2 ^ (prefixWord ++ tailWord_1631687).sum := by decide
  have hdescent : baseEnd_1631687 < baseStart_1631687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631690 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 5]
def baseStart_1631690 : Nat := 118140960795 + 1631690 * 2 ^ 59
def prefixEnd_1631690 : Nat := 4983230072969 + 3 ^ 40 * 1631690 * 2
def baseEnd_1631690 : Nat := 372373888504367217364889

theorem tailTrace_1631690 : CollatzResearch.WordTrace tailWord_1631690 prefixEnd_1631690 372373888504367217364889 := by
  unfold tailWord_1631690
  simp only [CollatzResearch.WordTrace]
  refine ⟨14878155864668318827755131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39675082305782183540680349 14878155864668318827755131)
  ·
    refine ⟨22317233797002478241632697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14878155864668318827755131 22317233797002478241632697)
    ·
      refine ⟨16737925347751858681224523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22317233797002478241632697 16737925347751858681224523)
      ·
        refine ⟨25106888021627788021836785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16737925347751858681224523 25106888021627788021836785)
        ·
          refine ⟨18830166016220841016377589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25106888021627788021836785 18830166016220841016377589)
          ·
            refine ⟨1765328064020703845285399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18830166016220841016377589 1765328064020703845285399)
            ·
              refine ⟨2647992096031055767928099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765328064020703845285399 2647992096031055767928099)
              ·
                refine ⟨3971988144046583651892149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647992096031055767928099 3971988144046583651892149)
                ·
                  refine ⟨372373888504367217364889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3971988144046583651892149 372373888504367217364889)
                  ·
                    rfl

theorem cell21_1631690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_1631690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631690 prefixEnd_1631690 := by exact prefixLift 1631690
  have htrace : WordTrace (prefixWord ++ tailWord_1631690) baseStart_1631690 baseEnd_1631690 := by
    simpa [prefixWord, tailWord_1631690, baseEnd_1631690] using wordTrace_append hprefix tailTrace_1631690
  have hstable : (prefixWord ++ tailWord_1631690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631690).length < 2 ^ (prefixWord ++ tailWord_1631690).sum := by decide
  have hdescent : baseEnd_1631690 < baseStart_1631690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631797 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 4]
def baseStart_1631797 : Nat := 118140960795 + 1631797 * 2 ^ 59
def prefixEnd_1631797 : Nat := 4983230072969 + 3 ^ 40 * 1631797 * 2
def baseEnd_1631797 : Nat := 372398307362158809081337

theorem tailTrace_1631797 : CollatzResearch.WordTrace tailWord_1631797 prefixEnd_1631797 372398307362158809081337 := by
  unfold tailWord_1631797
  simp only [CollatzResearch.WordTrace]
  refine ⟨59516526069285632585165645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39677684046190421723443763 59516526069285632585165645)
  ·
    refine ⟨22318697275982112219437117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59516526069285632585165645 22318697275982112219437117)
    ·
      refine ⟨8369511478493292082288919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22318697275982112219437117 8369511478493292082288919)
      ·
        refine ⟨12554267217739938123433379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8369511478493292082288919 12554267217739938123433379)
        ·
          refine ⟨18831400826609907185150069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12554267217739938123433379 18831400826609907185150069)
          ·
            refine ⟨1765443827494678798607819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18831400826609907185150069 1765443827494678798607819)
            ·
              refine ⟨2648165741242018197911729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765443827494678798607819 2648165741242018197911729)
              ·
                refine ⟨1986124305931513648433797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648165741242018197911729 1986124305931513648433797)
                ·
                  refine ⟨372398307362158809081337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1986124305931513648433797 372398307362158809081337)
                  ·
                    rfl

theorem cell21_1631797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_1631797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631797 prefixEnd_1631797 := by exact prefixLift 1631797
  have htrace : WordTrace (prefixWord ++ tailWord_1631797) baseStart_1631797 baseEnd_1631797 := by
    simpa [prefixWord, tailWord_1631797, baseEnd_1631797] using wordTrace_append hprefix tailTrace_1631797
  have hstable : (prefixWord ++ tailWord_1631797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631797).length < 2 ^ (prefixWord ++ tailWord_1631797).sum := by decide
  have hdescent : baseEnd_1631797 < baseStart_1631797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631873 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 4]
def baseStart_1631873 : Nat := 118140960795 + 1631873 * 2 ^ 59
def prefixEnd_1631873 : Nat := 4983230072969 + 3 ^ 40 * 1631873 * 2
def baseEnd_1631873 : Nat := 372415651597599565814515

theorem tailTrace_1631873 : CollatzResearch.WordTrace tailWord_1631873 prefixEnd_1631873 372415651597599565814515 := by
  unfold tailWord_1631873
  simp only [CollatzResearch.WordTrace]
  refine ⟨59519298017010297564932273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39679532011340198376621515 59519298017010297564932273)
  ·
    refine ⟨44639473512757723173699205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59519298017010297564932273 44639473512757723173699205)
    ·
      refine ⟨8369901283642073095068601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44639473512757723173699205 8369901283642073095068601)
      ·
        refine ⟨6277425962731554821301451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8369901283642073095068601 6277425962731554821301451)
        ·
          refine ⟨9416138944097332231952177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6277425962731554821301451 9416138944097332231952177)
          ·
            refine ⟨7062104208072999173964133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9416138944097332231952177 7062104208072999173964133)
            ·
              refine ⟨1324144539013687345118275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7062104208072999173964133 1324144539013687345118275)
              ·
                refine ⟨1986216808520531017677413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324144539013687345118275 1986216808520531017677413)
                ·
                  refine ⟨372415651597599565814515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1986216808520531017677413 372415651597599565814515)
                  ·
                    rfl

theorem cell21_1631873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_1631873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631873 prefixEnd_1631873 := by exact prefixLift 1631873
  have htrace : WordTrace (prefixWord ++ tailWord_1631873) baseStart_1631873 baseEnd_1631873 := by
    simpa [prefixWord, tailWord_1631873, baseEnd_1631873] using wordTrace_append hprefix tailTrace_1631873
  have hstable : (prefixWord ++ tailWord_1631873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631873).length < 2 ^ (prefixWord ++ tailWord_1631873).sum := by decide
  have hdescent : baseEnd_1631873 < baseStart_1631873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631884 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_1631884 : Nat := 118140960795 + 1631884 * 2 ^ 59
def prefixEnd_1631884 : Nat := 4983230072969 + 3 ^ 40 * 1631884 * 2
def baseEnd_1631884 : Nat := 372418161947465991131159

theorem tailTrace_1631884 : CollatzResearch.WordTrace tailWord_1631884 prefixEnd_1631884 372418161947465991131159 := by
  unfold tailWord_1631884
  simp only [CollatzResearch.WordTrace]
  refine ⟨29759849609985223221791353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39679799479980297629055137 29759849609985223221791353)
  ·
    refine ⟨22319887207488917416343515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29759849609985223221791353 22319887207488917416343515)
    ·
      refine ⟨33479830811233376124515273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22319887207488917416343515 33479830811233376124515273)
      ·
        refine ⟨25109873108425032093386455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33479830811233376124515273 25109873108425032093386455)
        ·
          refine ⟨37664809662637548140079683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25109873108425032093386455 37664809662637548140079683)
          ·
            refine ⟨56497214493956322210119525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37664809662637548140079683 56497214493956322210119525)
            ·
              refine ⟨10593227717616810414397411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56497214493956322210119525 10593227717616810414397411)
              ·
                refine ⟨15889841576425215621596117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10593227717616810414397411 15889841576425215621596117)
                ·
                  refine ⟨372418161947465991131159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15889841576425215621596117 372418161947465991131159)
                  ·
                    rfl

theorem cell21_1631884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_1631884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631884 prefixEnd_1631884 := by exact prefixLift 1631884
  have htrace : WordTrace (prefixWord ++ tailWord_1631884) baseStart_1631884 baseEnd_1631884 := by
    simpa [prefixWord, tailWord_1631884, baseEnd_1631884] using wordTrace_append hprefix tailTrace_1631884
  have hstable : (prefixWord ++ tailWord_1631884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631884).length < 2 ^ (prefixWord ++ tailWord_1631884).sum := by decide
  have hdescent : baseEnd_1631884 < baseStart_1631884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631932 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 4]
def baseStart_1631932 : Nat := 118140960795 + 1631932 * 2 ^ 59
def prefixEnd_1631932 : Nat := 4983230072969 + 3 ^ 40 * 1631932 * 2
def baseEnd_1631932 : Nat := 372429116201428574331061

theorem tailTrace_1631932 : CollatzResearch.WordTrace tailWord_1631932 prefixEnd_1631932 372429116201428574331061 := by
  unfold tailWord_1631932
  simp only [CollatzResearch.WordTrace]
  refine ⟨29760724961898275320665025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39680966615864367094220033 29760724961898275320665025)
  ·
    refine ⟨22320543721423706490498769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29760724961898275320665025 22320543721423706490498769)
    ·
      refine ⟨16740407791067779867874077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22320543721423706490498769 16740407791067779867874077)
      ·
        refine ⟨6277652921650417450452779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16740407791067779867874077 6277652921650417450452779)
        ·
          refine ⟨9416479382475626175679169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6277652921650417450452779 9416479382475626175679169)
          ·
            refine ⟨7062359536856719631759377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9416479382475626175679169 7062359536856719631759377)
            ·
              refine ⟨5296769652642539723819533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7062359536856719631759377 5296769652642539723819533)
              ·
                refine ⟨1986288619740952396432325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5296769652642539723819533 1986288619740952396432325)
                ·
                  refine ⟨372429116201428574331061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1986288619740952396432325 372429116201428574331061)
                  ·
                    rfl

theorem cell21_1631932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_1631932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631932 prefixEnd_1631932 := by exact prefixLift 1631932
  have htrace : WordTrace (prefixWord ++ tailWord_1631932) baseStart_1631932 baseEnd_1631932 := by
    simpa [prefixWord, tailWord_1631932, baseEnd_1631932] using wordTrace_append hprefix tailTrace_1631932
  have hstable : (prefixWord ++ tailWord_1631932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631932).length < 2 ^ (prefixWord ++ tailWord_1631932).sum := by decide
  have hdescent : baseEnd_1631932 < baseStart_1631932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631938 : List Nat := [3, 5, 1, 2, 1, 1, 3, 5]
def baseStart_1631938 : Nat := 118140960795 + 1631938 * 2 ^ 59
def prefixEnd_1631938 : Nat := 4983230072969 + 3 ^ 40 * 1631938 * 2
def baseEnd_1631938 : Nat := 124143495161057965743683

theorem tailTrace_1631938 : CollatzResearch.WordTrace tailWord_1631938 prefixEnd_1631938 124143495161057965743683 := by
  unfold tailWord_1631938
  simp only [CollatzResearch.WordTrace]
  refine ⟨14880417190443703416512117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39681112507849875777365645 14880417190443703416512117)
  ·
    refine ⟨1395039111604097195298011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14880417190443703416512117 1395039111604097195298011)
    ·
      refine ⟨2092558667406145792947017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395039111604097195298011 2092558667406145792947017)
      ·
        refine ⟨1569419000554609344710263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2092558667406145792947017 1569419000554609344710263)
        ·
          refine ⟨2354128500831914017065395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1569419000554609344710263 2354128500831914017065395)
          ·
            refine ⟨3531192751247871025598093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354128500831914017065395 3531192751247871025598093)
            ·
              refine ⟨1324197281717951634599285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3531192751247871025598093 1324197281717951634599285)
              ·
                refine ⟨124143495161057965743683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1324197281717951634599285 124143495161057965743683)
                ·
                  rfl

theorem cell21_1631938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_1631938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631938 prefixEnd_1631938 := by exact prefixLift 1631938
  have htrace : WordTrace (prefixWord ++ tailWord_1631938) baseStart_1631938 baseEnd_1631938 := by
    simpa [prefixWord, tailWord_1631938, baseEnd_1631938] using wordTrace_append hprefix tailTrace_1631938
  have hstable : (prefixWord ++ tailWord_1631938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631938).length < 2 ^ (prefixWord ++ tailWord_1631938).sum := by decide
  have hdescent : baseEnd_1631938 < baseStart_1631938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631960 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_1631960 : Nat := 118140960795 + 1631960 * 2 ^ 59
def prefixEnd_1631960 : Nat := 4983230072969 + 3 ^ 40 * 1631960 * 2
def baseEnd_1631960 : Nat := 372435506182906747864337

theorem tailTrace_1631960 : CollatzResearch.WordTrace tailWord_1631960 prefixEnd_1631960 372435506182906747864337 := by
  unfold tailWord_1631960
  simp only [CollatzResearch.WordTrace]
  refine ⟨29761235583847555711674667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39681647445130074282232889 29761235583847555711674667)
  ·
    refine ⟨44641853375771333567512001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29761235583847555711674667 44641853375771333567512001)
    ·
      refine ⟨33481390031828500175634001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44641853375771333567512001 33481390031828500175634001)
      ·
        refine ⟨25111042523871375131725501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33481390031828500175634001 25111042523871375131725501)
        ·
          refine ⟨9416640946451765674397063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25111042523871375131725501 9416640946451765674397063)
          ·
            refine ⟨14124961419677648511595595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9416640946451765674397063 14124961419677648511595595)
            ·
              refine ⟨21187442129516472767393393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14124961419677648511595595 21187442129516472767393393)
              ·
                refine ⟨15890581597137354575545045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21187442129516472767393393 15890581597137354575545045)
                ·
                  refine ⟨372435506182906747864337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15890581597137354575545045 372435506182906747864337)
                  ·
                    rfl

theorem cell21_1631960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_1631960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631960 prefixEnd_1631960 := by exact prefixLift 1631960
  have htrace : WordTrace (prefixWord ++ tailWord_1631960) baseStart_1631960 baseEnd_1631960 := by
    simpa [prefixWord, tailWord_1631960, baseEnd_1631960] using wordTrace_append hprefix tailTrace_1631960
  have hstable : (prefixWord ++ tailWord_1631960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631960).length < 2 ^ (prefixWord ++ tailWord_1631960).sum := by decide
  have hdescent : baseEnd_1631960 < baseStart_1631960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1631991 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 4]
def baseStart_1631991 : Nat := 118140960795 + 1631991 * 2 ^ 59
def prefixEnd_1631991 : Nat := 4983230072969 + 3 ^ 40 * 1631991 * 2
def baseEnd_1631991 : Nat := 372442580805257582847607

theorem tailTrace_1631991 : CollatzResearch.WordTrace tailWord_1631991 prefixEnd_1631991 372442580805257582847607 := by
  unfold tailWord_1631991
  simp only [CollatzResearch.WordTrace]
  refine ⟨59523601830582803717727827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39682401220388535811818551 59523601830582803717727827)
  ·
    refine ⟨89285402745874205576591741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59523601830582803717727827 89285402745874205576591741)
    ·
      refine ⟨33482026029702827091221903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89285402745874205576591741 33482026029702827091221903)
      ·
        refine ⟨50223039044554240636832855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33482026029702827091221903 50223039044554240636832855)
        ·
          refine ⟨75334558566831360955249283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50223039044554240636832855 75334558566831360955249283)
          ·
            refine ⟨113001837850247041432873925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75334558566831360955249283 113001837850247041432873925)
            ·
              refine ⟨21187844596921320268663861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113001837850247041432873925 21187844596921320268663861)
              ·
                refine ⟨1986360430961373775187237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21187844596921320268663861 1986360430961373775187237)
                ·
                  refine ⟨372442580805257582847607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1986360430961373775187237 372442580805257582847607)
                  ·
                    rfl

theorem cell21_1631991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 4].length) (baseStart_1631991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1631991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1631991 prefixEnd_1631991 := by exact prefixLift 1631991
  have htrace : WordTrace (prefixWord ++ tailWord_1631991) baseStart_1631991 baseEnd_1631991 := by
    simpa [prefixWord, tailWord_1631991, baseEnd_1631991] using wordTrace_append hprefix tailTrace_1631991
  have hstable : (prefixWord ++ tailWord_1631991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1631991).length < 2 ^ (prefixWord ++ tailWord_1631991).sum := by decide
  have hdescent : baseEnd_1631991 < baseStart_1631991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1631991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632081 : List Nat := [1, 2, 2, 1, 5, 10]
def baseStart_1632081 : Nat := 118140960795 + 1632081 * 2 ^ 59
def prefixEnd_1632081 : Nat := 4983230072969 + 3 ^ 40 * 1632081 * 2
def baseEnd_1632081 : Nat := 13794930371534719494349

theorem tailTrace_1632081 : CollatzResearch.WordTrace tailWord_1632081 prefixEnd_1632081 13794930371534719494349 := by
  unfold tailWord_1632081
  simp only [CollatzResearch.WordTrace]
  refine ⟨59526884400256749088504097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39684589600171166059002731 59526884400256749088504097)
  ·
    refine ⟨44645163300192561816378073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59526884400256749088504097 44645163300192561816378073)
    ·
      refine ⟨33483872475144421362283555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44645163300192561816378073 33483872475144421362283555)
      ·
        refine ⟨50225808712716632043425333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33483872475144421362283555 50225808712716632043425333)
        ·
          refine ⟨4708669566817184254071125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50225808712716632043425333 4708669566817184254071125)
          ·
            refine ⟨13794930371534719494349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4708669566817184254071125 13794930371534719494349)
            ·
              rfl

theorem cell21_1632081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 10].length) (baseStart_1632081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632081 prefixEnd_1632081 := by exact prefixLift 1632081
  have htrace : WordTrace (prefixWord ++ tailWord_1632081) baseStart_1632081 baseEnd_1632081 := by
    simpa [prefixWord, tailWord_1632081, baseEnd_1632081] using wordTrace_append hprefix tailTrace_1632081
  have hstable : (prefixWord ++ tailWord_1632081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632081).length < 2 ^ (prefixWord ++ tailWord_1632081).sum := by decide
  have hdescent : baseEnd_1632081 < baseStart_1632081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632084 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1632084 : Nat := 118140960795 + 1632084 * 2 ^ 59
def prefixEnd_1632084 : Nat := 4983230072969 + 3 ^ 40 * 1632084 * 2
def baseEnd_1632084 : Nat := 372463804672310087797417

theorem tailTrace_1632084 : CollatzResearch.WordTrace tailWord_1632084 prefixEnd_1632084 372463804672310087797417 := by
  unfold tailWord_1632084
  simp only [CollatzResearch.WordTrace]
  refine ⟨29763496909622940300431653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39684662546163920400575537 29763496909622940300431653)
  ·
    refine ⟨5580655670554301306330935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29763496909622940300431653 5580655670554301306330935)
    ·
      refine ⟨8370983505831451959496403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5580655670554301306330935 8370983505831451959496403)
      ·
        refine ⟨12556475258747177939244605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8370983505831451959496403 12556475258747177939244605)
        ·
          refine ⟨4708678222030191727216727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12556475258747177939244605 4708678222030191727216727)
          ·
            refine ⟨7063017333045287590825091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4708678222030191727216727 7063017333045287590825091)
            ·
              refine ⟨10594525999567931386237637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063017333045287590825091 10594525999567931386237637)
              ·
                refine ⟨1986473624918987134919557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10594525999567931386237637 1986473624918987134919557)
                ·
                  refine ⟨372463804672310087797417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1986473624918987134919557 372463804672310087797417)
                  ·
                    rfl

theorem cell21_1632084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1632084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632084 prefixEnd_1632084 := by exact prefixLift 1632084
  have htrace : WordTrace (prefixWord ++ tailWord_1632084) baseStart_1632084 baseEnd_1632084 := by
    simpa [prefixWord, tailWord_1632084, baseEnd_1632084] using wordTrace_append hprefix tailTrace_1632084
  have hstable : (prefixWord ++ tailWord_1632084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632084).length < 2 ^ (prefixWord ++ tailWord_1632084).sum := by decide
  have hdescent : baseEnd_1632084 < baseStart_1632084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632146 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_1632146 : Nat := 118140960795 + 1632146 * 2 ^ 59
def prefixEnd_1632146 : Nat := 4983230072969 + 3 ^ 40 * 1632146 * 2
def baseEnd_1632146 : Nat := 372477953917011757763957

theorem tailTrace_1632146 : CollatzResearch.WordTrace tailWord_1632146 prefixEnd_1632146 372477953917011757763957 := by
  unfold tailWord_1632146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14882313786255316297405073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39686170096680843459746861 14882313786255316297405073)
  ·
    refine ⟨11161735339691487223053805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14882313786255316297405073 11161735339691487223053805)
    ·
      refine ⟨4185650752384307708645177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11161735339691487223053805 4185650752384307708645177)
      ·
        refine ⟨3139238064288230781483883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4185650752384307708645177 3139238064288230781483883)
        ·
          refine ⟨4708857096432346172225825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3139238064288230781483883 4708857096432346172225825)
          ·
            refine ⟨3531642822324259629169369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4708857096432346172225825 3531642822324259629169369)
            ·
              refine ⟨2648732116743194721877027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3531642822324259629169369 2648732116743194721877027)
              ·
                refine ⟨3973098175114792082815541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648732116743194721877027 3973098175114792082815541)
                ·
                  refine ⟨372477953917011757763957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3973098175114792082815541 372477953917011757763957)
                  ·
                    rfl

theorem cell21_1632146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_1632146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632146 prefixEnd_1632146 := by exact prefixLift 1632146
  have htrace : WordTrace (prefixWord ++ tailWord_1632146) baseStart_1632146 baseEnd_1632146 := by
    simpa [prefixWord, tailWord_1632146, baseEnd_1632146] using wordTrace_append hprefix tailTrace_1632146
  have hstable : (prefixWord ++ tailWord_1632146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632146).length < 2 ^ (prefixWord ++ tailWord_1632146).sum := by decide
  have hdescent : baseEnd_1632146 < baseStart_1632146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632264 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_1632264 : Nat := 118140960795 + 1632264 * 2 ^ 59
def prefixEnd_1632264 : Nat := 4983230072969 + 3 ^ 40 * 1632264 * 2
def baseEnd_1632264 : Nat := 372504883124669774797049

theorem tailTrace_1632264 : CollatzResearch.WordTrace tailWord_1632264 prefixEnd_1632264 372504883124669774797049 := by
  unfold tailWord_1632264
  simp only [CollatzResearch.WordTrace]
  refine ⟨29766779479296885671207923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39689039305729180894943897 29766779479296885671207923)
  ·
    refine ⟨44650169218945328506811885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29766779479296885671207923 44650169218945328506811885)
    ·
      refine ⟨16743813457104498190054457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44650169218945328506811885 16743813457104498190054457)
      ·
        refine ⟨12557860092828373642540843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16743813457104498190054457 12557860092828373642540843)
        ·
          refine ⟨18836790139242560463811265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12557860092828373642540843 18836790139242560463811265)
          ·
            refine ⟨14127592604431920347858449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18836790139242560463811265 14127592604431920347858449)
            ·
              refine ⟨10595694453323940260893837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14127592604431920347858449 10595694453323940260893837)
              ·
                refine ⟨3973385419996477597835189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10595694453323940260893837 3973385419996477597835189)
                ·
                  refine ⟨372504883124669774797049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3973385419996477597835189 372504883124669774797049)
                  ·
                    rfl

theorem cell21_1632264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_1632264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632264 prefixEnd_1632264 := by exact prefixLift 1632264
  have htrace : WordTrace (prefixWord ++ tailWord_1632264) baseStart_1632264 baseEnd_1632264 := by
    simpa [prefixWord, tailWord_1632264, baseEnd_1632264] using wordTrace_append hprefix tailTrace_1632264
  have hstable : (prefixWord ++ tailWord_1632264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632264).length < 2 ^ (prefixWord ++ tailWord_1632264).sum := by decide
  have hdescent : baseEnd_1632264 < baseStart_1632264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632298 : List Nat := [3, 1, 4, 1, 2, 1, 1, 5, 3]
def baseStart_1632298 : Nat := 118140960795 + 1632298 * 2 ^ 59
def prefixEnd_1632298 : Nat := 4983230072969 + 3 ^ 40 * 1632298 * 2
def baseEnd_1632298 : Nat := 372512642387893271230313

theorem tailTrace_1632298 : CollatzResearch.WordTrace tailWord_1632298 prefixEnd_1632298 372512642387893271230313 := by
  unfold tailWord_1632298
  simp only [CollatzResearch.WordTrace]
  refine ⟨14883699760117648787288387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39689866026980396766102365 14883699760117648787288387)
  ·
    refine ⟨22325549640176473180932581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14883699760117648787288387 22325549640176473180932581)
    ·
      refine ⟨4186040557533088721424859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22325549640176473180932581 4186040557533088721424859)
      ·
        refine ⟨6279060836299633082137289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186040557533088721424859 6279060836299633082137289)
        ·
          refine ⟨4709295627224724811602967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6279060836299633082137289 4709295627224724811602967)
          ·
            refine ⟨7063943440837087217404451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709295627224724811602967 7063943440837087217404451)
            ·
              refine ⟨10595915161255630826106677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063943440837087217404451 10595915161255630826106677)
              ·
                refine ⟨993367046367715389947501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10595915161255630826106677 993367046367715389947501)
                ·
                  refine ⟨372512642387893271230313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993367046367715389947501 372512642387893271230313)
                  ·
                    rfl

theorem cell21_1632298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_1632298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632298 prefixEnd_1632298 := by exact prefixLift 1632298
  have htrace : WordTrace (prefixWord ++ tailWord_1632298) baseStart_1632298 baseEnd_1632298 := by
    simpa [prefixWord, tailWord_1632298, baseEnd_1632298] using wordTrace_append hprefix tailTrace_1632298
  have hstable : (prefixWord ++ tailWord_1632298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632298).length < 2 ^ (prefixWord ++ tailWord_1632298).sum := by decide
  have hdescent : baseEnd_1632298 < baseStart_1632298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632374 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1632374 : Nat := 118140960795 + 1632374 * 2 ^ 59
def prefixEnd_1632374 : Nat := 4983230072969 + 3 ^ 40 * 1632374 * 2
def baseEnd_1632374 : Nat := 372529986623334027963491

theorem tailTrace_1632374 : CollatzResearch.WordTrace tailWord_1632374 prefixEnd_1632374 372529986623334027963491 := by
  unfold tailWord_1632374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3721098186762203758057511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39691713992130173419280117 3721098186762203758057511)
  ·
    refine ⟨5581647280143305637086267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3721098186762203758057511 5581647280143305637086267)
    ·
      refine ⟨8372470920214958455629401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5581647280143305637086267 8372470920214958455629401)
      ·
        refine ⟨6279353190161218841722051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8372470920214958455629401 6279353190161218841722051)
        ·
          refine ⟨9419029785241828262583077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279353190161218841722051 9419029785241828262583077)
          ·
            refine ⟨1766068084732842799234327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9419029785241828262583077 1766068084732842799234327)
            ·
              refine ⟨2649102127099264198851491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766068084732842799234327 2649102127099264198851491)
              ·
                refine ⟨3973653190648896298277237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649102127099264198851491 3973653190648896298277237)
                ·
                  refine ⟨372529986623334027963491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3973653190648896298277237 372529986623334027963491)
                  ·
                    rfl

theorem cell21_1632374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1632374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632374 prefixEnd_1632374 := by exact prefixLift 1632374
  have htrace : WordTrace (prefixWord ++ tailWord_1632374) baseStart_1632374 baseEnd_1632374 := by
    simpa [prefixWord, tailWord_1632374, baseEnd_1632374] using wordTrace_append hprefix tailTrace_1632374
  have hstable : (prefixWord ++ tailWord_1632374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632374).length < 2 ^ (prefixWord ++ tailWord_1632374).sum := by decide
  have hdescent : baseEnd_1632374 < baseStart_1632374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632450 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1632450 : Nat := 118140960795 + 1632450 * 2 ^ 59
def prefixEnd_1632450 : Nat := 4983230072969 + 3 ^ 40 * 1632450 * 2
def baseEnd_1632450 : Nat := 372547330858774784696669

theorem tailTrace_1632450 : CollatzResearch.WordTrace tailWord_1632450 prefixEnd_1632450 372547330858774784696669 := by
  unfold tailWord_1632450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14885085733979981277171701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39693561957279950072457869 14885085733979981277171701)
  ·
    refine ⟨1395476787560623244734847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14885085733979981277171701 1395476787560623244734847)
    ·
      refine ⟨2093215181340934867102271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395476787560623244734847 2093215181340934867102271)
      ·
        refine ⟨3139822772011402300653407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093215181340934867102271 3139822772011402300653407)
        ·
          refine ⟨4709734158017103450980111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3139822772011402300653407 4709734158017103450980111)
          ·
            refine ⟨7064601237025655176470167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709734158017103450980111 7064601237025655176470167)
            ·
              refine ⟨10596901855538482764705251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7064601237025655176470167 10596901855538482764705251)
              ·
                refine ⟨15895352783307724147057877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10596901855538482764705251 15895352783307724147057877)
                ·
                  refine ⟨372547330858774784696669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15895352783307724147057877 372547330858774784696669)
                  ·
                    rfl

theorem cell21_1632450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1632450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632450 prefixEnd_1632450 := by exact prefixLift 1632450
  have htrace : WordTrace (prefixWord ++ tailWord_1632450) baseStart_1632450 baseEnd_1632450 := by
    simpa [prefixWord, tailWord_1632450, baseEnd_1632450] using wordTrace_append hprefix tailTrace_1632450
  have hstable : (prefixWord ++ tailWord_1632450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632450).length < 2 ^ (prefixWord ++ tailWord_1632450).sum := by decide
  have hdescent : baseEnd_1632450 < baseStart_1632450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632492 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 5]
def baseStart_1632492 : Nat := 118140960795 + 1632492 * 2 ^ 59
def prefixEnd_1632492 : Nat := 4983230072969 + 3 ^ 40 * 1632492 * 2
def baseEnd_1632492 : Nat := 372556915830992044996583

theorem tailTrace_1632492 : CollatzResearch.WordTrace tailWord_1632492 prefixEnd_1632492 372556915830992044996583 := by
  unfold tailWord_1632492
  simp only [CollatzResearch.WordTrace]
  refine ⟨29770937400883883140857865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39694583201178510854477153 29770937400883883140857865)
  ·
    refine ⟨22328203050662912355643399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29770937400883883140857865 22328203050662912355643399)
    ·
      refine ⟨33492304575994368533465099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22328203050662912355643399 33492304575994368533465099)
      ·
        refine ⟨50238456863991552800197649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33492304575994368533465099 50238456863991552800197649)
        ·
          refine ⟨37678842647993664600148237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50238456863991552800197649 37678842647993664600148237)
          ·
            refine ⟨14129565992997624225055589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37678842647993664600148237 14129565992997624225055589)
            ·
              refine ⟨2649293623687054542197923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14129565992997624225055589 2649293623687054542197923)
              ·
                refine ⟨3973940435530581813296885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649293623687054542197923 3973940435530581813296885)
                ·
                  refine ⟨372556915830992044996583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3973940435530581813296885 372556915830992044996583)
                  ·
                    rfl

theorem cell21_1632492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_1632492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632492 prefixEnd_1632492 := by exact prefixLift 1632492
  have htrace : WordTrace (prefixWord ++ tailWord_1632492) baseStart_1632492 baseEnd_1632492 := by
    simpa [prefixWord, tailWord_1632492, baseEnd_1632492] using wordTrace_append hprefix tailTrace_1632492
  have hstable : (prefixWord ++ tailWord_1632492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632492).length < 2 ^ (prefixWord ++ tailWord_1632492).sum := by decide
  have hdescent : baseEnd_1632492 < baseStart_1632492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632557 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1632557 : Nat := 118140960795 + 1632557 * 2 ^ 59
def prefixEnd_1632557 : Nat := 4983230072969 + 3 ^ 40 * 1632557 * 2
def baseEnd_1632557 : Nat := 372571749716566376413117

theorem tailTrace_1632557 : CollatzResearch.WordTrace tailWord_1632557 prefixEnd_1632557 372571749716566376413117 := by
  unfold tailWord_1632557
  simp only [CollatzResearch.WordTrace]
  refine ⟨59544245546532282382831925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39696163697688188255221283 59544245546532282382831925)
  ·
    refine ⟨5582273019987401473390493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59544245546532282382831925 5582273019987401473390493)
    ·
      refine ⟨2093352382495275552521435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5582273019987401473390493 2093352382495275552521435)
      ·
        refine ⟨3140028573742913328782153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093352382495275552521435 3140028573742913328782153)
        ·
          refine ⟨2355021430307184996586615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3140028573742913328782153 2355021430307184996586615)
          ·
            refine ⟨3532532145460777494879923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355021430307184996586615 3532532145460777494879923)
            ·
              refine ⟨5298798218191166242319885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532532145460777494879923 5298798218191166242319885)
              ·
                refine ⟨1987049331821687340869957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5298798218191166242319885 1987049331821687340869957)
                ·
                  refine ⟨372571749716566376413117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1987049331821687340869957 372571749716566376413117)
                  ·
                    rfl

theorem cell21_1632557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1632557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632557 prefixEnd_1632557 := by exact prefixLift 1632557
  have htrace : WordTrace (prefixWord ++ tailWord_1632557) baseStart_1632557 baseEnd_1632557 := by
    simpa [prefixWord, tailWord_1632557, baseEnd_1632557] using wordTrace_append hprefix tailTrace_1632557
  have hstable : (prefixWord ++ tailWord_1632557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632557).length < 2 ^ (prefixWord ++ tailWord_1632557).sum := by decide
  have hdescent : baseEnd_1632557 < baseStart_1632557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632599 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 4]
def baseStart_1632599 : Nat := 118140960795 + 1632599 * 2 ^ 59
def prefixEnd_1632599 : Nat := 4983230072969 + 3 ^ 40 * 1632599 * 2
def baseEnd_1632599 : Nat := 372581334688783636713031

theorem tailTrace_1632599 : CollatzResearch.WordTrace tailWord_1632599 prefixEnd_1632599 372581334688783636713031 := by
  unfold tailWord_1632599
  simp only [CollatzResearch.WordTrace]
  refine ⟨59545777412380123555860851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39697184941586749037240567 59545777412380123555860851)
  ·
    refine ⟨89318666118570185333791277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59545777412380123555860851 89318666118570185333791277)
    ·
      refine ⟨33494499794463819500171729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89318666118570185333791277 33494499794463819500171729)
      ·
        refine ⟨25120874845847864625128797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33494499794463819500171729 25120874845847864625128797)
        ·
          refine ⟨9420328067192949234423299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25120874845847864625128797 9420328067192949234423299)
          ·
            refine ⟨14130492100789423851634949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9420328067192949234423299 14130492100789423851634949)
            ·
              refine ⟨2649467268898016972181553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14130492100789423851634949 2649467268898016972181553)
              ·
                refine ⟨1987100451673512729136165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649467268898016972181553 1987100451673512729136165)
                ·
                  refine ⟨372581334688783636713031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1987100451673512729136165 372581334688783636713031)
                  ·
                    rfl

theorem cell21_1632599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 4].length) (baseStart_1632599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632599 prefixEnd_1632599 := by exact prefixLift 1632599
  have htrace : WordTrace (prefixWord ++ tailWord_1632599) baseStart_1632599 baseEnd_1632599 := by
    simpa [prefixWord, tailWord_1632599, baseEnd_1632599] using wordTrace_append hprefix tailTrace_1632599
  have hstable : (prefixWord ++ tailWord_1632599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632599).length < 2 ^ (prefixWord ++ tailWord_1632599).sum := by decide
  have hdescent : baseEnd_1632599 < baseStart_1632599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632613 : List Nat := [1, 3, 1, 3, 1, 3, 3, 6]
def baseStart_1632613 : Nat := 118140960795 + 1632613 * 2 ^ 59
def prefixEnd_1632613 : Nat := 4983230072969 + 3 ^ 40 * 1632613 * 2
def baseEnd_1632613 : Nat := 124194843226507574493223

theorem tailTrace_1632613 : CollatzResearch.WordTrace tailWord_1632613 prefixEnd_1632613 124194843226507574493223 := by
  unfold tailWord_1632613
  simp only [CollatzResearch.WordTrace]
  refine ⟨59546288034329403946870493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39697525356219602631246995 59546288034329403946870493)
  ·
    refine ⟨22329858012873526480076435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59546288034329403946870493 22329858012873526480076435)
    ·
      refine ⟨33494787019310289720114653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22329858012873526480076435 33494787019310289720114653)
      ·
        refine ⟨12560545132241358645042995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33494787019310289720114653 12560545132241358645042995)
        ·
          refine ⟨18840817698362037967564493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12560545132241358645042995 18840817698362037967564493)
          ·
            refine ⟨7065306636885764237836685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18840817698362037967564493 7065306636885764237836685)
            ·
              refine ⟨2649489988832161589188757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7065306636885764237836685 2649489988832161589188757)
              ·
                refine ⟨124194843226507574493223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2649489988832161589188757 124194843226507574493223)
                ·
                  rfl

theorem cell21_1632613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 6].length) (baseStart_1632613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632613 prefixEnd_1632613 := by exact prefixLift 1632613
  have htrace : WordTrace (prefixWord ++ tailWord_1632613) baseStart_1632613 baseEnd_1632613 := by
    simpa [prefixWord, tailWord_1632613, baseEnd_1632613] using wordTrace_append hprefix tailTrace_1632613
  have hstable : (prefixWord ++ tailWord_1632613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632613).length < 2 ^ (prefixWord ++ tailWord_1632613).sum := by decide
  have hdescent : baseEnd_1632613 < baseStart_1632613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632627 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 5]
def baseStart_1632627 : Nat := 118140960795 + 1632627 * 2 ^ 59
def prefixEnd_1632627 : Nat := 4983230072969 + 3 ^ 40 * 1632627 * 2
def baseEnd_1632627 : Nat := 372587724670261810246307

theorem tailTrace_1632627 : CollatzResearch.WordTrace tailWord_1632627 prefixEnd_1632627 372587724670261810246307 := by
  unfold tailWord_1632627
  simp only [CollatzResearch.WordTrace]
  refine ⟨59546798656278684337880135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39697865770852456225253423 59546798656278684337880135)
  ·
    refine ⟨89320197984418026506820203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59546798656278684337880135 89320197984418026506820203)
    ·
      refine ⟨133980296976627039760230305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89320197984418026506820203 133980296976627039760230305)
      ·
        refine ⟨100485222732470279820172729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133980296976627039760230305 100485222732470279820172729)
        ·
          refine ⟨75363917049352709865129547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100485222732470279820172729 75363917049352709865129547)
          ·
            refine ⟨113045875574029064797694321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75363917049352709865129547 113045875574029064797694321)
            ·
              refine ⟨84784406680521798598270741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113045875574029064797694321 84784406680521798598270741)
              ·
                refine ⟨3974269063149459309293941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84784406680521798598270741 3974269063149459309293941)
                ·
                  refine ⟨372587724670261810246307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974269063149459309293941 372587724670261810246307)
                  ·
                    rfl

theorem cell21_1632627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_1632627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632627 prefixEnd_1632627 := by exact prefixLift 1632627
  have htrace : WordTrace (prefixWord ++ tailWord_1632627) baseStart_1632627 baseEnd_1632627 := by
    simpa [prefixWord, tailWord_1632627, baseEnd_1632627] using wordTrace_append hprefix tailTrace_1632627
  have hstable : (prefixWord ++ tailWord_1632627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632627).length < 2 ^ (prefixWord ++ tailWord_1632627).sum := by decide
  have hdescent : baseEnd_1632627 < baseStart_1632627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632650 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 4]
def baseStart_1632650 : Nat := 118140960795 + 1632650 * 2 ^ 59
def prefixEnd_1632650 : Nat := 4983230072969 + 3 ^ 40 * 1632650 * 2
def baseEnd_1632650 : Nat := 372592973583618881362927

theorem tailTrace_1632650 : CollatzResearch.WordTrace tailWord_1632650 prefixEnd_1632650 372592973583618881362927 := by
  unfold tailWord_1632650
  simp only [CollatzResearch.WordTrace]
  refine ⟨14886909383798839816491851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39698425023463572843978269 14886909383798839816491851)
  ·
    refine ⟨22330364075698259724737777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14886909383798839816491851 22330364075698259724737777)
    ·
      refine ⟨16747773056773694793553333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22330364075698259724737777 16747773056773694793553333)
      ·
        refine ⟨1570103724072533886895625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16747773056773694793553333 1570103724072533886895625)
        ·
          refine ⟨1177577793054400415171719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1570103724072533886895625 1177577793054400415171719)
          ·
            refine ⟨1766366689581600622757579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177577793054400415171719 1766366689581600622757579)
            ·
              refine ⟨2649550034372400934136369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766366689581600622757579 2649550034372400934136369)
              ·
                refine ⟨1987162525779300700602277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649550034372400934136369 1987162525779300700602277)
                ·
                  refine ⟨372592973583618881362927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1987162525779300700602277 372592973583618881362927)
                  ·
                    rfl

theorem cell21_1632650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_1632650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632650 prefixEnd_1632650 := by exact prefixLift 1632650
  have htrace : WordTrace (prefixWord ++ tailWord_1632650) baseStart_1632650 baseEnd_1632650 := by
    simpa [prefixWord, tailWord_1632650, baseEnd_1632650] using wordTrace_append hprefix tailTrace_1632650
  have hstable : (prefixWord ++ tailWord_1632650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632650).length < 2 ^ (prefixWord ++ tailWord_1632650).sum := by decide
  have hdescent : baseEnd_1632650 < baseStart_1632650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632689 : List Nat := [1, 2, 2, 4, 1, 3, 1, 7]
def baseStart_1632689 : Nat := 118140960795 + 1632689 * 2 ^ 59
def prefixEnd_1632689 : Nat := 4983230072969 + 3 ^ 40 * 1632689 * 2
def baseEnd_1632689 : Nat := 124200624638321160070949

theorem tailTrace_1632689 : CollatzResearch.WordTrace tailWord_1632689 prefixEnd_1632689 124200624638321160070949 := by
  unfold tailWord_1632689
  simp only [CollatzResearch.WordTrace]
  refine ⟨59549059982054068926637121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39699373321369379284424747 59549059982054068926637121)
  ·
    refine ⟨44661794986540551694977841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59549059982054068926637121 44661794986540551694977841)
    ·
      refine ⟨33496346239905413771233381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44661794986540551694977841 33496346239905413771233381)
      ·
        refine ⟨6280564919982265082106259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33496346239905413771233381 6280564919982265082106259)
        ·
          refine ⟨9420847379973397623159389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6280564919982265082106259 9420847379973397623159389)
          ·
            refine ⟨3532817767490024108684771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9420847379973397623159389 3532817767490024108684771)
            ·
              refine ⟨5299226651235036163027157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532817767490024108684771 5299226651235036163027157)
              ·
                refine ⟨124200624638321160070949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5299226651235036163027157 124200624638321160070949)
                ·
                  rfl

theorem cell21_1632689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 7].length) (baseStart_1632689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632689 prefixEnd_1632689 := by exact prefixLift 1632689
  have htrace : WordTrace (prefixWord ++ tailWord_1632689) baseStart_1632689 baseEnd_1632689 := by
    simpa [prefixWord, tailWord_1632689, baseEnd_1632689] using wordTrace_append hprefix tailTrace_1632689
  have hstable : (prefixWord ++ tailWord_1632689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632689).length < 2 ^ (prefixWord ++ tailWord_1632689).sum := by decide
  have hdescent : baseEnd_1632689 < baseStart_1632689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632748 : List Nat := [2, 2, 1, 1, 2, 1, 3, 9]
def baseStart_1632748 : Nat := 118140960795 + 1632748 * 2 ^ 59
def prefixEnd_1632748 : Nat := 4983230072969 + 3 ^ 40 * 1632748 * 2
def baseEnd_1632748 : Nat := 124205112839597496243131

theorem tailTrace_1632748 : CollatzResearch.WordTrace tailWord_1632748 prefixEnd_1632748 124205112839597496243131 := by
  unfold tailWord_1632748
  simp only [CollatzResearch.WordTrace]
  refine ⟨29775605944420161001517449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39700807925893548002023265 29775605944420161001517449)
  ·
    refine ⟨22331704458315120751138087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29775605944420161001517449 22331704458315120751138087)
    ·
      refine ⟨33497556687472681126707131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22331704458315120751138087 33497556687472681126707131)
      ·
        refine ⟨50246335031209021690060697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33497556687472681126707131 50246335031209021690060697)
        ·
          refine ⟨37684751273406766267545523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50246335031209021690060697 37684751273406766267545523)
          ·
            refine ⟨56527126910110149401318285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37684751273406766267545523 56527126910110149401318285)
            ·
              refine ⟨21197672591291306025494357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56527126910110149401318285 21197672591291306025494357)
              ·
                refine ⟨124205112839597496243131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21197672591291306025494357 124205112839597496243131)
                ·
                  rfl

theorem cell21_1632748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_1632748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632748 prefixEnd_1632748 := by exact prefixLift 1632748
  have htrace : WordTrace (prefixWord ++ tailWord_1632748) baseStart_1632748 baseEnd_1632748 := by
    simpa [prefixWord, tailWord_1632748, baseEnd_1632748] using wordTrace_append hprefix tailTrace_1632748
  have hstable : (prefixWord ++ tailWord_1632748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632748).length < 2 ^ (prefixWord ++ tailWord_1632748).sum := by decide
  have hdescent : baseEnd_1632748 < baseStart_1632748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632782 : List Nat := [4, 1, 1, 2, 3, 3, 1, 6]
def baseStart_1632782 : Nat := 118140960795 + 1632782 * 2 ^ 59
def prefixEnd_1632782 : Nat := 4983230072969 + 3 ^ 40 * 1632782 * 2
def baseEnd_1632782 : Nat := 124207699260671995054219

theorem tailTrace_1632782 : CollatzResearch.WordTrace tailWord_1632782 prefixEnd_1632782 124207699260671995054219 := by
  unfold tailWord_1632782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7444056496339643226221575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39701634647144763873181733 7444056496339643226221575)
  ·
    refine ⟨11166084744509464839332363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7444056496339643226221575 11166084744509464839332363)
    ·
      refine ⟨16749127116764197258998545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11166084744509464839332363 16749127116764197258998545)
      ·
        refine ⟨12561845337573147944248909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16749127116764197258998545 12561845337573147944248909)
        ·
          refine ⟨4710692001589930479093341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12561845337573147944248909 4710692001589930479093341)
          ·
            refine ⟨1766509500596223929660003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4710692001589930479093341 1766509500596223929660003)
            ·
              refine ⟨2649764250894335894490005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766509500596223929660003 2649764250894335894490005)
              ·
                refine ⟨124207699260671995054219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2649764250894335894490005 124207699260671995054219)
                ·
                  rfl

theorem cell21_1632782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_1632782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632782 prefixEnd_1632782 := by exact prefixLift 1632782
  have htrace : WordTrace (prefixWord ++ tailWord_1632782) baseStart_1632782 baseEnd_1632782 := by
    simpa [prefixWord, tailWord_1632782, baseEnd_1632782] using wordTrace_append hprefix tailTrace_1632782
  have hstable : (prefixWord ++ tailWord_1632782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632782).length < 2 ^ (prefixWord ++ tailWord_1632782).sum := by decide
  have hdescent : baseEnd_1632782 < baseStart_1632782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632796 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 5]
def baseStart_1632796 : Nat := 118140960795 + 1632796 * 2 ^ 59
def prefixEnd_1632796 : Nat := 4983230072969 + 3 ^ 40 * 1632796 * 2
def baseEnd_1632796 : Nat := 372626292772755071929295

theorem tailTrace_1632796 : CollatzResearch.WordTrace tailWord_1632796 prefixEnd_1632796 372626292772755071929295 := by
  unfold tailWord_1632796
  simp only [CollatzResearch.WordTrace]
  refine ⟨29776481296333213100391121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39701975061777617467188161 29776481296333213100391121)
  ·
    refine ⟨22332360972249909825293341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29776481296333213100391121 22332360972249909825293341)
    ·
      refine ⟨8374635364593716184485003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22332360972249909825293341 8374635364593716184485003)
      ·
        refine ⟨12561953046890574276727505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8374635364593716184485003 12561953046890574276727505)
        ·
          refine ⟨9421464785167930707545629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12561953046890574276727505 9421464785167930707545629)
          ·
            refine ⟨3533049294437974015329611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9421464785167930707545629 3533049294437974015329611)
            ·
              refine ⟨5299573941656961022994417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533049294437974015329611 5299573941656961022994417)
              ·
                refine ⟨3974680456242720767245813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5299573941656961022994417 3974680456242720767245813)
                ·
                  refine ⟨372626292772755071929295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974680456242720767245813 372626292772755071929295)
                  ·
                    rfl

theorem cell21_1632796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_1632796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632796 prefixEnd_1632796 := by exact prefixLift 1632796
  have htrace : WordTrace (prefixWord ++ tailWord_1632796) baseStart_1632796 baseEnd_1632796 := by
    simpa [prefixWord, tailWord_1632796, baseEnd_1632796] using wordTrace_append hprefix tailTrace_1632796
  have hstable : (prefixWord ++ tailWord_1632796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632796).length < 2 ^ (prefixWord ++ tailWord_1632796).sum := by decide
  have hdescent : baseEnd_1632796 < baseStart_1632796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632824 : List Nat := [2, 1, 2, 1, 4, 1, 10]
def baseStart_1632824 : Nat := 118140960795 + 1632824 * 2 ^ 59
def prefixEnd_1632824 : Nat := 4983230072969 + 3 ^ 40 * 1632824 * 2
def baseEnd_1632824 : Nat := 41403631417137027273619

theorem tailTrace_1632824 : CollatzResearch.WordTrace tailWord_1632824 prefixEnd_1632824 41403631417137027273619 := by
  unfold tailWord_1632824
  simp only [CollatzResearch.WordTrace]
  refine ⟨29776991918282493491400763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39702655891043324655201017 29776991918282493491400763)
  ·
    refine ⟨44665487877423740237101145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29776991918282493491400763 44665487877423740237101145)
    ·
      refine ⟨33499115908067805177825859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44665487877423740237101145 33499115908067805177825859)
      ·
        refine ⟨50248673862101707766738789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33499115908067805177825859 50248673862101707766738789)
        ·
          refine ⟨9421626349144070206263523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50248673862101707766738789 9421626349144070206263523)
          ·
            refine ⟨14132439523716105309395285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9421626349144070206263523 14132439523716105309395285)
            ·
              refine ⟨41403631417137027273619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14132439523716105309395285 41403631417137027273619)
              ·
                rfl

theorem cell21_1632824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 10].length) (baseStart_1632824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632824 prefixEnd_1632824 := by exact prefixLift 1632824
  have htrace : WordTrace (prefixWord ++ tailWord_1632824) baseStart_1632824 baseEnd_1632824 := by
    simpa [prefixWord, tailWord_1632824, baseEnd_1632824] using wordTrace_append hprefix tailTrace_1632824
  have hstable : (prefixWord ++ tailWord_1632824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632824).length < 2 ^ (prefixWord ++ tailWord_1632824).sum := by decide
  have hdescent : baseEnd_1632824 < baseStart_1632824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632830 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_1632830 : Nat := 118140960795 + 1632830 * 2 ^ 59
def prefixEnd_1632830 : Nat := 4983230072969 + 3 ^ 40 * 1632830 * 2
def baseEnd_1632830 : Nat := 372634052035978568362559

theorem tailTrace_1632830 : CollatzResearch.WordTrace tailWord_1632830 prefixEnd_1632830 372634052035978568362559 := by
  unfold tailWord_1632830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7444275334317906250939993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39702801783028833338346629 7444275334317906250939993)
  ·
    refine ⟨5583206500738429688204995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7444275334317906250939993 5583206500738429688204995)
    ·
      refine ⟨8374809751107644532307493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5583206500738429688204995 8374809751107644532307493)
      ·
        refine ⟨1570276828332683349807655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8374809751107644532307493 1570276828332683349807655)
        ·
          refine ⟨2355415242499025024711483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570276828332683349807655 2355415242499025024711483)
          ·
            refine ⟨3533122863748537537067225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355415242499025024711483 3533122863748537537067225)
            ·
              refine ⟨2649842147811403152800419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3533122863748537537067225 2649842147811403152800419)
              ·
                refine ⟨3974763221717104729200629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649842147811403152800419 3974763221717104729200629)
                ·
                  refine ⟨372634052035978568362559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974763221717104729200629 372634052035978568362559)
                  ·
                    rfl

theorem cell21_1632830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_1632830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632830 prefixEnd_1632830 := by exact prefixLift 1632830
  have htrace : WordTrace (prefixWord ++ tailWord_1632830) baseStart_1632830 baseEnd_1632830 := by
    simpa [prefixWord, tailWord_1632830, baseEnd_1632830] using wordTrace_append hprefix tailTrace_1632830
  have hstable : (prefixWord ++ tailWord_1632830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632830).length < 2 ^ (prefixWord ++ tailWord_1632830).sum := by decide
  have hdescent : baseEnd_1632830 < baseStart_1632830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1632855 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 5]
def baseStart_1632855 : Nat := 118140960795 + 1632855 * 2 ^ 59
def prefixEnd_1632855 : Nat := 4983230072969 + 3 ^ 40 * 1632855 * 2
def baseEnd_1632855 : Nat := 372639757376584080445841

theorem tailTrace_1632855 : CollatzResearch.WordTrace tailWord_1632855 prefixEnd_1632855 372639757376584080445841 := by
  unfold tailWord_1632855
  simp only [CollatzResearch.WordTrace]
  refine ⟨59555114499452679277180019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39703409666301786184786679 59555114499452679277180019)
  ·
    refine ⟨89332671749179018915770029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59555114499452679277180019 89332671749179018915770029)
    ·
      refine ⟨33499751905942132093413761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89332671749179018915770029 33499751905942132093413761)
      ·
        refine ⟨25124813929456599070060321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33499751905942132093413761 25124813929456599070060321)
        ·
          refine ⟨18843610447092449302545241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25124813929456599070060321 18843610447092449302545241)
          ·
            refine ⟨14132707835319336976908931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18843610447092449302545241 14132707835319336976908931)
            ·
              refine ⟨21199061752979005465363397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14132707835319336976908931 21199061752979005465363397)
              ·
                refine ⟨3974824078683563524755637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21199061752979005465363397 3974824078683563524755637)
                ·
                  refine ⟨372639757376584080445841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974824078683563524755637 372639757376584080445841)
                  ·
                    rfl

theorem cell21_1632855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_1632855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1632855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1632855 prefixEnd_1632855 := by exact prefixLift 1632855
  have htrace : WordTrace (prefixWord ++ tailWord_1632855) baseStart_1632855 baseEnd_1632855 := by
    simpa [prefixWord, tailWord_1632855, baseEnd_1632855] using wordTrace_append hprefix tailTrace_1632855
  have hstable : (prefixWord ++ tailWord_1632855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1632855).length < 2 ^ (prefixWord ++ tailWord_1632855).sum := by decide
  have hdescent : baseEnd_1632855 < baseStart_1632855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1632855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633007 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 5]
def baseStart_1633007 : Nat := 118140960795 + 1633007 * 2 ^ 59
def prefixEnd_1633007 : Nat := 4983230072969 + 3 ^ 40 * 1633007 * 2
def baseEnd_1633007 : Nat := 372674445847465593912197

theorem tailTrace_1633007 : CollatzResearch.WordTrace tailWord_1633007 prefixEnd_1633007 372674445847465593912197 := by
  unfold tailWord_1633007
  simp only [CollatzResearch.WordTrace]
  refine ⟨59560658394902009236713275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39707105596601339491142183 59560658394902009236713275)
  ·
    refine ⟨89340987592353013855069913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59560658394902009236713275 89340987592353013855069913)
    ·
      refine ⟨67005740694264760391302435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89340987592353013855069913 67005740694264760391302435)
      ·
        refine ⟨100508611041397140586953653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67005740694264760391302435 100508611041397140586953653)
        ·
          refine ⟨9422682285130981930026905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100508611041397140586953653 9422682285130981930026905)
          ·
            refine ⟨7067011713848236447520179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9422682285130981930026905 7067011713848236447520179)
            ·
              refine ⟨10600517570772354671280269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7067011713848236447520179 10600517570772354671280269)
              ·
                refine ⟨3975194089039633001730101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10600517570772354671280269 3975194089039633001730101)
                ·
                  refine ⟨372674445847465593912197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3975194089039633001730101 372674445847465593912197)
                  ·
                    rfl

theorem cell21_1633007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_1633007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633007 prefixEnd_1633007 := by exact prefixLift 1633007
  have htrace : WordTrace (prefixWord ++ tailWord_1633007) baseStart_1633007 baseEnd_1633007 := by
    simpa [prefixWord, tailWord_1633007, baseEnd_1633007] using wordTrace_append hprefix tailTrace_1633007
  have hstable : (prefixWord ++ tailWord_1633007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633007).length < 2 ^ (prefixWord ++ tailWord_1633007).sum := by decide
  have hdescent : baseEnd_1633007 < baseStart_1633007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633052 : List Nat := [2, 2, 3, 1, 1, 3, 9]
def baseStart_1633052 : Nat := 118140960795 + 1633052 * 2 ^ 59
def prefixEnd_1633052 : Nat := 4983230072969 + 3 ^ 40 * 1633052 * 2
def baseEnd_1633052 : Nat := 41409412828950612851345

theorem tailTrace_1633052 : CollatzResearch.WordTrace tailWord_1633052 prefixEnd_1633052 41409412828950612851345 := by
  unfold tailWord_1633052
  simp only [CollatzResearch.WordTrace]
  refine ⟨29781149839869490961050705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39708199786492654614734273 29781149839869490961050705)
  ·
    refine ⟨22335862379902118220788029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29781149839869490961050705 22335862379902118220788029)
    ·
      refine ⟨8375948392463294332795511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22335862379902118220788029 8375948392463294332795511)
      ·
        refine ⟨12563922588694941499193267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8375948392463294332795511 12563922588694941499193267)
        ·
          refine ⟨18845883883042412248789901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12563922588694941499193267 18845883883042412248789901)
          ·
            refine ⟨7067206456140904593296213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18845883883042412248789901 7067206456140904593296213)
            ·
              refine ⟨41409412828950612851345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7067206456140904593296213 41409412828950612851345)
              ·
                rfl

theorem cell21_1633052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 9].length) (baseStart_1633052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633052 prefixEnd_1633052 := by exact prefixLift 1633052
  have htrace : WordTrace (prefixWord ++ tailWord_1633052) baseStart_1633052 baseEnd_1633052 := by
    simpa [prefixWord, tailWord_1633052, baseEnd_1633052] using wordTrace_append hprefix tailTrace_1633052
  have hstable : (prefixWord ++ tailWord_1633052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633052).length < 2 ^ (prefixWord ++ tailWord_1633052).sum := by decide
  have hdescent : baseEnd_1633052 < baseStart_1633052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633058 : List Nat := [3, 3, 1, 1, 2, 3, 3, 2, 3]
def baseStart_1633058 : Nat := 118140960795 + 1633058 * 2 ^ 59
def prefixEnd_1633058 : Nat := 4983230072969 + 3 ^ 40 * 1633058 * 2
def baseEnd_1633058 : Nat := 372686084742300838562093

theorem tailTrace_1633058 : CollatzResearch.WordTrace tailWord_1633058 prefixEnd_1633058 372686084742300838562093 := by
  unfold tailWord_1633058
  simp only [CollatzResearch.WordTrace]
  refine ⟨14890629629429311236704957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39708345678478163297879885 14890629629429311236704957)
  ·
    refine ⟨5583986111035991713764359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14890629629429311236704957 5583986111035991713764359)
    ·
      refine ⟨8375979166553987570646539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5583986111035991713764359 8375979166553987570646539)
      ·
        refine ⟨12563968749830981355969809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8375979166553987570646539 12563968749830981355969809)
        ·
          refine ⟨9422976562373236016977357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12563968749830981355969809 9422976562373236016977357)
          ·
            refine ⟨3533616210889963506366509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9422976562373236016977357 3533616210889963506366509)
            ·
              refine ⟨1325106079083736314887441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3533616210889963506366509 1325106079083736314887441)
              ·
                refine ⟨993829559312802236165581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325106079083736314887441 993829559312802236165581)
                ·
                  refine ⟨372686084742300838562093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993829559312802236165581 372686084742300838562093)
                  ·
                    rfl

theorem cell21_1633058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_1633058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633058 prefixEnd_1633058 := by exact prefixLift 1633058
  have htrace : WordTrace (prefixWord ++ tailWord_1633058) baseStart_1633058 baseEnd_1633058 := by
    simpa [prefixWord, tailWord_1633058, baseEnd_1633058] using wordTrace_append hprefix tailTrace_1633058
  have hstable : (prefixWord ++ tailWord_1633058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633058).length < 2 ^ (prefixWord ++ tailWord_1633058).sum := by decide
  have hdescent : baseEnd_1633058 < baseStart_1633058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633114 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_1633114 : Nat := 118140960795 + 1633114 * 2 ^ 59
def prefixEnd_1633114 : Nat := 4983230072969 + 3 ^ 40 * 1633114 * 2
def baseEnd_1633114 : Nat := 372698864705257185628645

theorem tailTrace_1633114 : CollatzResearch.WordTrace tailWord_1633114 prefixEnd_1633114 372698864705257185628645 := by
  unfold tailWord_1633114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14891140251378591627714599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39709707337009577673905597 14891140251378591627714599)
  ·
    refine ⟨22336710377067887441571899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14891140251378591627714599 22336710377067887441571899)
    ·
      refine ⟨33505065565601831162357849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22336710377067887441571899 33505065565601831162357849)
      ·
        refine ⟨25128799174201373371768387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33505065565601831162357849 25128799174201373371768387)
        ·
          refine ⟨37693198761302060057652581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25128799174201373371768387 37693198761302060057652581)
          ·
            refine ⟨7067474767744136260809859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37693198761302060057652581 7067474767744136260809859)
            ·
              refine ⟨10601212151616204391214789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7067474767744136260809859 10601212151616204391214789)
              ·
                refine ⟨1987727278428038323352773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10601212151616204391214789 1987727278428038323352773)
                ·
                  refine ⟨372698864705257185628645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1987727278428038323352773 372698864705257185628645)
                  ·
                    rfl

theorem cell21_1633114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_1633114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633114 prefixEnd_1633114 := by exact prefixLift 1633114
  have htrace : WordTrace (prefixWord ++ tailWord_1633114) baseStart_1633114 baseEnd_1633114 := by
    simpa [prefixWord, tailWord_1633114, baseEnd_1633114] using wordTrace_append hprefix tailTrace_1633114
  have hstable : (prefixWord ++ tailWord_1633114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633114).length < 2 ^ (prefixWord ++ tailWord_1633114).sum := by decide
  have hdescent : baseEnd_1633114 < baseStart_1633114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633145 : List Nat := [1, 2, 1, 3, 2, 4, 3, 5]
def baseStart_1633145 : Nat := 118140960795 + 1633145 * 2 ^ 59
def prefixEnd_1633145 : Nat := 4983230072969 + 3 ^ 40 * 1633145 * 2
def baseEnd_1633145 : Nat := 124235313109202673537305

theorem tailTrace_1633145 : CollatzResearch.WordTrace tailWord_1633145 prefixEnd_1633145 124235313109202673537305 := by
  unfold tailWord_1633145
  simp only [CollatzResearch.WordTrace]
  refine ⟨59565691668402058805236889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39710461112268039203491259 59565691668402058805236889)
  ·
    refine ⟨44674268751301544103927667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59565691668402058805236889 44674268751301544103927667)
    ·
      refine ⟨67011403126952316155891501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44674268751301544103927667 67011403126952316155891501)
      ·
        refine ⟨25129276172607118558459313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67011403126952316155891501 25129276172607118558459313)
        ·
          refine ⟨18846957129455338918844485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25129276172607118558459313 18846957129455338918844485)
          ·
            refine ⟨3533804461772876047283341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18846957129455338918844485 3533804461772876047283341)
            ·
              refine ⟨1325176673164828517731253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3533804461772876047283341 1325176673164828517731253)
              ·
                refine ⟨124235313109202673537305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1325176673164828517731253 124235313109202673537305)
                ·
                  rfl

theorem cell21_1633145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 5].length) (baseStart_1633145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633145 prefixEnd_1633145 := by exact prefixLift 1633145
  have htrace : WordTrace (prefixWord ++ tailWord_1633145) baseStart_1633145 baseEnd_1633145 := by
    simpa [prefixWord, tailWord_1633145, baseEnd_1633145] using wordTrace_append hprefix tailTrace_1633145
  have hstable : (prefixWord ++ tailWord_1633145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633145).length < 2 ^ (prefixWord ++ tailWord_1633145).sum := by decide
  have hdescent : baseEnd_1633145 < baseStart_1633145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633238 : List Nat := [5, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1633238 : Nat := 118140960795 + 1633238 * 2 ^ 59
def prefixEnd_1633238 : Nat := 4983230072969 + 3 ^ 40 * 1633238 * 2
def baseEnd_1633238 : Nat := 124242387731553508520575

theorem tailTrace_1633238 : CollatzResearch.WordTrace tailWord_1633238 prefixEnd_1633238 124242387731553508520575 := by
  unfold tailWord_1633238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3723067728566570980523273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39712722438043423792248245 3723067728566570980523273)
  ·
    refine ⟨2792300796424928235392455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3723067728566570980523273 2792300796424928235392455)
    ·
      refine ⟨4188451194637392353088683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2792300796424928235392455 4188451194637392353088683)
      ·
        refine ⟨6282676791956088529633025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4188451194637392353088683 6282676791956088529633025)
        ·
          refine ⟨4712007593967066397224769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6282676791956088529633025 4712007593967066397224769)
          ·
            refine ⟨3534005695475299797918577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4712007593967066397224769 3534005695475299797918577)
            ·
              refine ⟨2650504271606474848438933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3534005695475299797918577 2650504271606474848438933)
              ·
                refine ⟨124242387731553508520575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2650504271606474848438933 124242387731553508520575)
                ·
                  rfl

theorem cell21_1633238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1633238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633238 prefixEnd_1633238 := by exact prefixLift 1633238
  have htrace : WordTrace (prefixWord ++ tailWord_1633238) baseStart_1633238 baseEnd_1633238 := by
    simpa [prefixWord, tailWord_1633238, baseEnd_1633238] using wordTrace_append hprefix tailTrace_1633238
  have hstable : (prefixWord ++ tailWord_1633238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633238).length < 2 ^ (prefixWord ++ tailWord_1633238).sum := by decide
  have hdescent : baseEnd_1633238 < baseStart_1633238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633311 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 5]
def baseStart_1633311 : Nat := 118140960795 + 1633311 * 2 ^ 59
def prefixEnd_1633311 : Nat := 4983230072969 + 3 ^ 40 * 1633311 * 2
def baseEnd_1633311 : Nat := 372743822789228620844909

theorem tailTrace_1633311 : CollatzResearch.WordTrace tailWord_1633311 prefixEnd_1633311 372743822789228620844909 := by
  unfold tailWord_1633311
  simp only [CollatzResearch.WordTrace]
  refine ⟨59571746185800669155779787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39714497457200446103853191 59571746185800669155779787)
  ·
    refine ⟨89357619278701003733669681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59571746185800669155779787 89357619278701003733669681)
    ·
      refine ⟨67018214459025752800252261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89357619278701003733669681 67018214459025752800252261)
      ·
        refine ⟨12565915211067328650047299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67018214459025752800252261 12565915211067328650047299)
        ·
          refine ⟨18848872816600992975070949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12565915211067328650047299 18848872816600992975070949)
          ·
            refine ⟨3534163653112686182825803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18848872816600992975070949 3534163653112686182825803)
            ·
              refine ⟨5301245479669029274238705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3534163653112686182825803 5301245479669029274238705)
              ·
                refine ⟨3975934109751771955679029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5301245479669029274238705 3975934109751771955679029)
                ·
                  refine ⟨372743822789228620844909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3975934109751771955679029 372743822789228620844909)
                  ·
                    rfl

theorem cell21_1633311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 5].length) (baseStart_1633311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633311 prefixEnd_1633311 := by exact prefixLift 1633311
  have htrace : WordTrace (prefixWord ++ tailWord_1633311) baseStart_1633311 baseEnd_1633311 := by
    simpa [prefixWord, tailWord_1633311, baseEnd_1633311] using wordTrace_append hprefix tailTrace_1633311
  have hstable : (prefixWord ++ tailWord_1633311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633311).length < 2 ^ (prefixWord ++ tailWord_1633311).sum := by decide
  have hdescent : baseEnd_1633311 < baseStart_1633311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633328 : List Nat := [2, 1, 1, 1, 2, 4, 4, 3, 3]
def baseStart_1633328 : Nat := 118140960795 + 1633328 * 2 ^ 59
def prefixEnd_1633328 : Nat := 4983230072969 + 3 ^ 40 * 1633328 * 2
def baseEnd_1633328 : Nat := 372747702420840369061541

theorem tailTrace_1633328 : CollatzResearch.WordTrace tailWord_1633328 prefixEnd_1633328 372747702420840369061541 := by
  unfold tailWord_1633328
  simp only [CollatzResearch.WordTrace]
  refine ⟨29786183113369540529574319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39714910817826054039432425 29786183113369540529574319)
  ·
    refine ⟨44679274670054310794361479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29786183113369540529574319 44679274670054310794361479)
    ·
      refine ⟨67018912005081466191542219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44679274670054310794361479 67018912005081466191542219)
      ·
        refine ⟨100528368007622199287313329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67018912005081466191542219 100528368007622199287313329)
        ·
          refine ⟨75396276005716649465484997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100528368007622199287313329 75396276005716649465484997)
          ·
            refine ⟨14136801751071871774778437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75396276005716649465484997 14136801751071871774778437)
            ·
              refine ⟨2650650328325975957770957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14136801751071871774778437 2650650328325975957770957)
              ·
                refine ⟨993993873122240984164109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2650650328325975957770957 993993873122240984164109)
                ·
                  refine ⟨372747702420840369061541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993993873122240984164109 372747702420840369061541)
                  ·
                    rfl

theorem cell21_1633328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 3].length) (baseStart_1633328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633328 prefixEnd_1633328 := by exact prefixLift 1633328
  have htrace : WordTrace (prefixWord ++ tailWord_1633328) baseStart_1633328 baseEnd_1633328 := by
    simpa [prefixWord, tailWord_1633328, baseEnd_1633328] using wordTrace_append hprefix tailTrace_1633328
  have hstable : (prefixWord ++ tailWord_1633328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633328).length < 2 ^ (prefixWord ++ tailWord_1633328).sum := by decide
  have hdescent : baseEnd_1633328 < baseStart_1633328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633370 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_1633370 : Nat := 118140960795 + 1633370 * 2 ^ 59
def prefixEnd_1633370 : Nat := 4983230072969 + 3 ^ 40 * 1633370 * 2
def baseEnd_1633370 : Nat := 372757287393057629361455

theorem tailTrace_1633370 : CollatzResearch.WordTrace tailWord_1633370 prefixEnd_1633370 372757287393057629361455 := by
  unfold tailWord_1633370
  simp only [CollatzResearch.WordTrace]
  refine ⟨14893474523146730558044391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39715932061724614821451709 14893474523146730558044391)
  ·
    refine ⟨22340211784720095837066587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14893474523146730558044391 22340211784720095837066587)
    ·
      refine ⟨33510317677080143755599881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22340211784720095837066587 33510317677080143755599881)
      ·
        refine ⟨25132738257810107816699911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33510317677080143755599881 25132738257810107816699911)
        ·
          refine ⟨37699107386715161725049867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25132738257810107816699911 37699107386715161725049867)
          ·
            refine ⟨56548661080072742587574801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37699107386715161725049867 56548661080072742587574801)
            ·
              refine ⟨42411495810054556940681101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56548661080072742587574801 42411495810054556940681101)
              ·
                refine ⟨15904310928770458852755413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42411495810054556940681101 15904310928770458852755413)
                ·
                  refine ⟨372757287393057629361455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15904310928770458852755413 372757287393057629361455)
                  ·
                    rfl

theorem cell21_1633370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_1633370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633370 prefixEnd_1633370 := by exact prefixLift 1633370
  have htrace : WordTrace (prefixWord ++ tailWord_1633370) baseStart_1633370 baseEnd_1633370 := by
    simpa [prefixWord, tailWord_1633370, baseEnd_1633370] using wordTrace_append hprefix tailTrace_1633370
  have hstable : (prefixWord ++ tailWord_1633370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633370).length < 2 ^ (prefixWord ++ tailWord_1633370).sum := by decide
  have hdescent : baseEnd_1633370 < baseStart_1633370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633418 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_1633418 : Nat := 118140960795 + 1633418 * 2 ^ 59
def prefixEnd_1633418 : Nat := 4983230072969 + 3 ^ 40 * 1633418 * 2
def baseEnd_1633418 : Nat := 372768241647020212561357

theorem tailTrace_1633418 : CollatzResearch.WordTrace tailWord_1633418 prefixEnd_1633418 372768241647020212561357 := by
  unfold tailWord_1633418
  simp only [CollatzResearch.WordTrace]
  refine ⟨14893912199103256607481227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39717099197608684286616605 14893912199103256607481227)
  ·
    refine ⟨22340868298654884911221841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14893912199103256607481227 22340868298654884911221841)
    ·
      refine ⟨16755651223991163683416381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22340868298654884911221841 16755651223991163683416381)
      ·
        refine ⟨6283369208996686381281143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16755651223991163683416381 6283369208996686381281143)
        ·
          refine ⟨9425053813495029571921715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6283369208996686381281143 9425053813495029571921715)
          ·
            refine ⟨14137580720242544357882573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9425053813495029571921715 14137580720242544357882573)
            ·
              refine ⟨5301592770090954134205965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14137580720242544357882573 5301592770090954134205965)
              ·
                refine ⟨1988097288784107800327237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5301592770090954134205965 1988097288784107800327237)
                ·
                  refine ⟨372768241647020212561357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1988097288784107800327237 372768241647020212561357)
                  ·
                    rfl

theorem cell21_1633418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_1633418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633418 prefixEnd_1633418 := by exact prefixLift 1633418
  have htrace : WordTrace (prefixWord ++ tailWord_1633418) baseStart_1633418 baseEnd_1633418 := by
    simpa [prefixWord, tailWord_1633418, baseEnd_1633418] using wordTrace_append hprefix tailTrace_1633418
  have hstable : (prefixWord ++ tailWord_1633418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633418).length < 2 ^ (prefixWord ++ tailWord_1633418).sum := by decide
  have hdescent : baseEnd_1633418 < baseStart_1633418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633432 : List Nat := [2, 1, 2, 4, 2, 1, 2, 7]
def baseStart_1633432 : Nat := 118140960795 + 1633432 * 2 ^ 59
def prefixEnd_1633432 : Nat := 4983230072969 + 3 ^ 40 * 1633432 * 2
def baseEnd_1633432 : Nat := 124257145545919766442665

theorem tailTrace_1633432 : CollatzResearch.WordTrace tailWord_1633432 prefixEnd_1633432 124257145545919766442665 := by
  unfold tailWord_1633432
  simp only [CollatzResearch.WordTrace]
  refine ⟨29788079709181153410467275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39717439612241537880623033 29788079709181153410467275)
  ·
    refine ⟨44682119563771730115700913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29788079709181153410467275 44682119563771730115700913)
    ·
      refine ⟨33511589672828797586775685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44682119563771730115700913 33511589672828797586775685)
      ·
        refine ⟨6283423063655399547520441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33511589672828797586775685 6283423063655399547520441)
        ·
          refine ⟨4712567297741549660640331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6283423063655399547520441 4712567297741549660640331)
          ·
            refine ⟨7068850946612324490960497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4712567297741549660640331 7068850946612324490960497)
            ·
              refine ⟨5301638209959243368220373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7068850946612324490960497 5301638209959243368220373)
              ·
                refine ⟨124257145545919766442665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5301638209959243368220373 124257145545919766442665)
                ·
                  rfl

theorem cell21_1633432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_1633432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633432 prefixEnd_1633432 := by exact prefixLift 1633432
  have htrace : WordTrace (prefixWord ++ tailWord_1633432) baseStart_1633432 baseEnd_1633432 := by
    simpa [prefixWord, tailWord_1633432, baseEnd_1633432] using wordTrace_append hprefix tailTrace_1633432
  have hstable : (prefixWord ++ tailWord_1633432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633432).length < 2 ^ (prefixWord ++ tailWord_1633432).sum := by decide
  have hdescent : baseEnd_1633432 < baseStart_1633432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633573 : List Nat := [1, 3, 1, 2, 4, 2, 3, 2, 3]
def baseStart_1633573 : Nat := 118140960795 + 1633573 * 2 ^ 59
def prefixEnd_1633573 : Nat := 4983230072969 + 3 ^ 40 * 1633573 * 2
def baseEnd_1633573 : Nat := 372803614758774387477707

theorem tailTrace_1633573 : CollatzResearch.WordTrace tailWord_1633573 prefixEnd_1633573 372803614758774387477707 := by
  unfold tailWord_1633573
  simp only [CollatzResearch.WordTrace]
  refine ⟨59581302110851487901817373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39720868073900991934544915 59581302110851487901817373)
  ·
    refine ⟨22342988291569307963181515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59581302110851487901817373 22342988291569307963181515)
    ·
      refine ⟨33514482437353961944772273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22342988291569307963181515 33514482437353961944772273)
      ·
        refine ⟨25135861828015471458579205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33514482437353961944772273 25135861828015471458579205)
        ·
          refine ⟨4712974092752900898483601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25135861828015471458579205 4712974092752900898483601)
          ·
            refine ⟨3534730569564675673862701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4712974092752900898483601 3534730569564675673862701)
            ·
              refine ⟨1325523963586753377698513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3534730569564675673862701 1325523963586753377698513)
              ·
                refine ⟨994142972690065033273885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325523963586753377698513 994142972690065033273885)
                ·
                  refine ⟨372803614758774387477707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994142972690065033273885 372803614758774387477707)
                  ·
                    rfl

theorem cell21_1633573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_1633573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633573 prefixEnd_1633573 := by exact prefixLift 1633573
  have htrace : WordTrace (prefixWord ++ tailWord_1633573) baseStart_1633573 baseEnd_1633573 := by
    simpa [prefixWord, tailWord_1633573, baseEnd_1633573] using wordTrace_append hprefix tailTrace_1633573
  have hstable : (prefixWord ++ tailWord_1633573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633573).length < 2 ^ (prefixWord ++ tailWord_1633573).sum := by decide
  have hdescent : baseEnd_1633573 < baseStart_1633573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633587 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 4]
def baseStart_1633587 : Nat := 118140960795 + 1633587 * 2 ^ 59
def prefixEnd_1633587 : Nat := 4983230072969 + 3 ^ 40 * 1633587 * 2
def baseEnd_1633587 : Nat := 372806809749513474244345

theorem tailTrace_1633587 : CollatzResearch.WordTrace tailWord_1633587 prefixEnd_1633587 372806809749513474244345 := by
  unfold tailWord_1633587
  simp only [CollatzResearch.WordTrace]
  refine ⟨59581812732800768292827015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39721208488533845528551343 59581812732800768292827015)
  ·
    refine ⟨89372719099201152439240523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59581812732800768292827015 89372719099201152439240523)
    ·
      refine ⟨134059078648801728658860785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89372719099201152439240523 134059078648801728658860785)
      ·
        refine ⟨100544308986601296494145589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134059078648801728658860785 100544308986601296494145589)
        ·
          refine ⟨9426028967493871546326149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100544308986601296494145589 9426028967493871546326149)
          ·
            refine ⟨1767380431405100914936153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9426028967493871546326149 1767380431405100914936153)
            ·
              refine ⟨1325535323553825686202115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1767380431405100914936153 1325535323553825686202115)
              ·
                refine ⟨1988302985330738529303173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325535323553825686202115 1988302985330738529303173)
                ·
                  refine ⟨372806809749513474244345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1988302985330738529303173 372806809749513474244345)
                  ·
                    rfl

theorem cell21_1633587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 4].length) (baseStart_1633587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633587 prefixEnd_1633587 := by exact prefixLift 1633587
  have htrace : WordTrace (prefixWord ++ tailWord_1633587) baseStart_1633587 baseEnd_1633587 := by
    simpa [prefixWord, tailWord_1633587, baseEnd_1633587] using wordTrace_append hprefix tailTrace_1633587
  have hstable : (prefixWord ++ tailWord_1633587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633587).length < 2 ^ (prefixWord ++ tailWord_1633587).sum := by decide
  have hdescent : baseEnd_1633587 < baseStart_1633587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1633632 : List Nat := [2, 1, 1, 3, 4, 2, 1, 4, 3]
def baseStart_1633632 : Nat := 118140960795 + 1633632 * 2 ^ 59
def prefixEnd_1633632 : Nat := 4983230072969 + 3 ^ 40 * 1633632 * 2
def baseEnd_1633632 : Nat := 372817079362603395994253

theorem tailTrace_1633632 : CollatzResearch.WordTrace tailWord_1633632 prefixEnd_1633632 372817079362603395994253 := by
  unfold tailWord_1633632
  simp only [CollatzResearch.WordTrace]
  refine ⟨29791727008818870489107575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39722302678425160652143433 29791727008818870489107575)
  ·
    refine ⟨44687590513228305733661363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29791727008818870489107575 44687590513228305733661363)
    ·
      refine ⟨67031385769842458600492045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44687590513228305733661363 67031385769842458600492045)
      ·
        refine ⟨25136769663690921975184517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67031385769842458600492045 25136769663690921975184517)
        ·
          refine ⟨4713144311942047870347097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25136769663690921975184517 4713144311942047870347097)
          ·
            refine ⟨3534858233956535902760323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4713144311942047870347097 3534858233956535902760323)
            ·
              refine ⟨5302287350934803854140485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3534858233956535902760323 5302287350934803854140485)
              ·
                refine ⟨994178878300275722651341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5302287350934803854140485 994178878300275722651341)
                ·
                  refine ⟨372817079362603395994253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994178878300275722651341 372817079362603395994253)
                  ·
                    rfl

theorem cell21_1633632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 3].length) (baseStart_1633632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1633632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1633632 prefixEnd_1633632 := by exact prefixLift 1633632
  have htrace : WordTrace (prefixWord ++ tailWord_1633632) baseStart_1633632 baseEnd_1633632 := by
    simpa [prefixWord, tailWord_1633632, baseEnd_1633632] using wordTrace_append hprefix tailTrace_1633632
  have hstable : (prefixWord ++ tailWord_1633632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1633632).length < 2 ^ (prefixWord ++ tailWord_1633632).sum := by decide
  have hdescent : baseEnd_1633632 < baseStart_1633632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1633632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
