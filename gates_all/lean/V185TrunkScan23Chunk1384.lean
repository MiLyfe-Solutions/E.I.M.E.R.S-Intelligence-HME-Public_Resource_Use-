import V185TrunkScan23Chunk1383

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8197485 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 1, 3, 2]
def baseStart_8197485 : Nat := 118140960795 + 8197485 * 2 ^ 59
def prefixEnd_8197485 : Nat := 4983230072969 + 3 ^ 40 * 8197485 * 2
def baseEnd_8197485 : Nat := 4209249963021965035937959

theorem tailTrace_8197485 : CollatzResearch.WordTrace tailWord_8197485 prefixEnd_8197485 4209249963021965035937959 := by
  unfold tailWord_8197485
  simp only [CollatzResearch.WordTrace]
  refine ⟨298986840706919338821905909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199324560471279559214603939 298986840706919338821905909)
  ·
    refine ⟨28030016316273688014553679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298986840706919338821905909 28030016316273688014553679)
    ·
      refine ⟨42045024474410532021830519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28030016316273688014553679 42045024474410532021830519)
      ·
        refine ⟨63067536711615798032745779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42045024474410532021830519 63067536711615798032745779)
        ·
          refine ⟨94601305067423697049118669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63067536711615798032745779 94601305067423697049118669)
          ·
            refine ⟨35475489400283886393419501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94601305067423697049118669 35475489400283886393419501)
            ·
              refine ⟨13303308525106457397532313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35475489400283886393419501 13303308525106457397532313)
              ·
                refine ⟨9977481393829843048149235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13303308525106457397532313 9977481393829843048149235)
                ·
                  refine ⟨14966222090744764572223853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9977481393829843048149235 14966222090744764572223853)
                  ·
                    refine ⟨5612333284029286714583945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14966222090744764572223853 5612333284029286714583945)
                    ·
                      refine ⟨4209249963021965035937959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612333284029286714583945 4209249963021965035937959)
                      ·
                        rfl

theorem cell23_8197485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_8197485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197485 prefixEnd_8197485 := by exact prefixLift 8197485
  have htrace : WordTrace (prefixWord ++ tailWord_8197485) baseStart_8197485 baseEnd_8197485 := by
    simpa [prefixWord, tailWord_8197485, baseEnd_8197485] using wordTrace_append hprefix tailTrace_8197485
  have hstable : (prefixWord ++ tailWord_8197485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197485).length < 2 ^ (prefixWord ++ tailWord_8197485).sum := by decide
  have hdescent : baseEnd_8197485 < baseStart_8197485 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197515 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 2, 2, 2]
def baseStart_8197515 : Nat := 118140960795 + 8197515 * 2 ^ 59
def prefixEnd_8197515 : Nat := 4983230072969 + 3 ^ 40 * 8197515 * 2
def baseEnd_8197515 : Nat := 4209265367441599918562821

theorem tailTrace_8197515 : CollatzResearch.WordTrace tailWord_8197515 prefixEnd_8197515 4209265367441599918562821 := by
  unfold tailWord_8197515
  simp only [CollatzResearch.WordTrace]
  refine ⟨298987934896810653945497999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199325289931207102630331999 298987934896810653945497999)
  ·
    refine ⟨448481902345215980918246999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298987934896810653945497999 448481902345215980918246999)
    ·
      refine ⟨672722853517823971377370499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448481902345215980918246999 672722853517823971377370499)
      ·
        refine ⟨1009084280276735957066055749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672722853517823971377370499 1009084280276735957066055749)
        ·
          refine ⟨189203302551887991949885453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1009084280276735957066055749 189203302551887991949885453)
          ·
            refine ⟨70951238456957996981207045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189203302551887991949885453 70951238456957996981207045)
            ·
              refine ⟨13303357210679624433976321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70951238456957996981207045 13303357210679624433976321)
              ·
                refine ⟨9977517908009718325482241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13303357210679624433976321 9977517908009718325482241)
                ·
                  refine ⟨7483138431007288744111681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9977517908009718325482241 7483138431007288744111681)
                  ·
                    refine ⟨5612353823255466558083761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7483138431007288744111681 5612353823255466558083761)
                    ·
                      refine ⟨4209265367441599918562821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612353823255466558083761 4209265367441599918562821)
                      ·
                        rfl

theorem cell23_8197515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2, 2, 2].length) (baseStart_8197515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197515 prefixEnd_8197515 := by exact prefixLift 8197515
  have htrace : WordTrace (prefixWord ++ tailWord_8197515) baseStart_8197515 baseEnd_8197515 := by
    simpa [prefixWord, tailWord_8197515, baseEnd_8197515] using wordTrace_append hprefix tailTrace_8197515
  have hstable : (prefixWord ++ tailWord_8197515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197515).length < 2 ^ (prefixWord ++ tailWord_8197515).sum := by decide
  have hdescent : baseEnd_8197515 < baseStart_8197515 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197521 : List Nat := [1, 2, 2, 1, 1, 1, 2, 8, 5]
def baseStart_8197521 : Nat := 118140960795 + 8197521 * 2 ^ 59
def prefixEnd_8197521 : Nat := 4983230072969 + 3 ^ 40 * 8197521 * 2
def baseEnd_8197521 : Nat := 467696494258391877231977

theorem tailTrace_8197521 : CollatzResearch.WordTrace tailWord_8197521 prefixEnd_8197521 467696494258391877231977 := by
  unfold tailWord_8197521
  simp only [CollatzResearch.WordTrace]
  refine ⟨298988153734788916970216417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199325435823192611313477611 298988153734788916970216417)
  ·
    refine ⟨224241115301091687727662313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298988153734788916970216417 224241115301091687727662313)
    ·
      refine ⟨168180836475818765795746735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224241115301091687727662313 168180836475818765795746735)
      ·
        refine ⟨252271254713728148693620103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168180836475818765795746735 252271254713728148693620103)
        ·
          refine ⟨378406882070592223040430155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252271254713728148693620103 378406882070592223040430155)
          ·
            refine ⟨567610323105888334560645233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378406882070592223040430155 567610323105888334560645233)
            ·
              refine ⟨425707742329416250920483925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567610323105888334560645233 425707742329416250920483925)
              ·
                refine ⟨4988762605422846690474421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 425707742329416250920483925 4988762605422846690474421)
                ·
                  refine ⟨467696494258391877231977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4988762605422846690474421 467696494258391877231977)
                  ·
                    rfl

theorem cell23_8197521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 5].length) (baseStart_8197521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197521 prefixEnd_8197521 := by exact prefixLift 8197521
  have htrace : WordTrace (prefixWord ++ tailWord_8197521) baseStart_8197521 baseEnd_8197521 := by
    simpa [prefixWord, tailWord_8197521, baseEnd_8197521] using wordTrace_append hprefix tailTrace_8197521
  have hstable : (prefixWord ++ tailWord_8197521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197521).length < 2 ^ (prefixWord ++ tailWord_8197521).sum := by decide
  have hdescent : baseEnd_8197521 < baseStart_8197521 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197528 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 2, 2, 4]
def baseStart_8197528 : Nat := 118140960795 + 8197528 * 2 ^ 59
def prefixEnd_8197528 : Nat := 4983230072969 + 3 ^ 40 * 8197528 * 2
def baseEnd_8197528 : Nat := 4209272042690108367700261

theorem tailTrace_8197528 : CollatzResearch.WordTrace tailWord_8197528 prefixEnd_8197528 4209272042690108367700261 := by
  unfold tailWord_8197528
  simp only [CollatzResearch.WordTrace]
  refine ⟨149494204522881778582860619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199325606030509038110480825 149494204522881778582860619)
  ·
    refine ⟨224241306784322667874290929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149494204522881778582860619 224241306784322667874290929)
    ·
      refine ⟨168180980088242000905718197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224241306784322667874290929 168180980088242000905718197)
      ·
        refine ⟨15766966883272687584911081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168180980088242000905718197 15766966883272687584911081)
        ·
          refine ⟨11825225162454515688683311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15766966883272687584911081 11825225162454515688683311)
          ·
            refine ⟨17737837743681773533024967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11825225162454515688683311 17737837743681773533024967)
            ·
              refine ⟨26606756615522660299537451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17737837743681773533024967 26606756615522660299537451)
              ·
                refine ⟨39910134923283990449306177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26606756615522660299537451 39910134923283990449306177)
                ·
                  refine ⟨29932601192462992836979633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39910134923283990449306177 29932601192462992836979633)
                  ·
                    refine ⟨22449450894347244627734725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29932601192462992836979633 22449450894347244627734725)
                    ·
                      refine ⟨4209272042690108367700261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22449450894347244627734725 4209272042690108367700261)
                      ·
                        rfl

theorem cell23_8197528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_8197528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197528 prefixEnd_8197528 := by exact prefixLift 8197528
  have htrace : WordTrace (prefixWord ++ tailWord_8197528) baseStart_8197528 baseEnd_8197528 := by
    simpa [prefixWord, tailWord_8197528, baseEnd_8197528] using wordTrace_append hprefix tailTrace_8197528
  have hstable : (prefixWord ++ tailWord_8197528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197528).length < 2 ^ (prefixWord ++ tailWord_8197528).sum := by decide
  have hdescent : baseEnd_8197528 < baseStart_8197528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197532 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 1, 4, 2]
def baseStart_8197532 : Nat := 118140960795 + 8197532 * 2 ^ 59
def prefixEnd_8197532 : Nat := 4983230072969 + 3 ^ 40 * 8197532 * 2
def baseEnd_8197532 : Nat := 4209274096612726352050243

theorem tailTrace_8197532 : CollatzResearch.WordTrace tailWord_8197532 prefixEnd_8197532 4209274096612726352050243 := by
  unfold tailWord_8197532
  simp only [CollatzResearch.WordTrace]
  refine ⟨149494277468874532924433425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199325703291832710565911233 149494277468874532924433425)
  ·
    refine ⟨112120708101655899693325069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149494277468874532924433425 112120708101655899693325069)
    ·
      refine ⟨42045265538120962384996901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112120708101655899693325069 42045265538120962384996901)
      ·
        refine ⟨7883487288397680447186919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42045265538120962384996901 7883487288397680447186919)
        ·
          refine ⟨11825230932596520670780379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7883487288397680447186919 11825230932596520670780379)
          ·
            refine ⟨17737846398894781006170569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11825230932596520670780379 17737846398894781006170569)
            ·
              refine ⟨13303384799171085754627927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17737846398894781006170569 13303384799171085754627927)
              ·
                refine ⟨19955077198756628631941891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13303384799171085754627927 19955077198756628631941891)
                ·
                  refine ⟨29932615798134942947912837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19955077198756628631941891 29932615798134942947912837)
                  ·
                    refine ⟨5612365462150301802733657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29932615798134942947912837 5612365462150301802733657)
                    ·
                      refine ⟨4209274096612726352050243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612365462150301802733657 4209274096612726352050243)
                      ·
                        rfl

theorem cell23_8197532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_8197532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197532 prefixEnd_8197532 := by exact prefixLift 8197532
  have htrace : WordTrace (prefixWord ++ tailWord_8197532) baseStart_8197532 baseEnd_8197532 := by
    simpa [prefixWord, tailWord_8197532, baseEnd_8197532] using wordTrace_append hprefix tailTrace_8197532
  have hstable : (prefixWord ++ tailWord_8197532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197532).length < 2 ^ (prefixWord ++ tailWord_8197532).sum := by decide
  have hdescent : baseEnd_8197532 < baseStart_8197532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197571 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 4]
def baseStart_8197571 : Nat := 118140960795 + 8197571 * 2 ^ 59
def prefixEnd_8197571 : Nat := 4983230072969 + 3 ^ 40 * 8197571 * 2
def baseEnd_8197571 : Nat := 4209294122358251699462563

theorem tailTrace_8197571 : CollatzResearch.WordTrace tailWord_8197571 prefixEnd_8197571 4209294122358251699462563 := by
  unfold tailWord_8197571
  simp only [CollatzResearch.WordTrace]
  refine ⟨298989977384607775509536567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199326651589738517006357711 298989977384607775509536567)
  ·
    refine ⟨448484966076911663264304851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298989977384607775509536567 448484966076911663264304851)
    ·
      refine ⟨672727449115367494896457277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448484966076911663264304851 672727449115367494896457277)
      ·
        refine ⟨252272793418262810586171479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 672727449115367494896457277 252272793418262810586171479)
        ·
          refine ⟨378409190127394215879257219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252272793418262810586171479 378409190127394215879257219)
          ·
            refine ⟨567613785191091323818885829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378409190127394215879257219 567613785191091323818885829)
            ·
              refine ⟨106427584723329623216041093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 567613785191091323818885829 106427584723329623216041093)
              ·
                refine ⟨19955172135624304353007705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106427584723329623216041093 19955172135624304353007705)
                ·
                  refine ⟨14966379101718228264755779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19955172135624304353007705 14966379101718228264755779)
                  ·
                    refine ⟨22449568652577342397133669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14966379101718228264755779 22449568652577342397133669)
                    ·
                      refine ⟨4209294122358251699462563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22449568652577342397133669 4209294122358251699462563)
                      ·
                        rfl

theorem cell23_8197571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_8197571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197571 prefixEnd_8197571 := by exact prefixLift 8197571
  have htrace : WordTrace (prefixWord ++ tailWord_8197571) baseStart_8197571 baseEnd_8197571 := by
    simpa [prefixWord, tailWord_8197571, baseEnd_8197571] using wordTrace_append hprefix tailTrace_8197571
  have hstable : (prefixWord ++ tailWord_8197571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197571).length < 2 ^ (prefixWord ++ tailWord_8197571).sum := by decide
  have hdescent : baseEnd_8197571 < baseStart_8197571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197608 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_8197608 : Nat := 118140960795 + 8197608 * 2 ^ 59
def prefixEnd_8197608 : Nat := 4983230072969 + 3 ^ 40 * 8197608 * 2
def baseEnd_8197608 : Nat := 4209313121142468054699893

theorem tailTrace_8197608 : CollatzResearch.WordTrace tailWord_8197608 prefixEnd_8197608 4209313121142468054699893 := by
  unfold tailWord_8197608
  simp only [CollatzResearch.WordTrace]
  refine ⟨149495663442736865414316739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199327551256982487219088985 149495663442736865414316739)
  ·
    refine ⟨224243495164105298121475109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149495663442736865414316739 224243495164105298121475109)
    ·
      refine ⟨42045655343269743397776583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224243495164105298121475109 42045655343269743397776583)
      ·
        refine ⟨63068483014904615096664875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42045655343269743397776583 63068483014904615096664875)
        ·
          refine ⟨94602724522356922644997313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63068483014904615096664875 94602724522356922644997313)
          ·
            refine ⟨70952043391767691983747985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94602724522356922644997313 70952043391767691983747985)
            ·
              refine ⟨53214032543825768987810989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70952043391767691983747985 53214032543825768987810989)
              ·
                refine ⟨19955262203934663370429121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53214032543825768987810989 19955262203934663370429121)
                ·
                  refine ⟨14966446652950997527821841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19955262203934663370429121 14966446652950997527821841)
                  ·
                    refine ⟨11224834989713248145866381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14966446652950997527821841 11224834989713248145866381)
                    ·
                      refine ⟨4209313121142468054699893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11224834989713248145866381 4209313121142468054699893)
                      ·
                        rfl

theorem cell23_8197608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_8197608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197608 prefixEnd_8197608 := by exact prefixLift 8197608
  have htrace : WordTrace (prefixWord ++ tailWord_8197608) baseStart_8197608 baseEnd_8197608 := by
    simpa [prefixWord, tailWord_8197608, baseEnd_8197608] using wordTrace_append hprefix tailTrace_8197608
  have hstable : (prefixWord ++ tailWord_8197608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197608).length < 2 ^ (prefixWord ++ tailWord_8197608).sum := by decide
  have hdescent : baseEnd_8197608 < baseStart_8197608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197615 : List Nat := [1, 1, 2, 1, 4, 1, 5, 3, 1, 4]
def baseStart_8197615 : Nat := 118140960795 + 8197615 * 2 ^ 59
def prefixEnd_8197615 : Nat := 4983230072969 + 3 ^ 40 * 8197615 * 2
def baseEnd_8197615 : Nat := 1403105571835683175770787

theorem tailTrace_8197615 : CollatzResearch.WordTrace tailWord_8197615 prefixEnd_8197615 1403105571835683175770787 := by
  unfold tailWord_8197615
  simp only [CollatzResearch.WordTrace]
  refine ⟨298991582196448371024138299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199327721464298914016092199 298991582196448371024138299)
  ·
    refine ⟨448487373294672556536207449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298991582196448371024138299 448487373294672556536207449)
    ·
      refine ⟨336365529971004417402155587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448487373294672556536207449 336365529971004417402155587)
      ·
        refine ⟨504548294956506626103233381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336365529971004417402155587 504548294956506626103233381)
        ·
          refine ⟨94602805304344992394356259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504548294956506626103233381 94602805304344992394356259)
          ·
            refine ⟨141904207956517488591534389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94602805304344992394356259 141904207956517488591534389)
            ·
              refine ⟨13303519495923514555456349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141904207956517488591534389 13303519495923514555456349)
              ·
                refine ⟨4988819810971317958296131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13303519495923514555456349 4988819810971317958296131)
                ·
                  refine ⟨7483229716456976937444197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988819810971317958296131 7483229716456976937444197)
                  ·
                    refine ⟨1403105571835683175770787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7483229716456976937444197 1403105571835683175770787)
                    ·
                      rfl

theorem cell23_8197615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 1, 4].length) (baseStart_8197615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197615 prefixEnd_8197615 := by exact prefixLift 8197615
  have htrace : WordTrace (prefixWord ++ tailWord_8197615) baseStart_8197615 baseEnd_8197615 := by
    simpa [prefixWord, tailWord_8197615, baseEnd_8197615] using wordTrace_append hprefix tailTrace_8197615
  have hstable : (prefixWord ++ tailWord_8197615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197615).length < 2 ^ (prefixWord ++ tailWord_8197615).sum := by decide
  have hdescent : baseEnd_8197615 < baseStart_8197615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197641 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 3, 5]
def baseStart_8197641 : Nat := 118140960795 + 8197641 * 2 ^ 59
def prefixEnd_8197641 : Nat := 4983230072969 + 3 ^ 40 * 8197641 * 2
def baseEnd_8197641 : Nat := 1403110022001355475195747

theorem tailTrace_8197641 : CollatzResearch.WordTrace tailWord_8197641 prefixEnd_8197641 1403110022001355475195747 := by
  unfold tailWord_8197641
  simp only [CollatzResearch.WordTrace]
  refine ⟨298992530494354177464584777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199328353662902784976389851 298992530494354177464584777)
  ·
    refine ⟨224244397870765633098438583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298992530494354177464584777 224244397870765633098438583)
    ·
      refine ⟨336366596806148449647657875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224244397870765633098438583 336366596806148449647657875)
      ·
        refine ⟨504549895209222674471486813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336366596806148449647657875 504549895209222674471486813)
        ·
          refine ⟨189206210703458502926807555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504549895209222674471486813 189206210703458502926807555)
          ·
            refine ⟨283809316055187754390211333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189206210703458502926807555 283809316055187754390211333)
            ·
              refine ⟨53214246760347703948164625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283809316055187754390211333 53214246760347703948164625)
              ·
                refine ⟨39910685070260777961123469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53214246760347703948164625 39910685070260777961123469)
                ·
                  refine ⟨14966506901347791735421301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39910685070260777961123469 14966506901347791735421301)
                  ·
                    refine ⟨1403110022001355475195747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14966506901347791735421301 1403110022001355475195747)
                    ·
                      rfl

theorem cell23_8197641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_8197641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197641 prefixEnd_8197641 := by exact prefixLift 8197641
  have htrace : WordTrace (prefixWord ++ tailWord_8197641) baseStart_8197641 baseEnd_8197641 := by
    simpa [prefixWord, tailWord_8197641, baseEnd_8197641] using wordTrace_append hprefix tailTrace_8197641
  have hstable : (prefixWord ++ tailWord_8197641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197641).length < 2 ^ (prefixWord ++ tailWord_8197641).sum := by decide
  have hdescent : baseEnd_8197641 < baseStart_8197641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197665 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 2, 3, 2]
def baseStart_8197665 : Nat := 118140960795 + 8197665 * 2 ^ 59
def prefixEnd_8197665 : Nat := 4983230072969 + 3 ^ 40 * 8197665 * 2
def baseEnd_8197665 : Nat := 4209342389539774331687131

theorem tailTrace_8197665 : CollatzResearch.WordTrace tailWord_8197665 prefixEnd_8197665 4209342389539774331687131 := by
  unfold tailWord_8197665
  simp only [CollatzResearch.WordTrace]
  refine ⟨298993405846267229563458449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199328937230844819708972299 298993405846267229563458449)
  ·
    refine ⟨224245054384700422172593837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298993405846267229563458449 224245054384700422172593837)
    ·
      refine ⟨84091895394262658314722689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224245054384700422172593837 84091895394262658314722689)
      ·
        refine ⟨63068921545696993736042017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84091895394262658314722689 63068921545696993736042017)
        ·
          refine ⟨47301691159272745302031513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63068921545696993736042017 47301691159272745302031513)
          ·
            refine ⟨35476268369454558976523635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47301691159272745302031513 35476268369454558976523635)
            ·
              refine ⟨53214402554181838464785453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35476268369454558976523635 53214402554181838464785453)
              ·
                refine ⟨19955400957818189424294545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53214402554181838464785453 19955400957818189424294545)
                ·
                  refine ⟨14966550718363642068220909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19955400957818189424294545 14966550718363642068220909)
                  ·
                    refine ⟨5612456519386365775582841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14966550718363642068220909 5612456519386365775582841)
                    ·
                      refine ⟨4209342389539774331687131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612456519386365775582841 4209342389539774331687131)
                      ·
                        rfl

theorem cell23_8197665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_8197665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197665 prefixEnd_8197665 := by exact prefixLift 8197665
  have htrace : WordTrace (prefixWord ++ tailWord_8197665) baseStart_8197665 baseEnd_8197665 := by
    simpa [prefixWord, tailWord_8197665, baseEnd_8197665] using wordTrace_append hprefix tailTrace_8197665
  have hstable : (prefixWord ++ tailWord_8197665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197665).length < 2 ^ (prefixWord ++ tailWord_8197665).sum := by decide
  have hdescent : baseEnd_8197665 < baseStart_8197665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197689 : List Nat := [1, 2, 1, 5, 1, 2, 4, 2, 1, 1, 3]
def baseStart_8197689 : Nat := 118140960795 + 8197689 * 2 ^ 59
def prefixEnd_8197689 : Nat := 4983230072969 + 3 ^ 40 * 8197689 * 2
def baseEnd_8197689 : Nat := 4209354713075482237787021

theorem tailTrace_8197689 : CollatzResearch.WordTrace tailWord_8197689 prefixEnd_8197689 4209354713075482237787021 := by
  unfold tailWord_8197689
  simp only [CollatzResearch.WordTrace]
  refine ⟨298994281198180281662332121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199329520798786854441554747 298994281198180281662332121)
  ·
    refine ⟨224245710898635211246749091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298994281198180281662332121 224245710898635211246749091)
    ·
      refine ⟨336368566347952816870123637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224245710898635211246749091 336368566347952816870123637)
      ·
        refine ⟨31534553095120576581574091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336368566347952816870123637 31534553095120576581574091)
        ·
          refine ⟨47301829642680864872361137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31534553095120576581574091 47301829642680864872361137)
          ·
            refine ⟨35476372232010648654270853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47301829642680864872361137 35476372232010648654270853)
            ·
              refine ⟨6651819793501996622675785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35476372232010648654270853 6651819793501996622675785)
              ·
                refine ⟨4988864845126497467006839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6651819793501996622675785 4988864845126497467006839)
                ·
                  refine ⟨7483297267689746200510259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988864845126497467006839 7483297267689746200510259)
                  ·
                    refine ⟨11224945901534619300765389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7483297267689746200510259 11224945901534619300765389)
                    ·
                      refine ⟨4209354713075482237787021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11224945901534619300765389 4209354713075482237787021)
                      ·
                        rfl

theorem cell23_8197689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_8197689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197689 prefixEnd_8197689 := by exact prefixLift 8197689
  have htrace : WordTrace (prefixWord ++ tailWord_8197689) baseStart_8197689 baseEnd_8197689 := by
    simpa [prefixWord, tailWord_8197689, baseEnd_8197689] using wordTrace_append hprefix tailTrace_8197689
  have hstable : (prefixWord ++ tailWord_8197689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197689).length < 2 ^ (prefixWord ++ tailWord_8197689).sum := by decide
  have hdescent : baseEnd_8197689 < baseStart_8197689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197708 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_8197708 : Nat := 118140960795 + 8197708 * 2 ^ 59
def prefixEnd_8197708 : Nat := 4983230072969 + 3 ^ 40 * 8197708 * 2
def baseEnd_8197708 : Nat := 4209364469207917663449433

theorem tailTrace_8197708 : CollatzResearch.WordTrace tailWord_8197708 prefixEnd_8197708 4209364469207917663449433 := by
  unfold tailWord_8197708
  simp only [CollatzResearch.WordTrace]
  refine ⟨149497487092555723953636889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199329982790074298604849185 149497487092555723953636889)
  ·
    refine ⟨112123115319416792965227667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149497487092555723953636889 112123115319416792965227667)
    ·
      refine ⟨168184672979125189447841501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112123115319416792965227667 168184672979125189447841501)
      ·
        refine ⟨63069252367171946042940563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168184672979125189447841501 63069252367171946042940563)
        ·
          refine ⟨94603878550757919064410845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63069252367171946042940563 94603878550757919064410845)
          ·
            refine ⟨35476454456534219649154067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94603878550757919064410845 35476454456534219649154067)
            ·
              refine ⟨53214681684801329473731101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35476454456534219649154067 53214681684801329473731101)
              ·
                refine ⟨19955505631800498552649163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53214681684801329473731101 19955505631800498552649163)
                ·
                  refine ⟨29933258447700747828973745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19955505631800498552649163 29933258447700747828973745)
                  ·
                    refine ⟨22449943835775560871730309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29933258447700747828973745 22449943835775560871730309)
                    ·
                      refine ⟨4209364469207917663449433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22449943835775560871730309 4209364469207917663449433)
                      ·
                        rfl

theorem cell23_8197708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_8197708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197708 prefixEnd_8197708 := by exact prefixLift 8197708
  have htrace : WordTrace (prefixWord ++ tailWord_8197708) baseStart_8197708 baseEnd_8197708 := by
    simpa [prefixWord, tailWord_8197708, baseEnd_8197708] using wordTrace_append hprefix tailTrace_8197708
  have hstable : (prefixWord ++ tailWord_8197708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197708).length < 2 ^ (prefixWord ++ tailWord_8197708).sum := by decide
  have hdescent : baseEnd_8197708 < baseStart_8197708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197729 : List Nat := [1, 2, 3, 1, 1, 3, 4, 3, 1, 2, 2]
def baseStart_8197729 : Nat := 118140960795 + 8197729 * 2 ^ 59
def prefixEnd_8197729 : Nat := 4983230072969 + 3 ^ 40 * 8197729 * 2
def baseEnd_8197729 : Nat := 4209375252301662081286837

theorem tailTrace_8197729 : CollatzResearch.WordTrace tailWord_8197729 prefixEnd_8197729 4209375252301662081286837 := by
  unfold tailWord_8197729
  simp only [CollatzResearch.WordTrace]
  refine ⟨298995740118035368493788241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199330493412023578995858827 298995740118035368493788241)
  ·
    refine ⟨224246805088526526370341181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 298995740118035368493788241 224246805088526526370341181)
    ·
      refine ⟨84092551908197447388877943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224246805088526526370341181 84092551908197447388877943)
      ·
        refine ⟨126138827862296171083316915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84092551908197447388877943 126138827862296171083316915)
        ·
          refine ⟨189208241793444256624975373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126138827862296171083316915 189208241793444256624975373)
          ·
            refine ⟨70953090672541596234365765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189208241793444256624975373 70953090672541596234365765)
            ·
              refine ⟨13303704501101549293943581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70953090672541596234365765 13303704501101549293943581)
              ·
                refine ⟨4988889187913080985228843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13303704501101549293943581 4988889187913080985228843)
                ·
                  refine ⟨7483333781869621477843265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988889187913080985228843 7483333781869621477843265)
                  ·
                    refine ⟨5612500336402216108382449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7483333781869621477843265 5612500336402216108382449)
                    ·
                      refine ⟨4209375252301662081286837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612500336402216108382449 4209375252301662081286837)
                      ·
                        rfl

theorem cell23_8197729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 3, 1, 2, 2].length) (baseStart_8197729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197729 prefixEnd_8197729 := by exact prefixLift 8197729
  have htrace : WordTrace (prefixWord ++ tailWord_8197729) baseStart_8197729 baseEnd_8197729 := by
    simpa [prefixWord, tailWord_8197729, baseEnd_8197729] using wordTrace_append hprefix tailTrace_8197729
  have hstable : (prefixWord ++ tailWord_8197729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197729).length < 2 ^ (prefixWord ++ tailWord_8197729).sum := by decide
  have hdescent : baseEnd_8197729 < baseStart_8197729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197732 : List Nat := [2, 3, 1, 1, 2, 3, 4, 1, 1, 2, 3]
def baseStart_8197732 : Nat := 118140960795 + 8197732 * 2 ^ 59
def prefixEnd_8197732 : Nat := 4983230072969 + 3 ^ 40 * 8197732 * 2
def baseEnd_8197732 : Nat := 4209376792743625569549323

theorem tailTrace_8197732 : CollatzResearch.WordTrace tailWord_8197732 prefixEnd_8197732 4209376792743625569549323 := by
  unfold tailWord_8197732
  simp only [CollatzResearch.WordTrace]
  refine ⟨149497924768512250003073725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199330566358016333337431633 149497924768512250003073725)
  ·
    refine ⟨56061721788192093751152647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149497924768512250003073725 56061721788192093751152647)
    ·
      refine ⟨84092582682288140626728971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56061721788192093751152647 84092582682288140626728971)
      ·
        refine ⟨126138874023432210940093457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84092582682288140626728971 126138874023432210940093457)
        ·
          refine ⟨94604155517574158205070093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126138874023432210940093457 94604155517574158205070093)
          ·
            refine ⟨35476558319090309326901285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94604155517574158205070093 35476558319090309326901285)
            ·
              refine ⟨6651854684829432998793991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35476558319090309326901285 6651854684829432998793991)
              ·
                refine ⟨9977782027244149498190987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651854684829432998793991 9977782027244149498190987)
                ·
                  refine ⟨14966673040866224247286481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9977782027244149498190987 14966673040866224247286481)
                  ·
                    refine ⟨11225004780649668185464861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14966673040866224247286481 11225004780649668185464861)
                    ·
                      refine ⟨4209376792743625569549323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11225004780649668185464861 4209376792743625569549323)
                      ·
                        rfl

theorem cell23_8197732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_8197732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197732 prefixEnd_8197732 := by exact prefixLift 8197732
  have htrace : WordTrace (prefixWord ++ tailWord_8197732) baseStart_8197732 baseEnd_8197732 := by
    simpa [prefixWord, tailWord_8197732, baseEnd_8197732] using wordTrace_append hprefix tailTrace_8197732
  have hstable : (prefixWord ++ tailWord_8197732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197732).length < 2 ^ (prefixWord ++ tailWord_8197732).sum := by decide
  have hdescent : baseEnd_8197732 < baseStart_8197732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197772 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 1, 3, 2]
def baseStart_8197772 : Nat := 118140960795 + 8197772 * 2 ^ 59
def prefixEnd_8197772 : Nat := 4983230072969 + 3 ^ 40 * 8197772 * 2
def baseEnd_8197772 : Nat := 4209397331969805413049139

theorem tailTrace_8197772 : CollatzResearch.WordTrace tailWord_8197772 prefixEnd_8197772 4209397331969805413049139 := by
  unfold tailWord_8197772
  simp only [CollatzResearch.WordTrace]
  refine ⟨149498654228439793418801785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199331538971253057891735713 149498654228439793418801785)
  ·
    refine ⟨112123990671329845064101339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149498654228439793418801785 112123990671329845064101339)
    ·
      refine ⟨168185986006994767596152009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112123990671329845064101339 168185986006994767596152009)
      ·
        refine ⟨126139489505246075697114007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168185986006994767596152009 126139489505246075697114007)
        ·
          refine ⟨189209234257869113545671011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126139489505246075697114007 189209234257869113545671011)
          ·
            refine ⟨283813851386803670318506517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189209234257869113545671011 283813851386803670318506517)
            ·
              refine ⟨13303774283756422046179993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 283813851386803670318506517 13303774283756422046179993)
              ·
                refine ⟨9977830712817316534634995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13303774283756422046179993 9977830712817316534634995)
                ·
                  refine ⟨14966746069225974801952493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9977830712817316534634995 14966746069225974801952493)
                  ·
                    refine ⟨5612529775959740550732185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14966746069225974801952493 5612529775959740550732185)
                    ·
                      refine ⟨4209397331969805413049139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612529775959740550732185 4209397331969805413049139)
                      ·
                        rfl

theorem cell23_8197772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_8197772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197772 prefixEnd_8197772 := by exact prefixLift 8197772
  have htrace : WordTrace (prefixWord ++ tailWord_8197772) baseStart_8197772 baseEnd_8197772 := by
    simpa [prefixWord, tailWord_8197772, baseEnd_8197772] using wordTrace_append hprefix tailTrace_8197772
  have hstable : (prefixWord ++ tailWord_8197772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197772).length < 2 ^ (prefixWord ++ tailWord_8197772).sum := by decide
  have hdescent : baseEnd_8197772 < baseStart_8197772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197780 : List Nat := [2, 4, 2, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_8197780 : Nat := 118140960795 + 8197780 * 2 ^ 59
def prefixEnd_8197780 : Nat := 4983230072969 + 3 ^ 40 * 8197780 * 2
def baseEnd_8197780 : Nat := 4209401439815041381749103

theorem tailTrace_8197780 : CollatzResearch.WordTrace tailWord_8197780 prefixEnd_8197780 4209401439815041381749103 := by
  unfold tailWord_8197780
  simp only [CollatzResearch.WordTrace]
  refine ⟨149498800120425302101947397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199331733493900402802596529 149498800120425302101947397)
  ·
    refine ⟨28031025022579744144115137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149498800120425302101947397 28031025022579744144115137)
    ·
      refine ⟨21023268766934808108086353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28031025022579744144115137 21023268766934808108086353)
      ·
        refine ⟨15767451575201106081064765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21023268766934808108086353 15767451575201106081064765)
        ·
          refine ⟨5912794340700414780399287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15767451575201106081064765 5912794340700414780399287)
          ·
            refine ⟨8869191511050622170598931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912794340700414780399287 8869191511050622170598931)
            ·
              refine ⟨13303787266575933255898397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869191511050622170598931 13303787266575933255898397)
              ·
                refine ⟨4988920224965974970961899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13303787266575933255898397 4988920224965974970961899)
                ·
                  refine ⟨7483380337448962456442849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4988920224965974970961899 7483380337448962456442849)
                  ·
                    refine ⟨5612535253086721842332137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7483380337448962456442849 5612535253086721842332137)
                    ·
                      refine ⟨4209401439815041381749103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612535253086721842332137 4209401439815041381749103)
                      ·
                        rfl

theorem cell23_8197780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_8197780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197780 prefixEnd_8197780 := by exact prefixLift 8197780
  have htrace : WordTrace (prefixWord ++ tailWord_8197780) baseStart_8197780 baseEnd_8197780 := by
    simpa [prefixWord, tailWord_8197780, baseEnd_8197780] using wordTrace_append hprefix tailTrace_8197780
  have hstable : (prefixWord ++ tailWord_8197780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197780).length < 2 ^ (prefixWord ++ tailWord_8197780).sum := by decide
  have hdescent : baseEnd_8197780 < baseStart_8197780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197805 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_8197805 : Nat := 118140960795 + 8197805 * 2 ^ 59
def prefixEnd_8197805 : Nat := 4983230072969 + 3 ^ 40 * 8197805 * 2
def baseEnd_8197805 : Nat := 4209414276831403783936487

theorem tailTrace_8197805 : CollatzResearch.WordTrace tailWord_8197805 prefixEnd_8197805 4209414276831403783936487 := by
  unfold tailWord_8197805
  simp only [CollatzResearch.WordTrace]
  refine ⟨298998512065760033473554869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199332341377173355649036579 298998512065760033473554869)
  ·
    refine ⟨28031110506165003138145769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 298998512065760033473554869 28031110506165003138145769)
    ·
      refine ⟨21023332879623752353609327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28031110506165003138145769 21023332879623752353609327)
      ·
        refine ⟨31534999319435628530413991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21023332879623752353609327 31534999319435628530413991)
        ·
          refine ⟨47302498979153442795620987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31534999319435628530413991 47302498979153442795620987)
          ·
            refine ⟨70953748468730164193431481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47302498979153442795620987 70953748468730164193431481)
            ·
              refine ⟨53215311351547623145073611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70953748468730164193431481 53215311351547623145073611)
              ·
                refine ⟨79822967027321434717610417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53215311351547623145073611 79822967027321434717610417)
                ·
                  refine ⟨59867225270491076038207813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79822967027321434717610417 59867225270491076038207813)
                  ·
                    refine ⟨11225104738217076757163965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59867225270491076038207813 11225104738217076757163965)
                    ·
                      refine ⟨4209414276831403783936487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11225104738217076757163965 4209414276831403783936487)
                      ·
                        rfl

theorem cell23_8197805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_8197805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197805 prefixEnd_8197805 := by exact prefixLift 8197805
  have htrace : WordTrace (prefixWord ++ tailWord_8197805) baseStart_8197805 baseEnd_8197805 := by
    simpa [prefixWord, tailWord_8197805, baseEnd_8197805] using wordTrace_append hprefix tailTrace_8197805
  have hstable : (prefixWord ++ tailWord_8197805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197805).length < 2 ^ (prefixWord ++ tailWord_8197805).sum := by decide
  have hdescent : baseEnd_8197805 < baseStart_8197805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197808 : List Nat := [2, 1, 1, 1, 2, 1, 7, 1, 7]
def baseStart_8197808 : Nat := 118140960795 + 8197808 * 2 ^ 59
def prefixEnd_8197808 : Nat := 4983230072969 + 3 ^ 40 * 8197808 * 2
def baseEnd_8197808 : Nat := 467712868585929696910997

theorem tailTrace_8197808 : CollatzResearch.WordTrace tailWord_8197808 prefixEnd_8197808 467712868585929696910997 := by
  unfold tailWord_8197808
  simp only [CollatzResearch.WordTrace]
  refine ⟨149499310742374582492957039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199332414323166109990609385 149499310742374582492957039)
  ·
    refine ⟨224248966113561873739435559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149499310742374582492957039 224248966113561873739435559)
    ·
      refine ⟨336373449170342810609153339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224248966113561873739435559 336373449170342810609153339)
      ·
        refine ⟨504560173755514215913730009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336373449170342810609153339 504560173755514215913730009)
        ·
          refine ⟨378420130316635661935297507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504560173755514215913730009 378420130316635661935297507)
          ·
            refine ⟨567630195474953492902946261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378420130316635661935297507 567630195474953492902946261)
            ·
              refine ⟨13303832706444222489912803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 567630195474953492902946261 13303832706444222489912803)
              ·
                refine ⟨19955749059666333734869205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13303832706444222489912803 19955749059666333734869205)
                ·
                  refine ⟨467712868585929696910997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19955749059666333734869205 467712868585929696910997)
                  ·
                    rfl

theorem cell23_8197808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 7].length) (baseStart_8197808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197808 prefixEnd_8197808 := by exact prefixLift 8197808
  have htrace : WordTrace (prefixWord ++ tailWord_8197808) baseStart_8197808 baseEnd_8197808 := by
    simpa [prefixWord, tailWord_8197808, baseEnd_8197808] using wordTrace_append hprefix tailTrace_8197808
  have hstable : (prefixWord ++ tailWord_8197808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197808).length < 2 ^ (prefixWord ++ tailWord_8197808).sum := by decide
  have hdescent : baseEnd_8197808 < baseStart_8197808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197813 : List Nat := [1, 3, 3, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_8197813 : Nat := 118140960795 + 8197813 * 2 ^ 59
def prefixEnd_8197813 : Nat := 4983230072969 + 3 ^ 40 * 8197813 * 2
def baseEnd_8197813 : Nat := 4209418384676639752636451

theorem tailTrace_8197813 : CollatzResearch.WordTrace tailWord_8197813 prefixEnd_8197813 4209418384676639752636451 := by
  unfold tailWord_8197813
  simp only [CollatzResearch.WordTrace]
  refine ⟨298998803849731050839846093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199332535899820700559897395 298998803849731050839846093)
  ·
    refine ⟨112124551443649144064942285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 298998803849731050839846093 112124551443649144064942285)
    ·
      refine ⟨42046706791368429024353357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112124551443649144064942285 42046706791368429024353357)
      ·
        refine ⟨15767515046763160884132509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42046706791368429024353357 15767515046763160884132509)
        ·
          refine ⟨5912818142536185331549691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15767515046763160884132509 5912818142536185331549691)
          ·
            refine ⟨8869227213804277997324537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5912818142536185331549691 8869227213804277997324537)
            ·
              refine ⟨6651920410353208497993403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8869227213804277997324537 6651920410353208497993403)
              ·
                refine ⟨9977880615529812746990105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6651920410353208497993403 9977880615529812746990105)
                ·
                  refine ⟨7483410461647359560242579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9977880615529812746990105 7483410461647359560242579)
                  ·
                    refine ⟨11225115692471039340363869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7483410461647359560242579 11225115692471039340363869)
                    ·
                      refine ⟨4209418384676639752636451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11225115692471039340363869 4209418384676639752636451)
                      ·
                        rfl

theorem cell23_8197813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_8197813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197813 prefixEnd_8197813 := by exact prefixLift 8197813
  have htrace : WordTrace (prefixWord ++ tailWord_8197813) baseStart_8197813 baseEnd_8197813 := by
    simpa [prefixWord, tailWord_8197813, baseEnd_8197813] using wordTrace_append hprefix tailTrace_8197813
  have hstable : (prefixWord ++ tailWord_8197813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197813).length < 2 ^ (prefixWord ++ tailWord_8197813).sum := by decide
  have hdescent : baseEnd_8197813 < baseStart_8197813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197848 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_8197848 : Nat := 118140960795 + 8197848 * 2 ^ 59
def prefixEnd_8197848 : Nat := 4983230072969 + 3 ^ 40 * 8197848 * 2
def baseEnd_8197848 : Nat := 4209436356499547115698789

theorem tailTrace_8197848 : CollatzResearch.WordTrace tailWord_8197848 prefixEnd_8197848 4209436356499547115698789 := by
  unfold tailWord_8197848
  simp only [CollatzResearch.WordTrace]
  refine ⟨149500040202302125908685099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199333386936402834544913465 149500040202302125908685099)
  ·
    refine ⟨224250060303453188863027649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149500040202302125908685099 224250060303453188863027649)
    ·
      refine ⟨168187545227589891647270737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224250060303453188863027649 168187545227589891647270737)
      ·
        refine ⟨126140658920692418735453053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168187545227589891647270737 126140658920692418735453053)
        ·
          refine ⟨47302747095259657025794895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126140658920692418735453053 47302747095259657025794895)
          ·
            refine ⟨70954120642889485538692343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47302747095259657025794895 70954120642889485538692343)
            ·
              refine ⟨106431180964334228308038515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70954120642889485538692343 106431180964334228308038515)
              ·
                refine ⟨159646771446501342462057773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106431180964334228308038515 159646771446501342462057773)
                ·
                  refine ⟨59867539292438003423271665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159646771446501342462057773 59867539292438003423271665)
                  ·
                    refine ⟨44900654469328502567453749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59867539292438003423271665 44900654469328502567453749)
                    ·
                      refine ⟨4209436356499547115698789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44900654469328502567453749 4209436356499547115698789)
                      ·
                        rfl

theorem cell23_8197848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_8197848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197848 prefixEnd_8197848 := by exact prefixLift 8197848
  have htrace : WordTrace (prefixWord ++ tailWord_8197848) baseStart_8197848 baseEnd_8197848 := by
    simpa [prefixWord, tailWord_8197848, baseEnd_8197848] using wordTrace_append hprefix tailTrace_8197848
  have hstable : (prefixWord ++ tailWord_8197848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197848).length < 2 ^ (prefixWord ++ tailWord_8197848).sum := by decide
  have hdescent : baseEnd_8197848 < baseStart_8197848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197853 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_8197853 : Nat := 118140960795 + 8197853 * 2 ^ 59
def prefixEnd_8197853 : Nat := 4983230072969 + 3 ^ 40 * 8197853 * 2
def baseEnd_8197853 : Nat := 4209438923902819596136267

theorem tailTrace_8197853 : CollatzResearch.WordTrace tailWord_8197853 prefixEnd_8197853 4209438923902819596136267 := by
  unfold tailWord_8197853
  simp only [CollatzResearch.WordTrace]
  refine ⟨299000262769586137671302213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199333508513057425114201475 299000262769586137671302213)
  ·
    refine ⟨56062549269297400813369165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299000262769586137671302213 56062549269297400813369165)
    ·
      refine ⟨21023455975986525305013437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56062549269297400813369165 21023455975986525305013437)
      ·
        refine ⟨7883795990994946989380039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21023455975986525305013437 7883795990994946989380039)
        ·
          refine ⟨11825693986492420484070059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7883795990994946989380039 11825693986492420484070059)
          ·
            refine ⟨17738540979738630726105089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11825693986492420484070059 17738540979738630726105089)
            ·
              refine ⟨13303905734803973044578817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17738540979738630726105089 13303905734803973044578817)
              ·
                refine ⟨9977929301102979783434113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13303905734803973044578817 9977929301102979783434113)
                ·
                  refine ⟨7483446975827234837575585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9977929301102979783434113 7483446975827234837575585)
                  ·
                    refine ⟨5612585231870426128181689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7483446975827234837575585 5612585231870426128181689)
                    ·
                      refine ⟨4209438923902819596136267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612585231870426128181689 4209438923902819596136267)
                      ·
                        rfl

theorem cell23_8197853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_8197853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197853 prefixEnd_8197853 := by exact prefixLift 8197853
  have htrace : WordTrace (prefixWord ++ tailWord_8197853) baseStart_8197853 baseEnd_8197853 := by
    simpa [prefixWord, tailWord_8197853, baseEnd_8197853] using wordTrace_append hprefix tailTrace_8197853
  have hstable : (prefixWord ++ tailWord_8197853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197853).length < 2 ^ (prefixWord ++ tailWord_8197853).sum := by decide
  have hdescent : baseEnd_8197853 < baseStart_8197853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197875 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 1, 6, 2]
def baseStart_8197875 : Nat := 118140960795 + 8197875 * 2 ^ 59
def prefixEnd_8197875 : Nat := 4983230072969 + 3 ^ 40 * 8197875 * 2
def baseEnd_8197875 : Nat := 4209450220477218510061165

theorem tailTrace_8197875 : CollatzResearch.WordTrace tailWord_8197875 prefixEnd_8197875 4209450220477218510061165 := by
  unfold tailWord_8197875
  simp only [CollatzResearch.WordTrace]
  refine ⟨299001065175506435428603079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199334043450337623619068719 299001065175506435428603079)
  ·
    refine ⟨448501597763259653142904619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299001065175506435428603079 448501597763259653142904619)
    ·
      refine ⟨672752396644889479714356929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448501597763259653142904619 672752396644889479714356929)
      ·
        refine ⟨504564297483667109785767697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672752396644889479714356929 504564297483667109785767697)
        ·
          refine ⟨378423223112750332339325773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504564297483667109785767697 378423223112750332339325773)
          ·
            refine ⟨141908708667281374627247165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378423223112750332339325773 141908708667281374627247165)
            ·
              refine ⟨53215765750230515485217687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141908708667281374627247165 53215765750230515485217687)
              ·
                refine ⟨79823648625345773227826531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53215765750230515485217687 79823648625345773227826531)
                ·
                  refine ⟨119735472938018659841739797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79823648625345773227826531 119735472938018659841739797)
                  ·
                    refine ⟨5612600293969624680081553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119735472938018659841739797 5612600293969624680081553)
                    ·
                      refine ⟨4209450220477218510061165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612600293969624680081553 4209450220477218510061165)
                      ·
                        rfl

theorem cell23_8197875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 6, 2].length) (baseStart_8197875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197875 prefixEnd_8197875 := by exact prefixLift 8197875
  have htrace : WordTrace (prefixWord ++ tailWord_8197875) baseStart_8197875 baseEnd_8197875 := by
    simpa [prefixWord, tailWord_8197875, baseEnd_8197875] using wordTrace_append hprefix tailTrace_8197875
  have hstable : (prefixWord ++ tailWord_8197875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197875).length < 2 ^ (prefixWord ++ tailWord_8197875).sum := by decide
  have hdescent : baseEnd_8197875 < baseStart_8197875 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197888 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 4]
def baseStart_8197888 : Nat := 118140960795 + 8197888 * 2 ^ 59
def prefixEnd_8197888 : Nat := 4983230072969 + 3 ^ 40 * 8197888 * 2
def baseEnd_8197888 : Nat := 4209456895725726959198605

theorem tailTrace_8197888 : CollatzResearch.WordTrace tailWord_8197888 prefixEnd_8197888 4209456895725726959198605 := by
  unfold tailWord_8197888
  simp only [CollatzResearch.WordTrace]
  refine ⟨149500769662229669324413159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199334359549639559099217545 149500769662229669324413159)
  ·
    refine ⟨224251154493344503986619739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149500769662229669324413159 224251154493344503986619739)
    ·
      refine ⟨336376731740016755979929609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224251154493344503986619739 336376731740016755979929609)
      ·
        refine ⟨252282548805012566984947207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336376731740016755979929609 252282548805012566984947207)
        ·
          refine ⟨378423823207518850477420811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252282548805012566984947207 378423823207518850477420811)
          ·
            refine ⟨567635734811278275716131217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378423823207518850477420811 567635734811278275716131217)
            ·
              refine ⟨425726801108458706787098413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567635734811278275716131217 425726801108458706787098413)
              ·
                refine ⟨159647550415672015045161905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 425726801108458706787098413 159647550415672015045161905)
                ·
                  refine ⟨119735662811754011283871429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159647550415672015045161905 119735662811754011283871429)
                  ·
                    refine ⟨22450436777203877115725893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119735662811754011283871429 22450436777203877115725893)
                    ·
                      refine ⟨4209456895725726959198605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22450436777203877115725893 4209456895725726959198605)
                      ·
                        rfl

theorem cell23_8197888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_8197888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197888 prefixEnd_8197888 := by exact prefixLift 8197888
  have htrace : WordTrace (prefixWord ++ tailWord_8197888) baseStart_8197888 baseEnd_8197888 := by
    simpa [prefixWord, tailWord_8197888, baseEnd_8197888] using wordTrace_append hprefix tailTrace_8197888
  have hstable : (prefixWord ++ tailWord_8197888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197888).length < 2 ^ (prefixWord ++ tailWord_8197888).sum := by decide
  have hdescent : baseEnd_8197888 < baseStart_8197888 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197892 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_8197892 : Nat := 118140960795 + 8197892 * 2 ^ 59
def prefixEnd_8197892 : Nat := 4983230072969 + 3 ^ 40 * 8197892 * 2
def baseEnd_8197892 : Nat := 4209458949648344943548587

theorem tailTrace_8197892 : CollatzResearch.WordTrace tailWord_8197892 prefixEnd_8197892 4209458949648344943548587 := by
  unfold tailWord_8197892
  simp only [CollatzResearch.WordTrace]
  refine ⟨149500842608222423665985965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199334456810963231554647953 149500842608222423665985965)
  ·
    refine ⟨56062815978083408874744737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149500842608222423665985965 56062815978083408874744737)
    ·
      refine ⟨42047111983562556656058553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56062815978083408874744737 42047111983562556656058553)
      ·
        refine ⟨31535333987671917492043915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42047111983562556656058553 31535333987671917492043915)
        ·
          refine ⟨47303000981507876238065873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31535333987671917492043915 47303000981507876238065873)
          ·
            refine ⟨35477250736130907178549405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47303000981507876238065873 35477250736130907178549405)
            ·
              refine ⟨13303969026049090191956027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35477250736130907178549405 13303969026049090191956027)
              ·
                refine ⟨19955953539073635287934041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13303969026049090191956027 19955953539073635287934041)
                ·
                  refine ⟨14966965154305226465950531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19955953539073635287934041 14966965154305226465950531)
                  ·
                    refine ⟨22450447731457839698925797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14966965154305226465950531 22450447731457839698925797)
                    ·
                      refine ⟨4209458949648344943548587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22450447731457839698925797 4209458949648344943548587)
                      ·
                        rfl

theorem cell23_8197892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_8197892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197892 prefixEnd_8197892 := by exact prefixLift 8197892
  have htrace : WordTrace (prefixWord ++ tailWord_8197892) baseStart_8197892 baseEnd_8197892 := by
    simpa [prefixWord, tailWord_8197892, baseEnd_8197892] using wordTrace_append hprefix tailTrace_8197892
  have hstable : (prefixWord ++ tailWord_8197892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197892).length < 2 ^ (prefixWord ++ tailWord_8197892).sum := by decide
  have hdescent : baseEnd_8197892 < baseStart_8197892 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197932 : List Nat := [2, 2, 1, 1, 1, 6, 3, 1, 6]
def baseStart_8197932 : Nat := 118140960795 + 8197932 * 2 ^ 59
def prefixEnd_8197932 : Nat := 4983230072969 + 3 ^ 40 * 8197932 * 2
def baseEnd_8197932 : Nat := 467719943208280531894267

theorem tailTrace_8197932 : CollatzResearch.WordTrace tailWord_8197932 prefixEnd_8197932 467719943208280531894267 := by
  unfold tailWord_8197932
  simp only [CollatzResearch.WordTrace]
  refine ⟨149501572068149967081714025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199335429424199956108952033 149501572068149967081714025)
  ·
    refine ⟨112126179051112475311285519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149501572068149967081714025 112126179051112475311285519)
    ·
      refine ⟨168189268576668712966928279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112126179051112475311285519 168189268576668712966928279)
      ·
        refine ⟨252283902865003069450392419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168189268576668712966928279 252283902865003069450392419)
        ·
          refine ⟨378425854297504604175588629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252283902865003069450392419 378425854297504604175588629)
          ·
            refine ⟨17738711920195528320730717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 378425854297504604175588629 17738711920195528320730717)
            ·
              refine ⟨6652016970073323120274019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17738711920195528320730717 6652016970073323120274019)
              ·
                refine ⟨9978025455109984680411029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6652016970073323120274019 9978025455109984680411029)
                ·
                  refine ⟨467719943208280531894267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9978025455109984680411029 467719943208280531894267)
                  ·
                    rfl

theorem cell23_8197932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_8197932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197932 prefixEnd_8197932 := by exact prefixLift 8197932
  have htrace : WordTrace (prefixWord ++ tailWord_8197932) baseStart_8197932 baseEnd_8197932 := by
    simpa [prefixWord, tailWord_8197932, baseEnd_8197932] using wordTrace_append hprefix tailTrace_8197932
  have hstable : (prefixWord ++ tailWord_8197932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197932).length < 2 ^ (prefixWord ++ tailWord_8197932).sum := by decide
  have hdescent : baseEnd_8197932 < baseStart_8197932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197969 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 2, 3, 2]
def baseStart_8197969 : Nat := 118140960795 + 8197969 * 2 ^ 59
def prefixEnd_8197969 : Nat := 4983230072969 + 3 ^ 40 * 8197969 * 2
def baseEnd_8197969 : Nat := 4209498487658741142285733

theorem tailTrace_8197969 : CollatzResearch.WordTrace tailWord_8197969 prefixEnd_8197969 4209498487658741142285733 := by
  unfold tailWord_8197969
  simp only [CollatzResearch.WordTrace]
  refine ⟨299004493637165889482524961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199336329091443926321683307 299004493637165889482524961)
  ·
    refine ⟨224253370227874417111893721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299004493637165889482524961 224253370227874417111893721)
    ·
      refine ⟨168190027670905812833920291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224253370227874417111893721 168190027670905812833920291)
      ·
        refine ⟨252285041506358719250880437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168190027670905812833920291 252285041506358719250880437)
        ·
          refine ⟨23651722641221129929770041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252285041506358719250880437 23651722641221129929770041)
          ·
            refine ⟨17738791980915847447327531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23651722641221129929770041 17738791980915847447327531)
            ·
              refine ⟨26608187971373771170991297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17738791980915847447327531 26608187971373771170991297)
              ·
                refine ⟨19956140978530328378243473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26608187971373771170991297 19956140978530328378243473)
                ·
                  refine ⟨14967105733897746283682605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19956140978530328378243473 14967105733897746283682605)
                  ·
                    refine ⟨5612664650211654856380977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14967105733897746283682605 5612664650211654856380977)
                    ·
                      refine ⟨4209498487658741142285733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612664650211654856380977 4209498487658741142285733)
                      ·
                        rfl

theorem cell23_8197969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 3, 2].length) (baseStart_8197969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197969 prefixEnd_8197969 := by exact prefixLift 8197969
  have htrace : WordTrace (prefixWord ++ tailWord_8197969) baseStart_8197969 baseEnd_8197969 := by
    simpa [prefixWord, tailWord_8197969, baseEnd_8197969] using wordTrace_append hprefix tailTrace_8197969
  have hstable : (prefixWord ++ tailWord_8197969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197969).length < 2 ^ (prefixWord ++ tailWord_8197969).sum := by decide
  have hdescent : baseEnd_8197969 < baseStart_8197969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197985 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_8197985 : Nat := 118140960795 + 8197985 * 2 ^ 59
def prefixEnd_8197985 : Nat := 4983230072969 + 3 ^ 40 * 8197985 * 2
def baseEnd_8197985 : Nat := 4209506703349213079685659

theorem tailTrace_8197985 : CollatzResearch.WordTrace tailWord_8197985 prefixEnd_8197985 4209506703349213079685659 := by
  unfold tailWord_8197985
  simp only [CollatzResearch.WordTrace]
  refine ⟨299005077205107924215107409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199336718136738616143404939 299005077205107924215107409)
  ·
    refine ⟨224253807903830943161330557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299005077205107924215107409 224253807903830943161330557)
    ·
      refine ⟨84095177963936603685498959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224253807903830943161330557 84095177963936603685498959)
      ·
        refine ⟨126142766945904905528248439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84095177963936603685498959 126142766945904905528248439)
        ·
          refine ⟨189214150418857358292372659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126142766945904905528248439 189214150418857358292372659)
          ·
            refine ⟨283821225628286037438558989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189214150418857358292372659 283821225628286037438558989)
            ·
              refine ⟨106432959610607264039459621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283821225628286037438558989 106432959610607264039459621)
              ·
                refine ⟨19956179926988862007398679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106432959610607264039459621 19956179926988862007398679)
                ·
                  refine ⟨29934269890483293011098019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19956179926988862007398679 29934269890483293011098019)
                  ·
                    refine ⟨44901404835724939516647029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29934269890483293011098019 44901404835724939516647029)
                    ·
                      refine ⟨4209506703349213079685659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44901404835724939516647029 4209506703349213079685659)
                      ·
                        rfl

theorem cell23_8197985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_8197985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197985 prefixEnd_8197985 := by exact prefixLift 8197985
  have htrace : WordTrace (prefixWord ++ tailWord_8197985) baseStart_8197985 baseEnd_8197985 := by
    simpa [prefixWord, tailWord_8197985, baseEnd_8197985] using wordTrace_append hprefix tailTrace_8197985
  have hstable : (prefixWord ++ tailWord_8197985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197985).length < 2 ^ (prefixWord ++ tailWord_8197985).sum := by decide
  have hdescent : baseEnd_8197985 < baseStart_8197985 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8197995 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 4]
def baseStart_8197995 : Nat := 118140960795 + 8197995 * 2 ^ 59
def prefixEnd_8197995 : Nat := 4983230072969 + 3 ^ 40 * 8197995 * 2
def baseEnd_8197995 : Nat := 4209511838155758040560613

theorem tailTrace_8197995 : CollatzResearch.WordTrace tailWord_8197995 prefixEnd_8197995 4209511838155758040560613 := by
  unfold tailWord_8197995
  simp only [CollatzResearch.WordTrace]
  refine ⟨299005441935071695922971439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199336961290047797281980959 299005441935071695922971439)
  ·
    refine ⟨448508162902607543884457159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299005441935071695922971439 448508162902607543884457159)
    ·
      refine ⟨672762244353911315826685739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448508162902607543884457159 672762244353911315826685739)
      ·
        refine ⟨1009143366530866973740028609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672762244353911315826685739 1009143366530866973740028609)
        ·
          refine ⟨756857524898150230305021457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1009143366530866973740028609 756857524898150230305021457)
          ·
            refine ⟨567643143673612672728766093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756857524898150230305021457 567643143673612672728766093)
            ·
              refine ⟨212866178877604752273287285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 567643143673612672728766093 212866178877604752273287285)
              ·
                refine ⟨19956204269775445525620683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212866178877604752273287285 19956204269775445525620683)
                ·
                  refine ⟨29934306404663168288431025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19956204269775445525620683 29934306404663168288431025)
                  ·
                    refine ⟨22450729803497376216323269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29934306404663168288431025 22450729803497376216323269)
                    ·
                      refine ⟨4209511838155758040560613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22450729803497376216323269 4209511838155758040560613)
                      ·
                        rfl

theorem cell23_8197995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 4].length) (baseStart_8197995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8197995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8197995 prefixEnd_8197995 := by exact prefixLift 8197995
  have htrace : WordTrace (prefixWord ++ tailWord_8197995) baseStart_8197995 baseEnd_8197995 := by
    simpa [prefixWord, tailWord_8197995, baseEnd_8197995] using wordTrace_append hprefix tailTrace_8197995
  have hstable : (prefixWord ++ tailWord_8197995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8197995).length < 2 ^ (prefixWord ++ tailWord_8197995).sum := by decide
  have hdescent : baseEnd_8197995 < baseStart_8197995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8197995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198005 : List Nat := [1, 3, 4, 1, 1, 1, 1, 11]
def baseStart_8198005 : Nat := 118140960795 + 8198005 * 2 ^ 59
def prefixEnd_8198005 : Nat := 4983230072969 + 3 ^ 40 * 8198005 * 2
def baseEnd_8198005 : Nat := 155908036035640851905021

theorem tailTrace_8198005 : CollatzResearch.WordTrace tailWord_8198005 prefixEnd_8198005 155908036035640851905021 := by
  unfold tailWord_8198005
  simp only [CollatzResearch.WordTrace]
  refine ⟨299005806665035467630835469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199337204443356978420556979 299005806665035467630835469)
  ·
    refine ⟨112127177499388300361563301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299005806665035467630835469 112127177499388300361563301)
    ·
      refine ⟨21023845781135306317793119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112127177499388300361563301 21023845781135306317793119)
      ·
        refine ⟨31535768671702959476689679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21023845781135306317793119 31535768671702959476689679)
        ·
          refine ⟨47303653007554439215034519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31535768671702959476689679 47303653007554439215034519)
          ·
            refine ⟨70955479511331658822551779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47303653007554439215034519 70955479511331658822551779)
            ·
              refine ⟨106433219266997488233827669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70955479511331658822551779 106433219266997488233827669)
              ·
                refine ⟨155908036035640851905021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 106433219266997488233827669 155908036035640851905021)
                ·
                  rfl

theorem cell23_8198005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 11].length) (baseStart_8198005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198005 prefixEnd_8198005 := by exact prefixLift 8198005
  have htrace : WordTrace (prefixWord ++ tailWord_8198005) baseStart_8198005 baseEnd_8198005 := by
    simpa [prefixWord, tailWord_8198005, baseEnd_8198005] using wordTrace_append hprefix tailTrace_8198005
  have hstable : (prefixWord ++ tailWord_8198005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198005).length < 2 ^ (prefixWord ++ tailWord_8198005).sum := by decide
  have hdescent : baseEnd_8198005 < baseStart_8198005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198016 : List Nat := [2, 1, 1, 2, 1, 2, 4, 5, 1, 2, 2]
def baseStart_8198016 : Nat := 118140960795 + 8198016 * 2 ^ 59
def prefixEnd_8198016 : Nat := 4983230072969 + 3 ^ 40 * 8198016 * 2
def baseEnd_8198016 : Nat := 4209522621249502458398017

theorem tailTrace_8198016 : CollatzResearch.WordTrace tailWord_8198016 prefixEnd_8198016 4209522621249502458398017 := by
  unfold tailWord_8198016
  simp only [CollatzResearch.WordTrace]
  refine ⟨149503103933997808254742951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199337471911997077672990601 149503103933997808254742951)
  ·
    refine ⟨224254655900996712382114427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149503103933997808254742951 224254655900996712382114427)
    ·
      refine ⟨336381983851495068573171641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224254655900996712382114427 336381983851495068573171641)
      ·
        refine ⟨252286487888621301429878731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336381983851495068573171641 252286487888621301429878731)
        ·
          refine ⟨378429731832931952144818097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252286487888621301429878731 378429731832931952144818097)
          ·
            refine ⟨283822298874698964108613573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378429731832931952144818097 283822298874698964108613573)
            ·
              refine ⟨53216681039006055770365045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283822298874698964108613573 53216681039006055770365045)
              ·
                refine ⟨4989063847406817728471723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53216681039006055770365045 4989063847406817728471723)
                ·
                  refine ⟨7483595771110226592707585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989063847406817728471723 7483595771110226592707585)
                  ·
                    refine ⟨5612696828332669944530689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7483595771110226592707585 5612696828332669944530689)
                    ·
                      refine ⟨4209522621249502458398017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612696828332669944530689 4209522621249502458398017)
                      ·
                        rfl

theorem cell23_8198016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 1, 2, 2].length) (baseStart_8198016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198016 prefixEnd_8198016 := by exact prefixLift 8198016
  have htrace : WordTrace (prefixWord ++ tailWord_8198016) baseStart_8198016 baseEnd_8198016 := by
    simpa [prefixWord, tailWord_8198016, baseEnd_8198016] using wordTrace_append hprefix tailTrace_8198016
  have hstable : (prefixWord ++ tailWord_8198016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198016).length < 2 ^ (prefixWord ++ tailWord_8198016).sum := by decide
  have hdescent : baseEnd_8198016 < baseStart_8198016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198026 : List Nat := [3, 1, 2, 4, 2, 1, 2, 2, 2, 4]
def baseStart_8198026 : Nat := 118140960795 + 8198026 * 2 ^ 59
def prefixEnd_8198026 : Nat := 4983230072969 + 3 ^ 40 * 8198026 * 2
def baseEnd_8198026 : Nat := 1403175918685349139757657

theorem tailTrace_8198026 : CollatzResearch.WordTrace tailWord_8198026 prefixEnd_8198026 1403175918685349139757657 := by
  unfold tailWord_8198026
  simp only [CollatzResearch.WordTrace]
  refine ⟨74751643149489847054337483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199337715065306258811566621 74751643149489847054337483)
  ·
    refine ⟨112127464724234770581506225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74751643149489847054337483 112127464724234770581506225)
    ·
      refine ⟨84095598543176077936129669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112127464724234770581506225 84095598543176077936129669)
      ·
        refine ⟨15767924726845514613024313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84095598543176077936129669 15767924726845514613024313)
        ·
          refine ⟨11825943545134135959768235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15767924726845514613024313 11825943545134135959768235)
          ·
            refine ⟨17738915317701203939652353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11825943545134135959768235 17738915317701203939652353)
            ·
              refine ⟨13304186488275902954739265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17738915317701203939652353 13304186488275902954739265)
              ·
                refine ⟨9978139866206927216054449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13304186488275902954739265 9978139866206927216054449)
                ·
                  refine ⟨7483604899655195412040837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9978139866206927216054449 7483604899655195412040837)
                  ·
                    refine ⟨1403175918685349139757657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7483604899655195412040837 1403175918685349139757657)
                    ·
                      rfl

theorem cell23_8198026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_8198026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198026 prefixEnd_8198026 := by exact prefixLift 8198026
  have htrace : WordTrace (prefixWord ++ tailWord_8198026) baseStart_8198026 baseEnd_8198026 := by
    simpa [prefixWord, tailWord_8198026, baseEnd_8198026] using wordTrace_append hprefix tailTrace_8198026
  have hstable : (prefixWord ++ tailWord_8198026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198026).length < 2 ^ (prefixWord ++ tailWord_8198026).sum := by decide
  have hdescent : baseEnd_8198026 < baseStart_8198026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198033 : List Nat := [1, 2, 2, 1, 1, 1, 8, 2, 1, 2, 2]
def baseStart_8198033 : Nat := 118140960795 + 8198033 * 2 ^ 59
def prefixEnd_8198033 : Nat := 4983230072969 + 3 ^ 40 * 8198033 * 2
def baseEnd_8198033 : Nat := 4209531350420628891885439

theorem tailTrace_8198033 : CollatzResearch.WordTrace tailWord_8198033 prefixEnd_8198033 4209531350420628891885439 := by
  unfold tailWord_8198033
  simp only [CollatzResearch.WordTrace]
  refine ⟨299006827908934028412854753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199337885272622685608569835 299006827908934028412854753)
  ·
    refine ⟨224255120931700521309641065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299006827908934028412854753 224255120931700521309641065)
    ·
      refine ⟨168191340698775390982230799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224255120931700521309641065 168191340698775390982230799)
      ·
        refine ⟨252287011048163086473346199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168191340698775390982230799 252287011048163086473346199)
        ·
          refine ⟨378430516572244629710019299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252287011048163086473346199 378430516572244629710019299)
          ·
            refine ⟨567645774858366944565028949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378430516572244629710019299 567645774858366944565028949)
            ·
              refine ⟨6652098924121487631621433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 567645774858366944565028949 6652098924121487631621433)
              ·
                refine ⟨4989074193091115723716075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6652098924121487631621433 4989074193091115723716075)
                ·
                  refine ⟨7483611289636673585574113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989074193091115723716075 7483611289636673585574113)
                  ·
                    refine ⟨5612708467227505189180585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7483611289636673585574113 5612708467227505189180585)
                    ·
                      refine ⟨4209531350420628891885439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612708467227505189180585 4209531350420628891885439)
                      ·
                        rfl

theorem cell23_8198033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 1, 2, 2].length) (baseStart_8198033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198033 prefixEnd_8198033 := by exact prefixLift 8198033
  have htrace : WordTrace (prefixWord ++ tailWord_8198033) baseStart_8198033 baseEnd_8198033 := by
    simpa [prefixWord, tailWord_8198033, baseEnd_8198033] using wordTrace_append hprefix tailTrace_8198033
  have hstable : (prefixWord ++ tailWord_8198033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198033).length < 2 ^ (prefixWord ++ tailWord_8198033).sum := by decide
  have hdescent : baseEnd_8198033 < baseStart_8198033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198056 : List Nat := [2, 1, 6, 2, 1, 1, 3, 7]
def baseStart_8198056 : Nat := 118140960795 + 8198056 * 2 ^ 59
def prefixEnd_8198056 : Nat := 4983230072969 + 3 ^ 40 * 8198056 * 2
def baseEnd_8198056 : Nat := 155909005943543788959179

theorem tailTrace_8198056 : CollatzResearch.WordTrace tailWord_8198056 prefixEnd_8198056 155909005943543788959179 := by
  unfold tailWord_8198056
  simp only [CollatzResearch.WordTrace]
  refine ⟨149503833393925351670471011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199338444525233802227294681 149503833393925351670471011)
  ·
    refine ⟨224255750090888027505706517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149503833393925351670471011 224255750090888027505706517)
    ·
      refine ⟨10511988285510376289329993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224255750090888027505706517 10511988285510376289329993)
      ·
        refine ⟨7883991214132782216997495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10511988285510376289329993 7883991214132782216997495)
        ·
          refine ⟨11825986821199173325496243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7883991214132782216997495 11825986821199173325496243)
          ·
            refine ⟨17738980231798759988244365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11825986821199173325496243 17738980231798759988244365)
            ·
              refine ⟨6652117586924534995591637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17738980231798759988244365 6652117586924534995591637)
              ·
                refine ⟨155909005943543788959179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6652117586924534995591637 155909005943543788959179)
                ·
                  rfl

theorem cell23_8198056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 7].length) (baseStart_8198056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198056 prefixEnd_8198056 := by exact prefixLift 8198056
  have htrace : WordTrace (prefixWord ++ tailWord_8198056) baseStart_8198056 baseEnd_8198056 := by
    simpa [prefixWord, tailWord_8198056, baseEnd_8198056] using wordTrace_append hprefix tailTrace_8198056
  have hstable : (prefixWord ++ tailWord_8198056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198056).length < 2 ^ (prefixWord ++ tailWord_8198056).sum := by decide
  have hdescent : baseEnd_8198056 < baseStart_8198056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198089 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 4, 2, 2]
def baseStart_8198089 : Nat := 118140960795 + 8198089 * 2 ^ 59
def prefixEnd_8198089 : Nat := 4983230072969 + 3 ^ 40 * 8198089 * 2
def baseEnd_8198089 : Nat := 4209560105337280672785181

theorem tailTrace_8198089 : CollatzResearch.WordTrace tailWord_8198089 prefixEnd_8198089 4209560105337280672785181 := by
  unfold tailWord_8198089
  simp only [CollatzResearch.WordTrace]
  refine ⟨299008870396731149976893321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199339246931154099984595547 299008870396731149976893321)
  ·
    refine ⟨224256652797548362482669991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299008870396731149976893321 224256652797548362482669991)
    ·
      refine ⟨336384979196322543724004987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224256652797548362482669991 336384979196322543724004987)
      ·
        refine ⟨504577468794483815586007481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336384979196322543724004987 504577468794483815586007481)
        ·
          refine ⟨378433101595862861689505611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504577468794483815586007481 378433101595862861689505611)
          ·
            refine ⟨567649652393794292534258417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378433101595862861689505611 567649652393794292534258417)
            ·
              refine ⟨425737239295345719400693813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567649652393794292534258417 425737239295345719400693813)
              ·
                refine ⟨39912866183938661193815045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 425737239295345719400693813 39912866183938661193815045)
                ·
                  refine ⟨7483662409488498973840321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39912866183938661193815045 7483662409488498973840321)
                  ·
                    refine ⟨5612746807116374230380241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7483662409488498973840321 5612746807116374230380241)
                    ·
                      refine ⟨4209560105337280672785181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612746807116374230380241 4209560105337280672785181)
                      ·
                        rfl

theorem cell23_8198089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 4, 2, 2].length) (baseStart_8198089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198089 prefixEnd_8198089 := by exact prefixLift 8198089
  have htrace : WordTrace (prefixWord ++ tailWord_8198089) baseStart_8198089 baseEnd_8198089 := by
    simpa [prefixWord, tailWord_8198089, baseEnd_8198089] using wordTrace_append hprefix tailTrace_8198089
  have hstable : (prefixWord ++ tailWord_8198089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198089).length < 2 ^ (prefixWord ++ tailWord_8198089).sum := by decide
  have hdescent : baseEnd_8198089 < baseStart_8198089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198135 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_8198135 : Nat := 118140960795 + 8198135 * 2 ^ 59
def prefixEnd_8198135 : Nat := 4983230072969 + 3 ^ 40 * 8198135 * 2
def baseEnd_8198135 : Nat := 4209583725447387492809969

theorem tailTrace_8198135 : CollatzResearch.WordTrace tailWord_8198135 prefixEnd_8198135 4209583725447387492809969 := by
  unfold tailWord_8198135
  simp only [CollatzResearch.WordTrace]
  refine ⟨299010548154564499833067859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199340365436376333222045239 299010548154564499833067859)
  ·
    refine ⟨448515822231846749749601789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299010548154564499833067859 448515822231846749749601789)
    ·
      refine ⟨168193433336942531156100671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448515822231846749749601789 168193433336942531156100671)
      ·
        refine ⟨252290150005413796734151007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168193433336942531156100671 252290150005413796734151007)
        ·
          refine ⟨378435225008120695101226511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252290150005413796734151007 378435225008120695101226511)
          ·
            refine ⟨567652837512181042651839767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378435225008120695101226511 567652837512181042651839767)
            ·
              refine ⟨851479256268271563977759651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567652837512181042651839767 851479256268271563977759651)
              ·
                refine ⟨1277218884402407345966639477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851479256268271563977759651 1277218884402407345966639477)
                ·
                  refine ⟨119739270412725688684372451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1277218884402407345966639477 119739270412725688684372451)
                  ·
                    refine ⟨179608905619088533026558677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119739270412725688684372451 179608905619088533026558677)
                    ·
                      refine ⟨4209583725447387492809969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179608905619088533026558677 4209583725447387492809969)
                      ·
                        rfl

theorem cell23_8198135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_8198135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198135 prefixEnd_8198135 := by exact prefixLift 8198135
  have htrace : WordTrace (prefixWord ++ tailWord_8198135) baseStart_8198135 baseEnd_8198135 := by
    simpa [prefixWord, tailWord_8198135, baseEnd_8198135] using wordTrace_append hprefix tailTrace_8198135
  have hstable : (prefixWord ++ tailWord_8198135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198135).length < 2 ^ (prefixWord ++ tailWord_8198135).sum := by decide
  have hdescent : baseEnd_8198135 < baseStart_8198135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198152 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_8198152 : Nat := 118140960795 + 8198152 * 2 ^ 59
def prefixEnd_8198152 : Nat := 4983230072969 + 3 ^ 40 * 8198152 * 2
def baseEnd_8198152 : Nat := 4209592454618513926297391

theorem tailTrace_8198152 : CollatzResearch.WordTrace tailWord_8198152 prefixEnd_8198152 4209592454618513926297391 := by
  unfold tailWord_8198152
  simp only [CollatzResearch.WordTrace]
  refine ⟨149505584097751455868218355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199340778797001941157624473 149505584097751455868218355)
  ·
    refine ⟨224258376146627183802327533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149505584097751455868218355 224258376146627183802327533)
    ·
      refine ⟨84096891054985193925872825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224258376146627183802327533 84096891054985193925872825)
      ·
        refine ⟨63072668291238895444404619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84096891054985193925872825 63072668291238895444404619)
        ·
          refine ⟨94609002436858343166606929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63072668291238895444404619 94609002436858343166606929)
          ·
            refine ⟨70956751827643757374955197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94609002436858343166606929 70956751827643757374955197)
            ·
              refine ⟨26608781935366409015608199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70956751827643757374955197 26608781935366409015608199)
              ·
                refine ⟨39913172903049613523412299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26608781935366409015608199 39913172903049613523412299)
                ·
                  refine ⟨59869759354574420285118449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39913172903049613523412299 59869759354574420285118449)
                  ·
                    refine ⟨44902319515930815213838837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59869759354574420285118449 44902319515930815213838837)
                    ·
                      refine ⟨4209592454618513926297391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44902319515930815213838837 4209592454618513926297391)
                      ·
                        rfl

theorem cell23_8198152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_8198152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198152 prefixEnd_8198152 := by exact prefixLift 8198152
  have htrace : WordTrace (prefixWord ++ tailWord_8198152) baseStart_8198152 baseEnd_8198152 := by
    simpa [prefixWord, tailWord_8198152, baseEnd_8198152] using wordTrace_append hprefix tailTrace_8198152
  have hstable : (prefixWord ++ tailWord_8198152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198152).length < 2 ^ (prefixWord ++ tailWord_8198152).sum := by decide
  have hdescent : baseEnd_8198152 < baseStart_8198152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198179 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 4]
def baseStart_8198179 : Nat := 118140960795 + 8198179 * 2 ^ 59
def prefixEnd_8198179 : Nat := 4983230072969 + 3 ^ 40 * 8198179 * 2
def baseEnd_8198179 : Nat := 4209606318596185320659767

theorem tailTrace_8198179 : CollatzResearch.WordTrace tailWord_8198179 prefixEnd_8198179 4209606318596185320659767 := by
  unfold tailWord_8198179
  simp only [CollatzResearch.WordTrace]
  refine ⟨299012152966405095347669591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199341435310936730231779727 299012152966405095347669591)
  ·
    refine ⟨448518229449607643021504387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299012152966405095347669591 448518229449607643021504387)
    ·
      refine ⟨672777344174411464532256581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448518229449607643021504387 672777344174411464532256581)
      ·
        refine ⟨126145752032702149599798109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 672777344174411464532256581 126145752032702149599798109)
        ·
          refine ⟨47304657012263306099924291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126145752032702149599798109 47304657012263306099924291)
          ·
            refine ⟨70956985518394959149886437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47304657012263306099924291 70956985518394959149886437)
            ·
              refine ⟨13304434784699054840603707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70956985518394959149886437 13304434784699054840603707)
              ·
                refine ⟨19956652177048582260905561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13304434784699054840603707 19956652177048582260905561)
                ·
                  refine ⟨14967489132786436695679171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19956652177048582260905561 14967489132786436695679171)
                  ·
                    refine ⟨22451233699179655043518757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14967489132786436695679171 22451233699179655043518757)
                    ·
                      refine ⟨4209606318596185320659767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22451233699179655043518757 4209606318596185320659767)
                      ·
                        rfl

theorem cell23_8198179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_8198179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198179 prefixEnd_8198179 := by exact prefixLift 8198179
  have htrace : WordTrace (prefixWord ++ tailWord_8198179) baseStart_8198179 baseEnd_8198179 := by
    simpa [prefixWord, tailWord_8198179, baseEnd_8198179] using wordTrace_append hprefix tailTrace_8198179
  have hstable : (prefixWord ++ tailWord_8198179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198179).length < 2 ^ (prefixWord ++ tailWord_8198179).sum := by decide
  have hdescent : baseEnd_8198179 < baseStart_8198179 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198199 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 3]
def baseStart_8198199 : Nat := 118140960795 + 8198199 * 2 ^ 59
def prefixEnd_8198199 : Nat := 4983230072969 + 3 ^ 40 * 8198199 * 2
def baseEnd_8198199 : Nat := 4209616588209275242409675

theorem tailTrace_8198199 : CollatzResearch.WordTrace tailWord_8198199 prefixEnd_8198199 4209616588209275242409675 := by
  unfold tailWord_8198199
  simp only [CollatzResearch.WordTrace]
  refine ⟨299012882426332638763397651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199341921617555092508931767 299012882426332638763397651)
  ·
    refine ⟨448519323639498958145096477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299012882426332638763397651 448519323639498958145096477)
    ·
      refine ⟨168194746364812109304411179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448519323639498958145096477 168194746364812109304411179)
      ·
        refine ⟨252292119547218163956616769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168194746364812109304411179 252292119547218163956616769)
        ·
          refine ⟨189219089660413622967462577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252292119547218163956616769 189219089660413622967462577)
          ·
            refine ⟨141914317245310217225596933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189219089660413622967462577 141914317245310217225596933)
            ·
              refine ⟨26608934483495665729799425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141914317245310217225596933 26608934483495665729799425)
              ·
                refine ⟨19956700862621749297349569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26608934483495665729799425 19956700862621749297349569)
                ·
                  refine ⟨14967525646966311973012177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19956700862621749297349569 14967525646966311973012177)
                  ·
                    refine ⟨11225644235224733979759133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14967525646966311973012177 11225644235224733979759133)
                    ·
                      refine ⟨4209616588209275242409675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11225644235224733979759133 4209616588209275242409675)
                      ·
                        rfl

theorem cell23_8198199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_8198199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198199 prefixEnd_8198199 := by exact prefixLift 8198199
  have htrace : WordTrace (prefixWord ++ tailWord_8198199) baseStart_8198199 baseEnd_8198199 := by
    simpa [prefixWord, tailWord_8198199, baseEnd_8198199] using wordTrace_append hprefix tailTrace_8198199
  have hstable : (prefixWord ++ tailWord_8198199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198199).length < 2 ^ (prefixWord ++ tailWord_8198199).sum := by decide
  have hdescent : baseEnd_8198199 < baseStart_8198199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198230 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_8198230 : Nat := 118140960795 + 8198230 * 2 ^ 59
def prefixEnd_8198230 : Nat := 4983230072969 + 3 ^ 40 * 8198230 * 2
def baseEnd_8198230 : Nat := 4209632506109564621122033

theorem tailTrace_8198230 : CollatzResearch.WordTrace tailWord_8198230 prefixEnd_8198230 4209632506109564621122033 := by
  unfold tailWord_8198230
  simp only [CollatzResearch.WordTrace]
  refine ⟨18688375818076270691111009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199342675392813554038517429 18688375818076270691111009)
  ·
    refine ⟨14016281863557203018333257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18688375818076270691111009 14016281863557203018333257)
    ·
      refine ⟨10512211397667902263749943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14016281863557203018333257 10512211397667902263749943)
      ·
        refine ⟨15768317096501853395624915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10512211397667902263749943 15768317096501853395624915)
        ·
          refine ⟨23652475644752780093437373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15768317096501853395624915 23652475644752780093437373)
          ·
            refine ⟨8869678366782292535039015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23652475644752780093437373 8869678366782292535039015)
            ·
              refine ⟨13304517550173438802558523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869678366782292535039015 13304517550173438802558523)
              ·
                refine ⟨19956776325260158203837785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13304517550173438802558523 19956776325260158203837785)
                ·
                  refine ⟨14967582243945118652878339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19956776325260158203837785 14967582243945118652878339)
                  ·
                    refine ⟨22451373365917677979317509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14967582243945118652878339 22451373365917677979317509)
                    ·
                      refine ⟨4209632506109564621122033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22451373365917677979317509 4209632506109564621122033)
                      ·
                        rfl

theorem cell23_8198230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_8198230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198230 prefixEnd_8198230 := by exact prefixLift 8198230
  have htrace : WordTrace (prefixWord ++ tailWord_8198230) baseStart_8198230 baseEnd_8198230 := by
    simpa [prefixWord, tailWord_8198230, baseEnd_8198230] using wordTrace_append hprefix tailTrace_8198230
  have hstable : (prefixWord ++ tailWord_8198230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198230).length < 2 ^ (prefixWord ++ tailWord_8198230).sum := by decide
  have hdescent : baseEnd_8198230 < baseStart_8198230 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198249 : List Nat := [1, 2, 1, 1, 1, 5, 3, 3, 1, 5]
def baseStart_8198249 : Nat := 118140960795 + 8198249 * 2 ^ 59
def prefixEnd_8198249 : Nat := 4983230072969 + 3 ^ 40 * 8198249 * 2
def baseEnd_8198249 : Nat := 1403214087414000015594815

theorem tailTrace_8198249 : CollatzResearch.WordTrace tailWord_8198249 prefixEnd_8198249 1403214087414000015594815 := by
  unfold tailWord_8198249
  simp only [CollatzResearch.WordTrace]
  refine ⟨299014706076151497302717801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199343137384100998201811867 299014706076151497302717801)
  ·
    refine ⟨224261029557113622977038351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299014706076151497302717801 224261029557113622977038351)
    ·
      refine ⟨336391544335670434465557527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224261029557113622977038351 336391544335670434465557527)
      ·
        refine ⟨504587316503505651698336291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336391544335670434465557527 504587316503505651698336291)
        ·
          refine ⟨756880974755258477547504437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504587316503505651698336291 756880974755258477547504437)
          ·
            refine ⟨70957591383305482270078541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 756880974755258477547504437 70957591383305482270078541)
            ·
              refine ⟨26609096768739555851279453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70957591383305482270078541 26609096768739555851279453)
              ·
                refine ⟨9978411288277333444229795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26609096768739555851279453 9978411288277333444229795)
                ·
                  refine ⟨14967616932416000166344693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9978411288277333444229795 14967616932416000166344693)
                  ·
                    refine ⟨1403214087414000015594815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14967616932416000166344693 1403214087414000015594815)
                    ·
                      rfl

theorem cell23_8198249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 5].length) (baseStart_8198249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198249 prefixEnd_8198249 := by exact prefixLift 8198249
  have htrace : WordTrace (prefixWord ++ tailWord_8198249) baseStart_8198249 baseEnd_8198249 := by
    simpa [prefixWord, tailWord_8198249, baseEnd_8198249] using wordTrace_append hprefix tailTrace_8198249
  have hstable : (prefixWord ++ tailWord_8198249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198249).length < 2 ^ (prefixWord ++ tailWord_8198249).sum := by decide
  have hdescent : baseEnd_8198249 < baseStart_8198249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198263 : List Nat := [1, 1, 3, 1, 1, 5, 2, 4, 1, 1, 3]
def baseStart_8198263 : Nat := 118140960795 + 8198263 * 2 ^ 59
def prefixEnd_8198263 : Nat := 4983230072969 + 3 ^ 40 * 8198263 * 2
def baseEnd_8198263 : Nat := 4209649450971162992009381

theorem tailTrace_8198263 : CollatzResearch.WordTrace tailWord_8198263 prefixEnd_8198263 4209649450971162992009381 := by
  unfold tailWord_8198263
  simp only [CollatzResearch.WordTrace]
  refine ⟨299015216698100777693727443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199343477798733851795818295 299015216698100777693727443)
  ·
    refine ⟨448522825047151166540591165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299015216698100777693727443 448522825047151166540591165)
    ·
      refine ⟨168196059392681687452721687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448522825047151166540591165 168196059392681687452721687)
      ·
        refine ⟨252294089089022531179082531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168196059392681687452721687 252294089089022531179082531)
        ·
          refine ⟨378441133633533796768623797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252294089089022531179082531 378441133633533796768623797)
          ·
            refine ⟨35478856278143793447058481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 378441133633533796768623797 35478856278143793447058481)
            ·
              refine ⟨26609142208607845085293861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35478856278143793447058481 26609142208607845085293861)
              ·
                refine ⟨4989214164113970953492599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26609142208607845085293861 4989214164113970953492599)
                ·
                  refine ⟨7483821246170956430238899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989214164113970953492599 7483821246170956430238899)
                  ·
                    refine ⟨11225731869256434645358349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7483821246170956430238899 11225731869256434645358349)
                    ·
                      refine ⟨4209649450971162992009381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11225731869256434645358349 4209649450971162992009381)
                      ·
                        rfl

theorem cell23_8198263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4, 1, 1, 3].length) (baseStart_8198263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198263 prefixEnd_8198263 := by exact prefixLift 8198263
  have htrace : WordTrace (prefixWord ++ tailWord_8198263) baseStart_8198263 baseEnd_8198263 := by
    simpa [prefixWord, tailWord_8198263, baseEnd_8198263] using wordTrace_append hprefix tailTrace_8198263
  have hstable : (prefixWord ++ tailWord_8198263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198263).length < 2 ^ (prefixWord ++ tailWord_8198263).sum := by decide
  have hdescent : baseEnd_8198263 < baseStart_8198263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198279 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 1, 6]
def baseStart_8198279 : Nat := 118140960795 + 8198279 * 2 ^ 59
def prefixEnd_8198279 : Nat := 4983230072969 + 3 ^ 40 * 8198279 * 2
def baseEnd_8198279 : Nat := 1403219222220544976469769

theorem tailTrace_8198279 : CollatzResearch.WordTrace tailWord_8198279 prefixEnd_8198279 1403219222220544976469769 := by
  unfold tailWord_8198279
  simp only [CollatzResearch.WordTrace]
  refine ⟨299015800266042812426309891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199343866844028541617539927 299015800266042812426309891)
  ·
    refine ⟨448523700399064218639464837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299015800266042812426309891 448523700399064218639464837)
    ·
      refine ⟨84098193824824540994899657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448523700399064218639464837 84098193824824540994899657)
      ·
        refine ⟨63073645368618405746174743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84098193824824540994899657 63073645368618405746174743)
        ·
          refine ⟨94610468052927608619262115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63073645368618405746174743 94610468052927608619262115)
          ·
            refine ⟨141915702079391412928893173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94610468052927608619262115 141915702079391412928893173)
            ·
              refine ⟨13304597069942944962083735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141915702079391412928893173 13304597069942944962083735)
              ·
                refine ⟨19956895604914417443125603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13304597069942944962083735 19956895604914417443125603)
                ·
                  refine ⟨29935343407371626164688405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19956895604914417443125603 29935343407371626164688405)
                  ·
                    refine ⟨1403219222220544976469769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29935343407371626164688405 1403219222220544976469769)
                    ·
                      rfl

theorem cell23_8198279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_8198279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198279 prefixEnd_8198279 := by exact prefixLift 8198279
  have htrace : WordTrace (prefixWord ++ tailWord_8198279) baseStart_8198279 baseEnd_8198279 := by
    simpa [prefixWord, tailWord_8198279, baseEnd_8198279] using wordTrace_append hprefix tailTrace_8198279
  have hstable : (prefixWord ++ tailWord_8198279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198279).length < 2 ^ (prefixWord ++ tailWord_8198279).sum := by decide
  have hdescent : baseEnd_8198279 < baseStart_8198279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198306 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_8198306 : Nat := 118140960795 + 8198306 * 2 ^ 59
def prefixEnd_8198306 : Nat := 4983230072969 + 3 ^ 40 * 8198306 * 2
def baseEnd_8198306 : Nat := 4209671530639306323771683

theorem tailTrace_8198306 : CollatzResearch.WordTrace tailWord_8198306 prefixEnd_8198306 4209671530639306323771683 := by
  unfold tailWord_8198306
  simp only [CollatzResearch.WordTrace]
  refine ⟨74754196259236249009385693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199344523357963330691695181 74754196259236249009385693)
  ·
    refine ⟨28032823597213593378519635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74754196259236249009385693 28032823597213593378519635)
    ·
      refine ⟨42049235395820390067779453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28032823597213593378519635 42049235395820390067779453)
      ·
        refine ⟨15768463273432646275417295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42049235395820390067779453 15768463273432646275417295)
        ·
          refine ⟨23652694910148969413125943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15768463273432646275417295 23652694910148969413125943)
          ·
            refine ⟨35479042365223454119688915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23652694910148969413125943 35479042365223454119688915)
            ·
              refine ⟨53218563547835181179533373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35479042365223454119688915 53218563547835181179533373)
              ·
                refine ⟨19956961330438192942325015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53218563547835181179533373 19956961330438192942325015)
                ·
                  refine ⟨29935441995657289413487523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19956961330438192942325015 29935441995657289413487523)
                  ·
                    refine ⟨44903162993485934120231285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29935441995657289413487523 44903162993485934120231285)
                    ·
                      refine ⟨4209671530639306323771683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44903162993485934120231285 4209671530639306323771683)
                      ·
                        rfl

theorem cell23_8198306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_8198306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198306 prefixEnd_8198306 := by exact prefixLift 8198306
  have htrace : WordTrace (prefixWord ++ tailWord_8198306) baseStart_8198306 baseEnd_8198306 := by
    simpa [prefixWord, tailWord_8198306, baseEnd_8198306] using wordTrace_append hprefix tailTrace_8198306
  have hstable : (prefixWord ++ tailWord_8198306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198306).length < 2 ^ (prefixWord ++ tailWord_8198306).sum := by decide
  have hdescent : baseEnd_8198306 < baseStart_8198306 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198314 : List Nat := [3, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_8198314 : Nat := 118140960795 + 8198314 * 2 ^ 59
def prefixEnd_8198314 : Nat := 4983230072969 + 3 ^ 40 * 8198314 * 2
def baseEnd_8198314 : Nat := 4209675638484542292471647

theorem tailTrace_8198314 : CollatzResearch.WordTrace tailWord_8198314 prefixEnd_8198314 4209675638484542292471647 := by
  unfold tailWord_8198314
  simp only [CollatzResearch.WordTrace]
  refine ⟨74754269205229003350958499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199344717880610675602555997 74754269205229003350958499)
  ·
    refine ⟨112131403807843505026437749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74754269205229003350958499 112131403807843505026437749)
    ·
      refine ⟨10512319106985328596228539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112131403807843505026437749 10512319106985328596228539)
      ·
        refine ⟨15768478660477992894342809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10512319106985328596228539 15768478660477992894342809)
        ·
          refine ⟨11826358995358494670757107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15768478660477992894342809 11826358995358494670757107)
          ·
            refine ⟨17739538493037742006135661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11826358995358494670757107 17739538493037742006135661)
            ·
              refine ⟨6652326934889153252300873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17739538493037742006135661 6652326934889153252300873)
              ·
                refine ⟨4989245201166864939225655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6652326934889153252300873 4989245201166864939225655)
                ·
                  refine ⟨7483867801750297408838483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989245201166864939225655 7483867801750297408838483)
                  ·
                    refine ⟨11225801702625446113257725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7483867801750297408838483 11225801702625446113257725)
                    ·
                      refine ⟨4209675638484542292471647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11225801702625446113257725 4209675638484542292471647)
                      ·
                        rfl

theorem cell23_8198314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_8198314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198314 prefixEnd_8198314 := by exact prefixLift 8198314
  have htrace : WordTrace (prefixWord ++ tailWord_8198314) baseStart_8198314 baseEnd_8198314 := by
    simpa [prefixWord, tailWord_8198314, baseEnd_8198314] using wordTrace_append hprefix tailTrace_8198314
  have hstable : (prefixWord ++ tailWord_8198314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198314).length < 2 ^ (prefixWord ++ tailWord_8198314).sum := by decide
  have hdescent : baseEnd_8198314 < baseStart_8198314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198337 : List Nat := [1, 2, 6, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_8198337 : Nat := 118140960795 + 8198337 * 2 ^ 59
def prefixEnd_8198337 : Nat := 4983230072969 + 3 ^ 40 * 8198337 * 2
def baseEnd_8198337 : Nat := 4209687448539595702484041

theorem tailTrace_8198337 : CollatzResearch.WordTrace tailWord_8198337 prefixEnd_8198337 4209687448539595702484041 := by
  unfold tailWord_8198337
  simp only [CollatzResearch.WordTrace]
  refine ⟨299017915699832688331921265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199345277133221792221280843 299017915699832688331921265)
  ·
    refine ⟨224263436774874516248940949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299017915699832688331921265 224263436774874516248940949)
    ·
      refine ⟨10512348598822242949169107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224263436774874516248940949 10512348598822242949169107)
      ·
        refine ⟨15768522898233364423753661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10512348598822242949169107 15768522898233364423753661)
        ·
          refine ⟨5913196086837511658907623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15768522898233364423753661 5913196086837511658907623)
          ·
            refine ⟨8869794130256267488361435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5913196086837511658907623 8869794130256267488361435)
            ·
              refine ⟨13304691195384401232542153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869794130256267488361435 13304691195384401232542153)
              ·
                refine ⟨9978518396538300924406615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13304691195384401232542153 9978518396538300924406615)
                ·
                  refine ⟨14967777594807451386609923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9978518396538300924406615 14967777594807451386609923)
                  ·
                    refine ⟨22451666392211177079914885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14967777594807451386609923 22451666392211177079914885)
                    ·
                      refine ⟨4209687448539595702484041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22451666392211177079914885 4209687448539595702484041)
                      ·
                        rfl

theorem cell23_8198337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_8198337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198337 prefixEnd_8198337 := by exact prefixLift 8198337
  have htrace : WordTrace (prefixWord ++ tailWord_8198337) baseStart_8198337 baseEnd_8198337 := by
    simpa [prefixWord, tailWord_8198337, baseEnd_8198337] using wordTrace_append hprefix tailTrace_8198337
  have hstable : (prefixWord ++ tailWord_8198337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198337).length < 2 ^ (prefixWord ++ tailWord_8198337).sum := by decide
  have hdescent : baseEnd_8198337 < baseStart_8198337 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198340 : List Nat := [2, 3, 3, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_8198340 : Nat := 118140960795 + 8198340 * 2 ^ 59
def prefixEnd_8198340 : Nat := 4983230072969 + 3 ^ 40 * 8198340 * 2
def baseEnd_8198340 : Nat := 4209688988981559190746527

theorem tailTrace_8198340 : CollatzResearch.WordTrace tailWord_8198340 prefixEnd_8198340 4209688988981559190746527 := by
  unfold tailWord_8198340
  simp only [CollatzResearch.WordTrace]
  refine ⟨149509012559410909922140237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199345350079214546562853649 149509012559410909922140237)
  ·
    refine ⟨56065879709779091220802589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149509012559410909922140237 56065879709779091220802589)
    ·
      refine ⟨21024704891167159207800971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56065879709779091220802589 21024704891167159207800971)
      ·
        refine ⟨31537057336750738811701457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21024704891167159207800971 31537057336750738811701457)
        ·
          refine ⟨23652793002563054108776093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31537057336750738811701457 23652793002563054108776093)
          ·
            refine ⟨8869797375961145290791035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23652793002563054108776093 8869797375961145290791035)
            ·
              refine ⟨13304696063941717936186553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8869797375961145290791035 13304696063941717936186553)
              ·
                refine ⟨9978522047956288452139915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13304696063941717936186553 9978522047956288452139915)
                ·
                  refine ⟨14967783071934432678209873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9978522047956288452139915 14967783071934432678209873)
                  ·
                    refine ⟨11225837303950824508657405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14967783071934432678209873 11225837303950824508657405)
                    ·
                      refine ⟨4209688988981559190746527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11225837303950824508657405 4209688988981559190746527)
                      ·
                        rfl

theorem cell23_8198340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_8198340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198340 prefixEnd_8198340 := by exact prefixLift 8198340
  have htrace : WordTrace (prefixWord ++ tailWord_8198340) baseStart_8198340 baseEnd_8198340 := by
    simpa [prefixWord, tailWord_8198340, baseEnd_8198340] using wordTrace_append hprefix tailTrace_8198340
  have hstable : (prefixWord ++ tailWord_8198340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198340).length < 2 ^ (prefixWord ++ tailWord_8198340).sum := by decide
  have hdescent : baseEnd_8198340 < baseStart_8198340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198369 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 2, 6]
def baseStart_8198369 : Nat := 118140960795 + 8198369 * 2 ^ 59
def prefixEnd_8198369 : Nat := 4983230072969 + 3 ^ 40 * 8198369 * 2
def baseEnd_8198369 : Nat := 1403234626640179859094631

theorem tailTrace_8198369 : CollatzResearch.WordTrace tailWord_8198369 prefixEnd_8198369 1403234626640179859094631 := by
  unfold tailWord_8198369
  simp only [CollatzResearch.WordTrace]
  refine ⟨299019082835716757797086161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199346055223811171864724107 299019082835716757797086161)
  ·
    refine ⟨224264312126787568347814621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299019082835716757797086161 224264312126787568347814621)
    ·
      refine ⟨84099117047545338130430483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224264312126787568347814621 84099117047545338130430483)
      ·
        refine ⟨126148675571318007195645725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84099117047545338130430483 126148675571318007195645725)
        ·
          refine ⟨47305753339244252698367147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126148675571318007195645725 47305753339244252698367147)
          ·
            refine ⟨70958630008866379047550721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47305753339244252698367147 70958630008866379047550721)
            ·
              refine ⟨53218972506649784285663041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70958630008866379047550721 53218972506649784285663041)
              ·
                refine ⟨39914229379987338214247281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53218972506649784285663041 39914229379987338214247281)
                ·
                  refine ⟨29935672034990503660685461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39914229379987338214247281 29935672034990503660685461)
                  ·
                    refine ⟨1403234626640179859094631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29935672034990503660685461 1403234626640179859094631)
                    ·
                      rfl

theorem cell23_8198369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_8198369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198369 prefixEnd_8198369 := by exact prefixLift 8198369
  have htrace : WordTrace (prefixWord ++ tailWord_8198369) baseStart_8198369 baseEnd_8198369 := by
    simpa [prefixWord, tailWord_8198369, baseEnd_8198369] using wordTrace_append hprefix tailTrace_8198369
  have hstable : (prefixWord ++ tailWord_8198369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198369).length < 2 ^ (prefixWord ++ tailWord_8198369).sum := by decide
  have hdescent : baseEnd_8198369 < baseStart_8198369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198371 : List Nat := [1, 1, 1, 8, 1, 2, 2, 2, 1, 2, 2]
def baseStart_8198371 : Nat := 118140960795 + 8198371 * 2 ^ 59
def prefixEnd_8198371 : Nat := 4983230072969 + 3 ^ 40 * 8198371 * 2
def baseEnd_8198371 : Nat := 4209704906881848569458885

theorem tailTrace_8198371 : CollatzResearch.WordTrace tailWord_8198371 prefixEnd_8198371 4209704906881848569458885 := by
  unfold tailWord_8198371
  simp only [CollatzResearch.WordTrace]
  refine ⟨299019155781709512138658967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199346103854473008092439311 299019155781709512138658967)
  ·
    refine ⟨448528733672564268207988451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299019155781709512138658967 448528733672564268207988451)
    ·
      refine ⟨672793100508846402311982677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448528733672564268207988451 672793100508846402311982677)
      ·
        refine ⟨7884294146588043777093547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 672793100508846402311982677 7884294146588043777093547)
        ·
          refine ⟨11826441219882065665640321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7884294146588043777093547 11826441219882065665640321)
          ·
            refine ⟨8869830914911549249230241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11826441219882065665640321 8869830914911549249230241)
            ·
              refine ⟨6652373186183661936922681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8869830914911549249230241 6652373186183661936922681)
              ·
                refine ⟨4989279889637746452692011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6652373186183661936922681 4989279889637746452692011)
                ·
                  refine ⟨7483919834456619679038017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989279889637746452692011 7483919834456619679038017)
                  ·
                    refine ⟨5612939875842464759278513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7483919834456619679038017 5612939875842464759278513)
                    ·
                      refine ⟨4209704906881848569458885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5612939875842464759278513 4209704906881848569458885)
                      ·
                        rfl

theorem cell23_8198371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_8198371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198371 prefixEnd_8198371 := by exact prefixLift 8198371
  have htrace : WordTrace (prefixWord ++ tailWord_8198371) baseStart_8198371 baseEnd_8198371 := by
    simpa [prefixWord, tailWord_8198371, baseEnd_8198371] using wordTrace_append hprefix tailTrace_8198371
  have hstable : (prefixWord ++ tailWord_8198371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198371).length < 2 ^ (prefixWord ++ tailWord_8198371).sum := by decide
  have hdescent : baseEnd_8198371 < baseStart_8198371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198379 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 3]
def baseStart_8198379 : Nat := 118140960795 + 8198379 * 2 ^ 59
def prefixEnd_8198379 : Nat := 4983230072969 + 3 ^ 40 * 8198379 * 2
def baseEnd_8198379 : Nat := 4209709014727084538158847

theorem tailTrace_8198379 : CollatzResearch.WordTrace tailWord_8198379 prefixEnd_8198379 4209709014727084538158847 := by
  unfold tailWord_8198379
  simp only [CollatzResearch.WordTrace]
  refine ⟨299019447565680529504950191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199346298377120353003300127 299019447565680529504950191)
  ·
    refine ⟨448529171348520794257425287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299019447565680529504950191 448529171348520794257425287)
    ·
      refine ⟨672793757022781191386137931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448529171348520794257425287 672793757022781191386137931)
      ·
        refine ⟨1009190635534171787079206897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672793757022781191386137931 1009190635534171787079206897)
        ·
          refine ⟨756892976650628840309405173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1009190635534171787079206897 756892976650628840309405173)
          ·
            refine ⟨70958716560996453779006735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 756892976650628840309405173 70958716560996453779006735)
            ·
              refine ⟨106438074841494680668510103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70958716560996453779006735 106438074841494680668510103)
              ·
                refine ⟨159657112262242021002765155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106438074841494680668510103 159657112262242021002765155)
                ·
                  refine ⟨239485668393363031504147733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159657112262242021002765155 239485668393363031504147733)
                  ·
                    refine ⟨11225890705938892101756925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 239485668393363031504147733 11225890705938892101756925)
                    ·
                      refine ⟨4209709014727084538158847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11225890705938892101756925 4209709014727084538158847)
                      ·
                        rfl

theorem cell23_8198379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 3].length) (baseStart_8198379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198379 prefixEnd_8198379 := by exact prefixLift 8198379
  have htrace : WordTrace (prefixWord ++ tailWord_8198379) baseStart_8198379 baseEnd_8198379 := by
    simpa [prefixWord, tailWord_8198379, baseEnd_8198379] using wordTrace_append hprefix tailTrace_8198379
  have hstable : (prefixWord ++ tailWord_8198379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198379).length < 2 ^ (prefixWord ++ tailWord_8198379).sum := by decide
  have hdescent : baseEnd_8198379 < baseStart_8198379 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198386 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_8198386 : Nat := 118140960795 + 8198386 * 2 ^ 59
def prefixEnd_8198386 : Nat := 4983230072969 + 3 ^ 40 * 8198386 * 2
def baseEnd_8198386 : Nat := 1403237536363888670257105

theorem tailTrace_8198386 : CollatzResearch.WordTrace tailWord_8198386 prefixEnd_8198386 1403237536363888670257105 := by
  unfold tailWord_8198386
  simp only [CollatzResearch.WordTrace]
  refine ⟨74754925719163792425113753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199346468584436779800303341 74754925719163792425113753)
  ·
    refine ⟨56066194289372844318835315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74754925719163792425113753 56066194289372844318835315)
    ·
      refine ⟨84099291434059266478252973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56066194289372844318835315 84099291434059266478252973)
      ·
        refine ⟨31537234287772224929344865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84099291434059266478252973 31537234287772224929344865)
        ·
          refine ⟨23652925715829168697008649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31537234287772224929344865 23652925715829168697008649)
          ·
            refine ⟨17739694286871876522756487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23652925715829168697008649 17739694286871876522756487)
            ·
              refine ⟨26609541430307814784134731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17739694286871876522756487 26609541430307814784134731)
              ·
                refine ⟨39914312145461722176202097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26609541430307814784134731 39914312145461722176202097)
                ·
                  refine ⟨29935734109096291632151573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39914312145461722176202097 29935734109096291632151573)
                  ·
                    refine ⟨1403237536363888670257105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29935734109096291632151573 1403237536363888670257105)
                    ·
                      rfl

theorem cell23_8198386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_8198386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198386 prefixEnd_8198386 := by exact prefixLift 8198386
  have htrace : WordTrace (prefixWord ++ tailWord_8198386) baseStart_8198386 baseEnd_8198386 := by
    simpa [prefixWord, tailWord_8198386, baseEnd_8198386] using wordTrace_append hprefix tailTrace_8198386
  have hstable : (prefixWord ++ tailWord_8198386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198386).length < 2 ^ (prefixWord ++ tailWord_8198386).sum := by decide
  have hdescent : baseEnd_8198386 < baseStart_8198386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198399 : List Nat := [1, 1, 2, 2, 1, 4, 3, 2, 7]
def baseStart_8198399 : Nat := 118140960795 + 8198399 * 2 ^ 59
def prefixEnd_8198399 : Nat := 4983230072969 + 3 ^ 40 * 8198399 * 2
def baseEnd_8198399 : Nat := 467746587148908273323195

theorem tailTrace_8198399 : CollatzResearch.WordTrace tailWord_8198399 prefixEnd_8198399 467746587148908273323195 := by
  unfold tailWord_8198399
  simp only [CollatzResearch.WordTrace]
  refine ⟨299020177025608072920678251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199346784683738715280452167 299020177025608072920678251)
  ·
    refine ⟨448530265538412109381017377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299020177025608072920678251 448530265538412109381017377)
    ·
      refine ⟨336397699153809082035763033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448530265538412109381017377 336397699153809082035763033)
      ·
        refine ⟨252298274365356811526822275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336397699153809082035763033 252298274365356811526822275)
        ·
          refine ⟨378447411548035217290233413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252298274365356811526822275 378447411548035217290233413)
          ·
            refine ⟨70958889665256603241918765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378447411548035217290233413 70958889665256603241918765)
            ·
              refine ⟨26609583624471226215719537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70958889665256603241918765 26609583624471226215719537)
              ·
                refine ⟨19957187718353419661789653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26609583624471226215719537 19957187718353419661789653)
                ·
                  refine ⟨467746587148908273323195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19957187718353419661789653 467746587148908273323195)
                  ·
                    rfl

theorem cell23_8198399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 7].length) (baseStart_8198399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198399 prefixEnd_8198399 := by exact prefixLift 8198399
  have htrace : WordTrace (prefixWord ++ tailWord_8198399) baseStart_8198399 baseEnd_8198399 := by
    simpa [prefixWord, tailWord_8198399, baseEnd_8198399] using wordTrace_append hprefix tailTrace_8198399
  have hstable : (prefixWord ++ tailWord_8198399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198399).length < 2 ^ (prefixWord ++ tailWord_8198399).sum := by decide
  have hdescent : baseEnd_8198399 < baseStart_8198399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198469 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 5]
def baseStart_8198469 : Nat := 118140960795 + 8198469 * 2 ^ 59
def prefixEnd_8198469 : Nat := 4983230072969 + 3 ^ 40 * 8198469 * 2
def baseEnd_8198469 : Nat := 4209755227985989186033433

theorem tailTrace_8198469 : CollatzResearch.WordTrace tailWord_8198469 prefixEnd_8198469 4209755227985989186033433 := by
  unfold tailWord_8198469
  simp only [CollatzResearch.WordTrace]
  refine ⟨299022730135354474875726461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199348486756902983250484307 299022730135354474875726461)
  ·
    refine ⟨112133523800757928078397423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299022730135354474875726461 112133523800757928078397423)
    ·
      refine ⟨168200285701136892117596135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112133523800757928078397423 168200285701136892117596135)
      ·
        refine ⟨252300428551705338176394203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168200285701136892117596135 252300428551705338176394203)
        ·
          refine ⟨378450642827558007264591305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252300428551705338176394203 378450642827558007264591305)
          ·
            refine ⟨283837982120668505448443479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378450642827558007264591305 283837982120668505448443479)
            ·
              refine ⟨425756973181002758172665219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283837982120668505448443479 425756973181002758172665219)
              ·
                refine ⟨638635459771504137258997829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425756973181002758172665219 638635459771504137258997829)
                ·
                  refine ⟨119744148707157025736062093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638635459771504137258997829 119744148707157025736062093)
                  ·
                    refine ⟨44904055765183884651023285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119744148707157025736062093 44904055765183884651023285)
                    ·
                      refine ⟨4209755227985989186033433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44904055765183884651023285 4209755227985989186033433)
                      ·
                        rfl

theorem cell23_8198469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_8198469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198469 prefixEnd_8198469 := by exact prefixLift 8198469
  have htrace : WordTrace (prefixWord ++ tailWord_8198469) baseStart_8198469 baseEnd_8198469 := by
    simpa [prefixWord, tailWord_8198469, baseEnd_8198469] using wordTrace_append hprefix tailTrace_8198469
  have hstable : (prefixWord ++ tailWord_8198469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198469).length < 2 ^ (prefixWord ++ tailWord_8198469).sum := by decide
  have hdescent : baseEnd_8198469 < baseStart_8198469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198479 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 6]
def baseStart_8198479 : Nat := 118140960795 + 8198479 * 2 ^ 59
def prefixEnd_8198479 : Nat := 4983230072969 + 3 ^ 40 * 8198479 * 2
def baseEnd_8198479 : Nat := 4209760362792534146908387

theorem tailTrace_8198479 : CollatzResearch.WordTrace tailWord_8198479 prefixEnd_8198479 4209760362792534146908387 := by
  unfold tailWord_8198479
  simp only [CollatzResearch.WordTrace]
  refine ⟨299023094865318246583590491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199348729910212164389060327 299023094865318246583590491)
  ·
    refine ⟨448534642297977369875385737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299023094865318246583590491 448534642297977369875385737)
    ·
      refine ⟨336400981723483027406539303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448534642297977369875385737 336400981723483027406539303)
      ·
        refine ⟨504601472585224541109808955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336400981723483027406539303 504601472585224541109808955)
        ·
          refine ⟨756902208877836811664713433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504601472585224541109808955 756902208877836811664713433)
          ·
            refine ⟨567676656658377608748535075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 756902208877836811664713433 567676656658377608748535075)
            ·
              refine ⟨851514984987566413122802613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567676656658377608748535075 851514984987566413122802613)
              ·
                refine ⟨79829529842584351230262745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 851514984987566413122802613 79829529842584351230262745)
                ·
                  refine ⟨59872147381938263422697059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79829529842584351230262745 59872147381938263422697059)
                  ·
                    refine ⟨89808221072907395134045589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59872147381938263422697059 89808221072907395134045589)
                    ·
                      refine ⟨4209760362792534146908387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89808221072907395134045589 4209760362792534146908387)
                      ·
                        rfl

theorem cell23_8198479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 6].length) (baseStart_8198479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198479 prefixEnd_8198479 := by exact prefixLift 8198479
  have htrace : WordTrace (prefixWord ++ tailWord_8198479) baseStart_8198479 baseEnd_8198479 := by
    simpa [prefixWord, tailWord_8198479, baseEnd_8198479] using wordTrace_append hprefix tailTrace_8198479
  have hstable : (prefixWord ++ tailWord_8198479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198479).length < 2 ^ (prefixWord ++ tailWord_8198479).sum := by decide
  have hdescent : baseEnd_8198479 < baseStart_8198479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198577 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 2, 3, 2]
def baseStart_8198577 : Nat := 118140960795 + 8198577 * 2 ^ 59
def prefixEnd_8198577 : Nat := 4983230072969 + 3 ^ 40 * 8198577 * 2
def baseEnd_8198577 : Nat := 4209810683896674763482937

theorem tailTrace_8198577 : CollatzResearch.WordTrace tailWord_8198577 prefixEnd_8198577 4209810683896674763482937 := by
  unfold tailWord_8198577
  simp only [CollatzResearch.WordTrace]
  refine ⟨299026669218963209320657985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199351112812642139547105323 299026669218963209320657985)
  ·
    refine ⟨224270001914222406990493489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299026669218963209320657985 224270001914222406990493489)
    ·
      refine ⟨168202501435666805242870117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224270001914222406990493489 168202501435666805242870117)
      ·
        refine ⟨31537969019187525983038147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168202501435666805242870117 31537969019187525983038147)
        ·
          refine ⟨47306953528781288974557221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31537969019187525983038147 47306953528781288974557221)
          ·
            refine ⟨8870053786646491682729479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47306953528781288974557221 8870053786646491682729479)
            ·
              refine ⟨13305080679969737524094219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8870053786646491682729479 13305080679969737524094219)
              ·
                refine ⟨19957621019954606286141329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13305080679969737524094219 19957621019954606286141329)
                ·
                  refine ⟨14968215764965954714605997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19957621019954606286141329 14968215764965954714605997)
                  ·
                    refine ⟨5613080911862233017977249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14968215764965954714605997 5613080911862233017977249)
                    ·
                      refine ⟨4209810683896674763482937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5613080911862233017977249 4209810683896674763482937)
                      ·
                        rfl

theorem cell23_8198577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_8198577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198577 prefixEnd_8198577 := by exact prefixLift 8198577
  have htrace : WordTrace (prefixWord ++ tailWord_8198577) baseStart_8198577 baseEnd_8198577 := by
    simpa [prefixWord, tailWord_8198577, baseEnd_8198577] using wordTrace_append hprefix tailTrace_8198577
  have hstable : (prefixWord ++ tailWord_8198577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198577).length < 2 ^ (prefixWord ++ tailWord_8198577).sum := by decide
  have hdescent : baseEnd_8198577 < baseStart_8198577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198600 : List Nat := [2, 1, 3, 1, 3, 2, 3, 2, 2, 4]
def baseStart_8198600 : Nat := 118140960795 + 8198600 * 2 ^ 59
def prefixEnd_8198600 : Nat := 4983230072969 + 3 ^ 40 * 8198600 * 2
def baseEnd_8198600 : Nat := 1403274164650576057831777

theorem tailTrace_8198600 : CollatzResearch.WordTrace tailWord_8198600 prefixEnd_8198600 1403274164650576057831777 := by
  unfold tailWord_8198600
  simp only [CollatzResearch.WordTrace]
  refine ⟨149513754048939942124372627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199351672065253256165830169 149513754048939942124372627)
  ·
    refine ⟨224270631073409913186558941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149513754048939942124372627 224270631073409913186558941)
    ·
      refine ⟨84101486652528717444959603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224270631073409913186558941 84101486652528717444959603)
      ·
        refine ⟨126152229978793076167439405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84101486652528717444959603 126152229978793076167439405)
        ·
          refine ⟨47307086242047403562789777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126152229978793076167439405 47307086242047403562789777)
          ·
            refine ⟨35480314681535552672092333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47307086242047403562789777 35480314681535552672092333)
            ·
              refine ⟨13305118005575832252034625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35480314681535552672092333 13305118005575832252034625)
              ·
                refine ⟨9978838504181874189025969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13305118005575832252034625 9978838504181874189025969)
                ·
                  refine ⟨7484128878136405641769477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9978838504181874189025969 7484128878136405641769477)
                  ·
                    refine ⟨1403274164650576057831777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7484128878136405641769477 1403274164650576057831777)
                    ·
                      rfl

theorem cell23_8198600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_8198600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198600 prefixEnd_8198600 := by exact prefixLift 8198600
  have htrace : WordTrace (prefixWord ++ tailWord_8198600) baseStart_8198600 baseEnd_8198600 := by
    simpa [prefixWord, tailWord_8198600, baseEnd_8198600] using wordTrace_append hprefix tailTrace_8198600
  have hstable : (prefixWord ++ tailWord_8198600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198600).length < 2 ^ (prefixWord ++ tailWord_8198600).sum := by decide
  have hdescent : baseEnd_8198600 < baseStart_8198600 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198606 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_8198606 : Nat := 118140960795 + 8198606 * 2 ^ 59
def prefixEnd_8198606 : Nat := 4983230072969 + 3 ^ 40 * 8198606 * 2
def baseEnd_8198606 : Nat := 4209825574835655150020303

theorem tailTrace_8198606 : CollatzResearch.WordTrace tailWord_8198606 prefixEnd_8198606 4209825574835655150020303 := by
  unfold tailWord_8198606
  simp only [CollatzResearch.WordTrace]
  refine ⟨37378465866982268409182959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199351817957238764848975781 37378465866982268409182959)
  ·
    refine ⟨56067698800473402613774439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37378465866982268409182959 56067698800473402613774439)
    ·
      refine ⟨84101548200710103920661659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56067698800473402613774439 84101548200710103920661659)
      ·
        refine ⟨126152322301065155880992489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84101548200710103920661659 126152322301065155880992489)
        ·
          refine ⟨94614241725798866910744367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126152322301065155880992489 94614241725798866910744367)
          ·
            refine ⟨141921362588698300366116551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94614241725798866910744367 141921362588698300366116551)
            ·
              refine ⟨212882043883047450549174827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141921362588698300366116551 212882043883047450549174827)
              ·
                refine ⟨319323065824571175823762241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212882043883047450549174827 319323065824571175823762241)
                ·
                  refine ⟨239492299368428381867821681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319323065824571175823762241 239492299368428381867821681)
                  ·
                    refine ⟨179619224526321286400866261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 239492299368428381867821681 179619224526321286400866261)
                    ·
                      refine ⟨4209825574835655150020303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179619224526321286400866261 4209825574835655150020303)
                      ·
                        rfl

theorem cell23_8198606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_8198606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198606 prefixEnd_8198606 := by exact prefixLift 8198606
  have htrace : WordTrace (prefixWord ++ tailWord_8198606) baseStart_8198606 baseEnd_8198606 := by
    simpa [prefixWord, tailWord_8198606, baseEnd_8198606] using wordTrace_append hprefix tailTrace_8198606
  have hstable : (prefixWord ++ tailWord_8198606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198606).length < 2 ^ (prefixWord ++ tailWord_8198606).sum := by decide
  have hdescent : baseEnd_8198606 < baseStart_8198606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198627 : List Nat := [1, 1, 1, 6, 3, 1, 2, 2, 1, 2, 3]
def baseStart_8198627 : Nat := 118140960795 + 8198627 * 2 ^ 59
def prefixEnd_8198627 : Nat := 4983230072969 + 3 ^ 40 * 8198627 * 2
def baseEnd_8198627 : Nat := 4209836357929399567857707

theorem tailTrace_8198627 : CollatzResearch.WordTrace tailWord_8198627 prefixEnd_8198627 4209836357929399567857707 := by
  unfold tailWord_8198627
  simp only [CollatzResearch.WordTrace]
  refine ⟨299028492868782067859978135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199352328579188045239985423 299028492868782067859978135)
  ·
    refine ⟨448542739303173101789967203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299028492868782067859978135 448542739303173101789967203)
    ·
      refine ⟨672814108954759652684950805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448542739303173101789967203 672814108954759652684950805)
      ·
        refine ⟨31538161357254358719607069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 672814108954759652684950805 31538161357254358719607069)
        ·
          refine ⟨11826810508970384519852651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31538161357254358719607069 11826810508970384519852651)
          ·
            refine ⟨17740215763455576779778977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11826810508970384519852651 17740215763455576779778977)
            ·
              refine ⟨13305161822591682584834233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17740215763455576779778977 13305161822591682584834233)
              ·
                refine ⟨9978871366943761938625675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13305161822591682584834233 9978871366943761938625675)
                ·
                  refine ⟨14968307050415642907938513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9978871366943761938625675 14968307050415642907938513)
                  ·
                    refine ⟨11226230287811732180953885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14968307050415642907938513 11226230287811732180953885)
                    ·
                      refine ⟨4209836357929399567857707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11226230287811732180953885 4209836357929399567857707)
                      ·
                        rfl

theorem cell23_8198627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_8198627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198627 prefixEnd_8198627 := by exact prefixLift 8198627
  have htrace : WordTrace (prefixWord ++ tailWord_8198627) baseStart_8198627 baseEnd_8198627 := by
    simpa [prefixWord, tailWord_8198627, baseEnd_8198627] using wordTrace_append hprefix tailTrace_8198627
  have hstable : (prefixWord ++ tailWord_8198627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198627).length < 2 ^ (prefixWord ++ tailWord_8198627).sum := by decide
  have hdescent : baseEnd_8198627 < baseStart_8198627 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198636 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 5]
def baseStart_8198636 : Nat := 118140960795 + 8198636 * 2 ^ 59
def prefixEnd_8198636 : Nat := 4983230072969 + 3 ^ 40 * 8198636 * 2
def baseEnd_8198636 : Nat := 4209840979255290032645165

theorem tailTrace_8198636 : CollatzResearch.WordTrace tailWord_8198636 prefixEnd_8198636 4209840979255290032645165 := by
  unfold tailWord_8198636
  simp only [CollatzResearch.WordTrace]
  refine ⟨149514410562874731198527881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199352547417166308264703841 149514410562874731198527881)
  ·
    refine ⟨112135807922156048398895911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149514410562874731198527881 112135807922156048398895911)
    ·
      refine ⟨168203711883234072598343867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112135807922156048398895911 168203711883234072598343867)
      ·
        refine ⟨252305567824851108897515801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168203711883234072598343867 252305567824851108897515801)
        ·
          refine ⟨189229175868638331673136851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252305567824851108897515801 189229175868638331673136851)
          ·
            refine ⟨283843763802957497509705277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189229175868638331673136851 283843763802957497509705277)
            ·
              refine ⟨106441411426109061566139479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283843763802957497509705277 106441411426109061566139479)
              ·
                refine ⟨159662117139163592349209219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106441411426109061566139479 159662117139163592349209219)
                ·
                  refine ⟨239493175708745388523813829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159662117139163592349209219 239493175708745388523813829)
                  ·
                    refine ⟨44904970445389760348215093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 239493175708745388523813829 44904970445389760348215093)
                    ·
                      refine ⟨4209840979255290032645165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44904970445389760348215093 4209840979255290032645165)
                      ·
                        rfl

theorem cell23_8198636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_8198636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198636 prefixEnd_8198636 := by exact prefixLift 8198636
  have htrace : WordTrace (prefixWord ++ tailWord_8198636) baseStart_8198636 baseEnd_8198636 := by
    simpa [prefixWord, tailWord_8198636, baseEnd_8198636] using wordTrace_append hprefix tailTrace_8198636
  have hstable : (prefixWord ++ tailWord_8198636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198636).length < 2 ^ (prefixWord ++ tailWord_8198636).sum := by decide
  have hdescent : baseEnd_8198636 < baseStart_8198636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198658 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_8198658 : Nat := 118140960795 + 8198658 * 2 ^ 59
def prefixEnd_8198658 : Nat := 4983230072969 + 3 ^ 40 * 8198658 * 2
def baseEnd_8198658 : Nat := 4209852275829688946570065

theorem tailTrace_8198658 : CollatzResearch.WordTrace tailWord_8198658 prefixEnd_8198658 4209852275829688946570065 := by
  unfold tailWord_8198658
  simp only [CollatzResearch.WordTrace]
  refine ⟨74757405882917440038589157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199353082354446506769571085 74757405882917440038589157)
  ·
    refine ⟨14017013603047020007235467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74757405882917440038589157 14017013603047020007235467)
    ·
      refine ⟨21025520404570530010853201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14017013603047020007235467 21025520404570530010853201)
      ·
        refine ⟨15769140303427897508139901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21025520404570530010853201 15769140303427897508139901)
        ·
          refine ⟨5913427613785461565552463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15769140303427897508139901 5913427613785461565552463)
          ·
            refine ⟨8870141420678192348328695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5913427613785461565552463 8870141420678192348328695)
            ·
              refine ⟨13305212131017288522493043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8870141420678192348328695 13305212131017288522493043)
              ·
                refine ⟨19957818196525932783739565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13305212131017288522493043 19957818196525932783739565)
                ·
                  refine ⟨7484181823697224793902337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19957818196525932783739565 7484181823697224793902337)
                  ·
                    refine ⟨5613136367772918595426753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7484181823697224793902337 5613136367772918595426753)
                    ·
                      refine ⟨4209852275829688946570065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5613136367772918595426753 4209852275829688946570065)
                      ·
                        rfl

theorem cell23_8198658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_8198658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198658 prefixEnd_8198658 := by exact prefixLift 8198658
  have htrace : WordTrace (prefixWord ++ tailWord_8198658) baseStart_8198658 baseEnd_8198658 := by
    simpa [prefixWord, tailWord_8198658, baseEnd_8198658] using wordTrace_append hprefix tailTrace_8198658
  have hstable : (prefixWord ++ tailWord_8198658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198658).length < 2 ^ (prefixWord ++ tailWord_8198658).sum := by decide
  have hdescent : baseEnd_8198658 < baseStart_8198658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198684 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 1, 3, 2]
def baseStart_8198684 : Nat := 118140960795 + 8198684 * 2 ^ 59
def prefixEnd_8198684 : Nat := 4983230072969 + 3 ^ 40 * 8198684 * 2
def baseEnd_8198684 : Nat := 4209865626326705844844945

theorem tailTrace_8198684 : CollatzResearch.WordTrace tailWord_8198684 prefixEnd_8198684 4209865626326705844844945 := by
  unfold tailWord_8198684
  simp only [CollatzResearch.WordTrace]
  refine ⟨149515285914787783297401553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199353714553050377729868737 149515285914787783297401553)
  ·
    refine ⟨112136464436090837473051165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149515285914787783297401553 112136464436090837473051165)
    ·
      refine ⟨42051174163534064052394187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112136464436090837473051165 42051174163534064052394187)
      ·
        refine ⟨63076761245301096078591281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42051174163534064052394187 63076761245301096078591281)
        ·
          refine ⟨47307570933975822058943461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63076761245301096078591281 47307570933975822058943461)
          ·
            refine ⟨8870169550120466636051899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47307570933975822058943461 8870169550120466636051899)
            ·
              refine ⟨13305254325180699954077849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8870169550120466636051899 13305254325180699954077849)
              ·
                refine ⟨9978940743885524965558387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13305254325180699954077849 9978940743885524965558387)
                ·
                  refine ⟨14968411115828287448337581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9978940743885524965558387 14968411115828287448337581)
                  ·
                    refine ⟨5613154168435607793126593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14968411115828287448337581 5613154168435607793126593)
                    ·
                      refine ⟨4209865626326705844844945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5613154168435607793126593 4209865626326705844844945)
                      ·
                        rfl

theorem cell23_8198684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_8198684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198684 prefixEnd_8198684 := by exact prefixLift 8198684
  have htrace : WordTrace (prefixWord ++ tailWord_8198684) baseStart_8198684 baseEnd_8198684 := by
    simpa [prefixWord, tailWord_8198684, baseEnd_8198684] using wordTrace_append hprefix tailTrace_8198684
  have hstable : (prefixWord ++ tailWord_8198684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198684).length < 2 ^ (prefixWord ++ tailWord_8198684).sum := by decide
  have hdescent : baseEnd_8198684 < baseStart_8198684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198714 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2]
def baseStart_8198714 : Nat := 118140960795 + 8198714 * 2 ^ 59
def prefixEnd_8198714 : Nat := 4983230072969 + 3 ^ 40 * 8198714 * 2
def baseEnd_8198714 : Nat := 4209881030746340727469807

theorem tailTrace_8198714 : CollatzResearch.WordTrace tailWord_8198714 prefixEnd_8198714 4209881030746340727469807 := by
  unfold tailWord_8198714
  simp only [CollatzResearch.WordTrace]
  refine ⟨74757916504866720429598799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199354444012977921145596797 74757916504866720429598799)
  ·
    refine ⟨112136874757300080644398199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74757916504866720429598799 112136874757300080644398199)
    ·
      refine ⟨168205312135950120966597299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112136874757300080644398199 168205312135950120966597299)
      ·
        refine ⟨252307968203925181449895949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168205312135950120966597299 252307968203925181449895949)
        ·
          refine ⟨94615488076471943043710981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252307968203925181449895949 94615488076471943043710981)
          ·
            refine ⟨17740404014338489320695809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94615488076471943043710981 17740404014338489320695809)
            ·
              refine ⟨13305303010753866990521857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17740404014338489320695809 13305303010753866990521857)
              ·
                refine ⟨9978977258065400242891393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13305303010753866990521857 9978977258065400242891393)
                ·
                  refine ⟨7484232943549050182168545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9978977258065400242891393 7484232943549050182168545)
                  ·
                    refine ⟨5613174707661787636626409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7484232943549050182168545 5613174707661787636626409)
                    ·
                      refine ⟨4209881030746340727469807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5613174707661787636626409 4209881030746340727469807)
                      ·
                        rfl

theorem cell23_8198714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2].length) (baseStart_8198714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198714 prefixEnd_8198714 := by exact prefixLift 8198714
  have htrace : WordTrace (prefixWord ++ tailWord_8198714) baseStart_8198714 baseEnd_8198714 := by
    simpa [prefixWord, tailWord_8198714, baseEnd_8198714] using wordTrace_append hprefix tailTrace_8198714
  have hstable : (prefixWord ++ tailWord_8198714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198714).length < 2 ^ (prefixWord ++ tailWord_8198714).sum := by decide
  have hdescent : baseEnd_8198714 < baseStart_8198714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198724 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_8198724 : Nat := 118140960795 + 8198724 * 2 ^ 59
def prefixEnd_8198724 : Nat := 4983230072969 + 3 ^ 40 * 8198724 * 2
def baseEnd_8198724 : Nat := 1403295388517628562781587

theorem tailTrace_8198724 : CollatzResearch.WordTrace tailWord_8198724 prefixEnd_8198724 1403295388517628562781587 := by
  unfold tailWord_8198724
  simp only [CollatzResearch.WordTrace]
  refine ⟨149516015374715326713129613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199354687166287102284172817 149516015374715326713129613)
  ·
    refine ⟨56068505765518247517423605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149516015374715326713129613 56068505765518247517423605)
    ·
      refine ⟨5256422415517335704758463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56068505765518247517423605 5256422415517335704758463)
      ·
        refine ⟨7884633623276003557137695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5256422415517335704758463 7884633623276003557137695)
        ·
          refine ⟨11826950434914005335706543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7884633623276003557137695 11826950434914005335706543)
          ·
            refine ⟨17740425652371008003559815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11826950434914005335706543 17740425652371008003559815)
            ·
              refine ⟨26610638478556512005339723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17740425652371008003559815 26610638478556512005339723)
              ·
                refine ⟨39915957717834768008009585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26610638478556512005339723 39915957717834768008009585)
                ·
                  refine ⟨29936968288376076006007189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39915957717834768008009585 29936968288376076006007189)
                  ·
                    refine ⟨1403295388517628562781587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29936968288376076006007189 1403295388517628562781587)
                    ·
                      rfl

theorem cell23_8198724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_8198724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198724 prefixEnd_8198724 := by exact prefixLift 8198724
  have htrace : WordTrace (prefixWord ++ tailWord_8198724) baseStart_8198724 baseEnd_8198724 := by
    simpa [prefixWord, tailWord_8198724, baseEnd_8198724] using wordTrace_append hprefix tailTrace_8198724
  have hstable : (prefixWord ++ tailWord_8198724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198724).length < 2 ^ (prefixWord ++ tailWord_8198724).sum := by decide
  have hdescent : baseEnd_8198724 < baseStart_8198724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198730 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_8198730 : Nat := 118140960795 + 8198730 * 2 ^ 59
def prefixEnd_8198730 : Nat := 4983230072969 + 3 ^ 40 * 8198730 * 2
def baseEnd_8198730 : Nat := 4209889246436812664869733

theorem tailTrace_8198730 : CollatzResearch.WordTrace tailWord_8198730 prefixEnd_8198730 4209889246436812664869733 := by
  unfold tailWord_8198730
  simp only [CollatzResearch.WordTrace]
  refine ⟨74758062396852229112744411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199354833058272610967318429 74758062396852229112744411)
  ·
    refine ⟨112137093595278343669116617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74758062396852229112744411 112137093595278343669116617)
    ·
      refine ⟨84102820196458757751837463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112137093595278343669116617 84102820196458757751837463)
      ·
        refine ⟨126154230294688136627756195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84102820196458757751837463 126154230294688136627756195)
        ·
          refine ⟨189231345442032204941634293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126154230294688136627756195 189231345442032204941634293)
          ·
            refine ⟨17740438635190519213278215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189231345442032204941634293 17740438635190519213278215)
            ·
              refine ⟨26610657952785778819917323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17740438635190519213278215 26610657952785778819917323)
              ·
                refine ⟨39915986929178668229875985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26610657952785778819917323 39915986929178668229875985)
                ·
                  refine ⟨29936990196884001172406989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39915986929178668229875985 29936990196884001172406989)
                  ·
                    refine ⟨11226371323831500439652621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29936990196884001172406989 11226371323831500439652621)
                    ·
                      refine ⟨4209889246436812664869733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11226371323831500439652621 4209889246436812664869733)
                      ·
                        rfl

theorem cell23_8198730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_8198730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198730 prefixEnd_8198730 := by exact prefixLift 8198730
  have htrace : WordTrace (prefixWord ++ tailWord_8198730) baseStart_8198730 baseEnd_8198730 := by
    simpa [prefixWord, tailWord_8198730, baseEnd_8198730] using wordTrace_append hprefix tailTrace_8198730
  have hstable : (prefixWord ++ tailWord_8198730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198730).length < 2 ^ (prefixWord ++ tailWord_8198730).sum := by decide
  have hdescent : baseEnd_8198730 < baseStart_8198730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198780 : List Nat := [2, 2, 2, 1, 1, 2, 3, 3, 3, 4]
def baseStart_8198780 : Nat := 118140960795 + 8198780 * 2 ^ 59
def prefixEnd_8198780 : Nat := 4983230072969 + 3 ^ 40 * 8198780 * 2
def baseEnd_8198780 : Nat := 1403304973489845823081501

theorem tailTrace_8198780 : CollatzResearch.WordTrace tailWord_8198780 prefixEnd_8198780 1403304973489845823081501 := by
  unfold tailWord_8198780
  simp only [CollatzResearch.WordTrace]
  refine ⟨149517036618613887495148897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199356048824818516660198529 149517036618613887495148897)
  ·
    refine ⟨112137777463960415621361673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149517036618613887495148897 112137777463960415621361673)
    ·
      refine ⟨84103333097970311716021255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112137777463960415621361673 84103333097970311716021255)
      ·
        refine ⟨126154999646955467574031883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84103333097970311716021255 126154999646955467574031883)
        ·
          refine ⟨189232499470433201361047825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126154999646955467574031883 189232499470433201361047825)
          ·
            refine ⟨141924374602824901020785869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189232499470433201361047825 141924374602824901020785869)
            ·
              refine ⟨53221640476059337882794701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141924374602824901020785869 53221640476059337882794701)
              ·
                refine ⟨19958115178522251706048013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53221640476059337882794701 19958115178522251706048013)
                ·
                  refine ⟨7484293191945844389768005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19958115178522251706048013 7484293191945844389768005)
                  ·
                    refine ⟨1403304973489845823081501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7484293191945844389768005 1403304973489845823081501)
                    ·
                      rfl

theorem cell23_8198780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_8198780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198780 prefixEnd_8198780 := by exact prefixLift 8198780
  have htrace : WordTrace (prefixWord ++ tailWord_8198780) baseStart_8198780 baseEnd_8198780 := by
    simpa [prefixWord, tailWord_8198780, baseEnd_8198780] using wordTrace_append hprefix tailTrace_8198780
  have hstable : (prefixWord ++ tailWord_8198780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198780).length < 2 ^ (prefixWord ++ tailWord_8198780).sum := by decide
  have hdescent : baseEnd_8198780 < baseStart_8198780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198843 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 4]
def baseStart_8198843 : Nat := 118140960795 + 8198843 * 2 ^ 59
def prefixEnd_8198843 : Nat := 4983230072969 + 3 ^ 40 * 8198843 * 2
def baseEnd_8198843 : Nat := 4209947269750770722756713

theorem tailTrace_8198843 : CollatzResearch.WordTrace tailWord_8198843 prefixEnd_8198843 4209947269750770722756713 := by
  unfold tailWord_8198843
  simp only [CollatzResearch.WordTrace]
  refine ⟨299036371035999536749841183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199357580690666357833227455 299036371035999536749841183)
  ·
    refine ⟨448554556553999305124761775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299036371035999536749841183 448554556553999305124761775)
    ·
      refine ⟨672831834830998957687142663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448554556553999305124761775 672831834830998957687142663)
      ·
        refine ⟨1009247752246498436530713995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672831834830998957687142663 1009247752246498436530713995)
        ·
          refine ⟨1513871628369747654796070993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009247752246498436530713995 1513871628369747654796070993)
          ·
            refine ⟨1135403721277310741097053245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1513871628369747654796070993 1135403721277310741097053245)
            ·
              refine ⟨425776395478991527911394967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1135403721277310741097053245 425776395478991527911394967)
              ·
                refine ⟨638664593218487291867092451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425776395478991527911394967 638664593218487291867092451)
                ·
                  refine ⟨957996889827730937800638677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638664593218487291867092451 957996889827730937800638677)
                  ·
                    refine ⟨22453052105337443854702469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 957996889827730937800638677 22453052105337443854702469)
                    ·
                      refine ⟨4209947269750770722756713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22453052105337443854702469 4209947269750770722756713)
                      ·
                        rfl

theorem cell23_8198843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 4].length) (baseStart_8198843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198843 prefixEnd_8198843 := by exact prefixLift 8198843
  have htrace : WordTrace (prefixWord ++ tailWord_8198843) baseStart_8198843 baseEnd_8198843 := by
    simpa [prefixWord, tailWord_8198843, baseEnd_8198843] using wordTrace_append hprefix tailTrace_8198843
  have hstable : (prefixWord ++ tailWord_8198843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198843).length < 2 ^ (prefixWord ++ tailWord_8198843).sum := by decide
  have hdescent : baseEnd_8198843 < baseStart_8198843 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198863 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 5]
def baseStart_8198863 : Nat := 118140960795 + 8198863 * 2 ^ 59
def prefixEnd_8198863 : Nat := 4983230072969 + 3 ^ 40 * 8198863 * 2
def baseEnd_8198863 : Nat := 4209957539363860644506621

theorem tailTrace_8198863 : CollatzResearch.WordTrace tailWord_8198863 prefixEnd_8198863 4209957539363860644506621 := by
  unfold tailWord_8198863
  simp only [CollatzResearch.WordTrace]
  refine ⟨299037100495927080165569243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199358066997284720110379495 299037100495927080165569243)
  ·
    refine ⟨448555650743890620248353865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299037100495927080165569243 448555650743890620248353865)
    ·
      refine ⟨336416738057917965186265399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448555650743890620248353865 336416738057917965186265399)
      ·
        refine ⟨504625107086876947779398099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336416738057917965186265399 504625107086876947779398099)
        ·
          refine ⟨756937660630315421669097149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504625107086876947779398099 756937660630315421669097149)
          ·
            refine ⟨283851622736368283125911431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 756937660630315421669097149 283851622736368283125911431)
            ·
              refine ⟨425777434104552424688867147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283851622736368283125911431 425777434104552424688867147)
              ·
                refine ⟨638666151156828637033300721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425777434104552424688867147 638666151156828637033300721)
                ·
                  refine ⟨478999613367621477774975541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 638666151156828637033300721 478999613367621477774975541)
                  ·
                    refine ⟨44906213753214513541403957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 478999613367621477774975541 44906213753214513541403957)
                    ·
                      refine ⟨4209957539363860644506621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44906213753214513541403957 4209957539363860644506621)
                      ·
                        rfl

theorem cell23_8198863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_8198863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198863 prefixEnd_8198863 := by exact prefixLift 8198863
  have htrace : WordTrace (prefixWord ++ tailWord_8198863) baseStart_8198863 baseEnd_8198863 := by
    simpa [prefixWord, tailWord_8198863, baseEnd_8198863] using wordTrace_append hprefix tailTrace_8198863
  have hstable : (prefixWord ++ tailWord_8198863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198863).length < 2 ^ (prefixWord ++ tailWord_8198863).sum := by decide
  have hdescent : baseEnd_8198863 < baseStart_8198863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198890 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_8198890 : Nat := 118140960795 + 8198890 * 2 ^ 59
def prefixEnd_8198890 : Nat := 4983230072969 + 3 ^ 40 * 8198890 * 2
def baseEnd_8198890 : Nat := 4209971403341532038868997

theorem tailTrace_8198890 : CollatzResearch.WordTrace tailWord_8198890 prefixEnd_8198890 4209971403341532038868997 := by
  unfold tailWord_8198890
  simp only [CollatzResearch.WordTrace]
  refine ⟨74759521316707315944200531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199358723511219509184534749 74759521316707315944200531)
  ·
    refine ⟨112139281975060973916300797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74759521316707315944200531 112139281975060973916300797)
    ·
      refine ⟨42052230740647865218612799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112139281975060973916300797 42052230740647865218612799)
      ·
        refine ⟨63078346110971797827919199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42052230740647865218612799 63078346110971797827919199)
        ·
          refine ⟨94617519166457696741878799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63078346110971797827919199 94617519166457696741878799)
          ·
            refine ⟨141926278749686545112818199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94617519166457696741878799 141926278749686545112818199)
            ·
              refine ⟨212889418124529817669227299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141926278749686545112818199 212889418124529817669227299)
              ·
                refine ⟨319334127186794726503840949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212889418124529817669227299 319334127186794726503840949)
                ·
                  refine ⟨29937574423762005609735089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 319334127186794726503840949 29937574423762005609735089)
                  ·
                    refine ⟨22453180817821504207301317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29937574423762005609735089 22453180817821504207301317)
                    ·
                      refine ⟨4209971403341532038868997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22453180817821504207301317 4209971403341532038868997)
                      ·
                        rfl

theorem cell23_8198890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_8198890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198890 prefixEnd_8198890 := by exact prefixLift 8198890
  have htrace : WordTrace (prefixWord ++ tailWord_8198890) baseStart_8198890 baseEnd_8198890 := by
    simpa [prefixWord, tailWord_8198890, baseEnd_8198890] using wordTrace_append hprefix tailTrace_8198890
  have hstable : (prefixWord ++ tailWord_8198890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198890).length < 2 ^ (prefixWord ++ tailWord_8198890).sum := by decide
  have hdescent : baseEnd_8198890 < baseStart_8198890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198914 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_8198914 : Nat := 118140960795 + 8198914 * 2 ^ 59
def prefixEnd_8198914 : Nat := 4983230072969 + 3 ^ 40 * 8198914 * 2
def baseEnd_8198914 : Nat := 4209983726877239944968887

theorem tailTrace_8198914 : CollatzResearch.WordTrace tailWord_8198914 prefixEnd_8198914 4209983726877239944968887 := by
  unfold tailWord_8198914
  simp only [CollatzResearch.WordTrace]
  refine ⟨74759740154685578968918949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199359307079161543917117197 74759740154685578968918949)
  ·
    refine ⟨14017451279003546056672303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74759740154685578968918949 14017451279003546056672303)
    ·
      refine ⟨21026176918505319085008455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14017451279003546056672303 21026176918505319085008455)
      ·
        refine ⟨31539265377757978627512683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21026176918505319085008455 31539265377757978627512683)
        ·
          refine ⟨47308898066636967941269025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31539265377757978627512683 47308898066636967941269025)
          ·
            refine ⟨35481673549977725955951769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47308898066636967941269025 35481673549977725955951769)
            ·
              refine ⟨26611255162483294466963827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35481673549977725955951769 26611255162483294466963827)
              ·
                refine ⟨39916882743724941700445741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26611255162483294466963827 39916882743724941700445741)
                ·
                  refine ⟨14968831028896853137667153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39916882743724941700445741 14968831028896853137667153)
                  ·
                    refine ⟨11226623271672639853250365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14968831028896853137667153 11226623271672639853250365)
                    ·
                      refine ⟨4209983726877239944968887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11226623271672639853250365 4209983726877239944968887)
                      ·
                        rfl

theorem cell23_8198914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_8198914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198914 prefixEnd_8198914 := by exact prefixLift 8198914
  have htrace : WordTrace (prefixWord ++ tailWord_8198914) baseStart_8198914 baseEnd_8198914 := by
    simpa [prefixWord, tailWord_8198914, baseEnd_8198914] using wordTrace_append hprefix tailTrace_8198914
  have hstable : (prefixWord ++ tailWord_8198914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198914).length < 2 ^ (prefixWord ++ tailWord_8198914).sum := by decide
  have hdescent : baseEnd_8198914 < baseStart_8198914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198927 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 4, 1, 3]
def baseStart_8198927 : Nat := 118140960795 + 8198927 * 2 ^ 59
def prefixEnd_8198927 : Nat := 4983230072969 + 3 ^ 40 * 8198927 * 2
def baseEnd_8198927 : Nat := 4209990402125748394106327

theorem tailTrace_8198927 : CollatzResearch.WordTrace tailWord_8198927 prefixEnd_8198927 4209990402125748394106327 := by
  unfold tailWord_8198927
  simp only [CollatzResearch.WordTrace]
  refine ⟨299039434767695219095899035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199359623178463479397266023 299039434767695219095899035)
  ·
    refine ⟨448559152151542828643848553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299039434767695219095899035 448559152151542828643848553)
    ·
      refine ⟨336419364113657121482886415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448559152151542828643848553 336419364113657121482886415)
      ·
        refine ⟨504629046170485682224329623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336419364113657121482886415 504629046170485682224329623)
        ·
          refine ⟨756943569255728523336494435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504629046170485682224329623 756943569255728523336494435)
          ·
            refine ⟨1135415353883592785004741653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756943569255728523336494435 1135415353883592785004741653)
            ·
              refine ⟨53222594713293411797097265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1135415353883592785004741653 53222594713293411797097265)
              ·
                refine ⟨39916946034970058847822949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53222594713293411797097265 39916946034970058847822949)
                ·
                  refine ⟨7484427381556886033966803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39916946034970058847822949 7484427381556886033966803)
                  ·
                    refine ⟨11226641072335329050950205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7484427381556886033966803 11226641072335329050950205)
                    ·
                      refine ⟨4209990402125748394106327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11226641072335329050950205 4209990402125748394106327)
                      ·
                        rfl

theorem cell23_8198927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 4, 1, 3].length) (baseStart_8198927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198927 prefixEnd_8198927 := by exact prefixLift 8198927
  have htrace : WordTrace (prefixWord ++ tailWord_8198927) baseStart_8198927 baseEnd_8198927 := by
    simpa [prefixWord, tailWord_8198927, baseEnd_8198927] using wordTrace_append hprefix tailTrace_8198927
  have hstable : (prefixWord ++ tailWord_8198927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198927).length < 2 ^ (prefixWord ++ tailWord_8198927).sum := by decide
  have hdescent : baseEnd_8198927 < baseStart_8198927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198937 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 5, 3, 2]
def baseStart_8198937 : Nat := 118140960795 + 8198937 * 2 ^ 59
def prefixEnd_8198937 : Nat := 4983230072969 + 3 ^ 40 * 8198937 * 2
def baseEnd_8198937 : Nat := 4209995536932293354981281

theorem tailTrace_8198937 : CollatzResearch.WordTrace tailWord_8198937 prefixEnd_8198937 4209995536932293354981281 := by
  unfold tailWord_8198937
  simp only [CollatzResearch.WordTrace]
  refine ⟨299039799497658990803763065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199359866331772660535842043 299039799497658990803763065)
  ·
    refine ⟨224279849623244243102822299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299039799497658990803763065 224279849623244243102822299)
    ·
      refine ⟨336419774434866364654233449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224279849623244243102822299 336419774434866364654233449)
      ·
        refine ⟨252314830826149773490675087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336419774434866364654233449 252314830826149773490675087)
        ·
          refine ⟨378472246239224660236012631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252314830826149773490675087 378472246239224660236012631)
          ·
            refine ⟨567708369358836990354018947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378472246239224660236012631 567708369358836990354018947)
            ·
              refine ⟨851562554038255485531028421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567708369358836990354018947 851562554038255485531028421)
              ·
                refine ⟨159667978882172903537067829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 851562554038255485531028421 159667978882172903537067829)
                ·
                  refine ⟨14968873020203709706600109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159667978882172903537067829 14968873020203709706600109)
                  ·
                    refine ⟨5613327382576391139975041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14968873020203709706600109 5613327382576391139975041)
                    ·
                      refine ⟨4209995536932293354981281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5613327382576391139975041 4209995536932293354981281)
                      ·
                        rfl

theorem cell23_8198937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 3, 2].length) (baseStart_8198937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198937 prefixEnd_8198937 := by exact prefixLift 8198937
  have htrace : WordTrace (prefixWord ++ tailWord_8198937) baseStart_8198937 baseEnd_8198937 := by
    simpa [prefixWord, tailWord_8198937, baseEnd_8198937] using wordTrace_append hprefix tailTrace_8198937
  have hstable : (prefixWord ++ tailWord_8198937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198937).length < 2 ^ (prefixWord ++ tailWord_8198937).sum := by decide
  have hdescent : baseEnd_8198937 < baseStart_8198937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198944 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 4, 1, 3]
def baseStart_8198944 : Nat := 118140960795 + 8198944 * 2 ^ 59
def prefixEnd_8198944 : Nat := 4983230072969 + 3 ^ 40 * 8198944 * 2
def baseEnd_8198944 : Nat := 4209999131296874827593749

theorem tailTrace_8198944 : CollatzResearch.WordTrace tailWord_8198944 prefixEnd_8198944 4209999131296874827593749 := by
  unfold tailWord_8198944
  simp only [CollatzResearch.WordTrace]
  refine ⟨149520027404316815499633943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199360036539089087332845257 149520027404316815499633943)
  ·
    refine ⟨224280041106475223249450915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149520027404316815499633943 224280041106475223249450915)
    ·
      refine ⟨336420061659712834874176373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224280041106475223249450915 336420061659712834874176373)
      ·
        refine ⟨31539380780598078269454035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336420061659712834874176373 31539380780598078269454035)
        ·
          refine ⟨47309071170897117404181053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31539380780598078269454035 47309071170897117404181053)
          ·
            refine ⟨17740901689086419026567895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47309071170897117404181053 17740901689086419026567895)
            ·
              refine ⟨26611352533629628539851843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17740901689086419026567895 26611352533629628539851843)
              ·
                refine ⟨39917028800444442809777765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26611352533629628539851843 39917028800444442809777765)
                ·
                  refine ⟨7484442900083333026833331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39917028800444442809777765 7484442900083333026833331)
                  ·
                    refine ⟨11226664350124999540249997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7484442900083333026833331 11226664350124999540249997)
                    ·
                      refine ⟨4209999131296874827593749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11226664350124999540249997 4209999131296874827593749)
                      ·
                        rfl

theorem cell23_8198944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_8198944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198944 prefixEnd_8198944 := by exact prefixLift 8198944
  have htrace : WordTrace (prefixWord ++ tailWord_8198944) baseStart_8198944 baseEnd_8198944 := by
    simpa [prefixWord, tailWord_8198944, baseEnd_8198944] using wordTrace_append hprefix tailTrace_8198944
  have hstable : (prefixWord ++ tailWord_8198944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198944).length < 2 ^ (prefixWord ++ tailWord_8198944).sum := by decide
  have hdescent : baseEnd_8198944 < baseStart_8198944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198961 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 2, 1, 3]
def baseStart_8198961 : Nat := 118140960795 + 8198961 * 2 ^ 59
def prefixEnd_8198961 : Nat := 4983230072969 + 3 ^ 40 * 8198961 * 2
def baseEnd_8198961 : Nat := 4210007860468001261081171

theorem tailTrace_8198961 : CollatzResearch.WordTrace tailWord_8198961 prefixEnd_8198961 4210007860468001261081171 := by
  unfold tailWord_8198961
  simp only [CollatzResearch.WordTrace]
  refine ⟨299040674849572042902636737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199360449899714695268424491 299040674849572042902636737)
  ·
    refine ⟨224280506137179032176977553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299040674849572042902636737 224280506137179032176977553)
    ·
      refine ⟨168210379602884274132733165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224280506137179032176977553 168210379602884274132733165)
      ·
        refine ⟨63078892351081602799774937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168210379602884274132733165 63078892351081602799774937)
        ·
          refine ⟨47309169263311202099831203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63078892351081602799774937 47309169263311202099831203)
          ·
            refine ⟨70963753894966803149746805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47309169263311202099831203 70963753894966803149746805)
            ·
              refine ⟨6652851927653137795288763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70963753894966803149746805 6652851927653137795288763)
              ·
                refine ⟨9979277891479706692933145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6652851927653137795288763 9979277891479706692933145)
                ·
                  refine ⟨7484458418609780019699859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9979277891479706692933145 7484458418609780019699859)
                  ·
                    refine ⟨11226687627914670029549789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7484458418609780019699859 11226687627914670029549789)
                    ·
                      refine ⟨4210007860468001261081171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11226687627914670029549789 4210007860468001261081171)
                      ·
                        rfl

theorem cell23_8198961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_8198961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198961 prefixEnd_8198961 := by exact prefixLift 8198961
  have htrace : WordTrace (prefixWord ++ tailWord_8198961) baseStart_8198961 baseEnd_8198961 := by
    simpa [prefixWord, tailWord_8198961, baseEnd_8198961] using wordTrace_append hprefix tailTrace_8198961
  have hstable : (prefixWord ++ tailWord_8198961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198961).length < 2 ^ (prefixWord ++ tailWord_8198961).sum := by decide
  have hdescent : baseEnd_8198961 < baseStart_8198961 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198984 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 6, 2, 2]
def baseStart_8198984 : Nat := 118140960795 + 8198984 * 2 ^ 59
def prefixEnd_8198984 : Nat := 4983230072969 + 3 ^ 40 * 8198984 * 2
def baseEnd_8198984 : Nat := 4210019670523054671093565

theorem tailTrace_8198984 : CollatzResearch.WordTrace tailWord_8198984 prefixEnd_8198984 4210019670523054671093565 := by
  unfold tailWord_8198984
  simp only [CollatzResearch.WordTrace]
  refine ⟨149520756864244358915362003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199361009152325811887149337 149520756864244358915362003)
  ·
    refine ⟨224281135296366538373043005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149520756864244358915362003 224281135296366538373043005)
    ·
      refine ⟨84105425736137451889891127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224281135296366538373043005 84105425736137451889891127)
      ·
        refine ⟨126158138604206177834836691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84105425736137451889891127 126158138604206177834836691)
        ·
          refine ⟨189237207906309266752255037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126158138604206177834836691 189237207906309266752255037)
          ·
            refine ⟨70963952964865975032095639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189237207906309266752255037 70963952964865975032095639)
            ·
              refine ⟨106445929447298962548143459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70963952964865975032095639 106445929447298962548143459)
              ·
                refine ⟨159668894170948443822215189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106445929447298962548143459 159668894170948443822215189)
                ·
                  refine ⟨7484479414263208304166337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159668894170948443822215189 7484479414263208304166337)
                  ·
                    refine ⟨5613359560697406228124753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7484479414263208304166337 5613359560697406228124753)
                    ·
                      refine ⟨4210019670523054671093565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5613359560697406228124753 4210019670523054671093565)
                      ·
                        rfl

theorem cell23_8198984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_8198984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198984 prefixEnd_8198984 := by exact prefixLift 8198984
  have htrace : WordTrace (prefixWord ++ tailWord_8198984) baseStart_8198984 baseEnd_8198984 := by
    simpa [prefixWord, tailWord_8198984, baseEnd_8198984] using wordTrace_append hprefix tailTrace_8198984
  have hstable : (prefixWord ++ tailWord_8198984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198984).length < 2 ^ (prefixWord ++ tailWord_8198984).sum := by decide
  have hdescent : baseEnd_8198984 < baseStart_8198984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8198990 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_8198990 : Nat := 118140960795 + 8198990 * 2 ^ 59
def prefixEnd_8198990 : Nat := 4983230072969 + 3 ^ 40 * 8198990 * 2
def baseEnd_8198990 : Nat := 467780305711886849735393

theorem tailTrace_8198990 : CollatzResearch.WordTrace tailWord_8198990 prefixEnd_8198990 467780305711886849735393 := by
  unfold tailWord_8198990
  simp only [CollatzResearch.WordTrace]
  refine ⟨37380216570808372606930303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199361155044311320570294949 37380216570808372606930303)
  ·
    refine ⟨56070324856212558910395455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37380216570808372606930303 56070324856212558910395455)
    ·
      refine ⟨84105487284318838365593183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56070324856212558910395455 84105487284318838365593183)
      ·
        refine ⟨126158230926478257548389775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84105487284318838365593183 126158230926478257548389775)
        ·
          refine ⟨189237346389717386322584663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126158230926478257548389775 189237346389717386322584663)
          ·
            refine ⟨283856019584576079483876995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189237346389717386322584663 283856019584576079483876995)
            ·
              refine ⟨425784029376864119225815493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283856019584576079483876995 425784029376864119225815493)
              ·
                refine ⟨79834505508162022354840405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425784029376864119225815493 79834505508162022354840405)
                ·
                  refine ⟨467780305711886849735393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79834505508162022354840405 467780305711886849735393)
                  ·
                    rfl

theorem cell23_8198990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_8198990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8198990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8198990 prefixEnd_8198990 := by exact prefixLift 8198990
  have htrace : WordTrace (prefixWord ++ tailWord_8198990) baseStart_8198990 baseEnd_8198990 := by
    simpa [prefixWord, tailWord_8198990, baseEnd_8198990] using wordTrace_append hprefix tailTrace_8198990
  have hstable : (prefixWord ++ tailWord_8198990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8198990).length < 2 ^ (prefixWord ++ tailWord_8198990).sum := by decide
  have hdescent : baseEnd_8198990 < baseStart_8198990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8198990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199037 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 2, 5]
def baseStart_8199037 : Nat := 118140960795 + 8199037 * 2 ^ 59
def prefixEnd_8199037 : Nat := 4983230072969 + 3 ^ 40 * 8199037 * 2
def baseEnd_8199037 : Nat := 1403348961665914321243607

theorem tailTrace_8199037 : CollatzResearch.WordTrace tailWord_8199037 prefixEnd_8199037 1403348961665914321243607 := by
  unfold tailWord_8199037
  simp only [CollatzResearch.WordTrace]
  refine ⟨299043446797296707882403365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199362297864864471921602243 299043446797296707882403365)
  ·
    refine ⟨56070646274493132727950631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299043446797296707882403365 56070646274493132727950631)
    ·
      refine ⟨84105969411739699091925947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56070646274493132727950631 84105969411739699091925947)
      ·
        refine ⟨126158954117609548637888921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84105969411739699091925947 126158954117609548637888921)
        ·
          refine ⟨94619215588207161478416691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126158954117609548637888921 94619215588207161478416691)
          ·
            refine ⟨141928823382310742217625037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94619215588207161478416691 141928823382310742217625037)
            ·
              refine ⟨53223308768366528331609389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141928823382310742217625037 53223308768366528331609389)
              ·
                refine ⟨19958740788137448124353521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53223308768366528331609389 19958740788137448124353521)
                ·
                  refine ⟨14969055591103086093265141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19958740788137448124353521 14969055591103086093265141)
                  ·
                    refine ⟨1403348961665914321243607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14969055591103086093265141 1403348961665914321243607)
                    ·
                      rfl

theorem cell23_8199037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_8199037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199037 prefixEnd_8199037 := by exact prefixLift 8199037
  have htrace : WordTrace (prefixWord ++ tailWord_8199037) baseStart_8199037 baseEnd_8199037 := by
    simpa [prefixWord, tailWord_8199037, baseEnd_8199037] using wordTrace_append hprefix tailTrace_8199037
  have hstable : (prefixWord ++ tailWord_8199037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199037).length < 2 ^ (prefixWord ++ tailWord_8199037).sum := by decide
  have hdescent : baseEnd_8199037 < baseStart_8199037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199047 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_8199047 : Nat := 118140960795 + 8199047 * 2 ^ 59
def prefixEnd_8199047 : Nat := 4983230072969 + 3 ^ 40 * 8199047 * 2
def baseEnd_8199047 : Nat := 4210052019804287924605775

theorem tailTrace_8199047 : CollatzResearch.WordTrace tailWord_8199047 prefixEnd_8199047 4210052019804287924605775 := by
  unfold tailWord_8199047
  simp only [CollatzResearch.WordTrace]
  refine ⟨299043811527260479590267395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199362541018173653060178263 299043811527260479590267395)
  ·
    refine ⟨448565717290890719385401093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299043811527260479590267395 448565717290890719385401093)
    ·
      refine ⟨84106071992042009884762705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448565717290890719385401093 84106071992042009884762705)
      ·
        refine ⟨63079553994031507413572029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84106071992042009884762705 63079553994031507413572029)
        ·
          refine ⟨23654832747761815280089511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63079553994031507413572029 23654832747761815280089511)
          ·
            refine ⟨35482249121642722920134267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23654832747761815280089511 35482249121642722920134267)
            ·
              refine ⟨53223373682464084380201401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35482249121642722920134267 53223373682464084380201401)
              ·
                refine ⟨39917530261848063285151051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53223373682464084380201401 39917530261848063285151051)
                ·
                  refine ⟨59876295392772094927726577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39917530261848063285151051 59876295392772094927726577)
                  ·
                    refine ⟨44907221544579071195794933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59876295392772094927726577 44907221544579071195794933)
                    ·
                      refine ⟨4210052019804287924605775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44907221544579071195794933 4210052019804287924605775)
                      ·
                        rfl

theorem cell23_8199047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_8199047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199047 prefixEnd_8199047 := by exact prefixLift 8199047
  have htrace : WordTrace (prefixWord ++ tailWord_8199047) baseStart_8199047 baseEnd_8199047 := by
    simpa [prefixWord, tailWord_8199047, baseEnd_8199047] using wordTrace_append hprefix tailTrace_8199047
  have hstable : (prefixWord ++ tailWord_8199047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199047).length < 2 ^ (prefixWord ++ tailWord_8199047).sum := by decide
  have hdescent : baseEnd_8199047 < baseStart_8199047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199127 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 3, 5]
def baseStart_8199127 : Nat := 118140960795 + 8199127 * 2 ^ 59
def prefixEnd_8199127 : Nat := 4983230072969 + 3 ^ 40 * 8199127 * 2
def baseEnd_8199127 : Nat := 1403364366085549203868469

theorem tailTrace_8199127 : CollatzResearch.WordTrace tailWord_8199127 prefixEnd_8199127 1403364366085549203868469 := by
  unfold tailWord_8199127
  simp only [CollatzResearch.WordTrace]
  refine ⟨299046729366970653253179635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199364486244647102168786423 299046729366970653253179635)
  ·
    refine ⟨448570094050455979879769453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299046729366970653253179635 448570094050455979879769453)
    ·
      refine ⟨168213785268920992454913545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448570094050455979879769453 168213785268920992454913545)
      ·
        refine ⟨126160338951690744341185159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168213785268920992454913545 126160338951690744341185159)
        ·
          refine ⟨189240508427536116511777739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126160338951690744341185159 189240508427536116511777739)
          ·
            refine ⟨283860762641304174767666609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189240508427536116511777739 283860762641304174767666609)
            ·
              refine ⟨212895571980978131075749957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283860762641304174767666609 212895571980978131075749957)
              ·
                refine ⟨39917919746433399576703117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212895571980978131075749957 39917919746433399576703117)
                ·
                  refine ⟨14969219904912524841263669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39917919746433399576703117 14969219904912524841263669)
                  ·
                    refine ⟨1403364366085549203868469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14969219904912524841263669 1403364366085549203868469)
                    ·
                      rfl

theorem cell23_8199127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_8199127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199127 prefixEnd_8199127 := by exact prefixLift 8199127
  have htrace : WordTrace (prefixWord ++ tailWord_8199127) baseStart_8199127 baseEnd_8199127 := by
    simpa [prefixWord, tailWord_8199127, baseEnd_8199127] using wordTrace_append hprefix tailTrace_8199127
  have hstable : (prefixWord ++ tailWord_8199127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199127).length < 2 ^ (prefixWord ++ tailWord_8199127).sum := by decide
  have hdescent : baseEnd_8199127 < baseStart_8199127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199144 : List Nat := [2, 1, 4, 1, 1, 1, 3, 4, 1, 5]
def baseStart_8199144 : Nat := 118140960795 + 8199144 * 2 ^ 59
def prefixEnd_8199144 : Nat := 4983230072969 + 3 ^ 40 * 8199144 * 2
def baseEnd_8199144 : Nat := 1403367275809258015030943

theorem tailTrace_8199144 : CollatzResearch.WordTrace tailWord_8199144 prefixEnd_8199144 1403367275809258015030943 := by
  unfold tailWord_8199144
  simp only [CollatzResearch.WordTrace]
  refine ⟨149523674703954532578274243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199364899605272710104365657 149523674703954532578274243)
  ·
    refine ⟨224285512055931798867411365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149523674703954532578274243 224285512055931798867411365)
    ·
      refine ⟨42053533510487212287639631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224285512055931798867411365 42053533510487212287639631)
      ·
        refine ⟨63080300265730818431459447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42053533510487212287639631 63080300265730818431459447)
        ·
          refine ⟨94620450398596227647189171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63080300265730818431459447 94620450398596227647189171)
          ·
            refine ⟨141930675597894341470783757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94620450398596227647189171 141930675597894341470783757)
            ·
              refine ⟨53224003349210378051543909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141930675597894341470783757 53224003349210378051543909)
              ·
                refine ⟨9979500627976945884664483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53224003349210378051543909 9979500627976945884664483)
                ·
                  refine ⟨14969250941965418826996725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9979500627976945884664483 14969250941965418826996725)
                  ·
                    refine ⟨1403367275809258015030943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14969250941965418826996725 1403367275809258015030943)
                    ·
                      rfl

theorem cell23_8199144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_8199144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199144 prefixEnd_8199144 := by exact prefixLift 8199144
  have htrace : WordTrace (prefixWord ++ tailWord_8199144) baseStart_8199144 baseEnd_8199144 := by
    simpa [prefixWord, tailWord_8199144, baseEnd_8199144] using wordTrace_append hprefix tailTrace_8199144
  have hstable : (prefixWord ++ tailWord_8199144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199144).length < 2 ^ (prefixWord ++ tailWord_8199144).sum := by decide
  have hdescent : baseEnd_8199144 < baseStart_8199144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199175 : List Nat := [1, 1, 4, 3, 1, 1, 5, 2, 1, 1, 3]
def baseStart_8199175 : Nat := 118140960795 + 8199175 * 2 ^ 59
def prefixEnd_8199175 : Nat := 4983230072969 + 3 ^ 40 * 8199175 * 2
def baseEnd_8199175 : Nat := 4210117745328063423805187

theorem tailTrace_8199175 : CollatzResearch.WordTrace tailWord_8199175 prefixEnd_8199175 4210117745328063423805187 := by
  unfold tailWord_8199175
  simp only [CollatzResearch.WordTrace]
  refine ⟨299048480070796757450926979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199365653380531171633951319 299048480070796757450926979)
  ·
    refine ⟨448572720106195136176390469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299048480070796757450926979 448572720106195136176390469)
    ·
      refine ⟨84107385019911588033073213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448572720106195136176390469 84107385019911588033073213)
      ·
        refine ⟨31540269382466845512402455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84107385019911588033073213 31540269382466845512402455)
        ·
          refine ⟨47310404073700268268603683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31540269382466845512402455 47310404073700268268603683)
          ·
            refine ⟨70965606110550402402905525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47310404073700268268603683 70965606110550402402905525)
            ·
              refine ⟨6653025572864100225272393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70965606110550402402905525 6653025572864100225272393)
              ·
                refine ⟨4989769179648075168954295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653025572864100225272393 4989769179648075168954295)
                ·
                  refine ⟨7484653769472112753431443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989769179648075168954295 7484653769472112753431443)
                  ·
                    refine ⟨11226980654208169130147165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7484653769472112753431443 11226980654208169130147165)
                    ·
                      refine ⟨4210117745328063423805187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11226980654208169130147165 4210117745328063423805187)
                      ·
                        rfl

theorem cell23_8199175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_8199175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199175 prefixEnd_8199175 := by exact prefixLift 8199175
  have htrace : WordTrace (prefixWord ++ tailWord_8199175) baseStart_8199175 baseEnd_8199175 := by
    simpa [prefixWord, tailWord_8199175, baseEnd_8199175] using wordTrace_append hprefix tailTrace_8199175
  have hstable : (prefixWord ++ tailWord_8199175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199175).length < 2 ^ (prefixWord ++ tailWord_8199175).sum := by decide
  have hdescent : baseEnd_8199175 < baseStart_8199175 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199194 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_8199194 : Nat := 118140960795 + 8199194 * 2 ^ 59
def prefixEnd_8199194 : Nat := 4983230072969 + 3 ^ 40 * 8199194 * 2
def baseEnd_8199194 : Nat := 4210127501460498849467599

theorem tailTrace_8199194 : CollatzResearch.WordTrace tailWord_8199194 prefixEnd_8199194 4210127501460498849467599 := by
  unfold tailWord_8199194
  simp only [CollatzResearch.WordTrace]
  refine ⟨74762293264431980923967159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199366115371818615797245757 74762293264431980923967159)
  ·
    refine ⟨112143439896647971385950739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74762293264431980923967159 112143439896647971385950739)
    ·
      refine ⟨168215159844971957078926109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112143439896647971385950739 168215159844971957078926109)
      ·
        refine ⟨63080684941864483904597291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168215159844971957078926109 63080684941864483904597291)
        ·
          refine ⟨94621027412796725856895937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63080684941864483904597291 94621027412796725856895937)
          ·
            refine ⟨70965770559597544392671953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94621027412796725856895937 70965770559597544392671953)
            ·
              refine ⟨53224327919698158294503965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70965770559597544392671953 53224327919698158294503965)
              ·
                refine ⟨19959122969886809360438987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53224327919698158294503965 19959122969886809360438987)
                ·
                  refine ⟨29938684454830214040658481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19959122969886809360438987 29938684454830214040658481)
                  ·
                    refine ⟨22454013341122660530493861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29938684454830214040658481 22454013341122660530493861)
                    ·
                      refine ⟨4210127501460498849467599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22454013341122660530493861 4210127501460498849467599)
                      ·
                        rfl

theorem cell23_8199194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_8199194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199194 prefixEnd_8199194 := by exact prefixLift 8199194
  have htrace : WordTrace (prefixWord ++ tailWord_8199194) baseStart_8199194 baseEnd_8199194 := by
    simpa [prefixWord, tailWord_8199194, baseEnd_8199194] using wordTrace_append hprefix tailTrace_8199194
  have hstable : (prefixWord ++ tailWord_8199194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199194).length < 2 ^ (prefixWord ++ tailWord_8199194).sum := by decide
  have hdescent : baseEnd_8199194 < baseStart_8199194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199201 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 3, 2, 3]
def baseStart_8199201 : Nat := 118140960795 + 8199201 * 2 ^ 59
def prefixEnd_8199201 : Nat := 4983230072969 + 3 ^ 40 * 8199201 * 2
def baseEnd_8199201 : Nat := 4210131095825080322080067

theorem tailTrace_8199201 : CollatzResearch.WordTrace tailWord_8199201 prefixEnd_8199201 4210131095825080322080067 := by
  unfold tailWord_8199201
  simp only [CollatzResearch.WordTrace]
  refine ⟨299049428368702563891373457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199366285579135042594248971 299049428368702563891373457)
  ·
    refine ⟨224287071276526922918530093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299049428368702563891373457 224287071276526922918530093)
    ·
      refine ⟨84107651728697596094448785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224287071276526922918530093 84107651728697596094448785)
      ·
        refine ⟨63080738796523197070836589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84107651728697596094448785 63080738796523197070836589)
        ·
          refine ⟨23655277048696198901563721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63080738796523197070836589 23655277048696198901563721)
          ·
            refine ⟨17741457786522149176172791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23655277048696198901563721 17741457786522149176172791)
            ·
              refine ⟨26612186679783223764259187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17741457786522149176172791 26612186679783223764259187)
              ·
                refine ⟨39918280019674835646388781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26612186679783223764259187 39918280019674835646388781)
                ·
                  refine ⟨14969355007378063367395793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39918280019674835646388781 14969355007378063367395793)
                  ·
                    refine ⟨11227016255533547525546845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14969355007378063367395793 11227016255533547525546845)
                    ·
                      refine ⟨4210131095825080322080067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11227016255533547525546845 4210131095825080322080067)
                      ·
                        rfl

theorem cell23_8199201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_8199201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199201 prefixEnd_8199201 := by exact prefixLift 8199201
  have htrace : WordTrace (prefixWord ++ tailWord_8199201) baseStart_8199201 baseEnd_8199201 := by
    simpa [prefixWord, tailWord_8199201, baseEnd_8199201] using wordTrace_append hprefix tailTrace_8199201
  have hstable : (prefixWord ++ tailWord_8199201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199201).length < 2 ^ (prefixWord ++ tailWord_8199201).sum := by decide
  have hdescent : baseEnd_8199201 < baseStart_8199201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199204 : List Nat := [2, 3, 1, 4, 1, 1, 2, 9]
def baseStart_8199204 : Nat := 118140960795 + 8199204 * 2 ^ 59
def prefixEnd_8199204 : Nat := 4983230072969 + 3 ^ 40 * 8199204 * 2
def baseEnd_8199204 : Nat := 155930838380260881864539

theorem tailTrace_8199204 : CollatzResearch.WordTrace tailWord_8199204 prefixEnd_8199204 155930838380260881864539 := by
  unfold tailWord_8199204
  simp only [CollatzResearch.WordTrace]
  refine ⟨149524768893845847701866333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199366358525127796935821777 149524768893845847701866333)
  ·
    refine ⟨56071788335192192888199875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149524768893845847701866333 56071788335192192888199875)
    ·
      refine ⟨84107682502788289332299813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56071788335192192888199875 84107682502788289332299813)
      ·
        refine ⟨15770190469272804249806215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84107682502788289332299813 15770190469272804249806215)
        ·
          refine ⟨23655285703909206374709323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15770190469272804249806215 23655285703909206374709323)
          ·
            refine ⟨35482928555863809562063985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23655285703909206374709323 35482928555863809562063985)
            ·
              refine ⟨26612196416897857171547989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35482928555863809562063985 26612196416897857171547989)
              ·
                refine ⟨155930838380260881864539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26612196416897857171547989 155930838380260881864539)
                ·
                  rfl

theorem cell23_8199204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 9].length) (baseStart_8199204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199204 prefixEnd_8199204 := by exact prefixLift 8199204
  have htrace : WordTrace (prefixWord ++ tailWord_8199204) baseStart_8199204 baseEnd_8199204 := by
    simpa [prefixWord, tailWord_8199204, baseEnd_8199204] using wordTrace_append hprefix tailTrace_8199204
  have hstable : (prefixWord ++ tailWord_8199204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199204).length < 2 ^ (prefixWord ++ tailWord_8199204).sum := by decide
  have hdescent : baseEnd_8199204 < baseStart_8199204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199218 : List Nat := [3, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3]
def baseStart_8199218 : Nat := 118140960795 + 8199218 * 2 ^ 59
def prefixEnd_8199218 : Nat := 4983230072969 + 3 ^ 40 * 8199218 * 2
def baseEnd_8199218 : Nat := 4210139824996206755567489

theorem tailTrace_8199218 : CollatzResearch.WordTrace tailWord_8199218 prefixEnd_8199218 4210139824996206755567489 := by
  unfold tailWord_8199218
  simp only [CollatzResearch.WordTrace]
  refine ⟨74762512102410243948685577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199366698939760650529828205 74762512102410243948685577)
  ·
    refine ⟨56071884076807682961514183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74762512102410243948685577 56071884076807682961514183)
    ·
      refine ⟨84107826115211524442271275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56071884076807682961514183 84107826115211524442271275)
      ·
        refine ⟨126161739172817286663406913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84107826115211524442271275 126161739172817286663406913)
        ·
          refine ⟨94621304379612964997555185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126161739172817286663406913 94621304379612964997555185)
          ·
            refine ⟨70965978284709723748166389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94621304379612964997555185 70965978284709723748166389)
            ·
              refine ⟨6653060464191536601390599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70965978284709723748166389 6653060464191536601390599)
              ·
                refine ⟨9979590696287304902085899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6653060464191536601390599 9979590696287304902085899)
                ·
                  refine ⟨14969386044430957353128849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9979590696287304902085899 14969386044430957353128849)
                  ·
                    refine ⟨11227039533323218014846637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14969386044430957353128849 11227039533323218014846637)
                    ·
                      refine ⟨4210139824996206755567489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11227039533323218014846637 4210139824996206755567489)
                      ·
                        rfl

theorem cell23_8199218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_8199218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199218 prefixEnd_8199218 := by exact prefixLift 8199218
  have htrace : WordTrace (prefixWord ++ tailWord_8199218) baseStart_8199218 baseEnd_8199218 := by
    simpa [prefixWord, tailWord_8199218, baseEnd_8199218] using wordTrace_append hprefix tailTrace_8199218
  have hstable : (prefixWord ++ tailWord_8199218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199218).length < 2 ^ (prefixWord ++ tailWord_8199218).sum := by decide
  have hdescent : baseEnd_8199218 < baseStart_8199218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199238 : List Nat := [6, 1, 1, 1, 1, 4, 1, 8]
def baseStart_8199238 : Nat := 118140960795 + 8199238 * 2 ^ 59
def prefixEnd_8199238 : Nat := 4983230072969 + 3 ^ 40 * 8199238 * 2
def baseEnd_8199238 : Nat := 155931484985529506567311

theorem tailTrace_8199238 : CollatzResearch.WordTrace tailWord_8199238 prefixEnd_8199238 155931484985529506567311 := by
  unfold tailWord_8199238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9345336808424016225327199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199367185246379012806980245 9345336808424016225327199)
  ·
    refine ⟨14018005212636024337990799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9345336808424016225327199 14018005212636024337990799)
    ·
      refine ⟨21027007818954036506986199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14018005212636024337990799 21027007818954036506986199)
      ·
        refine ⟨31540511728431054760479299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21027007818954036506986199 31540511728431054760479299)
        ·
          refine ⟨47310767592646582140718949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31540511728431054760479299 47310767592646582140718949)
          ·
            refine ⟨8870768923621234151384803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47310767592646582140718949 8870768923621234151384803)
            ·
              refine ⟨13306153385431851227077205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8870768923621234151384803 13306153385431851227077205)
              ·
                refine ⟨155931484985529506567311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13306153385431851227077205 155931484985529506567311)
                ·
                  rfl

theorem cell23_8199238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_8199238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199238 prefixEnd_8199238 := by exact prefixLift 8199238
  have htrace : WordTrace (prefixWord ++ tailWord_8199238) baseStart_8199238 baseEnd_8199238 := by
    simpa [prefixWord, tailWord_8199238, baseEnd_8199238] using wordTrace_append hprefix tailTrace_8199238
  have hstable : (prefixWord ++ tailWord_8199238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199238).length < 2 ^ (prefixWord ++ tailWord_8199238).sum := by decide
  have hdescent : baseEnd_8199238 < baseStart_8199238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199345 : List Nat := [1, 2, 2, 5, 1, 2, 3, 2, 5]
def baseStart_8199345 : Nat := 118140960795 + 8199345 * 2 ^ 59
def prefixEnd_8199345 : Nat := 4983230072969 + 3 ^ 40 * 8199345 * 2
def baseEnd_8199345 : Nat := 467800559671036417631045

theorem tailTrace_8199345 : CollatzResearch.WordTrace tailWord_8199345 prefixEnd_8199345 467800559671036417631045 := by
  unfold tailWord_8199345
  simp only [CollatzResearch.WordTrace]
  refine ⟨299054680480180876484615489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199369786986787250989743659 299054680480180876484615489)
  ·
    refine ⟨224291010360135657363461617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299054680480180876484615489 224291010360135657363461617)
    ·
      refine ⟨168218257770101743022596213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224291010360135657363461617 168218257770101743022596213)
      ·
        refine ⟨15770461665947038408368395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168218257770101743022596213 15770461665947038408368395)
        ·
          refine ⟨23655692498920557612552593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15770461665947038408368395 23655692498920557612552593)
          ·
            refine ⟨17741769374190418209414445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23655692498920557612552593 17741769374190418209414445)
            ·
              refine ⟨6653163515321406828530417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17741769374190418209414445 6653163515321406828530417)
              ·
                refine ⟨4989872636491055121397813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653163515321406828530417 4989872636491055121397813)
                ·
                  refine ⟨467800559671036417631045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4989872636491055121397813 467800559671036417631045)
                  ·
                    rfl

theorem cell23_8199345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 2, 5].length) (baseStart_8199345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199345 prefixEnd_8199345 := by exact prefixLift 8199345
  have htrace : WordTrace (prefixWord ++ tailWord_8199345) baseStart_8199345 baseEnd_8199345 := by
    simpa [prefixWord, tailWord_8199345, baseEnd_8199345] using wordTrace_append hprefix tailTrace_8199345
  have hstable : (prefixWord ++ tailWord_8199345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199345).length < 2 ^ (prefixWord ++ tailWord_8199345).sum := by decide
  have hdescent : baseEnd_8199345 < baseStart_8199345 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199378 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 2, 1, 4]
def baseStart_8199378 : Nat := 118140960795 + 8199378 * 2 ^ 59
def prefixEnd_8199378 : Nat := 4983230072969 + 3 ^ 40 * 8199378 * 2
def baseEnd_8199378 : Nat := 4210221981900926129566753

theorem tailTrace_8199378 : CollatzResearch.WordTrace tailWord_8199378 prefixEnd_8199378 4210221981900926129566753 := by
  unfold tailWord_8199378
  simp only [CollatzResearch.WordTrace]
  refine ⟨74763971022265330780141697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199370589392707548747044525 74763971022265330780141697)
  ·
    refine ⟨56072978266698998085106273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74763971022265330780141697 56072978266698998085106273)
    ·
      refine ⟨42054733700024248563829705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56072978266698998085106273 42054733700024248563829705)
      ·
        refine ⟨31541050275018186422872279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42054733700024248563829705 31541050275018186422872279)
        ·
          refine ⟨47311575412527279634308419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31541050275018186422872279 47311575412527279634308419)
          ·
            refine ⟨70967363118790919451462629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47311575412527279634308419 70967363118790919451462629)
            ·
              refine ⟨13306380584773297397149243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70967363118790919451462629 13306380584773297397149243)
              ·
                refine ⟨19959570877159946095723865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13306380584773297397149243 19959570877159946095723865)
                ·
                  refine ⟨14969678157869959571792899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19959570877159946095723865 14969678157869959571792899)
                  ·
                    refine ⟨22454517236804939357689349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14969678157869959571792899 22454517236804939357689349)
                    ·
                      refine ⟨4210221981900926129566753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22454517236804939357689349 4210221981900926129566753)
                      ·
                        rfl

theorem cell23_8199378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_8199378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199378 prefixEnd_8199378 := by exact prefixLift 8199378
  have htrace : WordTrace (prefixWord ++ tailWord_8199378) baseStart_8199378 baseEnd_8199378 := by
    simpa [prefixWord, tailWord_8199378, baseEnd_8199378] using wordTrace_append hprefix tailTrace_8199378
  have hstable : (prefixWord ++ tailWord_8199378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199378).length < 2 ^ (prefixWord ++ tailWord_8199378).sum := by decide
  have hdescent : baseEnd_8199378 < baseStart_8199378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199424 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_8199424 : Nat := 118140960795 + 8199424 * 2 ^ 59
def prefixEnd_8199424 : Nat := 4983230072969 + 3 ^ 40 * 8199424 * 2
def baseEnd_8199424 : Nat := 4210245602011032949591541

theorem tailTrace_8199424 : CollatzResearch.WordTrace tailWord_8199424 prefixEnd_8199424 4210245602011032949591541 := by
  unfold tailWord_8199424
  simp only [CollatzResearch.WordTrace]
  refine ⟨149528780923447336488370663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199371707897929781984494217 149528780923447336488370663)
  ·
    refine ⟨224293171385171004732555995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149528780923447336488370663 224293171385171004732555995)
    ·
      refine ⟨336439757077756507098833993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224293171385171004732555995 336439757077756507098833993)
      ·
        refine ⟨252329817808317380324125495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336439757077756507098833993 252329817808317380324125495)
        ·
          refine ⟨378494726712476070486188243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252329817808317380324125495 378494726712476070486188243)
          ·
            refine ⟨567742090068714105729282365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378494726712476070486188243 567742090068714105729282365)
            ·
              refine ⟨212903283775767789648480887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 567742090068714105729282365 212903283775767789648480887)
              ·
                refine ⟨319354925663651684472721331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212903283775767789648480887 319354925663651684472721331)
                ·
                  refine ⟨479032388495477526709081997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319354925663651684472721331 479032388495477526709081997)
                  ·
                    refine ⟨179637145685804072515905749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 479032388495477526709081997 179637145685804072515905749)
                    ·
                      refine ⟨4210245602011032949591541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179637145685804072515905749 4210245602011032949591541)
                      ·
                        rfl

theorem cell23_8199424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_8199424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199424 prefixEnd_8199424 := by exact prefixLift 8199424
  have htrace : WordTrace (prefixWord ++ tailWord_8199424) baseStart_8199424 baseEnd_8199424 := by
    simpa [prefixWord, tailWord_8199424, baseEnd_8199424] using wordTrace_append hprefix tailTrace_8199424
  have hstable : (prefixWord ++ tailWord_8199424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199424).length < 2 ^ (prefixWord ++ tailWord_8199424).sum := by decide
  have hdescent : baseEnd_8199424 < baseStart_8199424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199432 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 2, 2, 3]
def baseStart_8199432 : Nat := 118140960795 + 8199432 * 2 ^ 59
def prefixEnd_8199432 : Nat := 4983230072969 + 3 ^ 40 * 8199432 * 2
def baseEnd_8199432 : Nat := 4210249709856268918291505

theorem tailTrace_8199432 : CollatzResearch.WordTrace tailWord_8199432 prefixEnd_8199432 4210249709856268918291505 := by
  unfold tailWord_8199432
  simp only [CollatzResearch.WordTrace]
  refine ⟨149528926815432845171516275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199371902420577126895355033 149528926815432845171516275)
  ·
    refine ⟨224293390223149267757274413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149528926815432845171516275 224293390223149267757274413)
    ·
      refine ⟨84110021333680975408977905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224293390223149267757274413 84110021333680975408977905)
      ·
        refine ⟨63082516000260731556733429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84110021333680975408977905 63082516000260731556733429)
        ·
          refine ⟨5913985875024443583443759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63082516000260731556733429 5913985875024443583443759)
          ·
            refine ⟨8870978812536665375165639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5913985875024443583443759 8870978812536665375165639)
            ·
              refine ⟨13306468218804998062748459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8870978812536665375165639 13306468218804998062748459)
              ·
                refine ⟨19959702328207497094122689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13306468218804998062748459 19959702328207497094122689)
                ·
                  refine ⟨14969776746155622820592017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19959702328207497094122689 14969776746155622820592017)
                  ·
                    refine ⟨11227332559616717115444013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14969776746155622820592017 11227332559616717115444013)
                    ·
                      refine ⟨4210249709856268918291505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11227332559616717115444013 4210249709856268918291505)
                      ·
                        rfl

theorem cell23_8199432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_8199432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199432 prefixEnd_8199432 := by exact prefixLift 8199432
  have htrace : WordTrace (prefixWord ++ tailWord_8199432) baseStart_8199432 baseEnd_8199432 := by
    simpa [prefixWord, tailWord_8199432, baseEnd_8199432] using wordTrace_append hprefix tailTrace_8199432
  have hstable : (prefixWord ++ tailWord_8199432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199432).length < 2 ^ (prefixWord ++ tailWord_8199432).sum := by decide
  have hdescent : baseEnd_8199432 < baseStart_8199432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199448 : List Nat := [2, 1, 2, 3, 1, 4, 1, 3, 1, 5]
def baseStart_8199448 : Nat := 118140960795 + 8199448 * 2 ^ 59
def prefixEnd_8199448 : Nat := 4983230072969 + 3 ^ 40 * 8199448 * 2
def baseEnd_8199448 : Nat := 1403419308515580285230477

theorem tailTrace_8199448 : CollatzResearch.WordTrace tailWord_8199448 prefixEnd_8199448 1403419308515580285230477 := by
  unfold tailWord_8199448
  simp only [CollatzResearch.WordTrace]
  refine ⟨149529218599403862537807499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199372291465871816717076665 149529218599403862537807499)
  ·
    refine ⟨224293827899105793806711249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149529218599403862537807499 224293827899105793806711249)
    ·
      refine ⟨168220370924329345355033437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224293827899105793806711249 168220370924329345355033437)
      ·
        refine ⟨63082639096623504508137539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168220370924329345355033437 63082639096623504508137539)
        ·
          refine ⟨94623958644935256762206309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63082639096623504508137539 94623958644935256762206309)
          ·
            refine ⟨17741992245925360642913683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94623958644935256762206309 17741992245925360642913683)
            ·
              refine ⟨26612988368888040964370525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17741992245925360642913683 26612988368888040964370525)
              ·
                refine ⟨9979870638333015361638947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26612988368888040964370525 9979870638333015361638947)
                ·
                  refine ⟨14969805957499523042458421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9979870638333015361638947 14969805957499523042458421)
                  ·
                    refine ⟨1403419308515580285230477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14969805957499523042458421 1403419308515580285230477)
                    ·
                      rfl

theorem cell23_8199448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 5].length) (baseStart_8199448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199448 prefixEnd_8199448 := by exact prefixLift 8199448
  have htrace : WordTrace (prefixWord ++ tailWord_8199448) baseStart_8199448 baseEnd_8199448 := by
    simpa [prefixWord, tailWord_8199448, baseEnd_8199448] using wordTrace_append hprefix tailTrace_8199448
  have hstable : (prefixWord ++ tailWord_8199448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199448).length < 2 ^ (prefixWord ++ tailWord_8199448).sum := by decide
  have hdescent : baseEnd_8199448 < baseStart_8199448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199535 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 2, 1, 3]
def baseStart_8199535 : Nat := 118140960795 + 8199535 * 2 ^ 59
def prefixEnd_8199535 : Nat := 4983230072969 + 3 ^ 40 * 8199535 * 2
def baseEnd_8199535 : Nat := 4210302598363682015303531

theorem tailTrace_8199535 : CollatzResearch.WordTrace tailWord_8199535 prefixEnd_8199535 4210302598363682015303531 := by
  unfold tailWord_8199535
  simp only [CollatzResearch.WordTrace]
  refine ⟨299061610349492538934032059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199374406899661692622688039 299061610349492538934032059)
  ·
    refine ⟨448592415524238808401048089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299061610349492538934032059 448592415524238808401048089)
    ·
      refine ⟨336444311643179106300786067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448592415524238808401048089 336444311643179106300786067)
      ·
        refine ⟨504666467464768659451179101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336444311643179106300786067 504666467464768659451179101)
        ·
          refine ⟨189249925299288247294192163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504666467464768659451179101 189249925299288247294192163)
          ·
            refine ⟨283874887948932370941288245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189249925299288247294192163 283874887948932370941288245)
            ·
              refine ⟨26613270745212409775745773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283874887948932370941288245 26613270745212409775745773)
              ·
                refine ⟨9979976529454653665904665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26613270745212409775745773 9979976529454653665904665)
                ·
                  refine ⟨7484982397090990249428499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9979976529454653665904665 7484982397090990249428499)
                  ·
                    refine ⟨11227473595636485374142749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7484982397090990249428499 11227473595636485374142749)
                    ·
                      refine ⟨4210302598363682015303531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11227473595636485374142749 4210302598363682015303531)
                      ·
                        rfl

theorem cell23_8199535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 2, 1, 3].length) (baseStart_8199535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199535 prefixEnd_8199535 := by exact prefixLift 8199535
  have htrace : WordTrace (prefixWord ++ tailWord_8199535) baseStart_8199535 baseEnd_8199535 := by
    simpa [prefixWord, tailWord_8199535, baseEnd_8199535] using wordTrace_append hprefix tailTrace_8199535
  have hstable : (prefixWord ++ tailWord_8199535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199535).length < 2 ^ (prefixWord ++ tailWord_8199535).sum := by decide
  have hdescent : baseEnd_8199535 < baseStart_8199535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199570 : List Nat := [3, 2, 3, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_8199570 : Nat := 118140960795 + 8199570 * 2 ^ 59
def prefixEnd_8199570 : Nat := 4983230072969 + 3 ^ 40 * 8199570 * 2
def baseEnd_8199570 : Nat := 4210320570186589378365871

theorem tailTrace_8199570 : CollatzResearch.WordTrace tailWord_8199570 prefixEnd_8199570 4210320570186589378365871 := by
  unfold tailWord_8199570
  simp only [CollatzResearch.WordTrace]
  refine ⟨74765721726091434977889041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199375257936243826607704109 74765721726091434977889041)
  ·
    refine ⟨56074291294568576233416781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74765721726091434977889041 56074291294568576233416781)
    ·
      refine ⟨21027859235463216087531293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56074291294568576233416781 21027859235463216087531293)
      ·
        refine ⟨7885447213298706032824235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21027859235463216087531293 7885447213298706032824235)
        ·
          refine ⟨11828170819948059049236353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7885447213298706032824235 11828170819948059049236353)
          ·
            refine ⟨8871128114961044286927265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11828170819948059049236353 8871128114961044286927265)
            ·
              refine ⟨6653346086220783215195449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8871128114961044286927265 6653346086220783215195449)
              ·
                refine ⟨4990009564665587411396587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653346086220783215195449 4990009564665587411396587)
                ·
                  refine ⟨7485014346998381117094881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4990009564665587411396587 7485014346998381117094881)
                  ·
                    refine ⟨5613760760248785837821161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7485014346998381117094881 5613760760248785837821161)
                    ·
                      refine ⟨4210320570186589378365871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5613760760248785837821161 4210320570186589378365871)
                      ·
                        rfl

theorem cell23_8199570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_8199570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199570 prefixEnd_8199570 := by exact prefixLift 8199570
  have htrace : WordTrace (prefixWord ++ tailWord_8199570) baseStart_8199570 baseEnd_8199570 := by
    simpa [prefixWord, tailWord_8199570, baseEnd_8199570] using wordTrace_append hprefix tailTrace_8199570
  have hstable : (prefixWord ++ tailWord_8199570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199570).length < 2 ^ (prefixWord ++ tailWord_8199570).sum := by decide
  have hdescent : baseEnd_8199570 < baseStart_8199570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199571 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 4]
def baseStart_8199571 : Nat := 118140960795 + 8199571 * 2 ^ 59
def prefixEnd_8199571 : Nat := 4983230072969 + 3 ^ 40 * 8199571 * 2
def baseEnd_8199571 : Nat := 4210321083667243874453365

theorem tailTrace_8199571 : CollatzResearch.WordTrace tailWord_8199571 prefixEnd_8199571 4210321083667243874453365 := by
  unfold tailWord_8199571
  simp only [CollatzResearch.WordTrace]
  refine ⟨299062923377362117082342567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199375282251574744721561711 299062923377362117082342567)
  ·
    refine ⟨448594385066043175623513851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299062923377362117082342567 448594385066043175623513851)
    ·
      refine ⟨672891577599064763435270777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448594385066043175623513851 672891577599064763435270777)
      ·
        refine ⟨504668683199298572576453083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672891577599064763435270777 504668683199298572576453083)
        ·
          refine ⟨757003024798947858864679625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504668683199298572576453083 757003024798947858864679625)
          ·
            refine ⟨567752268599210894148509719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757003024798947858864679625 567752268599210894148509719)
            ·
              refine ⟨851628402898816341222764579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567752268599210894148509719 851628402898816341222764579)
              ·
                refine ⟨1277442604348224511834146869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851628402898816341222764579 1277442604348224511834146869)
                ·
                  refine ⟨119760244157646047984451269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1277442604348224511834146869 119760244157646047984451269)
                  ·
                    refine ⟨22455045779558633997084613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119760244157646047984451269 22455045779558633997084613)
                    ·
                      refine ⟨4210321083667243874453365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22455045779558633997084613 4210321083667243874453365)
                      ·
                        rfl

theorem cell23_8199571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_8199571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199571 prefixEnd_8199571 := by exact prefixLift 8199571
  have htrace : WordTrace (prefixWord ++ tailWord_8199571) baseStart_8199571 baseEnd_8199571 := by
    simpa [prefixWord, tailWord_8199571, baseEnd_8199571] using wordTrace_append hprefix tailTrace_8199571
  have hstable : (prefixWord ++ tailWord_8199571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199571).length < 2 ^ (prefixWord ++ tailWord_8199571).sum := by decide
  have hdescent : baseEnd_8199571 < baseStart_8199571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199578 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3]
def baseStart_8199578 : Nat := 118140960795 + 8199578 * 2 ^ 59
def prefixEnd_8199578 : Nat := 4983230072969 + 3 ^ 40 * 8199578 * 2
def baseEnd_8199578 : Nat := 4210324678031825347065833

theorem tailTrace_8199578 : CollatzResearch.WordTrace tailWord_8199578 prefixEnd_8199578 4210324678031825347065833 := by
  unfold tailWord_8199578
  simp only [CollatzResearch.WordTrace]
  refine ⟨74765794672084189319461847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199375452458891171518564925 74765794672084189319461847)
  ·
    refine ⟨112148692008126283979192771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74765794672084189319461847 112148692008126283979192771)
    ·
      refine ⟨168223038012189425968789157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112148692008126283979192771 168223038012189425968789157)
      ·
        refine ⟨31541819627285517369147967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168223038012189425968789157 31541819627285517369147967)
        ·
          refine ⟨47312729440928276053721951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31541819627285517369147967 47312729440928276053721951)
          ·
            refine ⟨70969094161392414080582927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47312729440928276053721951 70969094161392414080582927)
            ·
              refine ⟨106453641242088621120874391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70969094161392414080582927 106453641242088621120874391)
              ·
                refine ⟨159680461863132931681311587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106453641242088621120874391 159680461863132931681311587)
                ·
                  refine ⟨239520692794699397521967381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159680461863132931681311587 239520692794699397521967381)
                  ·
                    refine ⟨11227532474751534258842221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 239520692794699397521967381 11227532474751534258842221)
                    ·
                      refine ⟨4210324678031825347065833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11227532474751534258842221 4210324678031825347065833)
                      ·
                        rfl

theorem cell23_8199578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_8199578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199578 prefixEnd_8199578 := by exact prefixLift 8199578
  have htrace : WordTrace (prefixWord ++ tailWord_8199578) baseStart_8199578 baseEnd_8199578 := by
    simpa [prefixWord, tailWord_8199578, baseEnd_8199578] using wordTrace_append hprefix tailTrace_8199578
  have hstable : (prefixWord ++ tailWord_8199578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199578).length < 2 ^ (prefixWord ++ tailWord_8199578).sum := by decide
  have hdescent : baseEnd_8199578 < baseStart_8199578 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199648 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 4]
def baseStart_8199648 : Nat := 118140960795 + 8199648 * 2 ^ 59
def prefixEnd_8199648 : Nat := 4983230072969 + 3 ^ 40 * 8199648 * 2
def baseEnd_8199648 : Nat := 4210360621677640073190511

theorem tailTrace_8199648 : CollatzResearch.WordTrace tailWord_8199648 prefixEnd_8199648 4210360621677640073190511 := by
  unfold tailWord_8199648
  simp only [CollatzResearch.WordTrace]
  refine ⟨149532865899041579616447799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199377154532055439488597065 149532865899041579616447799)
  ·
    refine ⟨224299298848562369424671699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149532865899041579616447799 224299298848562369424671699)
    ·
      refine ⟨336448948272843554137007549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224299298848562369424671699 336448948272843554137007549)
      ·
        refine ⟨126168355602316332801377831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336448948272843554137007549 126168355602316332801377831)
        ·
          refine ⟨189252533403474499202066747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126168355602316332801377831 189252533403474499202066747)
          ·
            refine ⟨283878800105211748803100121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189252533403474499202066747 283878800105211748803100121)
            ·
              refine ⟨212909100078908811602325091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283878800105211748803100121 212909100078908811602325091)
              ·
                refine ⟨319363650118363217403487637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212909100078908811602325091 319363650118363217403487637)
                ·
                  refine ⟨14970171099298275815788483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 319363650118363217403487637 14970171099298275815788483)
                  ·
                    refine ⟨22455256648947413723682725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14970171099298275815788483 22455256648947413723682725)
                    ·
                      refine ⟨4210360621677640073190511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22455256648947413723682725 4210360621677640073190511)
                      ·
                        rfl

theorem cell23_8199648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_8199648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199648 prefixEnd_8199648 := by exact prefixLift 8199648
  have htrace : WordTrace (prefixWord ++ tailWord_8199648) baseStart_8199648 baseEnd_8199648 := by
    simpa [prefixWord, tailWord_8199648, baseEnd_8199648] using wordTrace_append hprefix tailTrace_8199648
  have hstable : (prefixWord ++ tailWord_8199648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199648).length < 2 ^ (prefixWord ++ tailWord_8199648).sum := by decide
  have hdescent : baseEnd_8199648 < baseStart_8199648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199682 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_8199682 : Nat := 118140960795 + 8199682 * 2 ^ 59
def prefixEnd_8199682 : Nat := 4983230072969 + 3 ^ 40 * 8199682 * 2
def baseEnd_8199682 : Nat := 4210378080019892940165355

theorem tailTrace_8199682 : CollatzResearch.WordTrace tailWord_8199682 prefixEnd_8199682 4210378080019892940165355 := by
  unfold tailWord_8199682
  simp only [CollatzResearch.WordTrace]
  refine ⟨74766742969989995759908325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199377981253306655359755533 74766742969989995759908325)
  ·
    refine ⟨14018764306873124204982811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74766742969989995759908325 14018764306873124204982811)
    ·
      refine ⟨21028146460309686307474217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14018764306873124204982811 21028146460309686307474217)
      ·
        refine ⟨15771109845232264730605663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21028146460309686307474217 15771109845232264730605663)
        ·
          refine ⟨23656664767848397095908495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15771109845232264730605663 23656664767848397095908495)
          ·
            refine ⟨35484997151772595643862743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23656664767848397095908495 35484997151772595643862743)
            ·
              refine ⟨53227495727658893465794115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35484997151772595643862743 53227495727658893465794115)
              ·
                refine ⟨79841243591488340198691173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53227495727658893465794115 79841243591488340198691173)
                ·
                  refine ⟨14970233173404063787254595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79841243591488340198691173 14970233173404063787254595)
                  ·
                    refine ⟨22455349760106095680881893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14970233173404063787254595 22455349760106095680881893)
                    ·
                      refine ⟨4210378080019892940165355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22455349760106095680881893 4210378080019892940165355)
                      ·
                        rfl

theorem cell23_8199682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_8199682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199682 prefixEnd_8199682 := by exact prefixLift 8199682
  have htrace : WordTrace (prefixWord ++ tailWord_8199682) baseStart_8199682 baseEnd_8199682 := by
    simpa [prefixWord, tailWord_8199682, baseEnd_8199682] using wordTrace_append hprefix tailTrace_8199682
  have hstable : (prefixWord ++ tailWord_8199682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199682).length < 2 ^ (prefixWord ++ tailWord_8199682).sum := by decide
  have hdescent : baseEnd_8199682 < baseStart_8199682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199688 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 8]
def baseStart_8199688 : Nat := 118140960795 + 8199688 * 2 ^ 59
def prefixEnd_8199688 : Nat := 4983230072969 + 3 ^ 40 * 8199688 * 2
def baseEnd_8199688 : Nat := 467820128989313324076703

theorem tailTrace_8199688 : CollatzResearch.WordTrace tailWord_8199688 prefixEnd_8199688 467820128989313324076703 := by
  unfold tailWord_8199688
  simp only [CollatzResearch.WordTrace]
  refine ⟨149533595358969123032175859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199378127145292164042901145 149533595358969123032175859)
  ·
    refine ⟨224300393038453684548263789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149533595358969123032175859 224300393038453684548263789)
    ·
      refine ⟨84112647389420131705598921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224300393038453684548263789 84112647389420131705598921)
      ·
        refine ⟨63084485542065098779199191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84112647389420131705598921 63084485542065098779199191)
        ·
          refine ⟨94626728313097648168798787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63084485542065098779199191 94626728313097648168798787)
          ·
            refine ⟨141940092469646472253198181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94626728313097648168798787 141940092469646472253198181)
            ·
              refine ⟨26613767338058713547474659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141940092469646472253198181 26613767338058713547474659)
              ·
                refine ⟨39920651007088070321211989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26613767338058713547474659 39920651007088070321211989)
                ·
                  refine ⟨467820128989313324076703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39920651007088070321211989 467820128989313324076703)
                  ·
                    rfl

theorem cell23_8199688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 8].length) (baseStart_8199688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199688 prefixEnd_8199688 := by exact prefixLift 8199688
  have htrace : WordTrace (prefixWord ++ tailWord_8199688) baseStart_8199688 baseEnd_8199688 := by
    simpa [prefixWord, tailWord_8199688, baseEnd_8199688] using wordTrace_append hprefix tailTrace_8199688
  have hstable : (prefixWord ++ tailWord_8199688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199688).length < 2 ^ (prefixWord ++ tailWord_8199688).sum := by decide
  have hdescent : baseEnd_8199688 < baseStart_8199688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199749 : List Nat := [1, 3, 1, 1, 1, 4, 3, 4, 1, 1, 3]
def baseStart_8199749 : Nat := 118140960795 + 8199749 * 2 ^ 59
def prefixEnd_8199749 : Nat := 4983230072969 + 3 ^ 40 * 8199749 * 2
def baseEnd_8199749 : Nat := 4210412483223744178027547

theorem tailTrace_8199749 : CollatzResearch.WordTrace tailWord_8199749 prefixEnd_8199749 4210412483223744178027547 := by
  unfold tailWord_8199749
  simp only [CollatzResearch.WordTrace]
  refine ⟨299069415570717253482322301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199379610380478168988214867 299069415570717253482322301)
  ·
    refine ⟨112151030839018970055870863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299069415570717253482322301 112151030839018970055870863)
    ·
      refine ⟨168226546258528455083806295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112151030839018970055870863 168226546258528455083806295)
      ·
        refine ⟨252339819387792682625709443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168226546258528455083806295 252339819387792682625709443)
        ·
          refine ⟨378509729081689023938564165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252339819387792682625709443 378509729081689023938564165)
          ·
            refine ⟨70970574202816691988480781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378509729081689023938564165 70970574202816691988480781)
            ·
              refine ⟨26613965326056259495680293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70970574202816691988480781 26613965326056259495680293)
              ·
                refine ⟨4990118498635548655440055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26613965326056259495680293 4990118498635548655440055)
                ·
                  refine ⟨7485177747953322983160083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4990118498635548655440055 7485177747953322983160083)
                  ·
                    refine ⟨11227766621929984474740125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7485177747953322983160083 11227766621929984474740125)
                    ·
                      refine ⟨4210412483223744178027547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11227766621929984474740125 4210412483223744178027547)
                      ·
                        rfl

theorem cell23_8199749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 1, 1, 3].length) (baseStart_8199749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199749 prefixEnd_8199749 := by exact prefixLift 8199749
  have htrace : WordTrace (prefixWord ++ tailWord_8199749) baseStart_8199749 baseEnd_8199749 := by
    simpa [prefixWord, tailWord_8199749, baseEnd_8199749] using wordTrace_append hprefix tailTrace_8199749
  have hstable : (prefixWord ++ tailWord_8199749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199749).length < 2 ^ (prefixWord ++ tailWord_8199749).sum := by decide
  have hdescent : baseEnd_8199749 < baseStart_8199749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199755 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 2, 6, 2]
def baseStart_8199755 : Nat := 118140960795 + 8199755 * 2 ^ 59
def prefixEnd_8199755 : Nat := 4983230072969 + 3 ^ 40 * 8199755 * 2
def baseEnd_8199755 : Nat := 4210415564107671154552519

theorem tailTrace_8199755 : CollatzResearch.WordTrace tailWord_8199755 prefixEnd_8199755 4210415564107671154552519 := by
  unfold tailWord_8199755
  simp only [CollatzResearch.WordTrace]
  refine ⟨299069634408695516507040719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199379756272463677671360479 299069634408695516507040719)
  ·
    refine ⟨448604451613043274760561079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299069634408695516507040719 448604451613043274760561079)
    ·
      refine ⟨672906677419564912140841619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448604451613043274760561079 672906677419564912140841619)
      ·
        refine ⟨1009360016129347368211262429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672906677419564912140841619 1009360016129347368211262429)
        ·
          refine ⟨378510006048505263079223411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1009360016129347368211262429 378510006048505263079223411)
          ·
            refine ⟨567765009072757894618835117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378510006048505263079223411 567765009072757894618835117)
            ·
              refine ⟨212911878402284210482063169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 567765009072757894618835117 212911878402284210482063169)
              ·
                refine ⟨159683908801713157861547377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212911878402284210482063169 159683908801713157861547377)
                ·
                  refine ⟨119762931601284868396160533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159683908801713157861547377 119762931601284868396160533)
                  ·
                    refine ⟨5613887418810228206070025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119762931601284868396160533 5613887418810228206070025)
                    ·
                      refine ⟨4210415564107671154552519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5613887418810228206070025 4210415564107671154552519)
                      ·
                        rfl

theorem cell23_8199755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 6, 2].length) (baseStart_8199755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199755 prefixEnd_8199755 := by exact prefixLift 8199755
  have htrace : WordTrace (prefixWord ++ tailWord_8199755) baseStart_8199755 baseEnd_8199755 := by
    simpa [prefixWord, tailWord_8199755, baseEnd_8199755] using wordTrace_append hprefix tailTrace_8199755
  have hstable : (prefixWord ++ tailWord_8199755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199755).length < 2 ^ (prefixWord ++ tailWord_8199755).sum := by decide
  have hdescent : baseEnd_8199755 < baseStart_8199755 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199765 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 6, 4]
def baseStart_8199765 : Nat := 118140960795 + 8199765 * 2 ^ 59
def prefixEnd_8199765 : Nat := 4983230072969 + 3 ^ 40 * 8199765 * 2
def baseEnd_8199765 : Nat := 1403473566304738705142491

theorem tailTrace_8199765 : CollatzResearch.WordTrace tailWord_8199765 prefixEnd_8199765 1403473566304738705142491 := by
  unfold tailWord_8199765
  simp only [CollatzResearch.WordTrace]
  refine ⟨299069999138659288214904749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199379999425772858809936499 299069999138659288214904749)
  ·
    refine ⟨112151249676997233080589281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299069999138659288214904749 112151249676997233080589281)
    ·
      refine ⟨84113437257747924810441961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112151249676997233080589281 84113437257747924810441961)
      ·
        refine ⟨63085077943310943607831471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84113437257747924810441961 63085077943310943607831471)
        ·
          refine ⟨94627616914966415411747207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63085077943310943607831471 94627616914966415411747207)
          ·
            refine ⟨141941425372449623117620811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94627616914966415411747207 141941425372449623117620811)
            ·
              refine ⟨212912138058674434676431217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141941425372449623117620811 212912138058674434676431217)
              ·
                refine ⟨159684103544005826007323413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212912138058674434676431217 159684103544005826007323413)
                ·
                  refine ⟨7485192353625273094093285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159684103544005826007323413 7485192353625273094093285)
                  ·
                    refine ⟨1403473566304738705142491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7485192353625273094093285 1403473566304738705142491)
                    ·
                      rfl

theorem cell23_8199765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_8199765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199765 prefixEnd_8199765 := by exact prefixLift 8199765
  have htrace : WordTrace (prefixWord ++ tailWord_8199765) baseStart_8199765 baseEnd_8199765 := by
    simpa [prefixWord, tailWord_8199765, baseEnd_8199765] using wordTrace_append hprefix tailTrace_8199765
  have hstable : (prefixWord ++ tailWord_8199765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199765).length < 2 ^ (prefixWord ++ tailWord_8199765).sum := by decide
  have hdescent : baseEnd_8199765 < baseStart_8199765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199772 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_8199772 : Nat := 118140960795 + 8199772 * 2 ^ 59
def prefixEnd_8199772 : Nat := 4983230072969 + 3 ^ 40 * 8199772 * 2
def baseEnd_8199772 : Nat := 4210424293278797588039941

theorem tailTrace_8199772 : CollatzResearch.WordTrace tailWord_8199772 prefixEnd_8199772 4210424293278797588039941 := by
  unfold tailWord_8199772
  simp only [CollatzResearch.WordTrace]
  refine ⟨149535127224816964205204785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199380169633089285606939713 149535127224816964205204785)
  ·
    refine ⟨112151345418612723153903589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149535127224816964205204785 112151345418612723153903589)
    ·
      refine ⟨21028377265989885591356923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112151345418612723153903589 21028377265989885591356923)
      ·
        refine ⟨31542565898984828387035385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21028377265989885591356923 31542565898984828387035385)
        ·
          refine ⟨23656924424238621290276539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31542565898984828387035385 23656924424238621290276539)
          ·
            refine ⟨35485386636357931935414809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23656924424238621290276539 35485386636357931935414809)
            ·
              refine ⟨26614039977268448951561107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35485386636357931935414809 26614039977268448951561107)
              ·
                refine ⟨39921059965902673427341661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26614039977268448951561107 39921059965902673427341661)
                ·
                  refine ⟨14970397487213502535253123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39921059965902673427341661 14970397487213502535253123)
                  ·
                    refine ⟨22455596230820253802879685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14970397487213502535253123 22455596230820253802879685)
                    ·
                      refine ⟨4210424293278797588039941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22455596230820253802879685 4210424293278797588039941)
                      ·
                        rfl

theorem cell23_8199772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_8199772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199772 prefixEnd_8199772 := by exact prefixLift 8199772
  have htrace : WordTrace (prefixWord ++ tailWord_8199772) baseStart_8199772 baseEnd_8199772 := by
    simpa [prefixWord, tailWord_8199772, baseEnd_8199772] using wordTrace_append hprefix tailTrace_8199772
  have hstable : (prefixWord ++ tailWord_8199772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199772).length < 2 ^ (prefixWord ++ tailWord_8199772).sum := by decide
  have hdescent : baseEnd_8199772 < baseStart_8199772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199785 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 4]
def baseStart_8199785 : Nat := 118140960795 + 8199785 * 2 ^ 59
def prefixEnd_8199785 : Nat := 4983230072969 + 3 ^ 40 * 8199785 * 2
def baseEnd_8199785 : Nat := 4210430968527306037177381

theorem tailTrace_8199785 : CollatzResearch.WordTrace tailWord_8199785 prefixEnd_8199785 4210430968527306037177381 := by
  unfold tailWord_8199785
  simp only [CollatzResearch.WordTrace]
  refine ⟨299070728598586831630632809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199380485732391221087088539 299070728598586831630632809)
  ·
    refine ⟨224303046448940123722974607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299070728598586831630632809 224303046448940123722974607)
    ·
      refine ⟨336454569673410185584461911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224303046448940123722974607 336454569673410185584461911)
      ·
        refine ⟨504681854510115278376692867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336454569673410185584461911 504681854510115278376692867)
        ·
          refine ⟨757022781765172917565039301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504681854510115278376692867 757022781765172917565039301)
          ·
            refine ⟨141941771580969922043444869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 757022781765172917565039301 141941771580969922043444869)
            ·
              refine ⟨26614082171431860383145913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141941771580969922043444869 26614082171431860383145913)
              ·
                refine ⟨19960561628573895287359435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26614082171431860383145913 19960561628573895287359435)
                ·
                  refine ⟨29940842442860842931039153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19960561628573895287359435 29940842442860842931039153)
                  ·
                    refine ⟨22455631832145632198279365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29940842442860842931039153 22455631832145632198279365)
                    ·
                      refine ⟨4210430968527306037177381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22455631832145632198279365 4210430968527306037177381)
                      ·
                        rfl

theorem cell23_8199785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_8199785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199785 prefixEnd_8199785 := by exact prefixLift 8199785
  have htrace : WordTrace (prefixWord ++ tailWord_8199785) baseStart_8199785 baseEnd_8199785 := by
    simpa [prefixWord, tailWord_8199785, baseEnd_8199785] using wordTrace_append hprefix tailTrace_8199785
  have hstable : (prefixWord ++ tailWord_8199785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199785).length < 2 ^ (prefixWord ++ tailWord_8199785).sum := by decide
  have hdescent : baseEnd_8199785 < baseStart_8199785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199789 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_8199789 : Nat := 118140960795 + 8199789 * 2 ^ 59
def prefixEnd_8199789 : Nat := 4983230072969 + 3 ^ 40 * 8199789 * 2
def baseEnd_8199789 : Nat := 4210433022449924021527363

theorem tailTrace_8199789 : CollatzResearch.WordTrace tailWord_8199789 prefixEnd_8199789 4210433022449924021527363 := by
  unfold tailWord_8199789
  simp only [CollatzResearch.WordTrace]
  refine ⟨299070874490572340313778421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199380582993714893542518947 299070874490572340313778421)
  ·
    refine ⟨28037894483491156904416727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299070874490572340313778421 28037894483491156904416727)
    ·
      refine ⟨42056841725236735356625091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28037894483491156904416727 42056841725236735356625091)
      ·
        refine ⟨63085262587855103034937637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42056841725236735356625091 63085262587855103034937637)
        ·
          refine ⟨11828486735222831819050807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63085262587855103034937637 11828486735222831819050807)
          ·
            refine ⟨17742730102834247728576211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11828486735222831819050807 17742730102834247728576211)
            ·
              refine ⟨26614095154251371592864317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17742730102834247728576211 26614095154251371592864317)
              ·
                refine ⟨9980285682844264347324119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26614095154251371592864317 9980285682844264347324119)
                ·
                  refine ⟨14970428524266396520986179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9980285682844264347324119 14970428524266396520986179)
                  ·
                    refine ⟨22455642786399594781479269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14970428524266396520986179 22455642786399594781479269)
                    ·
                      refine ⟨4210433022449924021527363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22455642786399594781479269 4210433022449924021527363)
                      ·
                        rfl

theorem cell23_8199789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_8199789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199789 prefixEnd_8199789 := by exact prefixLift 8199789
  have htrace : WordTrace (prefixWord ++ tailWord_8199789) baseStart_8199789 baseEnd_8199789 := by
    simpa [prefixWord, tailWord_8199789, baseEnd_8199789] using wordTrace_append hprefix tailTrace_8199789
  have hstable : (prefixWord ++ tailWord_8199789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199789).length < 2 ^ (prefixWord ++ tailWord_8199789).sum := by decide
  have hdescent : baseEnd_8199789 < baseStart_8199789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199816 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 1, 6]
def baseStart_8199816 : Nat := 118140960795 + 8199816 * 2 ^ 59
def prefixEnd_8199816 : Nat := 4983230072969 + 3 ^ 40 * 8199816 * 2
def baseEnd_8199816 : Nat := 1403482295475865138629913

theorem tailTrace_8199816 : CollatzResearch.WordTrace tailWord_8199816 prefixEnd_8199816 1403482295475865138629913 := by
  unfold tailWord_8199816
  simp only [CollatzResearch.WordTrace]
  refine ⟨149535929630737261962505651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199381239507649682616674201 149535929630737261962505651)
  ·
    refine ⟨224303894446105892943758477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149535929630737261962505651 224303894446105892943758477)
    ·
      refine ⟨84113960417289709853909429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224303894446105892943758477 84113960417289709853909429)
      ·
        refine ⟨7885683789120910298804009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84113960417289709853909429 7885683789120910298804009)
        ·
          refine ⟨5914262841840682724103007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7885683789120910298804009 5914262841840682724103007)
          ·
            refine ⟨8871394262761024086154511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914262841840682724103007 8871394262761024086154511)
            ·
              refine ⟨13307091394141536129231767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8871394262761024086154511 13307091394141536129231767)
              ·
                refine ⟨19960637091212304193847651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13307091394141536129231767 19960637091212304193847651)
                ·
                  refine ⟨29940955636818456290771477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19960637091212304193847651 29940955636818456290771477)
                  ·
                    refine ⟨1403482295475865138629913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29940955636818456290771477 1403482295475865138629913)
                    ·
                      rfl

theorem cell23_8199816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_8199816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199816 prefixEnd_8199816 := by exact prefixLift 8199816
  have htrace : WordTrace (prefixWord ++ tailWord_8199816) baseStart_8199816 baseEnd_8199816 := by
    simpa [prefixWord, tailWord_8199816, baseEnd_8199816] using wordTrace_append hprefix tailTrace_8199816
  have hstable : (prefixWord ++ tailWord_8199816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199816).length < 2 ^ (prefixWord ++ tailWord_8199816).sum := by decide
  have hdescent : baseEnd_8199816 < baseStart_8199816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199826 : List Nat := [3, 2, 3, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_8199826 : Nat := 118140960795 + 8199826 * 2 ^ 59
def prefixEnd_8199826 : Nat := 4983230072969 + 3 ^ 40 * 8199826 * 2
def baseEnd_8199826 : Nat := 4210452021234140376764693

theorem tailTrace_8199826 : CollatzResearch.WordTrace tailWord_8199826 prefixEnd_8199826 4210452021234140376764693 := by
  unfold tailWord_8199826
  simp only [CollatzResearch.WordTrace]
  refine ⟨74768055997859573908218833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199381482660958863755250221 74768055997859573908218833)
  ·
    refine ⟨56076041998394680431164125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74768055997859573908218833 56076041998394680431164125)
    ·
      refine ⟨21028515749398005161686547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56076041998394680431164125 21028515749398005161686547)
      ·
        refine ⟨31542773624097007742529821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21028515749398005161686547 31542773624097007742529821)
        ·
          refine ⟨11828540109036377903448683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31542773624097007742529821 11828540109036377903448683)
          ·
            refine ⟨17742810163554566855173025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11828540109036377903448683 17742810163554566855173025)
            ·
              refine ⟨13307107622665925141379769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17742810163554566855173025 13307107622665925141379769)
              ·
                refine ⟨9980330716999443856034827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13307107622665925141379769 9980330716999443856034827)
                ·
                  refine ⟨14970496075499165784052241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9980330716999443856034827 14970496075499165784052241)
                  ·
                    refine ⟨11227872056624374338039181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14970496075499165784052241 11227872056624374338039181)
                    ·
                      refine ⟨4210452021234140376764693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11227872056624374338039181 4210452021234140376764693)
                      ·
                        rfl

theorem cell23_8199826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_8199826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199826 prefixEnd_8199826 := by exact prefixLift 8199826
  have htrace : WordTrace (prefixWord ++ tailWord_8199826) baseStart_8199826 baseEnd_8199826 := by
    simpa [prefixWord, tailWord_8199826, baseEnd_8199826] using wordTrace_append hprefix tailTrace_8199826
  have hstable : (prefixWord ++ tailWord_8199826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199826).length < 2 ^ (prefixWord ++ tailWord_8199826).sum := by decide
  have hdescent : baseEnd_8199826 < baseStart_8199826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199900 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_8199900 : Nat := 118140960795 + 8199900 * 2 ^ 59
def prefixEnd_8199900 : Nat := 4983230072969 + 3 ^ 40 * 8199900 * 2
def baseEnd_8199900 : Nat := 4210490018802573087239353

theorem tailTrace_8199900 : CollatzResearch.WordTrace tailWord_8199900 prefixEnd_8199900 4210490018802573087239353 := by
  unfold tailWord_8199900
  simp only [CollatzResearch.WordTrace]
  refine ⟨149537461496585103135534577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199383281995446804180712769 149537461496585103135534577)
  ·
    refine ⟨112153096122438827351650933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149537461496585103135534577 112153096122438827351650933)
    ·
      refine ⟨10514352761478640064217275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112153096122438827351650933 10514352761478640064217275)
      ·
        refine ⟨15771529142217960096325913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10514352761478640064217275 15771529142217960096325913)
        ·
          refine ⟨11828646856663470072244435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15771529142217960096325913 11828646856663470072244435)
          ·
            refine ⟨17742970284995205108366653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11828646856663470072244435 17742970284995205108366653)
            ·
              refine ⟨6653613856873201915637495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17742970284995205108366653 6653613856873201915637495)
              ·
                refine ⟨9980420785309802873456243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6653613856873201915637495 9980420785309802873456243)
                ·
                  refine ⟨14970631177964704310184365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9980420785309802873456243 14970631177964704310184365)
                  ·
                    refine ⟨5613986691736764116319137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14970631177964704310184365 5613986691736764116319137)
                    ·
                      refine ⟨4210490018802573087239353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5613986691736764116319137 4210490018802573087239353)
                      ·
                        rfl

theorem cell23_8199900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_8199900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199900 prefixEnd_8199900 := by exact prefixLift 8199900
  have htrace : WordTrace (prefixWord ++ tailWord_8199900) baseStart_8199900 baseEnd_8199900 := by
    simpa [prefixWord, tailWord_8199900, baseEnd_8199900] using wordTrace_append hprefix tailTrace_8199900
  have hstable : (prefixWord ++ tailWord_8199900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199900).length < 2 ^ (prefixWord ++ tailWord_8199900).sum := by decide
  have hdescent : baseEnd_8199900 < baseStart_8199900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199955 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 5]
def baseStart_8199955 : Nat := 118140960795 + 8199955 * 2 ^ 59
def prefixEnd_8199955 : Nat := 4983230072969 + 3 ^ 40 * 8199955 * 2
def baseEnd_8199955 : Nat := 4210518260238570372051599

theorem tailTrace_8199955 : CollatzResearch.WordTrace tailWord_8199955 prefixEnd_8199955 4210518260238570372051599 := by
  unfold tailWord_8199955
  simp only [CollatzResearch.WordTrace]
  refine ⟨299076929007970950664321319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199384619338647300442880879 299076929007970950664321319)
  ·
    refine ⟨448615393511956425996481979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299076929007970950664321319 448615393511956425996481979)
    ·
      refine ⟨672923090267934638994722969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448615393511956425996481979 672923090267934638994722969)
      ·
        refine ⟨504692317700950979246042227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 672923090267934638994722969 504692317700950979246042227)
        ·
          refine ⟨757038476551426468869063341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504692317700950979246042227 757038476551426468869063341)
          ·
            refine ⟨283889428706784925825898753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 757038476551426468869063341 283889428706784925825898753)
            ·
              refine ⟨212917071530088694369424065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283889428706784925825898753 212917071530088694369424065)
              ·
                refine ⟨159687803647566520777068049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212917071530088694369424065 159687803647566520777068049)
                ·
                  refine ⟨119765852735674890582801037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159687803647566520777068049 119765852735674890582801037)
                  ·
                    refine ⟨44912194775878083968550389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119765852735674890582801037 44912194775878083968550389)
                    ·
                      refine ⟨4210518260238570372051599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44912194775878083968550389 4210518260238570372051599)
                      ·
                        rfl

theorem cell23_8199955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_8199955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199955 prefixEnd_8199955 := by exact prefixLift 8199955
  have htrace : WordTrace (prefixWord ++ tailWord_8199955) baseStart_8199955 baseEnd_8199955 := by
    simpa [prefixWord, tailWord_8199955, baseEnd_8199955] using wordTrace_append hprefix tailTrace_8199955
  have hstable : (prefixWord ++ tailWord_8199955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199955).length < 2 ^ (prefixWord ++ tailWord_8199955).sum := by decide
  have hdescent : baseEnd_8199955 < baseStart_8199955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8199969 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 2, 4, 2]
def baseStart_8199969 : Nat := 118140960795 + 8199969 * 2 ^ 59
def prefixEnd_8199969 : Nat := 4983230072969 + 3 ^ 40 * 8199969 * 2
def baseEnd_8199969 : Nat := 4210525448967733317276535

theorem tailTrace_8199969 : CollatzResearch.WordTrace tailWord_8199969 prefixEnd_8199969 4210525448967733317276535 := by
  unfold tailWord_8199969
  simp only [CollatzResearch.WordTrace]
  refine ⟨299077439629920231055330961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199384959753280154036887307 299077439629920231055330961)
  ·
    refine ⟨224308079722440173291498221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299077439629920231055330961 224308079722440173291498221)
    ·
      refine ⟨84115529895915064984311833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224308079722440173291498221 84115529895915064984311833)
      ·
        refine ⟨63086647421936298738233875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84115529895915064984311833 63086647421936298738233875)
        ·
          refine ⟨94629971132904448107350813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63086647421936298738233875 94629971132904448107350813)
          ·
            refine ⟨35486239174839168040256555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94629971132904448107350813 35486239174839168040256555)
            ·
              refine ⟨53229358762258752060384833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35486239174839168040256555 53229358762258752060384833)
              ·
                refine ⟨39922019071694064045288625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53229358762258752060384833 39922019071694064045288625)
                ·
                  refine ⟨29941514303770548033966469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39922019071694064045288625 29941514303770548033966469)
                  ·
                    refine ⟨5614033931956977756368713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29941514303770548033966469 5614033931956977756368713)
                    ·
                      refine ⟨4210525448967733317276535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5614033931956977756368713 4210525448967733317276535)
                      ·
                        rfl

theorem cell23_8199969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_8199969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8199969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8199969 prefixEnd_8199969 := by exact prefixLift 8199969
  have htrace : WordTrace (prefixWord ++ tailWord_8199969) baseStart_8199969 baseEnd_8199969 := by
    simpa [prefixWord, tailWord_8199969, baseEnd_8199969] using wordTrace_append hprefix tailTrace_8199969
  have hstable : (prefixWord ++ tailWord_8199969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8199969).length < 2 ^ (prefixWord ++ tailWord_8199969).sum := by decide
  have hdescent : baseEnd_8199969 < baseStart_8199969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8199969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200126 : List Nat := [4, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_8200126 : Nat := 118140960795 + 8200126 * 2 ^ 59
def prefixEnd_8200126 : Nat := 4983230072969 + 3 ^ 40 * 8200126 * 2
def baseEnd_8200126 : Nat := 4210606065430489203013313

theorem tailTrace_8200126 : CollatzResearch.WordTrace tailWord_8200126 prefixEnd_8200126 4210606065430489203013313 := by
  unfold tailWord_8200126
  simp only [CollatzResearch.WordTrace]
  refine ⟨37385395736293930858599529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199388777260234297912530821 37385395736293930858599529)
  ·
    refine ⟨28039046802220448143949647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37385395736293930858599529 28039046802220448143949647)
    ·
      refine ⟨42058570203330672215924471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28039046802220448143949647 42058570203330672215924471)
      ·
        refine ⟨63087855304996008323886707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42058570203330672215924471 63087855304996008323886707)
        ·
          refine ⟨94631782957494012485830061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63087855304996008323886707 94631782957494012485830061)
          ·
            refine ⟨35486918609060254682186273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94631782957494012485830061 35486918609060254682186273)
            ·
              refine ⟨26615188956795191011639705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35486918609060254682186273 26615188956795191011639705)
              ·
                refine ⟨19961391717596393258729779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26615188956795191011639705 19961391717596393258729779)
                ·
                  refine ⟨29942087576394589888094669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19961391717596393258729779 29942087576394589888094669)
                  ·
                    refine ⟨11228282841147971208035501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29942087576394589888094669 11228282841147971208035501)
                    ·
                      refine ⟨4210606065430489203013313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11228282841147971208035501 4210606065430489203013313)
                      ·
                        rfl

theorem cell23_8200126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_8200126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200126 prefixEnd_8200126 := by exact prefixLift 8200126
  have htrace : WordTrace (prefixWord ++ tailWord_8200126) baseStart_8200126 baseEnd_8200126 := by
    simpa [prefixWord, tailWord_8200126, baseEnd_8200126] using wordTrace_append hprefix tailTrace_8200126
  have hstable : (prefixWord ++ tailWord_8200126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200126).length < 2 ^ (prefixWord ++ tailWord_8200126).sum := by decide
  have hdescent : baseEnd_8200126 < baseStart_8200126 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200159 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 2, 6]
def baseStart_8200159 : Nat := 118140960795 + 8200159 * 2 ^ 59
def prefixEnd_8200159 : Nat := 4983230072969 + 3 ^ 40 * 8200159 * 2
def baseEnd_8200159 : Nat := 1403541003430695857966887

theorem tailTrace_8200159 : CollatzResearch.WordTrace tailWord_8200159 prefixEnd_8200159 1403541003430695857966887 := by
  unfold tailWord_8200159
  simp only [CollatzResearch.WordTrace]
  refine ⟨299084369499231893504747531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199389579666154595669831687 299084369499231893504747531)
  ·
    refine ⟨448626554248847840257121297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299084369499231893504747531 448626554248847840257121297)
    ·
      refine ⟨336469915686635880192840973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448626554248847840257121297 336469915686635880192840973)
      ·
        refine ⟨126176218382488455072315365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336469915686635880192840973 126176218382488455072315365)
        ·
          refine ⟨23658040946716585326059131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126176218382488455072315365 23658040946716585326059131)
          ·
            refine ⟨35487061420074877989088697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23658040946716585326059131 35487061420074877989088697)
            ·
              refine ⟨26615296065056158491816523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35487061420074877989088697 26615296065056158491816523)
              ·
                refine ⟨39922944097584237737724785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26615296065056158491816523 39922944097584237737724785)
                ·
                  refine ⟨29942208073188178303293589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39922944097584237737724785 29942208073188178303293589)
                  ·
                    refine ⟨1403541003430695857966887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29942208073188178303293589 1403541003430695857966887)
                    ·
                      rfl

theorem cell23_8200159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_8200159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200159 prefixEnd_8200159 := by exact prefixLift 8200159
  have htrace : WordTrace (prefixWord ++ tailWord_8200159) baseStart_8200159 baseEnd_8200159 := by
    simpa [prefixWord, tailWord_8200159, baseEnd_8200159] using wordTrace_append hprefix tailTrace_8200159
  have hstable : (prefixWord ++ tailWord_8200159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200159).length < 2 ^ (prefixWord ++ tailWord_8200159).sum := by decide
  have hdescent : baseEnd_8200159 < baseStart_8200159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200246 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_8200246 : Nat := 118140960795 + 8200246 * 2 ^ 59
def prefixEnd_8200246 : Nat := 4983230072969 + 3 ^ 40 * 8200246 * 2
def baseEnd_8200246 : Nat := 4210667683109028733512761

theorem tailTrace_8200246 : CollatzResearch.WordTrace tailWord_8200246 prefixEnd_8200246 4210667683109028733512761 := by
  unfold tailWord_8200246
  simp only [CollatzResearch.WordTrace]
  refine ⟨18692971415619794210197787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199391695099944471575443061 18692971415619794210197787)
  ·
    refine ⟨28039457123429691315296681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18692971415619794210197787 28039457123429691315296681)
    ·
      refine ⟨21029592842572268486472511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28039457123429691315296681 21029592842572268486472511)
      ·
        refine ⟨31544389263858402729708767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21029592842572268486472511 31544389263858402729708767)
        ·
          refine ⟨47316583895787604094563151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31544389263858402729708767 47316583895787604094563151)
          ·
            refine ⟨70974875843681406141844727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47316583895787604094563151 70974875843681406141844727)
            ·
              refine ⟨106462313765522109212767091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70974875843681406141844727 106462313765522109212767091)
              ·
                refine ⟨159693470648283163819150637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106462313765522109212767091 159693470648283163819150637)
                ·
                  refine ⟨59885051493106186432181489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159693470648283163819150637 59885051493106186432181489)
                  ·
                    refine ⟨44913788619829639824136117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59885051493106186432181489 44913788619829639824136117)
                    ·
                      refine ⟨4210667683109028733512761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44913788619829639824136117 4210667683109028733512761)
                      ·
                        rfl

theorem cell23_8200246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_8200246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200246 prefixEnd_8200246 := by exact prefixLift 8200246
  have htrace : WordTrace (prefixWord ++ tailWord_8200246) baseStart_8200246 baseEnd_8200246 := by
    simpa [prefixWord, tailWord_8200246, baseEnd_8200246] using wordTrace_append hprefix tailTrace_8200246
  have hstable : (prefixWord ++ tailWord_8200246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200246).length < 2 ^ (prefixWord ++ tailWord_8200246).sum := by decide
  have hdescent : baseEnd_8200246 < baseStart_8200246 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200256 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 4]
def baseStart_8200256 : Nat := 118140960795 + 8200256 * 2 ^ 59
def prefixEnd_8200256 : Nat := 4983230072969 + 3 ^ 40 * 8200256 * 2
def baseEnd_8200256 : Nat := 4210672817915573694387715

theorem tailTrace_8200256 : CollatzResearch.WordTrace tailWord_8200256 prefixEnd_8200256 4210672817915573694387715 := by
  unfold tailWord_8200256
  simp only [CollatzResearch.WordTrace]
  refine ⟨149543953689940239535514311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199391938253253652714019081 149543953689940239535514311)
  ·
    refine ⟨224315930534910359303271467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149543953689940239535514311 224315930534910359303271467)
    ·
      refine ⟨336473895802365538954907201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224315930534910359303271467 336473895802365538954907201)
      ·
        refine ⟨252355421851774154216180401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336473895802365538954907201 252355421851774154216180401)
        ·
          refine ⟨189266566388830615662135301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252355421851774154216180401 189266566388830615662135301)
          ·
            refine ⟨35487481197905740436650369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189266566388830615662135301 35487481197905740436650369)
            ·
              refine ⟨26615610898429305327487777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35487481197905740436650369 26615610898429305327487777)
              ·
                refine ⟨19961708173821978995615833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26615610898429305327487777 19961708173821978995615833)
                ·
                  refine ⟨14971281130366484246711875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19961708173821978995615833 14971281130366484246711875)
                  ·
                    refine ⟨22456921695549726370067813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14971281130366484246711875 22456921695549726370067813)
                    ·
                      refine ⟨4210672817915573694387715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22456921695549726370067813 4210672817915573694387715)
                      ·
                        rfl

theorem cell23_8200256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_8200256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200256 prefixEnd_8200256 := by exact prefixLift 8200256
  have htrace : WordTrace (prefixWord ++ tailWord_8200256) baseStart_8200256 baseEnd_8200256 := by
    simpa [prefixWord, tailWord_8200256, baseEnd_8200256] using wordTrace_append hprefix tailTrace_8200256
  have hstable : (prefixWord ++ tailWord_8200256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200256).length < 2 ^ (prefixWord ++ tailWord_8200256).sum := by decide
  have hdescent : baseEnd_8200256 < baseStart_8200256 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200266 : List Nat := [3, 1, 2, 1, 1, 2, 1, 5, 3, 4]
def baseStart_8200266 : Nat := 118140960795 + 8200266 * 2 ^ 59
def prefixEnd_8200266 : Nat := 4983230072969 + 3 ^ 40 * 8200266 * 2
def baseEnd_8200266 : Nat := 1403559317574039551754223

theorem tailTrace_8200266 : CollatzResearch.WordTrace tailWord_8200266 prefixEnd_8200266 1403559317574039551754223 := by
  unfold tailWord_8200266
  simp only [CollatzResearch.WordTrace]
  refine ⟨74772068027461062694723163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199392181406562833852595101 74772068027461062694723163)
  ·
    refine ⟨112158102041191594042084745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74772068027461062694723163 112158102041191594042084745)
    ·
      refine ⟨84118576530893695531563559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112158102041191594042084745 84118576530893695531563559)
      ·
        refine ⟨126177864796340543297345339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84118576530893695531563559 126177864796340543297345339)
        ·
          refine ⟨189266797194510814946018009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126177864796340543297345339 189266797194510814946018009)
          ·
            refine ⟨141950097895883111209513507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189266797194510814946018009 141950097895883111209513507)
            ·
              refine ⟨212925146843824666814270261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141950097895883111209513507 212925146843824666814270261)
              ·
                refine ⟨19961732516608562513837837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212925146843824666814270261 19961732516608562513837837)
                ·
                  refine ⟨7485649693728210942689189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19961732516608562513837837 7485649693728210942689189)
                  ·
                    refine ⟨1403559317574039551754223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7485649693728210942689189 1403559317574039551754223)
                    ·
                      rfl

theorem cell23_8200266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_8200266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200266 prefixEnd_8200266 := by exact prefixLift 8200266
  have htrace : WordTrace (prefixWord ++ tailWord_8200266) baseStart_8200266 baseEnd_8200266 := by
    simpa [prefixWord, tailWord_8200266, baseEnd_8200266] using wordTrace_append hprefix tailTrace_8200266
  have hstable : (prefixWord ++ tailWord_8200266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200266).length < 2 ^ (prefixWord ++ tailWord_8200266).sum := by decide
  have hdescent : baseEnd_8200266 < baseStart_8200266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200276 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_8200276 : Nat := 118140960795 + 8200276 * 2 ^ 59
def prefixEnd_8200276 : Nat := 4983230072969 + 3 ^ 40 * 8200276 * 2
def baseEnd_8200276 : Nat := 4210683087528663616137623

theorem tailTrace_8200276 : CollatzResearch.WordTrace tailWord_8200276 prefixEnd_8200276 4210683087528663616137623 := by
  unfold tailWord_8200276
  simp only [CollatzResearch.WordTrace]
  refine ⟨149544318419904011243378341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199392424559872014991171121 149544318419904011243378341)
  ·
    refine ⟨28039559703732002108133439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149544318419904011243378341 28039559703732002108133439)
    ·
      refine ⟨42059339555598003162200159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28039559703732002108133439 42059339555598003162200159)
      ·
        refine ⟨63089009333397004743300239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42059339555598003162200159 63089009333397004743300239)
        ·
          refine ⟨94633514000095507114950359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63089009333397004743300239 94633514000095507114950359)
          ·
            refine ⟨141950271000143260672425539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94633514000095507114950359 141950271000143260672425539)
            ·
              refine ⟨212925406500214891008638309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141950271000143260672425539 212925406500214891008638309)
              ·
                refine ⟨39923513718790292064119683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212925406500214891008638309 39923513718790292064119683)
                ·
                  refine ⟨59885270578185438096179525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39923513718790292064119683 59885270578185438096179525)
                  ·
                    refine ⟨11228488233409769643033661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59885270578185438096179525 11228488233409769643033661)
                    ·
                      refine ⟨4210683087528663616137623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11228488233409769643033661 4210683087528663616137623)
                      ·
                        rfl

theorem cell23_8200276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_8200276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200276 prefixEnd_8200276 := by exact prefixLift 8200276
  have htrace : WordTrace (prefixWord ++ tailWord_8200276) baseStart_8200276 baseEnd_8200276 := by
    simpa [prefixWord, tailWord_8200276, baseEnd_8200276] using wordTrace_append hprefix tailTrace_8200276
  have hstable : (prefixWord ++ tailWord_8200276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200276).length < 2 ^ (prefixWord ++ tailWord_8200276).sum := by decide
  have hdescent : baseEnd_8200276 < baseStart_8200276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200293 : List Nat := [1, 3, 1, 3, 2, 2, 3, 1, 2, 2, 3]
def baseStart_8200293 : Nat := 118140960795 + 8200293 * 2 ^ 59
def prefixEnd_8200293 : Nat := 4983230072969 + 3 ^ 40 * 8200293 * 2
def baseEnd_8200293 : Nat := 4210691816699790049625045

theorem tailTrace_8200293 : CollatzResearch.WordTrace tailWord_8200293 prefixEnd_8200293 4210691816699790049625045 := by
  unfold tailWord_8200293
  simp only [CollatzResearch.WordTrace]
  refine ⟨299089256880746434390125533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199392837920497622926750355 299089256880746434390125533)
  ·
    refine ⟨112158471330279912896297075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299089256880746434390125533 112158471330279912896297075)
    ·
      refine ⟨168237706995419869344445613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112158471330279912896297075 168237706995419869344445613)
      ·
        refine ⟨63089140123282451004167105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168237706995419869344445613 63089140123282451004167105)
        ·
          refine ⟨47316855092461838253125329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63089140123282451004167105 47316855092461838253125329)
          ·
            refine ⟨35487641319346378689843997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47316855092461838253125329 35487641319346378689843997)
            ·
              refine ⟨13307865494754892008691499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35487641319346378689843997 13307865494754892008691499)
              ·
                refine ⟨19961798242132338013037249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13307865494754892008691499 19961798242132338013037249)
                ·
                  refine ⟨14971348681599253509777937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19961798242132338013037249 14971348681599253509777937)
                  ·
                    refine ⟨11228511511199440132333453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14971348681599253509777937 11228511511199440132333453)
                    ·
                      refine ⟨4210691816699790049625045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11228511511199440132333453 4210691816699790049625045)
                      ·
                        rfl

theorem cell23_8200293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_8200293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200293 prefixEnd_8200293 := by exact prefixLift 8200293
  have htrace : WordTrace (prefixWord ++ tailWord_8200293) baseStart_8200293 baseEnd_8200293 := by
    simpa [prefixWord, tailWord_8200293, baseEnd_8200293] using wordTrace_append hprefix tailTrace_8200293
  have hstable : (prefixWord ++ tailWord_8200293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200293).length < 2 ^ (prefixWord ++ tailWord_8200293).sum := by decide
  have hdescent : baseEnd_8200293 < baseStart_8200293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200300 : List Nat := [2, 2, 1, 1, 3, 4, 2, 3, 1, 4]
def baseStart_8200300 : Nat := 118140960795 + 8200300 * 2 ^ 59
def prefixEnd_8200300 : Nat := 4983230072969 + 3 ^ 40 * 8200300 * 2
def baseEnd_8200300 : Nat := 1403565137021457174079171

theorem tailTrace_8200300 : CollatzResearch.WordTrace tailWord_8200300 prefixEnd_8200300 1403565137021457174079171 := by
  unfold tailWord_8200300
  simp only [CollatzResearch.WordTrace]
  refine ⟨149544756095860537292815177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199393008127814049723753569 149544756095860537292815177)
  ·
    refine ⟨112158567071895402969611383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149544756095860537292815177 112158567071895402969611383)
    ·
      refine ⟨168237850607843104454417075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112158567071895402969611383 168237850607843104454417075)
      ·
        refine ⟨252356775911764656681625613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168237850607843104454417075 252356775911764656681625613)
        ·
          refine ⟨94633790966911746255609605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252356775911764656681625613 94633790966911746255609605)
          ·
            refine ⟨17743835806295952422926801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94633790966911746255609605 17743835806295952422926801)
            ·
              refine ⟨13307876854721964317195101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17743835806295952422926801 13307876854721964317195101)
              ·
                refine ⟨4990453820520736618948163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13307876854721964317195101 4990453820520736618948163)
                ·
                  refine ⟨7485680730781104928422245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4990453820520736618948163 7485680730781104928422245)
                  ·
                    refine ⟨1403565137021457174079171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7485680730781104928422245 1403565137021457174079171)
                    ·
                      rfl

theorem cell23_8200300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 1, 4].length) (baseStart_8200300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200300 prefixEnd_8200300 := by exact prefixLift 8200300
  have htrace : WordTrace (prefixWord ++ tailWord_8200300) baseStart_8200300 baseEnd_8200300 := by
    simpa [prefixWord, tailWord_8200300, baseEnd_8200300] using wordTrace_append hprefix tailTrace_8200300
  have hstable : (prefixWord ++ tailWord_8200300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200300).length < 2 ^ (prefixWord ++ tailWord_8200300).sum := by decide
  have hdescent : baseEnd_8200300 < baseStart_8200300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200313 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 6]
def baseStart_8200313 : Nat := 118140960795 + 8200313 * 2 ^ 59
def prefixEnd_8200313 : Nat := 4983230072969 + 3 ^ 40 * 8200313 * 2
def baseEnd_8200313 : Nat := 467855787368097774597217

theorem tailTrace_8200313 : CollatzResearch.WordTrace tailWord_8200313 prefixEnd_8200313 467855787368097774597217 := by
  unfold tailWord_8200313
  simp only [CollatzResearch.WordTrace]
  refine ⟨299089986340673977805853593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199393324227115985203902395 299089986340673977805853593)
  ·
    refine ⟨224317489755505483354390195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299089986340673977805853593 224317489755505483354390195)
    ·
      refine ⟨336476234633258225031585293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224317489755505483354390195 336476234633258225031585293)
      ·
        refine ⟨126178587987471834386844485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336476234633258225031585293 126178587987471834386844485)
        ·
          refine ⟨23658485247650968947533341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126178587987471834386844485 23658485247650968947533341)
          ·
            refine ⟨8871931967869113355325003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23658485247650968947533341 8871931967869113355325003)
            ·
              refine ⟨13307897951803670032987505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8871931967869113355325003 13307897951803670032987505)
              ·
                refine ⟨9980923463852752524740629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13307897951803670032987505 9980923463852752524740629)
                ·
                  refine ⟨467855787368097774597217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9980923463852752524740629 467855787368097774597217)
                  ·
                    rfl

theorem cell23_8200313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 6].length) (baseStart_8200313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200313 prefixEnd_8200313 := by exact prefixLift 8200313
  have htrace : WordTrace (prefixWord ++ tailWord_8200313) baseStart_8200313 baseEnd_8200313 := by
    simpa [prefixWord, tailWord_8200313, baseEnd_8200313] using wordTrace_append hprefix tailTrace_8200313
  have hstable : (prefixWord ++ tailWord_8200313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200313).length < 2 ^ (prefixWord ++ tailWord_8200313).sum := by decide
  have hdescent : baseEnd_8200313 < baseStart_8200313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200323 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 3, 1, 3]
def baseStart_8200323 : Nat := 118140960795 + 8200323 * 2 ^ 59
def prefixEnd_8200323 : Nat := 4983230072969 + 3 ^ 40 * 8200323 * 2
def baseEnd_8200323 : Nat := 4210707221119424932249907

theorem tailTrace_8200323 : CollatzResearch.WordTrace tailWord_8200323 prefixEnd_8200323 4210707221119424932249907 := by
  unfold tailWord_8200323
  simp only [CollatzResearch.WordTrace]
  refine ⟨299090351070637749513717623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199393567380425166342478415 299090351070637749513717623)
  ·
    refine ⟨448635526605956624270576435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299090351070637749513717623 448635526605956624270576435)
    ·
      refine ⟨672953289908934936405864653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448635526605956624270576435 672953289908934936405864653)
      ·
        refine ⟨252357483715850601152199245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 672953289908934936405864653 252357483715850601152199245)
        ·
          refine ⟨94634056393443975432074717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252357483715850601152199245 94634056393443975432074717)
          ·
            refine ⟨35487771147541490787028019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94634056393443975432074717 35487771147541490787028019)
            ·
              refine ⟨53231656721312236180542029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35487771147541490787028019 53231656721312236180542029)
              ·
                refine ⟨19961871270492088567703261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53231656721312236180542029 19961871270492088567703261)
                ·
                  refine ⟨7485701726434533212888723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19961871270492088567703261 7485701726434533212888723)
                  ·
                    refine ⟨11228552589651799819333085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7485701726434533212888723 11228552589651799819333085)
                    ·
                      refine ⟨4210707221119424932249907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11228552589651799819333085 4210707221119424932249907)
                      ·
                        rfl

theorem cell23_8200323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_8200323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200323 prefixEnd_8200323 := by exact prefixLift 8200323
  have htrace : WordTrace (prefixWord ++ tailWord_8200323) baseStart_8200323 baseEnd_8200323 := by
    simpa [prefixWord, tailWord_8200323, baseEnd_8200323] using wordTrace_append hprefix tailTrace_8200323
  have hstable : (prefixWord ++ tailWord_8200323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200323).length < 2 ^ (prefixWord ++ tailWord_8200323).sum := by decide
  have hdescent : baseEnd_8200323 < baseStart_8200323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200431 : List Nat := [1, 1, 2, 1, 6, 3, 2, 2, 1, 2, 2]
def baseStart_8200431 : Nat := 118140960795 + 8200431 * 2 ^ 59
def prefixEnd_8200431 : Nat := 4983230072969 + 3 ^ 40 * 8200431 * 2
def baseEnd_8200431 : Nat := 4210762677030110509699411

theorem tailTrace_8200431 : CollatzResearch.WordTrace tailWord_8200431 prefixEnd_8200431 4210762677030110509699411 := by
  unfold tailWord_8200431
  simp only [CollatzResearch.WordTrace]
  refine ⟨299094290154246483958649147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199396193436164322639099431 299094290154246483958649147)
  ·
    refine ⟨448641435231369725937973721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299094290154246483958649147 448641435231369725937973721)
    ·
      refine ⟨336481076423527294453480291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448641435231369725937973721 336481076423527294453480291)
      ·
        refine ⟨504721614635290941680220437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336481076423527294453480291 504721614635290941680220437)
        ·
          refine ⟨23658825686029262891260333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 504721614635290941680220437 23658825686029262891260333)
          ·
            refine ⟨8872059632260973584222625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23658825686029262891260333 8872059632260973584222625)
            ·
              refine ⟨6654044724195730188166969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8872059632260973584222625 6654044724195730188166969)
              ·
                refine ⟨4990533543146797641125227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6654044724195730188166969 4990533543146797641125227)
                ·
                  refine ⟨7485800314720196461687841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4990533543146797641125227 7485800314720196461687841)
                  ·
                    refine ⟨5614350236040147346265881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7485800314720196461687841 5614350236040147346265881)
                    ·
                      refine ⟨4210762677030110509699411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5614350236040147346265881 4210762677030110509699411)
                      ·
                        rfl

theorem cell23_8200431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 1, 2, 2].length) (baseStart_8200431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200431 prefixEnd_8200431 := by exact prefixLift 8200431
  have htrace : WordTrace (prefixWord ++ tailWord_8200431) baseStart_8200431 baseEnd_8200431 := by
    simpa [prefixWord, tailWord_8200431, baseEnd_8200431] using wordTrace_append hprefix tailTrace_8200431
  have hstable : (prefixWord ++ tailWord_8200431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200431).length < 2 ^ (prefixWord ++ tailWord_8200431).sum := by decide
  have hdescent : baseEnd_8200431 < baseStart_8200431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200476 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 11]
def baseStart_8200476 : Nat := 118140960795 + 8200476 * 2 ^ 59
def prefixEnd_8200476 : Nat := 4983230072969 + 3 ^ 40 * 8200476 * 2
def baseEnd_8200476 : Nat := 467865087073284759292967

theorem tailTrace_8200476 : CollatzResearch.WordTrace tailWord_8200476 prefixEnd_8200476 467865087073284759292967 := by
  unfold tailWord_8200476
  simp only [CollatzResearch.WordTrace]
  refine ⟨149547965719541728322018641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199397287626055637762691521 149547965719541728322018641)
  ·
    refine ⟨112160974289656296241513981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149547965719541728322018641 112160974289656296241513981)
    ·
      refine ⟨42060365358621111090567743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112160974289656296241513981 42060365358621111090567743)
      ·
        refine ⟨63090548037931666635851615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42060365358621111090567743 63090548037931666635851615)
        ·
          refine ⟨94635822056897499953777423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63090548037931666635851615 94635822056897499953777423)
          ·
            refine ⟨141953733085346249930666135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94635822056897499953777423 141953733085346249930666135)
            ·
              refine ⟨212930599628019374895999203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141953733085346249930666135 212930599628019374895999203)
              ·
                refine ⟨319395899442029062343998805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212930599628019374895999203 319395899442029062343998805)
                ·
                  refine ⟨467865087073284759292967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 319395899442029062343998805 467865087073284759292967)
                  ·
                    rfl

theorem cell23_8200476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_8200476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200476 prefixEnd_8200476 := by exact prefixLift 8200476
  have htrace : WordTrace (prefixWord ++ tailWord_8200476) baseStart_8200476 baseEnd_8200476 := by
    simpa [prefixWord, tailWord_8200476, baseEnd_8200476] using wordTrace_append hprefix tailTrace_8200476
  have hstable : (prefixWord ++ tailWord_8200476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200476).length < 2 ^ (prefixWord ++ tailWord_8200476).sum := by decide
  have hdescent : baseEnd_8200476 < baseStart_8200476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200500 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_8200500 : Nat := 118140960795 + 8200500 * 2 ^ 59
def prefixEnd_8200500 : Nat := 4983230072969 + 3 ^ 40 * 8200500 * 2
def baseEnd_8200500 : Nat := 4210798107195270739736593

theorem tailTrace_8200500 : CollatzResearch.WordTrace tailWord_8200500 prefixEnd_8200500 4210798107195270739736593 := by
  unfold tailWord_8200500
  simp only [CollatzResearch.WordTrace]
  refine ⟨149548403395498254371455477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199397871193997672495273969 149548403395498254371455477)
  ·
    refine ⟨14020162818327961347323951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149548403395498254371455477 14020162818327961347323951)
    ·
      refine ⟨21030244227491942020985927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14020162818327961347323951 21030244227491942020985927)
      ·
        refine ⟨31545366341237913031478891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21030244227491942020985927 31545366341237913031478891)
        ·
          refine ⟨47318049511856869547218337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31545366341237913031478891 47318049511856869547218337)
          ·
            refine ⟨35488537133892652160413753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47318049511856869547218337 35488537133892652160413753)
            ·
              refine ⟨26616402850419489120310315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35488537133892652160413753 26616402850419489120310315)
              ·
                refine ⟨39924604275629233680465473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26616402850419489120310315 39924604275629233680465473)
                ·
                  refine ⟨29943453206721925260349105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39924604275629233680465473 29943453206721925260349105)
                  ·
                    refine ⟨22457589905041443945261829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29943453206721925260349105 22457589905041443945261829)
                    ·
                      refine ⟨4210798107195270739736593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22457589905041443945261829 4210798107195270739736593)
                      ·
                        rfl

theorem cell23_8200500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_8200500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200500 prefixEnd_8200500 := by exact prefixLift 8200500
  have htrace : WordTrace (prefixWord ++ tailWord_8200500) baseStart_8200500 baseEnd_8200500 := by
    simpa [prefixWord, tailWord_8200500, baseEnd_8200500] using wordTrace_append hprefix tailTrace_8200500
  have hstable : (prefixWord ++ tailWord_8200500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200500).length < 2 ^ (prefixWord ++ tailWord_8200500).sum := by decide
  have hdescent : baseEnd_8200500 < baseStart_8200500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200543 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 4]
def baseStart_8200543 : Nat := 118140960795 + 8200543 * 2 ^ 59
def prefixEnd_8200543 : Nat := 4983230072969 + 3 ^ 40 * 8200543 * 2
def baseEnd_8200543 : Nat := 4210820186863414071498895

theorem tailTrace_8200543 : CollatzResearch.WordTrace tailWord_8200543 prefixEnd_8200543 4210820186863414071498895 := by
  unfold tailWord_8200543
  simp only [CollatzResearch.WordTrace]
  refine ⟨299098375129840727086726283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199398916753227151391150855 299098375129840727086726283)
  ·
    refine ⟨448647562694761090630089425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299098375129840727086726283 448647562694761090630089425)
    ·
      refine ⟨336485672021070817972567069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448647562694761090630089425 336485672021070817972567069)
      ·
        refine ⟨126182127007901556739712651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336485672021070817972567069 126182127007901556739712651)
        ·
          refine ⟨189273190511852335109568977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126182127007901556739712651 189273190511852335109568977)
          ·
            refine ⟨141954892883889251332176733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189273190511852335109568977 141954892883889251332176733)
            ·
              refine ⟨53233084831458469249566275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141954892883889251332176733 53233084831458469249566275)
              ·
                refine ⟨79849627247187703874349413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53233084831458469249566275 79849627247187703874349413)
                ·
                  refine ⟨14971805108847694476440515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79849627247187703874349413 14971805108847694476440515)
                  ·
                    refine ⟨22457707663271541714660773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14971805108847694476440515 22457707663271541714660773)
                    ·
                      refine ⟨4210820186863414071498895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22457707663271541714660773 4210820186863414071498895)
                      ·
                        rfl

theorem cell23_8200543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_8200543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200543 prefixEnd_8200543 := by exact prefixLift 8200543
  have htrace : WordTrace (prefixWord ++ tailWord_8200543) baseStart_8200543 baseEnd_8200543 := by
    simpa [prefixWord, tailWord_8200543, baseEnd_8200543] using wordTrace_append hprefix tailTrace_8200543
  have hstable : (prefixWord ++ tailWord_8200543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200543).length < 2 ^ (prefixWord ++ tailWord_8200543).sum := by decide
  have hdescent : baseEnd_8200543 < baseStart_8200543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200577 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 4]
def baseStart_8200577 : Nat := 118140960795 + 8200577 * 2 ^ 59
def prefixEnd_8200577 : Nat := 4983230072969 + 3 ^ 40 * 8200577 * 2
def baseEnd_8200577 : Nat := 4210837645205666938473739

theorem tailTrace_8200577 : CollatzResearch.WordTrace tailWord_8200577 prefixEnd_8200577 4210837645205666938473739 := by
  unfold tailWord_8200577
  simp only [CollatzResearch.WordTrace]
  refine ⟨299099615211717550893463985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199399743474478367262309323 299099615211717550893463985)
  ·
    refine ⟨224324711408788163170097989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299099615211717550893463985 224324711408788163170097989)
    ·
      refine ⟨42060883389147780594393373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224324711408788163170097989 42060883389147780594393373)
      ·
        refine ⟨15772831270930417722897515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42060883389147780594393373 15772831270930417722897515)
        ·
          refine ⟨23659246906395626584346273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15772831270930417722897515 23659246906395626584346273)
          ·
            refine ⟨17744435179796719938259705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23659246906395626584346273 17744435179796719938259705)
            ·
              refine ⟨13308326384847539953694779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17744435179796719938259705 13308326384847539953694779)
              ·
                refine ⟨19962489577271309930542169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13308326384847539953694779 19962489577271309930542169)
                ·
                  refine ⟨14971867182953482447906627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19962489577271309930542169 14971867182953482447906627)
                  ·
                    refine ⟨22457800774430223671859941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14971867182953482447906627 22457800774430223671859941)
                    ·
                      refine ⟨4210837645205666938473739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22457800774430223671859941 4210837645205666938473739)
                      ·
                        rfl

theorem cell23_8200577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_8200577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200577 prefixEnd_8200577 := by exact prefixLift 8200577
  have htrace : WordTrace (prefixWord ++ tailWord_8200577) baseStart_8200577 baseEnd_8200577 := by
    simpa [prefixWord, tailWord_8200577, baseEnd_8200577] using wordTrace_append hprefix tailTrace_8200577
  have hstable : (prefixWord ++ tailWord_8200577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200577).length < 2 ^ (prefixWord ++ tailWord_8200577).sum := by decide
  have hdescent : baseEnd_8200577 < baseStart_8200577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200600 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 6]
def baseStart_8200600 : Nat := 118140960795 + 8200600 * 2 ^ 59
def prefixEnd_8200600 : Nat := 4983230072969 + 3 ^ 40 * 8200600 * 2
def baseEnd_8200600 : Nat := 467872161695635594276237

theorem tailTrace_8200600 : CollatzResearch.WordTrace tailWord_8200600 prefixEnd_8200600 467872161695635594276237 := by
  unfold tailWord_8200600
  simp only [CollatzResearch.WordTrace]
  refine ⟨149550227045317112910775627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199400302727089483881034169 149550227045317112910775627)
  ·
    refine ⟨224325340567975669366163441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149550227045317112910775627 224325340567975669366163441)
    ·
      refine ⟨168244005425981752024622581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224325340567975669366163441 168244005425981752024622581)
      ·
        refine ⟨15772875508685789252308367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168244005425981752024622581 15772875508685789252308367)
        ·
          refine ⟨23659313263028683878462551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15772875508685789252308367 23659313263028683878462551)
          ·
            refine ⟨35488969894543025817693827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23659313263028683878462551 35488969894543025817693827)
            ·
              refine ⟨53233454841814538726540741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35488969894543025817693827 53233454841814538726540741)
              ·
                refine ⟨9981272782840226011226389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53233454841814538726540741 9981272782840226011226389)
                ·
                  refine ⟨467872161695635594276237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9981272782840226011226389 467872161695635594276237)
                  ·
                    rfl

theorem cell23_8200600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 6].length) (baseStart_8200600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200600 prefixEnd_8200600 := by exact prefixLift 8200600
  have htrace : WordTrace (prefixWord ++ tailWord_8200600) baseStart_8200600 baseEnd_8200600 := by
    simpa [prefixWord, tailWord_8200600, baseEnd_8200600] using wordTrace_append hprefix tailTrace_8200600
  have hstable : (prefixWord ++ tailWord_8200600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200600).length < 2 ^ (prefixWord ++ tailWord_8200600).sum := by decide
  have hdescent : baseEnd_8200600 < baseStart_8200600 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200613 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_8200613 : Nat := 118140960795 + 8200613 * 2 ^ 59
def prefixEnd_8200613 : Nat := 4983230072969 + 3 ^ 40 * 8200613 * 2
def baseEnd_8200613 : Nat := 1403618710169742932541191

theorem tailTrace_8200613 : CollatzResearch.WordTrace tailWord_8200613 prefixEnd_8200613 1403618710169742932541191 := by
  unfold tailWord_8200613
  simp only [CollatzResearch.WordTrace]
  refine ⟨299100928239587129041774493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199400618826391419361182995 299100928239587129041774493)
  ·
    refine ⟨112162848089845173390665435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299100928239587129041774493 112162848089845173390665435)
    ·
      refine ⟨168244272134767760085998153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112162848089845173390665435 168244272134767760085998153)
      ·
        refine ⟨126183204101075820064498615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168244272134767760085998153 126183204101075820064498615)
        ·
          refine ⟨189274806151613730096747923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126183204101075820064498615 189274806151613730096747923)
          ·
            refine ⟨283912209227420595145121885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189274806151613730096747923 283912209227420595145121885)
            ·
              refine ⟨106467078460282723179420707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283912209227420595145121885 106467078460282723179420707)
              ·
                refine ⟨159700617690424084769131061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106467078460282723179420707 159700617690424084769131061)
                ·
                  refine ⟨14971932908477257947106037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159700617690424084769131061 14971932908477257947106037)
                  ·
                    refine ⟨1403618710169742932541191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14971932908477257947106037 1403618710169742932541191)
                    ·
                      rfl

theorem cell23_8200613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_8200613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200613 prefixEnd_8200613 := by exact prefixLift 8200613
  have htrace : WordTrace (prefixWord ++ tailWord_8200613) baseStart_8200613 baseEnd_8200613 := by
    simpa [prefixWord, tailWord_8200613, baseEnd_8200613] using wordTrace_append hprefix tailTrace_8200613
  have hstable : (prefixWord ++ tailWord_8200613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200613).length < 2 ^ (prefixWord ++ tailWord_8200613).sum := by decide
  have hdescent : baseEnd_8200613 < baseStart_8200613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200620 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 1, 5, 2]
def baseStart_8200620 : Nat := 118140960795 + 8200620 * 2 ^ 59
def prefixEnd_8200620 : Nat := 4983230072969 + 3 ^ 40 * 8200620 * 2
def baseEnd_8200620 : Nat := 4210859724873810270236041

theorem tailTrace_8200620 : CollatzResearch.WordTrace tailWord_8200620 prefixEnd_8200620 4210859724873810270236041 := by
  unfold tailWord_8200620
  simp only [CollatzResearch.WordTrace]
  refine ⟨149550591775280884618639657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199400789033707846158186209 149550591775280884618639657)
  ·
    refine ⟨112162943831460663463979743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149550591775280884618639657 112162943831460663463979743)
    ·
      refine ⟨168244415747190995195969615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112162943831460663463979743 168244415747190995195969615)
      ·
        refine ⟨252366623620786492793954423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168244415747190995195969615 252366623620786492793954423)
        ·
          refine ⟨378549935431179739190931635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252366623620786492793954423 378549935431179739190931635)
          ·
            refine ⟨567824903146769608786397453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378549935431179739190931635 567824903146769608786397453)
            ·
              refine ⟨212934338680038603294899045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 567824903146769608786397453 212934338680038603294899045)
              ·
                refine ⟨39925188502507238117793571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212934338680038603294899045 39925188502507238117793571)
                ·
                  refine ⟨59887782753760857176690357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39925188502507238117793571 59887782753760857176690357)
                  ·
                    refine ⟨5614479633165080360314721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59887782753760857176690357 5614479633165080360314721)
                    ·
                      refine ⟨4210859724873810270236041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5614479633165080360314721 4210859724873810270236041)
                      ·
                        rfl

theorem cell23_8200620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 5, 2].length) (baseStart_8200620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200620 prefixEnd_8200620 := by exact prefixLift 8200620
  have htrace : WordTrace (prefixWord ++ tailWord_8200620) baseStart_8200620 baseEnd_8200620 := by
    simpa [prefixWord, tailWord_8200620, baseEnd_8200620] using wordTrace_append hprefix tailTrace_8200620
  have hstable : (prefixWord ++ tailWord_8200620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200620).length < 2 ^ (prefixWord ++ tailWord_8200620).sum := by decide
  have hdescent : baseEnd_8200620 < baseStart_8200620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200628 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 2, 1, 4]
def baseStart_8200628 : Nat := 118140960795 + 8200628 * 2 ^ 59
def prefixEnd_8200628 : Nat := 4983230072969 + 3 ^ 40 * 8200628 * 2
def baseEnd_8200628 : Nat := 4210863832719046238936005

theorem tailTrace_8200628 : CollatzResearch.WordTrace tailWord_8200628 prefixEnd_8200628 4210863832719046238936005 := by
  unfold tailWord_8200628
  simp only [CollatzResearch.WordTrace]
  refine ⟨149550737667266393301785269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199400983556355191069047025 149550737667266393301785269)
  ·
    refine ⟨14020381656306224372042369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149550737667266393301785269 14020381656306224372042369)
    ·
      refine ⟨10515286242229668279031777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14020381656306224372042369 10515286242229668279031777)
      ·
        refine ⟨7886464681672251209273833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10515286242229668279031777 7886464681672251209273833)
        ·
          refine ⟨5914848511254188406955375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7886464681672251209273833 5914848511254188406955375)
          ·
            refine ⟨8872272766881282610433063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914848511254188406955375 8872272766881282610433063)
            ·
              refine ⟨13308409150321923915649595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872272766881282610433063 13308409150321923915649595)
              ·
                refine ⟨19962613725482885873474393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13308409150321923915649595 19962613725482885873474393)
                ·
                  refine ⟨14971960294112164405105795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19962613725482885873474393 14971960294112164405105795)
                  ·
                    refine ⟨22457940441168246607658693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14971960294112164405105795 22457940441168246607658693)
                    ·
                      refine ⟨4210863832719046238936005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22457940441168246607658693 4210863832719046238936005)
                      ·
                        rfl

theorem cell23_8200628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_8200628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200628 prefixEnd_8200628 := by exact prefixLift 8200628
  have htrace : WordTrace (prefixWord ++ tailWord_8200628) baseStart_8200628 baseEnd_8200628 := by
    simpa [prefixWord, tailWord_8200628, baseEnd_8200628] using wordTrace_append hprefix tailTrace_8200628
  have hstable : (prefixWord ++ tailWord_8200628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200628).length < 2 ^ (prefixWord ++ tailWord_8200628).sum := by decide
  have hdescent : baseEnd_8200628 < baseStart_8200628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200637 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 1, 5, 2]
def baseStart_8200637 : Nat := 118140960795 + 8200637 * 2 ^ 59
def prefixEnd_8200637 : Nat := 4983230072969 + 3 ^ 40 * 8200637 * 2
def baseEnd_8200637 : Nat := 4210868454044936703723463

theorem tailTrace_8200637 : CollatzResearch.WordTrace tailWord_8200637 prefixEnd_8200637 4210868454044936703723463 := by
  unfold tailWord_8200637
  simp only [CollatzResearch.WordTrace]
  refine ⟨299101803591500181140648165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199401202394333454093765443 299101803591500181140648165)
  ·
    refine ⟨56081588173406283963871531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299101803591500181140648165 56081588173406283963871531)
    ·
      refine ⟨84122382260109425945807297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56081588173406283963871531 84122382260109425945807297)
      ·
        refine ⟨63091786695082069459355473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84122382260109425945807297 63091786695082069459355473)
        ·
          refine ⟨47318840021311552094516605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63091786695082069459355473 47318840021311552094516605)
          ·
            refine ⟨17744565007991832035443727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47318840021311552094516605 17744565007991832035443727)
            ·
              refine ⟨26616847511987748053165591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17744565007991832035443727 26616847511987748053165591)
              ·
                refine ⟨39925271267981622079748387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26616847511987748053165591 39925271267981622079748387)
                ·
                  refine ⟨59887906901972433119622581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39925271267981622079748387 59887906901972433119622581)
                  ·
                    refine ⟨5614491272059915604964617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59887906901972433119622581 5614491272059915604964617)
                    ·
                      refine ⟨4210868454044936703723463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5614491272059915604964617 4210868454044936703723463)
                      ·
                        rfl

theorem cell23_8200637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_8200637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200637 prefixEnd_8200637 := by exact prefixLift 8200637
  have htrace : WordTrace (prefixWord ++ tailWord_8200637) baseStart_8200637 baseEnd_8200637 := by
    simpa [prefixWord, tailWord_8200637, baseEnd_8200637] using wordTrace_append hprefix tailTrace_8200637
  have hstable : (prefixWord ++ tailWord_8200637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200637).length < 2 ^ (prefixWord ++ tailWord_8200637).sum := by decide
  have hdescent : baseEnd_8200637 < baseStart_8200637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200647 : List Nat := [1, 1, 4, 1, 1, 4, 4, 1, 1, 5]
def baseStart_8200647 : Nat := 118140960795 + 8200647 * 2 ^ 59
def prefixEnd_8200647 : Nat := 4983230072969 + 3 ^ 40 * 8200647 * 2
def baseEnd_8200647 : Nat := 1403624529617160554866139

theorem tailTrace_8200647 : CollatzResearch.WordTrace tailWord_8200647 prefixEnd_8200647 1403624529617160554866139 := by
  unfold tailWord_8200647
  simp only [CollatzResearch.WordTrace]
  refine ⟨299102168321463952848512195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199401445547642635232341463 299102168321463952848512195)
  ·
    refine ⟨448653252482195929272768293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299102168321463952848512195 448653252482195929272768293)
    ·
      refine ⟨84122484840411736738644055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448653252482195929272768293 84122484840411736738644055)
      ·
        refine ⟨126183727260617605107966083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84122484840411736738644055 126183727260617605107966083)
        ·
          refine ⟨189275590890926407661949125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126183727260617605107966083 189275590890926407661949125)
          ·
            refine ⟨35489173292048701436615461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189275590890926407661949125 35489173292048701436615461)
            ·
              refine ⟨6654219992259131519365399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35489173292048701436615461 6654219992259131519365399)
              ·
                refine ⟨9981329988388697279048099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654219992259131519365399 9981329988388697279048099)
                ·
                  refine ⟨14971994982583045918572149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9981329988388697279048099 14971994982583045918572149)
                  ·
                    refine ⟨1403624529617160554866139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14971994982583045918572149 1403624529617160554866139)
                    ·
                      rfl

theorem cell23_8200647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_8200647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200647 prefixEnd_8200647 := by exact prefixLift 8200647
  have htrace : WordTrace (prefixWord ++ tailWord_8200647) baseStart_8200647 baseEnd_8200647 := by
    simpa [prefixWord, tailWord_8200647, baseEnd_8200647] using wordTrace_append hprefix tailTrace_8200647
  have hstable : (prefixWord ++ tailWord_8200647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200647).length < 2 ^ (prefixWord ++ tailWord_8200647).sum := by decide
  have hdescent : baseEnd_8200647 < baseStart_8200647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200663 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_8200663 : Nat := 118140960795 + 8200663 * 2 ^ 59
def prefixEnd_8200663 : Nat := 4983230072969 + 3 ^ 40 * 8200663 * 2
def baseEnd_8200663 : Nat := 4210881804541953601998343

theorem tailTrace_8200663 : CollatzResearch.WordTrace tailWord_8200663 prefixEnd_8200663 4210881804541953601998343 := by
  unfold tailWord_8200663
  simp only [CollatzResearch.WordTrace]
  refine ⟨299102751889405987581094643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199401834592937325054063095 299102751889405987581094643)
  ·
    refine ⟨448654127834108981371641965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299102751889405987581094643 448654127834108981371641965)
    ·
      refine ⟨168245297937790868014365737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448654127834108981371641965 168245297937790868014365737)
      ·
        refine ⟨126183973453343151010774303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168245297937790868014365737 126183973453343151010774303)
        ·
          refine ⟨189275960180014726516161455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126183973453343151010774303 189275960180014726516161455)
          ·
            refine ⟨283913940270022089774242183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189275960180014726516161455 283913940270022089774242183)
            ·
              refine ⟨425870910405033134661363275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283913940270022089774242183 425870910405033134661363275)
              ·
                refine ⟨638806365607549701992044913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425870910405033134661363275 638806365607549701992044913)
                ·
                  refine ⟨479104774205662276494033685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 638806365607549701992044913 479104774205662276494033685)
                  ·
                    refine ⟨22458036290890419210657829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 479104774205662276494033685 22458036290890419210657829)
                    ·
                      refine ⟨4210881804541953601998343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22458036290890419210657829 4210881804541953601998343)
                      ·
                        rfl

theorem cell23_8200663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_8200663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200663 prefixEnd_8200663 := by exact prefixLift 8200663
  have htrace : WordTrace (prefixWord ++ tailWord_8200663) baseStart_8200663 baseEnd_8200663 := by
    simpa [prefixWord, tailWord_8200663, baseEnd_8200663] using wordTrace_append hprefix tailTrace_8200663
  have hstable : (prefixWord ++ tailWord_8200663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200663).length < 2 ^ (prefixWord ++ tailWord_8200663).sum := by decide
  have hdescent : baseEnd_8200663 < baseStart_8200663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200673 : List Nat := [1, 2, 3, 1, 2, 2, 2, 10]
def baseStart_8200673 : Nat := 118140960795 + 8200673 * 2 ^ 59
def prefixEnd_8200673 : Nat := 4983230072969 + 3 ^ 40 * 8200673 * 2
def baseEnd_8200673 : Nat := 155958775531425872699011

theorem tailTrace_8200673 : CollatzResearch.WordTrace tailWord_8200673 prefixEnd_8200673 155958775531425872699011 := by
  unfold tailWord_8200673
  simp only [CollatzResearch.WordTrace]
  refine ⟨299103116619369759288958673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199402077746246506192639115 299103116619369759288958673)
  ·
    refine ⟨224327337464527319466719005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299103116619369759288958673 224327337464527319466719005)
    ·
      refine ⟨84122751549197744800019627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224327337464527319466719005 84122751549197744800019627)
      ·
        refine ⟨126184127323796617200029441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84122751549197744800019627 126184127323796617200029441)
        ·
          refine ⟨94638095492847462900022081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126184127323796617200029441 94638095492847462900022081)
          ·
            refine ⟨70978571619635597175016561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94638095492847462900022081 70978571619635597175016561)
            ·
              refine ⟨53233928714726697881262421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70978571619635597175016561 53233928714726697881262421)
              ·
                refine ⟨155958775531425872699011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53233928714726697881262421 155958775531425872699011)
                ·
                  rfl

theorem cell23_8200673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 10].length) (baseStart_8200673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200673 prefixEnd_8200673 := by exact prefixLift 8200673
  have htrace : WordTrace (prefixWord ++ tailWord_8200673) baseStart_8200673 baseEnd_8200673 := by
    simpa [prefixWord, tailWord_8200673, baseEnd_8200673] using wordTrace_append hprefix tailTrace_8200673
  have hstable : (prefixWord ++ tailWord_8200673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200673).length < 2 ^ (prefixWord ++ tailWord_8200673).sum := by decide
  have hdescent : baseEnd_8200673 < baseStart_8200673 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200680 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_8200680 : Nat := 118140960795 + 8200680 * 2 ^ 59
def prefixEnd_8200680 : Nat := 4983230072969 + 3 ^ 40 * 8200680 * 2
def baseEnd_8200680 : Nat := 4210890533713080035485765

theorem tailTrace_8200680 : CollatzResearch.WordTrace tailWord_8200680 prefixEnd_8200680 4210890533713080035485765 := by
  unfold tailWord_8200680
  simp only [CollatzResearch.WordTrace]
  refine ⟨149551685965172199742231747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199402247953562932989642329 149551685965172199742231747)
  ·
    refine ⟨224327528947758299613347621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149551685965172199742231747 224327528947758299613347621)
    ·
      refine ⟨42061411677704681177502679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224327528947758299613347621 42061411677704681177502679)
      ·
        refine ⟨63092117516557021766254019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42061411677704681177502679 63092117516557021766254019)
        ·
          refine ⟨94638176274835532649381029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63092117516557021766254019 94638176274835532649381029)
          ·
            refine ⟨17744658051531662371758943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94638176274835532649381029 17744658051531662371758943)
            ·
              refine ⟨26616987077297493557638415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17744658051531662371758943 26616987077297493557638415)
              ·
                refine ⟨39925480615946240336457623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26616987077297493557638415 39925480615946240336457623)
                ·
                  refine ⟨59888220923919360504686435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39925480615946240336457623 59888220923919360504686435)
                  ·
                    refine ⟨89832331385879040757029653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59888220923919360504686435 89832331385879040757029653)
                    ·
                      refine ⟨4210890533713080035485765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89832331385879040757029653 4210890533713080035485765)
                      ·
                        rfl

theorem cell23_8200680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_8200680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200680 prefixEnd_8200680 := by exact prefixLift 8200680
  have htrace : WordTrace (prefixWord ++ tailWord_8200680) baseStart_8200680 baseEnd_8200680 := by
    simpa [prefixWord, tailWord_8200680, baseEnd_8200680] using wordTrace_append hprefix tailTrace_8200680
  have hstable : (prefixWord ++ tailWord_8200680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200680).length < 2 ^ (prefixWord ++ tailWord_8200680).sum := by decide
  have hdescent : baseEnd_8200680 < baseStart_8200680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200700 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 3, 3, 3]
def baseStart_8200700 : Nat := 118140960795 + 8200700 * 2 ^ 59
def prefixEnd_8200700 : Nat := 4983230072969 + 3 ^ 40 * 8200700 * 2
def baseEnd_8200700 : Nat := 4210900803326169957235673

theorem tailTrace_8200700 : CollatzResearch.WordTrace tailWord_8200700 prefixEnd_8200700 4210900803326169957235673 := by
  unfold tailWord_8200700
  simp only [CollatzResearch.WordTrace]
  refine ⟨149552050695135971450095777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199402734260181295266794369 149552050695135971450095777)
  ·
    refine ⟨112164038021351978587571833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149552050695135971450095777 112164038021351978587571833)
    ·
      refine ⟨84123028516013983940678875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112164038021351978587571833 84123028516013983940678875)
      ·
        refine ⟨126184542774020975911018313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84123028516013983940678875 126184542774020975911018313)
        ·
          refine ⟨94638407080515731933263735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126184542774020975911018313 94638407080515731933263735)
          ·
            refine ⟨141957610620773597899895603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94638407080515731933263735 141957610620773597899895603)
            ·
              refine ⟨212936415931160396849843405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141957610620773597899895603 212936415931160396849843405)
              ·
                refine ⟨79851155974185148818691277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212936415931160396849843405 79851155974185148818691277)
                ·
                  refine ⟨29944183490319430807009229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79851155974185148818691277 29944183490319430807009229)
                  ·
                    refine ⟨11229068808869786552628461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29944183490319430807009229 11229068808869786552628461)
                    ·
                      refine ⟨4210900803326169957235673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11229068808869786552628461 4210900803326169957235673)
                      ·
                        rfl

theorem cell23_8200700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_8200700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200700 prefixEnd_8200700 := by exact prefixLift 8200700
  have htrace : WordTrace (prefixWord ++ tailWord_8200700) baseStart_8200700 baseEnd_8200700 := by
    simpa [prefixWord, tailWord_8200700, baseEnd_8200700] using wordTrace_append hprefix tailTrace_8200700
  have hstable : (prefixWord ++ tailWord_8200700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200700).length < 2 ^ (prefixWord ++ tailWord_8200700).sum := by decide
  have hdescent : baseEnd_8200700 < baseStart_8200700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200760 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 2, 1, 5]
def baseStart_8200760 : Nat := 118140960795 + 8200760 * 2 ^ 59
def prefixEnd_8200760 : Nat := 4983230072969 + 3 ^ 40 * 8200760 * 2
def baseEnd_8200760 : Nat := 4210931612165439722485397

theorem tailTrace_8200760 : CollatzResearch.WordTrace tailWord_8200760 prefixEnd_8200760 4210931612165439722485397 := by
  unfold tailWord_8200760
  simp only [CollatzResearch.WordTrace]
  refine ⟨149553144885027286573687867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199404193180036382098250489 149553144885027286573687867)
  ·
    refine ⟨224329717327540929860531801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149553144885027286573687867 224329717327540929860531801)
    ·
      refine ⟨168247287995655697395398851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224329717327540929860531801 168247287995655697395398851)
      ·
        refine ⟨252370931993483546093098277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168247287995655697395398851 252370931993483546093098277)
        ·
          refine ⟨47319549748778164892455927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252370931993483546093098277 47319549748778164892455927)
          ·
            refine ⟨70979324623167247338683891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47319549748778164892455927 70979324623167247338683891)
            ·
              refine ⟨106468986934750871008025837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70979324623167247338683891 106468986934750871008025837)
              ·
                refine ⟨39925870100531576628009689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106468986934750871008025837 39925870100531576628009689)
                ·
                  refine ⟨29944402575398682471007267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39925870100531576628009689 29944402575398682471007267)
                  ·
                    refine ⟨44916603863098023706510901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29944402575398682471007267 44916603863098023706510901)
                    ·
                      refine ⟨4210931612165439722485397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44916603863098023706510901 4210931612165439722485397)
                      ·
                        rfl

theorem cell23_8200760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_8200760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200760 prefixEnd_8200760 := by exact prefixLift 8200760
  have htrace : WordTrace (prefixWord ++ tailWord_8200760) baseStart_8200760 baseEnd_8200760 := by
    simpa [prefixWord, tailWord_8200760, baseEnd_8200760] using wordTrace_append hprefix tailTrace_8200760
  have hstable : (prefixWord ++ tailWord_8200760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200760).length < 2 ^ (prefixWord ++ tailWord_8200760).sum := by decide
  have hdescent : baseEnd_8200760 < baseStart_8200760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200761 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 1, 3, 2]
def baseStart_8200761 : Nat := 118140960795 + 8200761 * 2 ^ 59
def prefixEnd_8200761 : Nat := 4983230072969 + 3 ^ 40 * 8200761 * 2
def baseEnd_8200761 : Nat := 4210932125646094218572893

theorem tailTrace_8200761 : CollatzResearch.WordTrace tailWord_8200761 prefixEnd_8200761 4210932125646094218572893 := by
  unfold tailWord_8200761
  simp only [CollatzResearch.WordTrace]
  refine ⟨299106326243050950318162137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199404217495367300212108091 299106326243050950318162137)
  ·
    refine ⟨224329744682288212738621603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299106326243050950318162137 224329744682288212738621603)
    ·
      refine ⟨336494617023432319107932405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224329744682288212738621603 336494617023432319107932405)
      ·
        refine ⟨31546370345946779916368663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336494617023432319107932405 31546370345946779916368663)
        ·
          refine ⟨47319555518920169874552995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31546370345946779916368663 47319555518920169874552995)
          ·
            refine ⟨70979333278380254811829493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47319555518920169874552995 70979333278380254811829493)
            ·
              refine ⟨6654312494848148888609015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70979333278380254811829493 6654312494848148888609015)
              ·
                refine ⟨9981468742272223332913523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654312494848148888609015 9981468742272223332913523)
                ·
                  refine ⟨14972203113408334999370285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9981468742272223332913523 14972203113408334999370285)
                  ·
                    refine ⟨5614576167528125624763857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14972203113408334999370285 5614576167528125624763857)
                    ·
                      refine ⟨4210932125646094218572893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5614576167528125624763857 4210932125646094218572893)
                      ·
                        rfl

theorem cell23_8200761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_8200761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200761 prefixEnd_8200761 := by exact prefixLift 8200761
  have htrace : WordTrace (prefixWord ++ tailWord_8200761) baseStart_8200761 baseEnd_8200761 := by
    simpa [prefixWord, tailWord_8200761, baseEnd_8200761] using wordTrace_append hprefix tailTrace_8200761
  have hstable : (prefixWord ++ tailWord_8200761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200761).length < 2 ^ (prefixWord ++ tailWord_8200761).sum := by decide
  have hdescent : baseEnd_8200761 < baseStart_8200761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200774 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_8200774 : Nat := 118140960795 + 8200774 * 2 ^ 59
def prefixEnd_8200774 : Nat := 4983230072969 + 3 ^ 40 * 8200774 * 2
def baseEnd_8200774 : Nat := 4210938800894602667710333

theorem tailTrace_8200774 : CollatzResearch.WordTrace tailWord_8200774 prefixEnd_8200774 4210938800894602667710333 := by
  unfold tailWord_8200774
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347087512250120423074543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199404533594669235692256917 9347087512250120423074543)
  ·
    refine ⟨14020631268375180634611815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9347087512250120423074543 14020631268375180634611815)
    ·
      refine ⟨21030946902562770951917723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14020631268375180634611815 21030946902562770951917723)
      ·
        refine ⟨31546420353844156427876585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21030946902562770951917723 31546420353844156427876585)
        ·
          refine ⟨23659815265383117320907439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31546420353844156427876585 23659815265383117320907439)
          ·
            refine ⟨35489722898074675981361159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23659815265383117320907439 35489722898074675981361159)
            ·
              refine ⟨53234584347112013972041739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35489722898074675981361159 53234584347112013972041739)
              ·
                refine ⟨79851876520668020958062609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53234584347112013972041739 79851876520668020958062609)
                ·
                  refine ⟨59888907390501015718546957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79851876520668020958062609 59888907390501015718546957)
                  ·
                    refine ⟨22458340271437880894455109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59888907390501015718546957 22458340271437880894455109)
                    ·
                      refine ⟨4210938800894602667710333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22458340271437880894455109 4210938800894602667710333)
                      ·
                        rfl

theorem cell23_8200774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_8200774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200774 prefixEnd_8200774 := by exact prefixLift 8200774
  have htrace : WordTrace (prefixWord ++ tailWord_8200774) baseStart_8200774 baseEnd_8200774 := by
    simpa [prefixWord, tailWord_8200774, baseEnd_8200774] using wordTrace_append hprefix tailTrace_8200774
  have hstable : (prefixWord ++ tailWord_8200774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200774).length < 2 ^ (prefixWord ++ tailWord_8200774).sum := by decide
  have hdescent : baseEnd_8200774 < baseStart_8200774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200780 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 7]
def baseStart_8200780 : Nat := 118140960795 + 8200780 * 2 ^ 59
def prefixEnd_8200780 : Nat := 4983230072969 + 3 ^ 40 * 8200780 * 2
def baseEnd_8200780 : Nat := 467882431308725516026145

theorem tailTrace_8200780 : CollatzResearch.WordTrace tailWord_8200780 prefixEnd_8200780 467882431308725516026145 := by
  unfold tailWord_8200780
  simp only [CollatzResearch.WordTrace]
  refine ⟨149553509614991058281551897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199404679486654744375402529 149553509614991058281551897)
  ·
    refine ⟨112165132211243293711163923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149553509614991058281551897 112165132211243293711163923)
    ·
      refine ⟨168247698316864940566745885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112165132211243293711163923 168247698316864940566745885)
      ·
        refine ⟨63092886868824352712529707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168247698316864940566745885 63092886868824352712529707)
        ·
          refine ⟨94639330303236529068794561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63092886868824352712529707 94639330303236529068794561)
          ·
            refine ⟨70979497727427396801595921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94639330303236529068794561 70979497727427396801595921)
            ·
              refine ⟨53234623295570547601196941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70979497727427396801595921 53234623295570547601196941)
              ·
                refine ⟨19962983735838955350448853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53234623295570547601196941 19962983735838955350448853)
                ·
                  refine ⟨467882431308725516026145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19962983735838955350448853 467882431308725516026145)
                  ·
                    rfl

theorem cell23_8200780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 7].length) (baseStart_8200780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200780 prefixEnd_8200780 := by exact prefixLift 8200780
  have htrace : WordTrace (prefixWord ++ tailWord_8200780) baseStart_8200780 baseEnd_8200780 := by
    simpa [prefixWord, tailWord_8200780, baseEnd_8200780] using wordTrace_append hprefix tailTrace_8200780
  have hstable : (prefixWord ++ tailWord_8200780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200780).length < 2 ^ (prefixWord ++ tailWord_8200780).sum := by decide
  have hdescent : baseEnd_8200780 < baseStart_8200780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200814 : List Nat := [4, 1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_8200814 : Nat := 118140960795 + 8200814 * 2 ^ 59
def prefixEnd_8200814 : Nat := 4983230072969 + 3 ^ 40 * 8200814 * 2
def baseEnd_8200814 : Nat := 467884371124531390134461

theorem tailTrace_8200814 : CollatzResearch.WordTrace tailWord_8200814 prefixEnd_8200814 467884371124531390134461 := by
  unfold tailWord_8200814
  simp only [CollatzResearch.WordTrace]
  refine ⟨37388532413982367546230187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199405506207905960246560997 37388532413982367546230187)
  ·
    refine ⟨56082798620973551319345281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37388532413982367546230187 56082798620973551319345281)
    ·
      refine ⟨42062098965730163489508961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56082798620973551319345281 42062098965730163489508961)
      ·
        refine ⟨31546574224297622617131721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42062098965730163489508961 31546574224297622617131721)
        ·
          refine ⟨23659930668223216962848791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31546574224297622617131721 23659930668223216962848791)
          ·
            refine ⟨35489896002334825444273187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23659930668223216962848791 35489896002334825444273187)
            ·
              refine ⟨53234844003502238166409781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35489896002334825444273187 53234844003502238166409781)
              ·
                refine ⟨4990766625328334828100917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53234844003502238166409781 4990766625328334828100917)
                ·
                  refine ⟨467884371124531390134461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4990766625328334828100917 467884371124531390134461)
                  ·
                    rfl

theorem cell23_8200814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_8200814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200814 prefixEnd_8200814 := by exact prefixLift 8200814
  have htrace : WordTrace (prefixWord ++ tailWord_8200814) baseStart_8200814 baseEnd_8200814 := by
    simpa [prefixWord, tailWord_8200814, baseEnd_8200814] using wordTrace_append hprefix tailTrace_8200814
  have hstable : (prefixWord ++ tailWord_8200814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200814).length < 2 ^ (prefixWord ++ tailWord_8200814).sum := by decide
  have hdescent : baseEnd_8200814 < baseStart_8200814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200857 : List Nat := [1, 2, 1, 2, 1, 2, 3, 4, 3, 4]
def baseStart_8200857 : Nat := 118140960795 + 8200857 * 2 ^ 59
def prefixEnd_8200857 : Nat := 4983230072969 + 3 ^ 40 * 8200857 * 2
def baseEnd_8200857 : Nat := 1403660473262975280990817

theorem tailTrace_8200857 : CollatzResearch.WordTrace tailWord_8200857 prefixEnd_8200857 1403660473262975280990817 := by
  unfold tailWord_8200857
  simp only [CollatzResearch.WordTrace]
  refine ⟨299109827650703158713656825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199406551767135439142437883 299109827650703158713656825)
  ·
    refine ⟨224332370738027369035242619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299109827650703158713656825 224332370738027369035242619)
    ·
      refine ⟨336498556107041053552863929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224332370738027369035242619 336498556107041053552863929)
      ·
        refine ⟨252373917080280790164647947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336498556107041053552863929 252373917080280790164647947)
        ·
          refine ⟨378560875620421185246971921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252373917080280790164647947 378560875620421185246971921)
          ·
            refine ⟨283920656715315888935228941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378560875620421185246971921 283920656715315888935228941)
            ·
              refine ⟨106470246268243458350710853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283920656715315888935228941 106470246268243458350710853)
              ·
                refine ⟨19963171175295648440758285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106470246268243458350710853 19963171175295648440758285)
                ·
                  refine ⟨7486189190735868165284357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19963171175295648440758285 7486189190735868165284357)
                  ·
                    refine ⟨1403660473262975280990817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7486189190735868165284357 1403660473262975280990817)
                    ·
                      rfl

theorem cell23_8200857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 4].length) (baseStart_8200857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200857 prefixEnd_8200857 := by exact prefixLift 8200857
  have htrace : WordTrace (prefixWord ++ tailWord_8200857) baseStart_8200857 baseEnd_8200857 := by
    simpa [prefixWord, tailWord_8200857, baseEnd_8200857] using wordTrace_append hprefix tailTrace_8200857
  have hstable : (prefixWord ++ tailWord_8200857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200857).length < 2 ^ (prefixWord ++ tailWord_8200857).sum := by decide
  have hdescent : baseEnd_8200857 < baseStart_8200857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200881 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 4]
def baseStart_8200881 : Nat := 118140960795 + 8200881 * 2 ^ 59
def prefixEnd_8200881 : Nat := 4983230072969 + 3 ^ 40 * 8200881 * 2
def baseEnd_8200881 : Nat := 4210993743324633749072341

theorem tailTrace_8200881 : CollatzResearch.WordTrace tailWord_8200881 prefixEnd_8200881 4210993743324633749072341 := by
  unfold tailWord_8200881
  simp only [CollatzResearch.WordTrace]
  refine ⟨299110703002616210812530497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199407135335077473875020331 299110703002616210812530497)
  ·
    refine ⟨224333027251962158109397873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299110703002616210812530497 224333027251962158109397873)
    ·
      refine ⟨168249770438971618582048405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224333027251962158109397873 168249770438971618582048405)
      ·
        refine ⟨7886707989326794621033519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168249770438971618582048405 7886707989326794621033519)
        ·
          refine ⟨11830061983990191931550279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7886707989326794621033519 11830061983990191931550279)
          ·
            refine ⟨17745092975985287897325419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11830061983990191931550279 17745092975985287897325419)
            ·
              refine ⟨26617639463977931845988129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17745092975985287897325419 26617639463977931845988129)
              ·
                refine ⟨19963229597983448884491097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26617639463977931845988129 19963229597983448884491097)
                ·
                  refine ⟨14972422198487586663368323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19963229597983448884491097 14972422198487586663368323)
                  ·
                    refine ⟨22458633297731379995052485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14972422198487586663368323 22458633297731379995052485)
                    ·
                      refine ⟨4210993743324633749072341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22458633297731379995052485 4210993743324633749072341)
                      ·
                        rfl

theorem cell23_8200881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_8200881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200881 prefixEnd_8200881 := by exact prefixLift 8200881
  have htrace : WordTrace (prefixWord ++ tailWord_8200881) baseStart_8200881 baseEnd_8200881 := by
    simpa [prefixWord, tailWord_8200881, baseEnd_8200881] using wordTrace_append hprefix tailTrace_8200881
  have hstable : (prefixWord ++ tailWord_8200881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200881).length < 2 ^ (prefixWord ++ tailWord_8200881).sum := by decide
  have hdescent : baseEnd_8200881 < baseStart_8200881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200904 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 6]
def baseStart_8200904 : Nat := 118140960795 + 8200904 * 2 ^ 59
def prefixEnd_8200904 : Nat := 4983230072969 + 3 ^ 40 * 8200904 * 2
def baseEnd_8200904 : Nat := 467889505931076351009415

theorem tailTrace_8200904 : CollatzResearch.WordTrace tailWord_8200904 prefixEnd_8200904 467889505931076351009415 := by
  unfold tailWord_8200904
  simp only [CollatzResearch.WordTrace]
  refine ⟨149555770940766442870308883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199407694587688590493745177 149555770940766442870308883)
  ·
    refine ⟨224333656411149664305463325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149555770940766442870308883 224333656411149664305463325)
    ·
      refine ⟨84125121154181124114548747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224333656411149664305463325 84125121154181124114548747)
      ·
        refine ⟨126187681731271686171823121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84125121154181124114548747 126187681731271686171823121)
        ·
          refine ⟨94640761298453764628867341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126187681731271686171823121 94640761298453764628867341)
          ·
            refine ⟨35490285486920161735825253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94640761298453764628867341 35490285486920161735825253)
            ·
              refine ⟨6654428528797530325467235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35490285486920161735825253 6654428528797530325467235)
              ·
                refine ⟨9981642793196295488200853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654428528797530325467235 9981642793196295488200853)
                ·
                  refine ⟨467889505931076351009415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9981642793196295488200853 467889505931076351009415)
                  ·
                    rfl

theorem cell23_8200904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 6].length) (baseStart_8200904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200904 prefixEnd_8200904 := by exact prefixLift 8200904
  have htrace : WordTrace (prefixWord ++ tailWord_8200904) baseStart_8200904 baseEnd_8200904 := by
    simpa [prefixWord, tailWord_8200904, baseEnd_8200904] using wordTrace_append hprefix tailTrace_8200904
  have hstable : (prefixWord ++ tailWord_8200904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200904).length < 2 ^ (prefixWord ++ tailWord_8200904).sum := by decide
  have hdescent : baseEnd_8200904 < baseStart_8200904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200941 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_8200941 : Nat := 118140960795 + 8200941 * 2 ^ 59
def prefixEnd_8200941 : Nat := 4983230072969 + 3 ^ 40 * 8200941 * 2
def baseEnd_8200941 : Nat := 4211024552163903514322065

theorem tailTrace_8200941 : CollatzResearch.WordTrace tailWord_8200941 prefixEnd_8200941 4211024552163903514322065 := by
  unfold tailWord_8200941
  simp only [CollatzResearch.WordTrace]
  refine ⟨299112891382398841059714677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199408594254932560706476451 299112891382398841059714677)
  ·
    refine ⟨28041833567099891349348251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299112891382398841059714677 28041833567099891349348251)
    ·
      refine ⟨42062750350649837024022377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28041833567099891349348251 42062750350649837024022377)
      ·
        refine ⟨31547062762987377768016783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42062750350649837024022377 31547062762987377768016783)
        ·
          refine ⟨47320594144481066652025175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31547062762987377768016783 47320594144481066652025175)
          ·
            refine ⟨70980891216721599978037763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47320594144481066652025175 70980891216721599978037763)
            ·
              refine ⟨106471336825082399967056645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70980891216721599978037763 106471336825082399967056645)
              ·
                refine ⟨19963375654702949993823121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106471336825082399967056645 19963375654702949993823121)
                ·
                  refine ⟨14972531741027212495367341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19963375654702949993823121 14972531741027212495367341)
                  ·
                    refine ⟨5614699402885204685762753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14972531741027212495367341 5614699402885204685762753)
                    ·
                      refine ⟨4211024552163903514322065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5614699402885204685762753 4211024552163903514322065)
                      ·
                        rfl

theorem cell23_8200941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_8200941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200941 prefixEnd_8200941 := by exact prefixLift 8200941
  have htrace : WordTrace (prefixWord ++ tailWord_8200941) baseStart_8200941 baseEnd_8200941 := by
    simpa [prefixWord, tailWord_8200941, baseEnd_8200941] using wordTrace_append hprefix tailTrace_8200941
  have hstable : (prefixWord ++ tailWord_8200941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200941).length < 2 ^ (prefixWord ++ tailWord_8200941).sum := by decide
  have hdescent : baseEnd_8200941 < baseStart_8200941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200957 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_8200957 : Nat := 118140960795 + 8200957 * 2 ^ 59
def prefixEnd_8200957 : Nat := 4983230072969 + 3 ^ 40 * 8200957 * 2
def baseEnd_8200957 : Nat := 4211032767854375451721991

theorem tailTrace_8200957 : CollatzResearch.WordTrace tailWord_8200957 prefixEnd_8200957 4211032767854375451721991 := by
  unfold tailWord_8200957
  simp only [CollatzResearch.WordTrace]
  refine ⟨299113474950340875792297125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199408983300227250528198083 299113474950340875792297125)
  ·
    refine ⟨56083776553188914211055711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299113474950340875792297125 56083776553188914211055711)
    ·
      refine ⟨84125664829783371316583567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56083776553188914211055711 84125664829783371316583567)
      ·
        refine ⟨126188497244675056974875351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84125664829783371316583567 126188497244675056974875351)
        ·
          refine ⟨189282745867012585462313027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126188497244675056974875351 189282745867012585462313027)
          ·
            refine ⟨283924118800518878193469541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189282745867012585462313027 283924118800518878193469541)
            ·
              refine ⟨53235772275097289661275539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 283924118800518878193469541 53235772275097289661275539)
              ·
                refine ⟨79853658412645934491913309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53235772275097289661275539 79853658412645934491913309)
                ·
                  refine ⟨29945121904742225434467491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79853658412645934491913309 29945121904742225434467491)
                  ·
                    refine ⟨44917682857113338151701237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29945121904742225434467491 44917682857113338151701237)
                    ·
                      refine ⟨4211032767854375451721991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44917682857113338151701237 4211032767854375451721991)
                      ·
                        rfl

theorem cell23_8200957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_8200957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200957 prefixEnd_8200957 := by exact prefixLift 8200957
  have htrace : WordTrace (prefixWord ++ tailWord_8200957) baseStart_8200957 baseEnd_8200957 := by
    simpa [prefixWord, tailWord_8200957, baseEnd_8200957] using wordTrace_append hprefix tailTrace_8200957
  have hstable : (prefixWord ++ tailWord_8200957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200957).length < 2 ^ (prefixWord ++ tailWord_8200957).sum := by decide
  have hdescent : baseEnd_8200957 < baseStart_8200957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200964 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_8200964 : Nat := 118140960795 + 8200964 * 2 ^ 59
def prefixEnd_8200964 : Nat := 4983230072969 + 3 ^ 40 * 8200964 * 2
def baseEnd_8200964 : Nat := 1403678787406318974778153

theorem tailTrace_8200964 : CollatzResearch.WordTrace tailWord_8200964 prefixEnd_8200964 1403678787406318974778153 := by
  unfold tailWord_8200964
  simp only [CollatzResearch.WordTrace]
  refine ⟨149556865130657757993900973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199409153507543677325201297 149556865130657757993900973)
  ·
    refine ⟨56083824423996659247712865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149556865130657757993900973 56083824423996659247712865)
    ·
      refine ⟨42062868317997494435784649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56083824423996659247712865 42062868317997494435784649)
      ·
        refine ⟨31547151238498120826838487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42062868317997494435784649 31547151238498120826838487)
        ·
          refine ⟨47320726857747181240257731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31547151238498120826838487 47320726857747181240257731)
          ·
            refine ⟨70981090286620771860386597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47320726857747181240257731 70981090286620771860386597)
            ·
              refine ⟨13308954428741394723822487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70981090286620771860386597 13308954428741394723822487)
              ·
                refine ⟨19963431643112092085733731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13308954428741394723822487 19963431643112092085733731)
                ·
                  refine ⟨29945147464668138128600597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19963431643112092085733731 29945147464668138128600597)
                  ·
                    refine ⟨1403678787406318974778153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29945147464668138128600597 1403678787406318974778153)
                    ·
                      rfl

theorem cell23_8200964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_8200964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200964 prefixEnd_8200964 := by exact prefixLift 8200964
  have htrace : WordTrace (prefixWord ++ tailWord_8200964) baseStart_8200964 baseEnd_8200964 := by
    simpa [prefixWord, tailWord_8200964, baseEnd_8200964] using wordTrace_append hprefix tailTrace_8200964
  have hstable : (prefixWord ++ tailWord_8200964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200964).length < 2 ^ (prefixWord ++ tailWord_8200964).sum := by decide
  have hdescent : baseEnd_8200964 < baseStart_8200964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200988 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 1, 1, 4]
def baseStart_8200988 : Nat := 118140960795 + 8200988 * 2 ^ 59
def prefixEnd_8200988 : Nat := 4983230072969 + 3 ^ 40 * 8200988 * 2
def baseEnd_8200988 : Nat := 4211048685754664830434349

theorem tailTrace_8200988 : CollatzResearch.WordTrace tailWord_8200988 prefixEnd_8200988 4211048685754664830434349 := by
  unfold tailWord_8200988
  simp only [CollatzResearch.WordTrace]
  refine ⟨149557302806614284043337809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199409737075485712057783745 149557302806614284043337809)
  ·
    refine ⟨112167977104960713032503357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149557302806614284043337809 112167977104960713032503357)
    ·
      refine ⟨42062991414360267387188759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112167977104960713032503357 42062991414360267387188759)
      ·
        refine ⟨63094487121540401080783139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42062991414360267387188759 63094487121540401080783139)
        ·
          refine ⟨94641730682310601621174709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63094487121540401080783139 94641730682310601621174709)
          ·
            refine ⟨8872662251466618901985129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94641730682310601621174709 8872662251466618901985129)
            ·
              refine ⟨6654496688599964176488847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8872662251466618901985129 6654496688599964176488847)
              ·
                refine ⟨9981745032899946264733271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654496688599964176488847 9981745032899946264733271)
                ·
                  refine ⟨14972617549349919397099907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9981745032899946264733271 14972617549349919397099907)
                  ·
                    refine ⟨22458926324024879095649861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14972617549349919397099907 22458926324024879095649861)
                    ·
                      refine ⟨4211048685754664830434349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22458926324024879095649861 4211048685754664830434349)
                      ·
                        rfl

theorem cell23_8200988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_8200988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200988 prefixEnd_8200988 := by exact prefixLift 8200988
  have htrace : WordTrace (prefixWord ++ tailWord_8200988) baseStart_8200988 baseEnd_8200988 := by
    simpa [prefixWord, tailWord_8200988, baseEnd_8200988] using wordTrace_append hprefix tailTrace_8200988
  have hstable : (prefixWord ++ tailWord_8200988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200988).length < 2 ^ (prefixWord ++ tailWord_8200988).sum := by decide
  have hdescent : baseEnd_8200988 < baseStart_8200988 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8200991 : List Nat := [1, 1, 2, 4, 2, 3, 1, 3, 1, 2, 3]
def baseStart_8200991 : Nat := 118140960795 + 8200991 * 2 ^ 59
def prefixEnd_8200991 : Nat := 4983230072969 + 3 ^ 40 * 8200991 * 2
def baseEnd_8200991 : Nat := 4211050226196628318696835

theorem tailTrace_8200991 : CollatzResearch.WordTrace tailWord_8200991 prefixEnd_8200991 4211050226196628318696835 := by
  unfold tailWord_8200991
  simp only [CollatzResearch.WordTrace]
  refine ⟨299114715032217699599034827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199409810021478466399356551 299114715032217699599034827)
  ·
    refine ⟨448672072548326549398552241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299114715032217699599034827 448672072548326549398552241)
    ·
      refine ⟨336504054411244912048914181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 448672072548326549398552241 336504054411244912048914181)
      ·
        refine ⟨63094510202108421009171409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336504054411244912048914181 63094510202108421009171409)
        ·
          refine ⟨47320882651581315756878557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63094510202108421009171409 47320882651581315756878557)
          ·
            refine ⟨17745330994342993408829459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47320882651581315756878557 17745330994342993408829459)
            ·
              refine ⟨26617996491514490113244189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17745330994342993408829459 26617996491514490113244189)
              ·
                refine ⟨9981748684317933792466571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26617996491514490113244189 9981748684317933792466571)
                ·
                  refine ⟨14972623026476900688699857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9981748684317933792466571 14972623026476900688699857)
                  ·
                    refine ⟨11229467269857675516524893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14972623026476900688699857 11229467269857675516524893)
                    ·
                      refine ⟨4211050226196628318696835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11229467269857675516524893 4211050226196628318696835)
                      ·
                        rfl

theorem cell23_8200991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_8200991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8200991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8200991 prefixEnd_8200991 := by exact prefixLift 8200991
  have htrace : WordTrace (prefixWord ++ tailWord_8200991) baseStart_8200991 baseEnd_8200991 := by
    simpa [prefixWord, tailWord_8200991, baseEnd_8200991] using wordTrace_append hprefix tailTrace_8200991
  have hstable : (prefixWord ++ tailWord_8200991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8200991).length < 2 ^ (prefixWord ++ tailWord_8200991).sum := by decide
  have hdescent : baseEnd_8200991 < baseStart_8200991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8200991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201018 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4]
def baseStart_8201018 : Nat := 118140960795 + 8201018 * 2 ^ 59
def prefixEnd_8201018 : Nat := 4983230072969 + 3 ^ 40 * 8201018 * 2
def baseEnd_8201018 : Nat := 4211064090174299713059211

theorem tailTrace_8201018 : CollatzResearch.WordTrace tailWord_8201018 prefixEnd_8201018 4211064090174299713059211 := by
  unfold tailWord_8201018
  simp only [CollatzResearch.WordTrace]
  refine ⟨74778924950779970802566927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199410466535413255473511805 74778924950779970802566927)
  ·
    refine ⟨112168387426169956203850391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74778924950779970802566927 112168387426169956203850391)
    ·
      refine ⟨168252581139254934305775587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112168387426169956203850391 168252581139254934305775587)
      ·
        refine ⟨252378871708882401458663381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168252581139254934305775587 252378871708882401458663381)
        ·
          refine ⟨5915129805676931284187423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 252378871708882401458663381 5915129805676931284187423)
          ·
            refine ⟨8872694708515396926281135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915129805676931284187423 8872694708515396926281135)
            ·
              refine ⟨13309042062773095389421703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872694708515396926281135 13309042062773095389421703)
              ·
                refine ⟨19963563094159643084132555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13309042062773095389421703 19963563094159643084132555)
                ·
                  refine ⟨29945344641239464626198833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19963563094159643084132555 29945344641239464626198833)
                  ·
                    refine ⟨22459008480929598469649125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29945344641239464626198833 22459008480929598469649125)
                    ·
                      refine ⟨4211064090174299713059211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22459008480929598469649125 4211064090174299713059211)
                      ·
                        rfl

theorem cell23_8201018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 1, 2, 4].length) (baseStart_8201018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201018 prefixEnd_8201018 := by exact prefixLift 8201018
  have htrace : WordTrace (prefixWord ++ tailWord_8201018) baseStart_8201018 baseEnd_8201018 := by
    simpa [prefixWord, tailWord_8201018, baseEnd_8201018] using wordTrace_append hprefix tailTrace_8201018
  have hstable : (prefixWord ++ tailWord_8201018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201018).length < 2 ^ (prefixWord ++ tailWord_8201018).sum := by decide
  have hdescent : baseEnd_8201018 < baseStart_8201018 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201025 : List Nat := [1, 2, 5, 3, 1, 1, 2, 2, 1, 2, 3]
def baseStart_8201025 : Nat := 118140960795 + 8201025 * 2 ^ 59
def prefixEnd_8201025 : Nat := 4983230072969 + 3 ^ 40 * 8201025 * 2
def baseEnd_8201025 : Nat := 4211067684538881185671679

theorem tailTrace_8201025 : CollatzResearch.WordTrace tailWord_8201025 prefixEnd_8201025 4211067684538881185671679 := by
  unfold tailWord_8201025
  simp only [CollatzResearch.WordTrace]
  refine ⟨299115955114094523405772529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199410636742729682270515019 299115955114094523405772529)
  ·
    refine ⟨224336966335570892554329397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299115955114094523405772529 224336966335570892554329397)
    ·
      refine ⟨21031590593959771176968381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224336966335570892554329397 21031590593959771176968381)
      ·
        refine ⟨7886846472734914191363143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21031590593959771176968381 7886846472734914191363143)
        ·
          refine ⟨11830269709102371287044715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7886846472734914191363143 11830269709102371287044715)
          ·
            refine ⟨17745404563653556930567073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11830269709102371287044715 17745404563653556930567073)
            ·
              refine ⟨13309053422740167697925305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17745404563653556930567073 13309053422740167697925305)
              ·
                refine ⟨9981790067055125773443979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13309053422740167697925305 9981790067055125773443979)
                ·
                  refine ⟨14972685100582688660165969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9981790067055125773443979 14972685100582688660165969)
                  ·
                    refine ⟨11229513825437016495124477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14972685100582688660165969 11229513825437016495124477)
                    ·
                      refine ⟨4211067684538881185671679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11229513825437016495124477 4211067684538881185671679)
                      ·
                        rfl

theorem cell23_8201025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_8201025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201025 prefixEnd_8201025 := by exact prefixLift 8201025
  have htrace : WordTrace (prefixWord ++ tailWord_8201025) baseStart_8201025 baseEnd_8201025 := by
    simpa [prefixWord, tailWord_8201025, baseEnd_8201025] using wordTrace_append hprefix tailTrace_8201025
  have hstable : (prefixWord ++ tailWord_8201025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201025).length < 2 ^ (prefixWord ++ tailWord_8201025).sum := by decide
  have hdescent : baseEnd_8201025 < baseStart_8201025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201057 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 6]
def baseStart_8201057 : Nat := 118140960795 + 8201057 * 2 ^ 59
def prefixEnd_8201057 : Nat := 4983230072969 + 3 ^ 40 * 8201057 * 2
def baseEnd_8201057 : Nat := 4211084115919825060471531

theorem tailTrace_8201057 : CollatzResearch.WordTrace tailWord_8201057 prefixEnd_8201057 4211084115919825060471531 := by
  unfold tailWord_8201057
  simp only [CollatzResearch.WordTrace]
  refine ⟨299117122249978592870937425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199411414833319061913958283 299117122249978592870937425)
  ·
    refine ⟨224337841687483944653203069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299117122249978592870937425 224337841687483944653203069)
    ·
      refine ⟨84126690632806479244951151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224337841687483944653203069 84126690632806479244951151)
      ·
        refine ⟨126190035949209718867426727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84126690632806479244951151 126190035949209718867426727)
        ·
          refine ⟨189285053923814578301140091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126190035949209718867426727 189285053923814578301140091)
          ·
            refine ⟨283927580885721867451710137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189285053923814578301140091 283927580885721867451710137)
            ·
              refine ⟨212945685664291400588782603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283927580885721867451710137 212945685664291400588782603)
              ·
                refine ⟨319418528496437100883173905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212945685664291400588782603 319418528496437100883173905)
                ·
                  refine ⟨239563896372327825662380429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319418528496437100883173905 239563896372327825662380429)
                  ·
                    refine ⟨89836461139622934623392661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239563896372327825662380429 89836461139622934623392661)
                    ·
                      refine ⟨4211084115919825060471531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89836461139622934623392661 4211084115919825060471531)
                      ·
                        rfl

theorem cell23_8201057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_8201057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201057 prefixEnd_8201057 := by exact prefixLift 8201057
  have htrace : WordTrace (prefixWord ++ tailWord_8201057) baseStart_8201057 baseEnd_8201057 := by
    simpa [prefixWord, tailWord_8201057, baseEnd_8201057] using wordTrace_append hprefix tailTrace_8201057
  have hstable : (prefixWord ++ tailWord_8201057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201057).length < 2 ^ (prefixWord ++ tailWord_8201057).sum := by decide
  have hdescent : baseEnd_8201057 < baseStart_8201057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201074 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_8201074 : Nat := 118140960795 + 8201074 * 2 ^ 59
def prefixEnd_8201074 : Nat := 4983230072969 + 3 ^ 40 * 8201074 * 2
def baseEnd_8201074 : Nat := 4211092845090951493958953

theorem tailTrace_8201074 : CollatzResearch.WordTrace tailWord_8201074 prefixEnd_8201074 4211092845090951493958953 := by
  unfold tailWord_8201074
  simp only [CollatzResearch.WordTrace]
  refine ⟨74779435572729251193576569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199411828193944669849537517 74779435572729251193576569)
  ·
    refine ⟨56084576679546938395182427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74779435572729251193576569 56084576679546938395182427)
    ·
      refine ⟨84126865019320407592773641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56084576679546938395182427 84126865019320407592773641)
      ·
        refine ⟨63095148764490305694580231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84126865019320407592773641 63095148764490305694580231)
        ·
          refine ⟨94642723146735458541870347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63095148764490305694580231 94642723146735458541870347)
          ·
            refine ⟨141964084720103187812805521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94642723146735458541870347 141964084720103187812805521)
            ·
              refine ⟨106473063540077390859604141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141964084720103187812805521 106473063540077390859604141)
              ·
                refine ⟨39927398827529021572351553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106473063540077390859604141 39927398827529021572351553)
                ·
                  refine ⟨29945549120646766179263665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39927398827529021572351553 29945549120646766179263665)
                  ·
                    refine ⟨22459161840485074634447749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29945549120646766179263665 22459161840485074634447749)
                    ·
                      refine ⟨4211092845090951493958953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22459161840485074634447749 4211092845090951493958953)
                      ·
                        rfl

theorem cell23_8201074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_8201074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201074 prefixEnd_8201074 := by exact prefixLift 8201074
  have htrace : WordTrace (prefixWord ++ tailWord_8201074) baseStart_8201074 baseEnd_8201074 := by
    simpa [prefixWord, tailWord_8201074, baseEnd_8201074] using wordTrace_append hprefix tailTrace_8201074
  have hstable : (prefixWord ++ tailWord_8201074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201074).length < 2 ^ (prefixWord ++ tailWord_8201074).sum := by decide
  have hdescent : baseEnd_8201074 < baseStart_8201074 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201124 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_8201124 : Nat := 118140960795 + 8201124 * 2 ^ 59
def prefixEnd_8201124 : Nat := 4983230072969 + 3 ^ 40 * 8201124 * 2
def baseEnd_8201124 : Nat := 4211118519123676298333723

theorem tailTrace_8201124 : CollatzResearch.WordTrace tailWord_8201124 prefixEnd_8201124 4211118519123676298333723 := by
  unfold tailWord_8201124
  simp only [CollatzResearch.WordTrace]
  refine ⟨149559782970367931656813213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199413043960490575542417617 149559782970367931656813213)
  ·
    refine ⟨56084918613887974371304955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149559782970367931656813213 56084918613887974371304955)
    ·
      refine ⟨84127377920831961556957433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56084918613887974371304955 84127377920831961556957433)
      ·
        refine ⟨63095533440623971167718075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84127377920831961556957433 63095533440623971167718075)
        ·
          refine ⟨94643300160935956751577113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63095533440623971167718075 94643300160935956751577113)
          ·
            refine ⟨70982475120701967563682835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94643300160935956751577113 70982475120701967563682835)
            ·
              refine ⟨106473712681052951345524253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70982475120701967563682835 106473712681052951345524253)
              ·
                refine ⟨39927642255394856754571595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106473712681052951345524253 39927642255394856754571595)
                ·
                  refine ⟨59891463383092285131857393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39927642255394856754571595 59891463383092285131857393)
                  ·
                    refine ⟨44918597537319213848893045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59891463383092285131857393 44918597537319213848893045)
                    ·
                      refine ⟨4211118519123676298333723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44918597537319213848893045 4211118519123676298333723)
                      ·
                        rfl

theorem cell23_8201124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_8201124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201124 prefixEnd_8201124 := by exact prefixLift 8201124
  have htrace : WordTrace (prefixWord ++ tailWord_8201124) baseStart_8201124 baseEnd_8201124 := by
    simpa [prefixWord, tailWord_8201124, baseEnd_8201124] using wordTrace_append hprefix tailTrace_8201124
  have hstable : (prefixWord ++ tailWord_8201124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201124).length < 2 ^ (prefixWord ++ tailWord_8201124).sum := by decide
  have hdescent : baseEnd_8201124 < baseStart_8201124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201164 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_8201164 : Nat := 118140960795 + 8201164 * 2 ^ 59
def prefixEnd_8201164 : Nat := 4983230072969 + 3 ^ 40 * 8201164 * 2
def baseEnd_8201164 : Nat := 4211139058349856141833539

theorem tailTrace_8201164 : CollatzResearch.WordTrace tailWord_8201164 prefixEnd_8201164 4211139058349856141833539 := by
  unfold tailWord_8201164
  simp only [CollatzResearch.WordTrace]
  refine ⟨149560512430295475072541273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199414016573727300096721697 149560512430295475072541273)
  ·
    refine ⟨112170384322721606304405955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149560512430295475072541273 112170384322721606304405955)
    ·
      refine ⟨168255576484082409456608933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112170384322721606304405955 168255576484082409456608933)
      ·
        refine ⟨31547920590765451773114175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168255576484082409456608933 31547920590765451773114175)
        ·
          refine ⟨47321880886148177659671263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31547920590765451773114175 47321880886148177659671263)
          ·
            refine ⟨70982821329222266489506895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47321880886148177659671263 70982821329222266489506895)
            ·
              refine ⟨106474231993833399734260343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70982821329222266489506895 106474231993833399734260343)
              ·
                refine ⟨159711347990750099601390515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106474231993833399734260343 159711347990750099601390515)
                ·
                  refine ⟨239567021986125149402085773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159711347990750099601390515 239567021986125149402085773)
                  ·
                    refine ⟨89837633244796931025782165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 239567021986125149402085773 89837633244796931025782165)
                    ·
                      refine ⟨4211139058349856141833539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89837633244796931025782165 4211139058349856141833539)
                      ·
                        rfl

theorem cell23_8201164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_8201164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201164 prefixEnd_8201164 := by exact prefixLift 8201164
  have htrace : WordTrace (prefixWord ++ tailWord_8201164) baseStart_8201164 baseEnd_8201164 := by
    simpa [prefixWord, tailWord_8201164, baseEnd_8201164] using wordTrace_append hprefix tailTrace_8201164
  have hstable : (prefixWord ++ tailWord_8201164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201164).length < 2 ^ (prefixWord ++ tailWord_8201164).sum := by decide
  have hdescent : baseEnd_8201164 < baseStart_8201164 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201178 : List Nat := [3, 1, 1, 2, 4, 2, 2, 1, 3, 4]
def baseStart_8201178 : Nat := 118140960795 + 8201178 * 2 ^ 59
def prefixEnd_8201178 : Nat := 4983230072969 + 3 ^ 40 * 8201178 * 2
def baseEnd_8201178 : Nat := 1403715415693006362352825

theorem tailTrace_8201178 : CollatzResearch.WordTrace tailWord_8201178 prefixEnd_8201178 1403715415693006362352825 := by
  unfold tailWord_8201178
  simp only [CollatzResearch.WordTrace]
  refine ⟨74780383870635057634023047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199414356988360153690728125 74780383870635057634023047)
  ·
    refine ⟨112170575805952586451034571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74780383870635057634023047 112170575805952586451034571)
    ·
      refine ⟨168255863708928879676551857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112170575805952586451034571 168255863708928879676551857)
      ·
        refine ⟨126191897781696659757413893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168255863708928879676551857 126191897781696659757413893)
        ·
          refine ⟨23660980834068123704515105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126191897781696659757413893 23660980834068123704515105)
          ·
            refine ⟨17745735625551092778386329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23660980834068123704515105 17745735625551092778386329)
            ·
              refine ⟨13309301719163319583789747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17745735625551092778386329 13309301719163319583789747)
              ·
                refine ⟨19963952578744979375684621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13309301719163319583789747 19963952578744979375684621)
                ·
                  refine ⟨7486482217029367265881733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19963952578744979375684621 7486482217029367265881733)
                  ·
                    refine ⟨1403715415693006362352825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7486482217029367265881733 1403715415693006362352825)
                    ·
                      rfl

theorem cell23_8201178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_8201178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201178 prefixEnd_8201178 := by exact prefixLift 8201178
  have htrace : WordTrace (prefixWord ++ tailWord_8201178) baseStart_8201178 baseEnd_8201178 := by
    simpa [prefixWord, tailWord_8201178, baseEnd_8201178] using wordTrace_append hprefix tailTrace_8201178
  have hstable : (prefixWord ++ tailWord_8201178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201178).length < 2 ^ (prefixWord ++ tailWord_8201178).sum := by decide
  have hdescent : baseEnd_8201178 < baseStart_8201178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201221 : List Nat := [1, 3, 1, 1, 2, 3, 1, 5, 1, 5]
def baseStart_8201221 : Nat := 118140960795 + 8201221 * 2 ^ 59
def prefixEnd_8201221 : Nat := 4983230072969 + 3 ^ 40 * 8201221 * 2
def baseEnd_8201221 : Nat := 1403722775582387472940259

theorem tailTrace_8201221 : CollatzResearch.WordTrace tailWord_8201221 prefixEnd_8201221 1403722775582387472940259 := by
  unfold tailWord_8201221
  simp only [CollatzResearch.WordTrace]
  refine ⟨299123103821384448879907517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199415402547589632586605011 299123103821384448879907517)
  ·
    refine ⟨112171163933019168329965319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299123103821384448879907517 112171163933019168329965319)
    ·
      refine ⟨168256745899528752494947979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112171163933019168329965319 168256745899528752494947979)
      ·
        refine ⟨252385118849293128742421969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168256745899528752494947979 252385118849293128742421969)
        ·
          refine ⟨189288839136969846556816477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252385118849293128742421969 189288839136969846556816477)
          ·
            refine ⟨70983314676363692458806179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189288839136969846556816477 70983314676363692458806179)
            ·
              refine ⟨106474972014545538688209269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70983314676363692458806179 106474972014545538688209269)
              ·
                refine ⟨9982028626363644252019619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106474972014545538688209269 9982028626363644252019619)
                ·
                  refine ⟨14973042939545466378029429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9982028626363644252019619 14973042939545466378029429)
                  ·
                    refine ⟨1403722775582387472940259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14973042939545466378029429 1403722775582387472940259)
                    ·
                      rfl

theorem cell23_8201221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_8201221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201221 prefixEnd_8201221 := by exact prefixLift 8201221
  have htrace : WordTrace (prefixWord ++ tailWord_8201221) baseStart_8201221 baseEnd_8201221 := by
    simpa [prefixWord, tailWord_8201221, baseEnd_8201221] using wordTrace_append hprefix tailTrace_8201221
  have hstable : (prefixWord ++ tailWord_8201221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201221).length < 2 ^ (prefixWord ++ tailWord_8201221).sum := by decide
  have hdescent : baseEnd_8201221 < baseStart_8201221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201228 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 4, 3, 2]
def baseStart_8201228 : Nat := 118140960795 + 8201228 * 2 ^ 59
def prefixEnd_8201228 : Nat := 4983230072969 + 3 ^ 40 * 8201228 * 2
def baseEnd_8201228 : Nat := 4211171921111743891433245

theorem tailTrace_8201228 : CollatzResearch.WordTrace tailWord_8201228 prefixEnd_8201228 4211171921111743891433245 := by
  unfold tailWord_8201228
  simp only [CollatzResearch.WordTrace]
  refine ⟨149561679566179544537706169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199415572754906059383608225 149561679566179544537706169)
  ·
    refine ⟨112171259674634658403279627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149561679566179544537706169 112171259674634658403279627)
    ·
      refine ⟨168256889511951987604919441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112171259674634658403279627 168256889511951987604919441)
      ·
        refine ⟨126192667133963990703689581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168256889511951987604919441 126192667133963990703689581)
        ·
          refine ⟨47322250175236496513883593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126192667133963990703689581 47322250175236496513883593)
          ·
            refine ⟨35491687631427372385412695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47322250175236496513883593 35491687631427372385412695)
            ·
              refine ⟨53237531447141058578119043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35491687631427372385412695 53237531447141058578119043)
              ·
                refine ⟨79856297170711587867178565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53237531447141058578119043 79856297170711587867178565)
                ·
                  refine ⟨14973055719508422725095981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79856297170711587867178565 14973055719508422725095981)
                  ·
                    refine ⟨5614895894815658521910993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14973055719508422725095981 5614895894815658521910993)
                    ·
                      refine ⟨4211171921111743891433245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5614895894815658521910993 4211171921111743891433245)
                      ·
                        rfl

theorem cell23_8201228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_8201228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201228 prefixEnd_8201228 := by exact prefixLift 8201228
  have htrace : WordTrace (prefixWord ++ tailWord_8201228) baseStart_8201228 baseEnd_8201228 := by
    simpa [prefixWord, tailWord_8201228, baseEnd_8201228] using wordTrace_append hprefix tailTrace_8201228
  have hstable : (prefixWord ++ tailWord_8201228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201228).length < 2 ^ (prefixWord ++ tailWord_8201228).sum := by decide
  have hdescent : baseEnd_8201228 < baseStart_8201228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201255 : List Nat := [1, 1, 7, 1, 1, 1, 3, 2, 1, 5]
def baseStart_8201255 : Nat := 118140960795 + 8201255 * 2 ^ 59
def prefixEnd_8201255 : Nat := 4983230072969 + 3 ^ 40 * 8201255 * 2
def baseEnd_8201255 : Nat := 1403728595029805095265207

theorem tailTrace_8201255 : CollatzResearch.WordTrace tailWord_8201255 prefixEnd_8201255 1403728595029805095265207 := by
  unfold tailWord_8201255
  simp only [CollatzResearch.WordTrace]
  refine ⟨299124343903261272686645219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199416229268840848457763479 299124343903261272686645219)
  ·
    refine ⟨448686515854891909029967829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299124343903261272686645219 448686515854891909029967829)
    ·
      refine ⟨10516090215349029117889871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 448686515854891909029967829 10516090215349029117889871)
      ·
        refine ⟨15774135323023543676834807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10516090215349029117889871 15774135323023543676834807)
        ·
          refine ⟨23661202984535315515252211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15774135323023543676834807 23661202984535315515252211)
          ·
            refine ⟨35491804476802973272878317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23661202984535315515252211 35491804476802973272878317)
            ·
              refine ⟨13309426678801114977329369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35491804476802973272878317 13309426678801114977329369)
              ·
                refine ⟨9982070009100836232997027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13309426678801114977329369 9982070009100836232997027)
                ·
                  refine ⟨14973105013651254349495541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9982070009100836232997027 14973105013651254349495541)
                  ·
                    refine ⟨1403728595029805095265207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14973105013651254349495541 1403728595029805095265207)
                    ·
                      rfl

theorem cell23_8201255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_8201255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201255 prefixEnd_8201255 := by exact prefixLift 8201255
  have htrace : WordTrace (prefixWord ++ tailWord_8201255) baseStart_8201255 baseEnd_8201255 := by
    simpa [prefixWord, tailWord_8201255, baseEnd_8201255] using wordTrace_append hprefix tailTrace_8201255
  have hstable : (prefixWord ++ tailWord_8201255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201255).length < 2 ^ (prefixWord ++ tailWord_8201255).sum := by decide
  have hdescent : baseEnd_8201255 < baseStart_8201255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201264 : List Nat := [2, 1, 1, 1, 2, 4, 1, 11]
def baseStart_8201264 : Nat := 118140960795 + 8201264 * 2 ^ 59
def prefixEnd_8201264 : Nat := 4983230072969 + 3 ^ 40 * 8201264 * 2
def baseEnd_8201264 : Nat := 155970015052418731503077

theorem tailTrace_8201264 : CollatzResearch.WordTrace tailWord_8201264 prefixEnd_8201264 155970015052418731503077 := by
  unfold tailWord_8201264
  simp only [CollatzResearch.WordTrace]
  refine ⟨149562336080114333611861423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199416448106819111482481897 149562336080114333611861423)
  ·
    refine ⟨224343504120171500417792135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149562336080114333611861423 224343504120171500417792135)
    ·
      refine ⟨336515256180257250626688203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224343504120171500417792135 336515256180257250626688203)
      ·
        refine ⟨504772884270385875940032305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336515256180257250626688203 504772884270385875940032305)
        ·
          refine ⟨378579663202789406955024229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504772884270385875940032305 378579663202789406955024229)
          ·
            refine ⟨70983686850523013804067043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378579663202789406955024229 70983686850523013804067043)
            ·
              refine ⟨106475530275784520706100565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70983686850523013804067043 106475530275784520706100565)
              ·
                refine ⟨155970015052418731503077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 106475530275784520706100565 155970015052418731503077)
                ·
                  rfl

theorem cell23_8201264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 11].length) (baseStart_8201264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201264 prefixEnd_8201264 := by exact prefixLift 8201264
  have htrace : WordTrace (prefixWord ++ tailWord_8201264) baseStart_8201264 baseEnd_8201264 := by
    simpa [prefixWord, tailWord_8201264, baseEnd_8201264] using wordTrace_append hprefix tailTrace_8201264
  have hstable : (prefixWord ++ tailWord_8201264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201264).length < 2 ^ (prefixWord ++ tailWord_8201264).sum := by decide
  have hdescent : baseEnd_8201264 < baseStart_8201264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201268 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_8201268 : Nat := 118140960795 + 8201268 * 2 ^ 59
def prefixEnd_8201268 : Nat := 4983230072969 + 3 ^ 40 * 8201268 * 2
def baseEnd_8201268 : Nat := 1403730820112641244977687

theorem tailTrace_8201268 : CollatzResearch.WordTrace tailWord_8201268 prefixEnd_8201268 1403730820112641244977687 := by
  unfold tailWord_8201268
  simp only [CollatzResearch.WordTrace]
  refine ⟨149562409026107087953434229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199416545368142783937912305 149562409026107087953434229)
  ·
    refine ⟨14021475846197539495634459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149562409026107087953434229 14021475846197539495634459)
    ·
      refine ⟨21032213769296309243451689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14021475846197539495634459 21032213769296309243451689)
      ·
        refine ⟨15774160326972231932588767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21032213769296309243451689 15774160326972231932588767)
        ·
          refine ⟨23661240490458347898883151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15774160326972231932588767 23661240490458347898883151)
          ·
            refine ⟨35491860735687521848324727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23661240490458347898883151 35491860735687521848324727)
            ·
              refine ⟨53237791103531282772487091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35491860735687521848324727 53237791103531282772487091)
              ·
                refine ⟨79856686655296924158730637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53237791103531282772487091 79856686655296924158730637)
                ·
                  refine ⟨29946257495736346559523989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79856686655296924158730637 29946257495736346559523989)
                  ·
                    refine ⟨1403730820112641244977687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29946257495736346559523989 1403730820112641244977687)
                    ·
                      rfl

theorem cell23_8201268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_8201268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201268 prefixEnd_8201268 := by exact prefixLift 8201268
  have htrace : WordTrace (prefixWord ++ tailWord_8201268) baseStart_8201268 baseEnd_8201268 := by
    simpa [prefixWord, tailWord_8201268, baseEnd_8201268] using wordTrace_append hprefix tailTrace_8201268
  have hstable : (prefixWord ++ tailWord_8201268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201268).length < 2 ^ (prefixWord ++ tailWord_8201268).sum := by decide
  have hdescent : baseEnd_8201268 < baseStart_8201268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201281 : List Nat := [1, 2, 5, 1, 3, 11]
def baseStart_8201281 : Nat := 118140960795 + 8201281 * 2 ^ 59
def prefixEnd_8201281 : Nat := 4983230072969 + 3 ^ 40 * 8201281 * 2
def baseEnd_8201281 : Nat := 17330037595005893761607

theorem tailTrace_8201281 : CollatzResearch.WordTrace tailWord_8201281 prefixEnd_8201281 17330037595005893761607 := by
  unfold tailWord_8201281
  simp only [CollatzResearch.WordTrace]
  refine ⟨299125292201167079127091697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199416861467444719418061131 299125292201167079127091697)
  ·
    refine ⟨224343969150875309345318773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299125292201167079127091697 224343969150875309345318773)
    ·
      refine ⟨21032247107894560251123635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224343969150875309345318773 21032247107894560251123635)
      ·
        refine ⟨31548370661841840376685453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21032247107894560251123635 31548370661841840376685453)
        ·
          refine ⟨11830638998190690141257045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31548370661841840376685453 11830638998190690141257045)
          ·
            refine ⟨17330037595005893761607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11830638998190690141257045 17330037595005893761607)
            ·
              rfl

theorem cell23_8201281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 11].length) (baseStart_8201281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201281 prefixEnd_8201281 := by exact prefixLift 8201281
  have htrace : WordTrace (prefixWord ++ tailWord_8201281) baseStart_8201281 baseEnd_8201281 := by
    simpa [prefixWord, tailWord_8201281, baseEnd_8201281] using wordTrace_append hprefix tailTrace_8201281
  have hstable : (prefixWord ++ tailWord_8201281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201281).length < 2 ^ (prefixWord ++ tailWord_8201281).sum := by decide
  have hdescent : baseEnd_8201281 < baseStart_8201281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201286 : List Nat := [6, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_8201286 : Nat := 118140960795 + 8201286 * 2 ^ 59
def prefixEnd_8201286 : Nat := 4983230072969 + 3 ^ 40 * 8201286 * 2
def baseEnd_8201286 : Nat := 4211201702989704664507979

theorem tailTrace_8201286 : CollatzResearch.WordTrace tailWord_8201286 prefixEnd_8201286 4211201702989704664507979 := by
  unfold tailWord_8201286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347671080192155155656991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 199416983044099309987349141 9347671080192155155656991)
  ·
    refine ⟨14021506620288232733485487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9347671080192155155656991 14021506620288232733485487)
    ·
      refine ⟨21032259930432349100228231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14021506620288232733485487 21032259930432349100228231)
      ·
        refine ⟨31548389895648523650342347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21032259930432349100228231 31548389895648523650342347)
        ·
          refine ⟨47322584843472785475513521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31548389895648523650342347 47322584843472785475513521)
          ·
            refine ⟨35491938632604589106635141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47322584843472785475513521 35491938632604589106635141)
            ·
              refine ⟨6654738493613360457494089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35491938632604589106635141 6654738493613360457494089)
              ·
                refine ⟨4991053870210020343120567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6654738493613360457494089 4991053870210020343120567)
                ·
                  refine ⟨7486580805315030514680851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991053870210020343120567 7486580805315030514680851)
                  ·
                    refine ⟨11229871207972545772021277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7486580805315030514680851 11229871207972545772021277)
                    ·
                      refine ⟨4211201702989704664507979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11229871207972545772021277 4211201702989704664507979)
                      ·
                        rfl

theorem cell23_8201286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_8201286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201286 prefixEnd_8201286 := by exact prefixLift 8201286
  have htrace : WordTrace (prefixWord ++ tailWord_8201286) baseStart_8201286 baseEnd_8201286 := by
    simpa [prefixWord, tailWord_8201286, baseEnd_8201286] using wordTrace_append hprefix tailTrace_8201286
  have hstable : (prefixWord ++ tailWord_8201286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201286).length < 2 ^ (prefixWord ++ tailWord_8201286).sum := by decide
  have hdescent : baseEnd_8201286 < baseStart_8201286 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201298 : List Nat := [3, 2, 2, 1, 3, 3, 1, 8]
def baseStart_8201298 : Nat := 118140960795 + 8201298 * 2 ^ 59
def prefixEnd_8201298 : Nat := 4983230072969 + 3 ^ 40 * 8201298 * 2
def baseEnd_8201298 : Nat := 155970661657687356205849

theorem tailTrace_8201298 : CollatzResearch.WordTrace tailWord_8201298 prefixEnd_8201298 155970661657687356205849 := by
  unfold tailWord_8201298
  simp only [CollatzResearch.WordTrace]
  refine ⟨74781478060526372757615137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199417274828070327353640365 74781478060526372757615137)
  ·
    refine ⟨56086108545394779568211353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74781478060526372757615137 56086108545394779568211353)
    ·
      refine ⟨42064581409046084676158515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56086108545394779568211353 42064581409046084676158515)
      ·
        refine ⟨63096872113569127014237773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42064581409046084676158515 63096872113569127014237773)
        ·
          refine ⟨23661327042588422630339165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63096872113569127014237773 23661327042588422630339165)
          ·
            refine ⟨8872997640970658486377187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23661327042588422630339165 8872997640970658486377187)
            ·
              refine ⟨13309496461455987729565781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872997640970658486377187 13309496461455987729565781)
              ·
                refine ⟨155970661657687356205849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13309496461455987729565781 155970661657687356205849)
                ·
                  rfl

theorem cell23_8201298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 8].length) (baseStart_8201298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201298 prefixEnd_8201298 := by exact prefixLift 8201298
  have htrace : WordTrace (prefixWord ++ tailWord_8201298) baseStart_8201298 baseEnd_8201298 := by
    simpa [prefixWord, tailWord_8201298, baseEnd_8201298] using wordTrace_append hprefix tailTrace_8201298
  have hstable : (prefixWord ++ tailWord_8201298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201298).length < 2 ^ (prefixWord ++ tailWord_8201298).sum := by decide
  have hdescent : baseEnd_8201298 < baseStart_8201298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201302 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_8201302 : Nat := 118140960795 + 8201302 * 2 ^ 59
def prefixEnd_8201302 : Nat := 4983230072969 + 3 ^ 40 * 8201302 * 2
def baseEnd_8201302 : Nat := 1403736639560058867302635

theorem tailTrace_8201302 : CollatzResearch.WordTrace tailWord_8201302 prefixEnd_8201302 1403736639560058867302635 := by
  unfold tailWord_8201302
  simp only [CollatzResearch.WordTrace]
  refine ⟨18695378633380687482100385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199417372089393999809070773 18695378633380687482100385)
  ·
    refine ⟨14021533975035515611575289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18695378633380687482100385 14021533975035515611575289)
    ·
      refine ⟨10516150481276636708681467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14021533975035515611575289 10516150481276636708681467)
      ·
        refine ⟨15774225721914955063022201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10516150481276636708681467 15774225721914955063022201)
        ·
          refine ⟨11830669291436216297266651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15774225721914955063022201 11830669291436216297266651)
          ·
            refine ⟨17746003937154324445899977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11830669291436216297266651 17746003937154324445899977)
            ·
              refine ⟨13309502952865743334424983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17746003937154324445899977 13309502952865743334424983)
              ·
                refine ⟨19964254429298615001637475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13309502952865743334424983 19964254429298615001637475)
                ·
                  refine ⟨29946381643947922502456213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19964254429298615001637475 29946381643947922502456213)
                  ·
                    refine ⟨1403736639560058867302635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29946381643947922502456213 1403736639560058867302635)
                    ·
                      rfl

theorem cell23_8201302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_8201302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201302 prefixEnd_8201302 := by exact prefixLift 8201302
  have htrace : WordTrace (prefixWord ++ tailWord_8201302) baseStart_8201302 baseEnd_8201302 := by
    simpa [prefixWord, tailWord_8201302, baseEnd_8201302] using wordTrace_append hprefix tailTrace_8201302
  have hstable : (prefixWord ++ tailWord_8201302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201302).length < 2 ^ (prefixWord ++ tailWord_8201302).sum := by decide
  have hdescent : baseEnd_8201302 < baseStart_8201302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201309 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_8201309 : Nat := 118140960795 + 8201309 * 2 ^ 59
def prefixEnd_8201309 : Nat := 4983230072969 + 3 ^ 40 * 8201309 * 2
def baseEnd_8201309 : Nat := 4211213513044758074520373

theorem tailTrace_8201309 : CollatzResearch.WordTrace tailWord_8201309 prefixEnd_8201309 4211213513044758074520373 := by
  unfold tailWord_8201309
  simp only [CollatzResearch.WordTrace]
  refine ⟨299126313445065639909110981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199417542296710426606073987 299126313445065639909110981)
  ·
    refine ⟨56086183770949807482958309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299126313445065639909110981 56086183770949807482958309)
    ·
      refine ⟨10516159457053088903054683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56086183770949807482958309 10516159457053088903054683)
      ·
        refine ⟨15774239185579633354582025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10516159457053088903054683 15774239185579633354582025)
        ·
          refine ⟨11830679389184725015936519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15774239185579633354582025 11830679389184725015936519)
          ·
            refine ⟨17746019083777087523904779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11830679389184725015936519 17746019083777087523904779)
            ·
              refine ⟨26619028625665631285857169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17746019083777087523904779 26619028625665631285857169)
              ·
                refine ⟨19964271469249223464392877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26619028625665631285857169 19964271469249223464392877)
                ·
                  refine ⟨7486601800968458799147329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19964271469249223464392877 7486601800968458799147329)
                  ·
                    refine ⟨5614951350726344099360497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7486601800968458799147329 5614951350726344099360497)
                    ·
                      refine ⟨4211213513044758074520373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5614951350726344099360497 4211213513044758074520373)
                      ·
                        rfl

theorem cell23_8201309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_8201309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201309 prefixEnd_8201309 := by exact prefixLift 8201309
  have htrace : WordTrace (prefixWord ++ tailWord_8201309) baseStart_8201309 baseEnd_8201309 := by
    simpa [prefixWord, tailWord_8201309, baseEnd_8201309] using wordTrace_append hprefix tailTrace_8201309
  have hstable : (prefixWord ++ tailWord_8201309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201309).length < 2 ^ (prefixWord ++ tailWord_8201309).sum := by decide
  have hdescent : baseEnd_8201309 < baseStart_8201309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201335 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 1, 3, 2]
def baseStart_8201335 : Nat := 118140960795 + 8201335 * 2 ^ 59
def prefixEnd_8201335 : Nat := 4983230072969 + 3 ^ 40 * 8201335 * 2
def baseEnd_8201335 : Nat := 4211226863541774972795253

theorem tailTrace_8201335 : CollatzResearch.WordTrace tailWord_8201335 prefixEnd_8201335 4211226863541774972795253 := by
  unfold tailWord_8201335
  simp only [CollatzResearch.WordTrace]
  refine ⟨299127261742971446349557459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199418174495314297566371639 299127261742971446349557459)
  ·
    refine ⟨448690892614457169524336189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299127261742971446349557459 448690892614457169524336189)
    ·
      refine ⟨168259084730421438571626071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448690892614457169524336189 168259084730421438571626071)
      ·
        refine ⟨252388627095632157857439107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168259084730421438571626071 252388627095632157857439107)
        ·
          refine ⟨378582940643448236786158661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252388627095632157857439107 378582940643448236786158661)
          ·
            refine ⟨70984301370646544397404749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378582940643448236786158661 70984301370646544397404749)
            ·
              refine ⟨26619113013992454149026781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70984301370646544397404749 26619113013992454149026781)
              ·
                refine ⟨9982167380247170305885043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26619113013992454149026781 9982167380247170305885043)
                ·
                  refine ⟨14973251070370755458827565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9982167380247170305885043 14973251070370755458827565)
                  ·
                    refine ⟨5614969151389033297060337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14973251070370755458827565 5614969151389033297060337)
                    ·
                      refine ⟨4211226863541774972795253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5614969151389033297060337 4211226863541774972795253)
                      ·
                        rfl

theorem cell23_8201335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 3, 2].length) (baseStart_8201335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201335 prefixEnd_8201335 := by exact prefixLift 8201335
  have htrace : WordTrace (prefixWord ++ tailWord_8201335) baseStart_8201335 baseEnd_8201335 := by
    simpa [prefixWord, tailWord_8201335, baseEnd_8201335] using wordTrace_append hprefix tailTrace_8201335
  have hstable : (prefixWord ++ tailWord_8201335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201335).length < 2 ^ (prefixWord ++ tailWord_8201335).sum := by decide
  have hdescent : baseEnd_8201335 < baseStart_8201335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201341 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_8201341 : Nat := 118140960795 + 8201341 * 2 ^ 59
def prefixEnd_8201341 : Nat := 4983230072969 + 3 ^ 40 * 8201341 * 2
def baseEnd_8201341 : Nat := 1403743314808567316440075

theorem tailTrace_8201341 : CollatzResearch.WordTrace tailWord_8201341 prefixEnd_8201341 1403743314808567316440075 := by
  unfold tailWord_8201341
  simp only [CollatzResearch.WordTrace]
  refine ⟨299127480580949709374275877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199418320387299806249517251 299127480580949709374275877)
  ·
    refine ⟨56086402608928070507676727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299127480580949709374275877 56086402608928070507676727)
    ·
      refine ⟨84129603913392105761515091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56086402608928070507676727 84129603913392105761515091)
      ·
        refine ⟨126194405870088158642272637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84129603913392105761515091 126194405870088158642272637)
        ·
          refine ⟨47322902201283059490852239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126194405870088158642272637 47322902201283059490852239)
          ·
            refine ⟨70984353301924589236278359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47322902201283059490852239 70984353301924589236278359)
            ·
              refine ⟨106476529952886883854417539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70984353301924589236278359 106476529952886883854417539)
              ·
                refine ⟨159714794929330325781626309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106476529952886883854417539 159714794929330325781626309)
                ·
                  refine ⟨29946524049249436084054933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159714794929330325781626309 29946524049249436084054933)
                  ·
                    refine ⟨1403743314808567316440075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29946524049249436084054933 1403743314808567316440075)
                    ·
                      rfl

theorem cell23_8201341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_8201341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201341 prefixEnd_8201341 := by exact prefixLift 8201341
  have htrace : WordTrace (prefixWord ++ tailWord_8201341) baseStart_8201341 baseEnd_8201341 := by
    simpa [prefixWord, tailWord_8201341, baseEnd_8201341] using wordTrace_append hprefix tailTrace_8201341
  have hstable : (prefixWord ++ tailWord_8201341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201341).length < 2 ^ (prefixWord ++ tailWord_8201341).sum := by decide
  have hdescent : baseEnd_8201341 < baseStart_8201341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201351 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_8201351 : Nat := 118140960795 + 8201351 * 2 ^ 59
def prefixEnd_8201351 : Nat := 4983230072969 + 3 ^ 40 * 8201351 * 2
def baseEnd_8201351 : Nat := 4211235079232246910195179

theorem tailTrace_8201351 : CollatzResearch.WordTrace tailWord_8201351 prefixEnd_8201351 4211235079232246910195179 := by
  unfold tailWord_8201351
  simp only [CollatzResearch.WordTrace]
  refine ⟨299127845310913481082139907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199418563540608987388093271 299127845310913481082139907)
  ·
    refine ⟨448691767966370221623209861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299127845310913481082139907 448691767966370221623209861)
    ·
      refine ⟨84129706493694416554351849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448691767966370221623209861 84129706493694416554351849)
      ·
        refine ⟨63097279870270812415763887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84129706493694416554351849 63097279870270812415763887)
        ·
          refine ⟨94645919805406218623645831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63097279870270812415763887 94645919805406218623645831)
          ·
            refine ⟨141968879708109327935468747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94645919805406218623645831 141968879708109327935468747)
            ·
              refine ⟨212953319562163991903203121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141968879708109327935468747 212953319562163991903203121)
              ·
                refine ⟨159714989671622993927402341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212953319562163991903203121 159714989671622993927402341)
                ·
                  refine ⟨29946560563429311361387939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159714989671622993927402341 29946560563429311361387939)
                  ·
                    refine ⟨44919840845143967042081909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29946560563429311361387939 44919840845143967042081909)
                    ·
                      refine ⟨4211235079232246910195179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44919840845143967042081909 4211235079232246910195179)
                      ·
                        rfl

theorem cell23_8201351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_8201351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201351 prefixEnd_8201351 := by exact prefixLift 8201351
  have htrace : WordTrace (prefixWord ++ tailWord_8201351) baseStart_8201351 baseEnd_8201351 := by
    simpa [prefixWord, tailWord_8201351, baseEnd_8201351] using wordTrace_append hprefix tailTrace_8201351
  have hstable : (prefixWord ++ tailWord_8201351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201351).length < 2 ^ (prefixWord ++ tailWord_8201351).sum := by decide
  have hdescent : baseEnd_8201351 < baseStart_8201351 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201358 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_8201358 : Nat := 118140960795 + 8201358 * 2 ^ 59
def prefixEnd_8201358 : Nat := 4983230072969 + 3 ^ 40 * 8201358 * 2
def baseEnd_8201358 : Nat := 1403746224532276127602549

theorem tailTrace_8201358 : CollatzResearch.WordTrace tailWord_8201358 prefixEnd_8201358 1403746224532276127602549 := by
  unfold tailWord_8201358
  simp only [CollatzResearch.WordTrace]
  refine ⟨37391012577736015159705591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199418733747925414185096485 37391012577736015159705591)
  ·
    refine ⟨56086518866604022739558387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37391012577736015159705591 56086518866604022739558387)
    ·
      refine ⟨84129778299906034109337581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56086518866604022739558387 84129778299906034109337581)
      ·
        refine ⟨31548666862464762791001593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84129778299906034109337581 31548666862464762791001593)
        ·
          refine ⟨23661500146848572093251195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31548666862464762791001593 23661500146848572093251195)
          ·
            refine ⟨35492250220272858139876793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23661500146848572093251195 35492250220272858139876793)
            ·
              refine ⟨26619187665204643604907595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35492250220272858139876793 26619187665204643604907595)
              ·
                refine ⟨39928781497806965407361393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26619187665204643604907595 39928781497806965407361393)
                ·
                  refine ⟨29946586123355224055521045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39928781497806965407361393 29946586123355224055521045)
                  ·
                    refine ⟨1403746224532276127602549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29946586123355224055521045 1403746224532276127602549)
                    ·
                      rfl

theorem cell23_8201358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_8201358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201358 prefixEnd_8201358 := by exact prefixLift 8201358
  have htrace : WordTrace (prefixWord ++ tailWord_8201358) baseStart_8201358 baseEnd_8201358 := by
    simpa [prefixWord, tailWord_8201358, baseEnd_8201358] using wordTrace_append hprefix tailTrace_8201358
  have hstable : (prefixWord ++ tailWord_8201358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201358).length < 2 ^ (prefixWord ++ tailWord_8201358).sum := by decide
  have hdescent : baseEnd_8201358 < baseStart_8201358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201388 : List Nat := [2, 2, 1, 1, 1, 1, 1, 9, 5]
def baseStart_8201388 : Nat := 118140960795 + 8201388 * 2 ^ 59
def prefixEnd_8201388 : Nat := 4983230072969 + 3 ^ 40 * 8201388 * 2
def baseEnd_8201388 : Nat := 467917119779607029492501

theorem tailTrace_8201388 : CollatzResearch.WordTrace tailWord_8201388 prefixEnd_8201388 467917119779607029492501 := by
  unfold tailWord_8201388
  simp only [CollatzResearch.WordTrace]
  refine ⟨149564597405889718200618409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199419463207852957600824545 149564597405889718200618409)
  ·
    refine ⟨112173448054417288650463807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149564597405889718200618409 112173448054417288650463807)
    ·
      refine ⟨168260172081625932975695711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112173448054417288650463807 168260172081625932975695711)
      ·
        refine ⟨252390258122438899463543567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168260172081625932975695711 252390258122438899463543567)
        ·
          refine ⟨378585387183658349195315351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252390258122438899463543567 378585387183658349195315351)
          ·
            refine ⟨567878080775487523792973027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378585387183658349195315351 567878080775487523792973027)
            ·
              refine ⟨851817121163231285689459541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567878080775487523792973027 851817121163231285689459541)
              ·
                refine ⟨4991115944315808314586677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 851817121163231285689459541 4991115944315808314586677)
                ·
                  refine ⟨467917119779607029492501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4991115944315808314586677 467917119779607029492501)
                  ·
                    rfl

theorem cell23_8201388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_8201388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201388 prefixEnd_8201388 := by exact prefixLift 8201388
  have htrace : WordTrace (prefixWord ++ tailWord_8201388) baseStart_8201388 baseEnd_8201388 := by
    simpa [prefixWord, tailWord_8201388, baseEnd_8201388] using wordTrace_append hprefix tailTrace_8201388
  have hstable : (prefixWord ++ tailWord_8201388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201388).length < 2 ^ (prefixWord ++ tailWord_8201388).sum := by decide
  have hdescent : baseEnd_8201388 < baseStart_8201388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201410 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 2, 1, 3]
def baseStart_8201410 : Nat := 118140960795 + 8201410 * 2 ^ 59
def prefixEnd_8201410 : Nat := 4983230072969 + 3 ^ 40 * 8201410 * 2
def baseEnd_8201410 : Nat := 4211265374590862179357409

theorem tailTrace_8201410 : CollatzResearch.WordTrace tailWord_8201410 prefixEnd_8201410 4211265374590862179357409 := by
  unfold tailWord_8201410
  simp only [CollatzResearch.WordTrace]
  refine ⟨74782499304424933539634421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199419998145133156105691789 74782499304424933539634421)
  ·
    refine ⟨7010859309789837519340727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74782499304424933539634421 7010859309789837519340727)
    ·
      refine ⟨10516288964684756279011091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7010859309789837519340727 10516288964684756279011091)
      ·
        refine ⟨15774433447027134418516637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10516288964684756279011091 15774433447027134418516637)
        ·
          refine ⟨5915412542635175406943739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15774433447027134418516637 5915412542635175406943739)
          ·
            refine ⟨8873118813952763110415609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915412542635175406943739 8873118813952763110415609)
            ·
              refine ⟨6654839110464572332811707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8873118813952763110415609 6654839110464572332811707)
              ·
                refine ⟨9982258665696858499217561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654839110464572332811707 9982258665696858499217561)
                ·
                  refine ⟨7486693999272643874413171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9982258665696858499217561 7486693999272643874413171)
                  ·
                    refine ⟨11230040998908965811619757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7486693999272643874413171 11230040998908965811619757)
                    ·
                      refine ⟨4211265374590862179357409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11230040998908965811619757 4211265374590862179357409)
                      ·
                        rfl

theorem cell23_8201410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_8201410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201410 prefixEnd_8201410 := by exact prefixLift 8201410
  have htrace : WordTrace (prefixWord ++ tailWord_8201410) baseStart_8201410 baseEnd_8201410 := by
    simpa [prefixWord, tailWord_8201410, baseEnd_8201410] using wordTrace_append hprefix tailTrace_8201410
  have hstable : (prefixWord ++ tailWord_8201410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201410).length < 2 ^ (prefixWord ++ tailWord_8201410).sum := by decide
  have hdescent : baseEnd_8201410 < baseStart_8201410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201431 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 2, 8]
def baseStart_8201431 : Nat := 118140960795 + 8201431 * 2 ^ 59
def prefixEnd_8201431 : Nat := 4983230072969 + 3 ^ 40 * 8201431 * 2
def baseEnd_8201431 : Nat := 1403758719228202199064937

theorem tailTrace_8201431 : CollatzResearch.WordTrace tailWord_8201431 prefixEnd_8201431 1403758719228202199064937 := by
  unfold tailWord_8201431
  simp only [CollatzResearch.WordTrace]
  refine ⟨299130763150623654745052147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199420508767082436496701431 299130763150623654745052147)
  ·
    refine ⟨448696144725935482117578221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299130763150623654745052147 448696144725935482117578221)
    ·
      refine ⟨168261054272225805794091833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448696144725935482117578221 168261054272225805794091833)
      ·
        refine ⟨126195790704169354345568875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168261054272225805794091833 126195790704169354345568875)
        ·
          refine ⟨189293686056254031518353313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126195790704169354345568875 189293686056254031518353313)
          ·
            refine ⟨141970264542190523638764985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189293686056254031518353313 141970264542190523638764985)
            ·
              refine ⟨106477698406642892729073739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141970264542190523638764985 106477698406642892729073739)
              ·
                refine ⟨159716547609964339093610609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106477698406642892729073739 159716547609964339093610609)
                ·
                  refine ⟨119787410707473254320207957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159716547609964339093610609 119787410707473254320207957)
                  ·
                    refine ⟨1403758719228202199064937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119787410707473254320207957 1403758719228202199064937)
                    ·
                      rfl

theorem cell23_8201431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_8201431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201431 prefixEnd_8201431 := by exact prefixLift 8201431
  have htrace : WordTrace (prefixWord ++ tailWord_8201431) baseStart_8201431 baseEnd_8201431 := by
    simpa [prefixWord, tailWord_8201431, baseEnd_8201431] using wordTrace_append hprefix tailTrace_8201431
  have hstable : (prefixWord ++ tailWord_8201431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201431).length < 2 ^ (prefixWord ++ tailWord_8201431).sum := by decide
  have hdescent : baseEnd_8201431 < baseStart_8201431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201505 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 7, 1, 3]
def baseStart_8201505 : Nat := 118140960795 + 8201505 * 2 ^ 59
def prefixEnd_8201505 : Nat := 4983230072969 + 3 ^ 40 * 8201505 * 2
def baseEnd_8201505 : Nat := 4211314155253039307669471

theorem tailTrace_8201505 : CollatzResearch.WordTrace tailWord_8201505 prefixEnd_8201505 4211314155253039307669471 := by
  unfold tailWord_8201505
  simp only [CollatzResearch.WordTrace]
  refine ⟨299133462152355565383245969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199422308101570376922163979 299133462152355565383245969)
  ·
    refine ⟨224350096614266674037434477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299133462152355565383245969 224350096614266674037434477)
    ·
      refine ⟨84131286230350002764037929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224350096614266674037434477 84131286230350002764037929)
      ·
        refine ⟨63098464672762502073028447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84131286230350002764037929 63098464672762502073028447)
        ·
          refine ⟨94647697009143753109542671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63098464672762502073028447 94647697009143753109542671)
          ·
            refine ⟨141971545513715629664314007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94647697009143753109542671 141971545513715629664314007)
            ·
              refine ⟨212957318270573444496471011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141971545513715629664314007 212957318270573444496471011)
              ·
                refine ⟨319435977405860166744706517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212957318270573444496471011 319435977405860166744706517)
                ·
                  refine ⟨7486780720449847658079059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 319435977405860166744706517 7486780720449847658079059)
                  ·
                    refine ⟨11230171080674771487118589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7486780720449847658079059 11230171080674771487118589)
                    ·
                      refine ⟨4211314155253039307669471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11230171080674771487118589 4211314155253039307669471)
                      ·
                        rfl

theorem cell23_8201505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_8201505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201505 prefixEnd_8201505 := by exact prefixLift 8201505
  have htrace : WordTrace (prefixWord ++ tailWord_8201505) baseStart_8201505 baseEnd_8201505 := by
    simpa [prefixWord, tailWord_8201505, baseEnd_8201505] using wordTrace_append hprefix tailTrace_8201505
  have hstable : (prefixWord ++ tailWord_8201505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201505).length < 2 ^ (prefixWord ++ tailWord_8201505).sum := by decide
  have hdescent : baseEnd_8201505 < baseStart_8201505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201512 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 6]
def baseStart_8201512 : Nat := 118140960795 + 8201512 * 2 ^ 59
def prefixEnd_8201512 : Nat := 4983230072969 + 3 ^ 40 * 8201512 * 2
def baseEnd_8201512 : Nat := 467924194401957864475771

theorem tailTrace_8201512 : CollatzResearch.WordTrace tailWord_8201512 prefixEnd_8201512 467924194401957864475771 := by
  unfold tailWord_8201512
  simp only [CollatzResearch.WordTrace]
  refine ⟨149566858731665102789375395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199422478308886803719167193 149566858731665102789375395)
  ·
    refine ⟨224350288097497654184063093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149566858731665102789375395 224350288097497654184063093)
    ·
      refine ⟨21032839509140405079755915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224350288097497654184063093 21032839509140405079755915)
      ·
        refine ⟨31549259263710607619633873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21032839509140405079755915 31549259263710607619633873)
        ·
          refine ⟨23661944447782955714725405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31549259263710607619633873 23661944447782955714725405)
          ·
            refine ⟨8873229167918608393022027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23661944447782955714725405 8873229167918608393022027)
            ·
              refine ⟨13309843751877912589533041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8873229167918608393022027 13309843751877912589533041)
              ·
                refine ⟨9982382813908434442149781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13309843751877912589533041 9982382813908434442149781)
                ·
                  refine ⟨467924194401957864475771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9982382813908434442149781 467924194401957864475771)
                  ·
                    rfl

theorem cell23_8201512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 6].length) (baseStart_8201512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201512 prefixEnd_8201512 := by exact prefixLift 8201512
  have htrace : WordTrace (prefixWord ++ tailWord_8201512) baseStart_8201512 baseEnd_8201512 := by
    simpa [prefixWord, tailWord_8201512, baseEnd_8201512] using wordTrace_append hprefix tailTrace_8201512
  have hstable : (prefixWord ++ tailWord_8201512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201512).length < 2 ^ (prefixWord ++ tailWord_8201512).sum := by decide
  have hdescent : baseEnd_8201512 < baseStart_8201512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201522 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_8201522 : Nat := 118140960795 + 8201522 * 2 ^ 59
def prefixEnd_8201522 : Nat := 4983230072969 + 3 ^ 40 * 8201522 * 2
def baseEnd_8201522 : Nat := 4211322884424165741156893

theorem tailTrace_8201522 : CollatzResearch.WordTrace tailWord_8201522 prefixEnd_8201522 4211322884424165741156893 := by
  unfold tailWord_8201522
  simp only [CollatzResearch.WordTrace]
  refine ⟨74783520548323494321653705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199422721462195984857743213 74783520548323494321653705)
  ·
    refine ⟨56087640411242620741240279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74783520548323494321653705 56087640411242620741240279)
    ·
      refine ⟨84131460616863931111860419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56087640411242620741240279 84131460616863931111860419)
      ·
        refine ⟨126197190925295896667790629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84131460616863931111860419 126197190925295896667790629)
        ·
          refine ⟨23661973298492980625210743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126197190925295896667790629 23661973298492980625210743)
          ·
            refine ⟨35492959947739470937816115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23661973298492980625210743 35492959947739470937816115)
            ·
              refine ⟨53239439921609206406724173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35492959947739470937816115 53239439921609206406724173)
              ·
                refine ⟨19964789970603452402521565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53239439921609206406724173 19964789970603452402521565)
                ·
                  refine ⟨7486796238976294650945587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19964789970603452402521565 7486796238976294650945587)
                  ·
                    refine ⟨11230194358464441976418381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7486796238976294650945587 11230194358464441976418381)
                    ·
                      refine ⟨4211322884424165741156893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11230194358464441976418381 4211322884424165741156893)
                      ·
                        rfl

theorem cell23_8201522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_8201522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201522 prefixEnd_8201522 := by exact prefixLift 8201522
  have htrace : WordTrace (prefixWord ++ tailWord_8201522) baseStart_8201522 baseEnd_8201522 := by
    simpa [prefixWord, tailWord_8201522, baseEnd_8201522] using wordTrace_append hprefix tailTrace_8201522
  have hstable : (prefixWord ++ tailWord_8201522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201522).length < 2 ^ (prefixWord ++ tailWord_8201522).sum := by decide
  have hdescent : baseEnd_8201522 < baseStart_8201522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201545 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 4]
def baseStart_8201545 : Nat := 118140960795 + 8201545 * 2 ^ 59
def prefixEnd_8201545 : Nat := 4983230072969 + 3 ^ 40 * 8201545 * 2
def baseEnd_8201545 : Nat := 4211334694479219151169287

theorem tailTrace_8201545 : CollatzResearch.WordTrace tailWord_8201545 prefixEnd_8201545 4211334694479219151169287 := by
  unfold tailWord_8201545
  simp only [CollatzResearch.WordTrace]
  refine ⟨299134921072210652214702089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199423280714807101476468059 299134921072210652214702089)
  ·
    refine ⟨224351190804157989161026567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299134921072210652214702089 224351190804157989161026567)
    ·
      refine ⟨336526786206236983741539851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224351190804157989161026567 336526786206236983741539851)
      ·
        refine ⟨504790179309355475612309777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336526786206236983741539851 504790179309355475612309777)
        ·
          refine ⟨378592634482016606709232333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504790179309355475612309777 378592634482016606709232333)
          ·
            refine ⟨141972237930756227515962125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378592634482016606709232333 141972237930756227515962125)
            ·
              refine ⟨53239589224033585318485797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141972237930756227515962125 53239589224033585318485797)
              ·
                refine ⟨9982422979506297247216087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53239589224033585318485797 9982422979506297247216087)
                ·
                  refine ⟨14973634469259445870824131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9982422979506297247216087 14973634469259445870824131)
                  ·
                    refine ⟨22460451703889168806236197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14973634469259445870824131 22460451703889168806236197)
                    ·
                      refine ⟨4211334694479219151169287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22460451703889168806236197 4211334694479219151169287)
                      ·
                        rfl

theorem cell23_8201545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 1, 1, 4].length) (baseStart_8201545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201545 prefixEnd_8201545 := by exact prefixLift 8201545
  have htrace : WordTrace (prefixWord ++ tailWord_8201545) baseStart_8201545 baseEnd_8201545 := by
    simpa [prefixWord, tailWord_8201545, baseEnd_8201545] using wordTrace_append hprefix tailTrace_8201545
  have hstable : (prefixWord ++ tailWord_8201545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201545).length < 2 ^ (prefixWord ++ tailWord_8201545).sum := by decide
  have hdescent : baseEnd_8201545 < baseStart_8201545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201562 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2]
def baseStart_8201562 : Nat := 118140960795 + 8201562 * 2 ^ 59
def prefixEnd_8201562 : Nat := 4983230072969 + 3 ^ 40 * 8201562 * 2
def baseEnd_8201562 : Nat := 4211343423650345584656709

theorem tailTrace_8201562 : CollatzResearch.WordTrace tailWord_8201562 prefixEnd_8201562 4211343423650345584656709 := by
  unfold tailWord_8201562
  simp only [CollatzResearch.WordTrace]
  refine ⟨74783885278287266029517735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199423694075432709412047293 74783885278287266029517735)
  ·
    refine ⟨112175827917430899044276603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74783885278287266029517735 112175827917430899044276603)
    ·
      refine ⟨168263741876146348566414905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112175827917430899044276603 168263741876146348566414905)
      ·
        refine ⟨126197806407109761424811179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168263741876146348566414905 126197806407109761424811179)
        ·
          refine ⟨189296709610664642137216769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126197806407109761424811179 189296709610664642137216769)
          ·
            refine ⟨141972532207998481602912577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189296709610664642137216769 141972532207998481602912577)
            ·
              refine ⟨106479399155998861202184433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141972532207998481602912577 106479399155998861202184433)
              ·
                refine ⟨79859549366999145901638325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106479399155998861202184433 79859549366999145901638325)
                ·
                  refine ⟨7486832753156169928278593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79859549366999145901638325 7486832753156169928278593)
                  ·
                    refine ⟨5615124564867127446208945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7486832753156169928278593 5615124564867127446208945)
                    ·
                      refine ⟨4211343423650345584656709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615124564867127446208945 4211343423650345584656709)
                      ·
                        rfl

theorem cell23_8201562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_8201562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201562 prefixEnd_8201562 := by exact prefixLift 8201562
  have htrace : WordTrace (prefixWord ++ tailWord_8201562) baseStart_8201562 baseEnd_8201562 := by
    simpa [prefixWord, tailWord_8201562, baseEnd_8201562] using wordTrace_append hprefix tailTrace_8201562
  have hstable : (prefixWord ++ tailWord_8201562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201562).length < 2 ^ (prefixWord ++ tailWord_8201562).sum := by decide
  have hdescent : baseEnd_8201562 < baseStart_8201562 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201568 : List Nat := [2, 1, 1, 3, 4, 1, 11]
def baseStart_8201568 : Nat := 118140960795 + 8201568 * 2 ^ 59
def prefixEnd_8201568 : Nat := 4983230072969 + 3 ^ 40 * 8201568 * 2
def baseEnd_8201568 : Nat := 51991932154744105693601

theorem tailTrace_8201568 : CollatzResearch.WordTrace tailWord_8201568 prefixEnd_8201568 51991932154744105693601 := by
  unfold tailWord_8201568
  simp only [CollatzResearch.WordTrace]
  refine ⟨149567879975563663571394679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199423839967418218095192905 149567879975563663571394679)
  ·
    refine ⟨224351819963345495357092019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149567879975563663571394679 224351819963345495357092019)
    ·
      refine ⟨336527729945018243035638029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224351819963345495357092019 336527729945018243035638029)
      ·
        refine ⟨126197898729381841138364261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336527729945018243035638029 126197898729381841138364261)
        ·
          refine ⟨23662106011759095213443299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126197898729381841138364261 23662106011759095213443299)
          ·
            refine ⟨35493159017638642820164949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23662106011759095213443299 35493159017638642820164949)
            ·
              refine ⟨51991932154744105693601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35493159017638642820164949 51991932154744105693601)
              ·
                rfl

theorem cell23_8201568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 11].length) (baseStart_8201568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201568 prefixEnd_8201568 := by exact prefixLift 8201568
  have htrace : WordTrace (prefixWord ++ tailWord_8201568) baseStart_8201568 baseEnd_8201568 := by
    simpa [prefixWord, tailWord_8201568, baseEnd_8201568] using wordTrace_append hprefix tailTrace_8201568
  have hstable : (prefixWord ++ tailWord_8201568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201568).length < 2 ^ (prefixWord ++ tailWord_8201568).sum := by decide
  have hdescent : baseEnd_8201568 < baseStart_8201568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201589 : List Nat := [1, 3, 4, 1, 3, 1, 1, 3, 2, 4]
def baseStart_8201589 : Nat := 118140960795 + 8201589 * 2 ^ 59
def prefixEnd_8201589 : Nat := 4983230072969 + 3 ^ 40 * 8201589 * 2
def baseEnd_8201589 : Nat := 1403785762542672326339695

theorem tailTrace_8201589 : CollatzResearch.WordTrace tailWord_8201589 prefixEnd_8201589 1403785762542672326339695 := by
  unfold tailWord_8201589
  simp only [CollatzResearch.WordTrace]
  refine ⟨299136525884051247729303821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199424350589367498486202547 299136525884051247729303821)
  ·
    refine ⟨112176197206519217898488933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299136525884051247729303821 112176197206519217898488933)
    ·
      refine ⟨21033036976222353355966675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112176197206519217898488933 21033036976222353355966675)
      ·
        refine ⟨31549555464333530033950013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21033036976222353355966675 31549555464333530033950013)
        ·
          refine ⟨11831083299125073762731255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31549555464333530033950013 11831083299125073762731255)
          ·
            refine ⟨17746624948687610644096883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11831083299125073762731255 17746624948687610644096883)
            ·
              refine ⟨26619937423031415966145325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17746624948687610644096883 26619937423031415966145325)
              ·
                refine ⟨9982476533636780987304497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26619937423031415966145325 9982476533636780987304497)
                ·
                  refine ⟨7486857400227585740478373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9982476533636780987304497 7486857400227585740478373)
                  ·
                    refine ⟨1403785762542672326339695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7486857400227585740478373 1403785762542672326339695)
                    ·
                      rfl

theorem cell23_8201589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_8201589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201589 prefixEnd_8201589 := by exact prefixLift 8201589
  have htrace : WordTrace (prefixWord ++ tailWord_8201589) baseStart_8201589 baseEnd_8201589 := by
    simpa [prefixWord, tailWord_8201589, baseEnd_8201589] using wordTrace_append hprefix tailTrace_8201589
  have hstable : (prefixWord ++ tailWord_8201589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201589).length < 2 ^ (prefixWord ++ tailWord_8201589).sum := by decide
  have hdescent : baseEnd_8201589 < baseStart_8201589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201595 : List Nat := [1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 3]
def baseStart_8201595 : Nat := 118140960795 + 8201595 * 2 ^ 59
def prefixEnd_8201595 : Nat := 4983230072969 + 3 ^ 40 * 8201595 * 2
def baseEnd_8201595 : Nat := 4211360368511943955544057

theorem tailTrace_8201595 : CollatzResearch.WordTrace tailWord_8201595 prefixEnd_8201595 4211360368511943955544057 := by
  unfold tailWord_8201595
  simp only [CollatzResearch.WordTrace]
  refine ⟨299136744722029510754022239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199424496481353007169348159 299136744722029510754022239)
  ·
    refine ⟨448705117083044266131033359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299136744722029510754022239 448705117083044266131033359)
    ·
      refine ⟨673057675624566399196550039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448705117083044266131033359 673057675624566399196550039)
      ·
        refine ⟨1009586513436849598794825059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673057675624566399196550039 1009586513436849598794825059)
        ·
          refine ⟨1514379770155274398192237589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009586513436849598794825059 1514379770155274398192237589)
          ·
            refine ⟨70986551726028487415261137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1514379770155274398192237589 70986551726028487415261137)
            ·
              refine ⟨53239913794521365561445853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70986551726028487415261137 53239913794521365561445853)
              ·
                refine ⟨19964967672945512085542195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53239913794521365561445853 19964967672945512085542195)
                ·
                  refine ⟨29947451509418268128313293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19964967672945512085542195 29947451509418268128313293)
                  ·
                    refine ⟨11230294316031850548117485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29947451509418268128313293 11230294316031850548117485)
                    ·
                      refine ⟨4211360368511943955544057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11230294316031850548117485 4211360368511943955544057)
                      ·
                        rfl

theorem cell23_8201595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 3, 3].length) (baseStart_8201595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201595 prefixEnd_8201595 := by exact prefixLift 8201595
  have htrace : WordTrace (prefixWord ++ tailWord_8201595) baseStart_8201595 baseEnd_8201595 := by
    simpa [prefixWord, tailWord_8201595, baseEnd_8201595] using wordTrace_append hprefix tailTrace_8201595
  have hstable : (prefixWord ++ tailWord_8201595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201595).length < 2 ^ (prefixWord ++ tailWord_8201595).sum := by decide
  have hdescent : baseEnd_8201595 < baseStart_8201595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201602 : List Nat := [3, 4, 2, 1, 1, 1, 2, 9]
def baseStart_8201602 : Nat := 118140960795 + 8201602 * 2 ^ 59
def prefixEnd_8201602 : Nat := 4983230072969 + 3 ^ 40 * 8201602 * 2
def baseEnd_8201602 : Nat := 155976443069500941783575

theorem tailTrace_8201602 : CollatzResearch.WordTrace tailWord_8201602 prefixEnd_8201602 155976443069500941783575 := by
  unfold tailWord_8201602
  simp only [CollatzResearch.WordTrace]
  refine ⟨74784250008251037737381765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199424666688669433966351373 74784250008251037737381765)
  ·
    refine ⟨14022046876547069575759081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74784250008251037737381765 14022046876547069575759081)
    ·
      refine ⟨10516535157410302181819311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14022046876547069575759081 10516535157410302181819311)
      ·
        refine ⟨15774802736115453272728967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10516535157410302181819311 15774802736115453272728967)
        ·
          refine ⟨23662204104173179909093451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15774802736115453272728967 23662204104173179909093451)
          ·
            refine ⟨35493306156259769863640177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23662204104173179909093451 35493306156259769863640177)
            ·
              refine ⟨26619979617194827397730133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35493306156259769863640177 26619979617194827397730133)
              ·
                refine ⟨155976443069500941783575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26619979617194827397730133 155976443069500941783575)
                ·
                  rfl

theorem cell23_8201602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 9].length) (baseStart_8201602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201602 prefixEnd_8201602 := by exact prefixLift 8201602
  have htrace : WordTrace (prefixWord ++ tailWord_8201602) baseStart_8201602 baseEnd_8201602 := by
    simpa [prefixWord, tailWord_8201602, baseEnd_8201602] using wordTrace_append hprefix tailTrace_8201602
  have hstable : (prefixWord ++ tailWord_8201602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201602).length < 2 ^ (prefixWord ++ tailWord_8201602).sum := by decide
  have hdescent : baseEnd_8201602 < baseStart_8201602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201629 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_8201629 : Nat := 118140960795 + 8201629 * 2 ^ 59
def prefixEnd_8201629 : Nat := 4983230072969 + 3 ^ 40 * 8201629 * 2
def baseEnd_8201629 : Nat := 4211377826854196822518901

theorem tailTrace_8201629 : CollatzResearch.WordTrace tailWord_8201629 prefixEnd_8201629 4211377826854196822518901 := by
  unfold tailWord_8201629
  simp only [CollatzResearch.WordTrace]
  refine ⟨299137984803906334560759941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199425323202604223040506627 299137984803906334560759941)
  ·
    refine ⟨56088372150732437730142489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299137984803906334560759941 56088372150732437730142489)
    ·
      refine ⟨42066279113049328297606867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56088372150732437730142489 42066279113049328297606867)
      ·
        refine ⟨63099418669573992446410301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42066279113049328297606867 63099418669573992446410301)
        ·
          refine ⟨23662282001090247167403863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63099418669573992446410301 23662282001090247167403863)
          ·
            refine ⟨35493423001635370751105795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23662282001090247167403863 35493423001635370751105795)
            ·
              refine ⟨53240134502453056126658693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35493423001635370751105795 53240134502453056126658693)
              ·
                refine ⟨9982525219209948023748505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53240134502453056126658693 9982525219209948023748505)
                ·
                  refine ⟨7486893914407461017811379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9982525219209948023748505 7486893914407461017811379)
                  ·
                    refine ⟨11230340871611191526717069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7486893914407461017811379 11230340871611191526717069)
                    ·
                      refine ⟨4211377826854196822518901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11230340871611191526717069 4211377826854196822518901)
                      ·
                        rfl

theorem cell23_8201629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_8201629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201629 prefixEnd_8201629 := by exact prefixLift 8201629
  have htrace : WordTrace (prefixWord ++ tailWord_8201629) baseStart_8201629 baseEnd_8201629 := by
    simpa [prefixWord, tailWord_8201629, baseEnd_8201629] using wordTrace_append hprefix tailTrace_8201629
  have hstable : (prefixWord ++ tailWord_8201629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201629).length < 2 ^ (prefixWord ++ tailWord_8201629).sum := by decide
  have hdescent : baseEnd_8201629 < baseStart_8201629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201630 : List Nat := [4, 3, 1, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_8201630 : Nat := 118140960795 + 8201630 * 2 ^ 59
def prefixEnd_8201630 : Nat := 4983230072969 + 3 ^ 40 * 8201630 * 2
def baseEnd_8201630 : Nat := 4211378340334851318606397

theorem tailTrace_8201630 : CollatzResearch.WordTrace tailWord_8201630 prefixEnd_8201630 4211378340334851318606397 := by
  unfold tailWord_8201630
  simp only [CollatzResearch.WordTrace]
  refine ⟨37392252659612838966443293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199425347517935141154364229 37392252659612838966443293)
  ·
    refine ⟨14022094747354814612416235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37392252659612838966443293 14022094747354814612416235)
    ·
      refine ⟨21033142121032221918624353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14022094747354814612416235 21033142121032221918624353)
      ·
        refine ⟨15774856590774166438968265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21033142121032221918624353 15774856590774166438968265)
        ·
          refine ⟨11831142443080624829226199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15774856590774166438968265 11831142443080624829226199)
          ·
            refine ⟨17746713664620937243839299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11831142443080624829226199 17746713664620937243839299)
            ·
              refine ⟨26620070496931405865758949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17746713664620937243839299 26620070496931405865758949)
              ·
                refine ⟨4991263218174638599829803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26620070496931405865758949 4991263218174638599829803)
                ·
                  refine ⟨7486894827261957899744705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991263218174638599829803 7486894827261957899744705)
                  ·
                    refine ⟨5615171120446468424808529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7486894827261957899744705 5615171120446468424808529)
                    ·
                      refine ⟨4211378340334851318606397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615171120446468424808529 4211378340334851318606397)
                      ·
                        rfl

theorem cell23_8201630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_8201630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201630 prefixEnd_8201630 := by exact prefixLift 8201630
  have htrace : WordTrace (prefixWord ++ tailWord_8201630) baseStart_8201630 baseEnd_8201630 := by
    simpa [prefixWord, tailWord_8201630, baseEnd_8201630] using wordTrace_append hprefix tailTrace_8201630
  have hstable : (prefixWord ++ tailWord_8201630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201630).length < 2 ^ (prefixWord ++ tailWord_8201630).sum := by decide
  have hdescent : baseEnd_8201630 < baseStart_8201630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201655 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 3]
def baseStart_8201655 : Nat := 118140960795 + 8201655 * 2 ^ 59
def prefixEnd_8201655 : Nat := 4983230072969 + 3 ^ 40 * 8201655 * 2
def baseEnd_8201655 : Nat := 4211391177351213720793781

theorem tailTrace_8201655 : CollatzResearch.WordTrace tailWord_8201655 prefixEnd_8201655 4211391177351213720793781 := by
  unfold tailWord_8201655
  simp only [CollatzResearch.WordTrace]
  refine ⟨299138933101812141001206419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199425955401208094000804279 299138933101812141001206419)
  ·
    refine ⟨448708399652718211501809629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299138933101812141001206419 448708399652718211501809629)
    ·
      refine ⟨168265649869769329313178611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448708399652718211501809629 168265649869769329313178611)
      ·
        refine ⟨252398474804653993969767917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168265649869769329313178611 252398474804653993969767917)
        ·
          refine ⟨94649428051745247738662969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252398474804653993969767917 94649428051745247738662969)
          ·
            refine ⟨70987071038808935803997227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94649428051745247738662969 70987071038808935803997227)
            ·
              refine ⟨106480606558213403705995841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70987071038808935803997227 106480606558213403705995841)
              ·
                refine ⟨79860454918660052779496881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106480606558213403705995841 79860454918660052779496881)
                ·
                  refine ⟨59895341188995039584622661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79860454918660052779496881 59895341188995039584622661)
                  ·
                    refine ⟨11230376472936569922116749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59895341188995039584622661 11230376472936569922116749)
                    ·
                      refine ⟨4211391177351213720793781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11230376472936569922116749 4211391177351213720793781)
                      ·
                        rfl

theorem cell23_8201655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_8201655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201655 prefixEnd_8201655 := by exact prefixLift 8201655
  have htrace : WordTrace (prefixWord ++ tailWord_8201655) baseStart_8201655 baseEnd_8201655 := by
    simpa [prefixWord, tailWord_8201655, baseEnd_8201655] using wordTrace_append hprefix tailTrace_8201655
  have hstable : (prefixWord ++ tailWord_8201655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201655).length < 2 ^ (prefixWord ++ tailWord_8201655).sum := by decide
  have hdescent : baseEnd_8201655 < baseStart_8201655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201703 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_8201703 : Nat := 118140960795 + 8201703 * 2 ^ 59
def prefixEnd_8201703 : Nat := 4983230072969 + 3 ^ 40 * 8201703 * 2
def baseEnd_8201703 : Nat := 4211415824422629532993561

theorem tailTrace_8201703 : CollatzResearch.WordTrace tailWord_8201703 prefixEnd_8201703 4211415824422629532993561 := by
  unfold tailWord_8201703
  simp only [CollatzResearch.WordTrace]
  refine ⟨299140683805638245198953763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199427122537092163465969175 299140683805638245198953763)
  ·
    refine ⟨448711025708457367798430645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299140683805638245198953763 448711025708457367798430645)
    ·
      refine ⟨42066658660167878231102873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 448711025708457367798430645 42066658660167878231102873)
      ·
        refine ⟨31549993995125908673327155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42066658660167878231102873 31549993995125908673327155)
        ·
          refine ⟨47324990992688863009990733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31549993995125908673327155 47324990992688863009990733)
          ·
            refine ⟨17746871622258323628746525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47324990992688863009990733 17746871622258323628746525)
            ·
              refine ⟨6655076858346871360779947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17746871622258323628746525 6655076858346871360779947)
              ·
                refine ⟨9982615287520307041169921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655076858346871360779947 9982615287520307041169921)
                ·
                  refine ⟨7486961465640230280877441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9982615287520307041169921 7486961465640230280877441)
                  ·
                    refine ⟨5615221099230172710658081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7486961465640230280877441 5615221099230172710658081)
                    ·
                      refine ⟨4211415824422629532993561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615221099230172710658081 4211415824422629532993561)
                      ·
                        rfl

theorem cell23_8201703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_8201703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201703 prefixEnd_8201703 := by exact prefixLift 8201703
  have htrace : WordTrace (prefixWord ++ tailWord_8201703) baseStart_8201703 baseEnd_8201703 := by
    simpa [prefixWord, tailWord_8201703, baseEnd_8201703] using wordTrace_append hprefix tailTrace_8201703
  have hstable : (prefixWord ++ tailWord_8201703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201703).length < 2 ^ (prefixWord ++ tailWord_8201703).sum := by decide
  have hdescent : baseEnd_8201703 < baseStart_8201703 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201762 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_8201762 : Nat := 118140960795 + 8201762 * 2 ^ 59
def prefixEnd_8201762 : Nat := 4983230072969 + 3 ^ 40 * 8201762 * 2
def baseEnd_8201762 : Nat := 4211446119781244802155789

theorem tailTrace_8201762 : CollatzResearch.WordTrace tailWord_8201762 prefixEnd_8201762 4211446119781244802155789 := by
  unfold tailWord_8201762
  simp only [CollatzResearch.WordTrace]
  refine ⟨74785708928106124568837885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199428557141616332183567693 74785708928106124568837885)
  ·
    refine ⟨28044640848039796713314207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74785708928106124568837885 28044640848039796713314207)
    ·
      refine ⟨42066961272059695069971311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28044640848039796713314207 42066961272059695069971311)
      ·
        refine ⟨63100441908089542604956967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42066961272059695069971311 63100441908089542604956967)
        ·
          refine ⟨94650662862134313907435451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63100441908089542604956967 94650662862134313907435451)
          ·
            refine ⟨141975994293201470861153177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94650662862134313907435451 141975994293201470861153177)
            ·
              refine ⟨106481995719901103145864883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141975994293201470861153177 106481995719901103145864883)
              ·
                refine ⟨159722993579851654718797325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106481995719901103145864883 159722993579851654718797325)
                ·
                  refine ⟨59896122592444370519548997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159722993579851654718797325 59896122592444370519548997)
                  ·
                    refine ⟨11230522986083319472415437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59896122592444370519548997 11230522986083319472415437)
                    ·
                      refine ⟨4211446119781244802155789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11230522986083319472415437 4211446119781244802155789)
                      ·
                        rfl

theorem cell23_8201762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_8201762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201762 prefixEnd_8201762 := by exact prefixLift 8201762
  have htrace : WordTrace (prefixWord ++ tailWord_8201762) baseStart_8201762 baseEnd_8201762 := by
    simpa [prefixWord, tailWord_8201762, baseEnd_8201762] using wordTrace_append hprefix tailTrace_8201762
  have hstable : (prefixWord ++ tailWord_8201762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201762).length < 2 ^ (prefixWord ++ tailWord_8201762).sum := by decide
  have hdescent : baseEnd_8201762 < baseStart_8201762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201779 : List Nat := [1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 3]
def baseStart_8201779 : Nat := 118140960795 + 8201779 * 2 ^ 59
def prefixEnd_8201779 : Nat := 4983230072969 + 3 ^ 40 * 8201779 * 2
def baseEnd_8201779 : Nat := 4211454848952371235643211

theorem tailTrace_8201779 : CollatzResearch.WordTrace tailWord_8201779 prefixEnd_8201779 4211454848952371235643211 := by
  unfold tailWord_8201779
  simp only [CollatzResearch.WordTrace]
  refine ⟨299143455753362910178720391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199428970502241940119146927 299143455753362910178720391)
  ·
    refine ⟨448715183630044365268080587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299143455753362910178720391 448715183630044365268080587)
    ·
      refine ⟨673072775445066547902120881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448715183630044365268080587 673072775445066547902120881)
      ·
        refine ⟨504804581583799910926590661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673072775445066547902120881 504804581583799910926590661)
        ·
          refine ⟨94650859046962483298735749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 504804581583799910926590661 94650859046962483298735749)
          ·
            refine ⟨17747036071305465618512953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94650859046962483298735749 17747036071305465618512953)
            ·
              refine ⟨13310277053479099213884715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17747036071305465618512953 13310277053479099213884715)
              ·
                refine ⟨19965415580218648820827073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13310277053479099213884715 19965415580218648820827073)
                ·
                  refine ⟨14974061685163986615620305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19965415580218648820827073 14974061685163986615620305)
                  ·
                    refine ⟨11230546263872989961715229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14974061685163986615620305 11230546263872989961715229)
                    ·
                      refine ⟨4211454848952371235643211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11230546263872989961715229 4211454848952371235643211)
                      ·
                        rfl

theorem cell23_8201779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 2, 3].length) (baseStart_8201779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201779 prefixEnd_8201779 := by exact prefixLift 8201779
  have htrace : WordTrace (prefixWord ++ tailWord_8201779) baseStart_8201779 baseEnd_8201779 := by
    simpa [prefixWord, tailWord_8201779, baseEnd_8201779] using wordTrace_append hprefix tailTrace_8201779
  have hstable : (prefixWord ++ tailWord_8201779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201779).length < 2 ^ (prefixWord ++ tailWord_8201779).sum := by decide
  have hdescent : baseEnd_8201779 < baseStart_8201779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201799 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 6]
def baseStart_8201799 : Nat := 118140960795 + 8201799 * 2 ^ 59
def prefixEnd_8201799 : Nat := 4983230072969 + 3 ^ 40 * 8201799 * 2
def baseEnd_8201799 : Nat := 467940568729495684154791

theorem tailTrace_8201799 : CollatzResearch.WordTrace tailWord_8201799 prefixEnd_8201799 467940568729495684154791 := by
  unfold tailWord_8201799
  simp only [CollatzResearch.WordTrace]
  refine ⟨299144185213290453594448451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199429456808860302396298967 299144185213290453594448451)
  ·
    refine ⟨448716277819935680391672677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299144185213290453594448451 448716277819935680391672677)
    ·
      refine ⟨84134302091237940073438627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 448716277819935680391672677 84134302091237940073438627)
      ·
        refine ⟨126201453136856910110157941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84134302091237940073438627 126201453136856910110157941)
        ·
          refine ⟨11831386231580335322827307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126201453136856910110157941 11831386231580335322827307)
          ·
            refine ⟨17747079347370502984240961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11831386231580335322827307 17747079347370502984240961)
            ·
              refine ⟨13310309510527877238180721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17747079347370502984240961 13310309510527877238180721)
              ·
                refine ⟨9982732132895907928635541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13310309510527877238180721 9982732132895907928635541)
                ·
                  refine ⟨467940568729495684154791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9982732132895907928635541 467940568729495684154791)
                  ·
                    rfl

theorem cell23_8201799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 6].length) (baseStart_8201799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201799 prefixEnd_8201799 := by exact prefixLift 8201799
  have htrace : WordTrace (prefixWord ++ tailWord_8201799) baseStart_8201799 baseEnd_8201799 := by
    simpa [prefixWord, tailWord_8201799, baseEnd_8201799] using wordTrace_append hprefix tailTrace_8201799
  have hstable : (prefixWord ++ tailWord_8201799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201799).length < 2 ^ (prefixWord ++ tailWord_8201799).sum := by decide
  have hdescent : baseEnd_8201799 < baseStart_8201799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201809 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 3, 1, 3]
def baseStart_8201809 : Nat := 118140960795 + 8201809 * 2 ^ 59
def prefixEnd_8201809 : Nat := 4983230072969 + 3 ^ 40 * 8201809 * 2
def baseEnd_8201809 : Nat := 4211470253372006118268073

theorem tailTrace_8201809 : CollatzResearch.WordTrace tailWord_8201809 prefixEnd_8201809 4211470253372006118268073 := by
  unfold tailWord_8201809
  simp only [CollatzResearch.WordTrace]
  refine ⟨299144549943254225302312481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199429699962169483534874987 299144549943254225302312481)
  ·
    refine ⟨224358412457440668976734361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299144549943254225302312481 224358412457440668976734361)
    ·
      refine ⟨168268809343080501732550771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224358412457440668976734361 168268809343080501732550771)
      ·
        refine ⟨252403214014620752598826157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168268809343080501732550771 252403214014620752598826157)
        ·
          refine ⟨94651205255482782224559809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252403214014620752598826157 94651205255482782224559809)
          ·
            refine ⟨70988403941612086668419857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94651205255482782224559809 70988403941612086668419857)
            ·
              refine ⟨53241302956209065001314893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70988403941612086668419857 53241302956209065001314893)
              ·
                refine ⟨19965488608578399375493085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53241302956209065001314893 19965488608578399375493085)
                ·
                  refine ⟨7487058228216899765809907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19965488608578399375493085 7487058228216899765809907)
                  ·
                    refine ⟨11230587342325349648714861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7487058228216899765809907 11230587342325349648714861)
                    ·
                      refine ⟨4211470253372006118268073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11230587342325349648714861 4211470253372006118268073)
                      ·
                        rfl

theorem cell23_8201809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 1, 3].length) (baseStart_8201809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201809 prefixEnd_8201809 := by exact prefixLift 8201809
  have htrace : WordTrace (prefixWord ++ tailWord_8201809) baseStart_8201809 baseEnd_8201809 := by
    simpa [prefixWord, tailWord_8201809, baseEnd_8201809] using wordTrace_append hprefix tailTrace_8201809
  have hstable : (prefixWord ++ tailWord_8201809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201809).length < 2 ^ (prefixWord ++ tailWord_8201809).sum := by decide
  have hdescent : baseEnd_8201809 < baseStart_8201809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201812 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 5, 5]
def baseStart_8201812 : Nat := 118140960795 + 8201812 * 2 ^ 59
def prefixEnd_8201812 : Nat := 4983230072969 + 3 ^ 40 * 8201812 * 2
def baseEnd_8201812 : Nat := 1403823931271323202176853

theorem tailTrace_8201812 : CollatzResearch.WordTrace tailWord_8201812 prefixEnd_8201812 1403823931271323202176853 := by
  unfold tailWord_8201812
  simp only [CollatzResearch.WordTrace]
  refine ⟨149572329681121678407335845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199429772908162237876447793 149572329681121678407335845)
  ·
    refine ⟨28044811815210314701375471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149572329681121678407335845 28044811815210314701375471)
    ·
      refine ⟨42067217722815472052063207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28044811815210314701375471 42067217722815472052063207)
      ·
        refine ⟨63100826584223208078094811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42067217722815472052063207 63100826584223208078094811)
        ·
          refine ⟨94651239876334812117142217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63100826584223208078094811 94651239876334812117142217)
          ·
            refine ⟨70988429907251109087856663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94651239876334812117142217 70988429907251109087856663)
            ·
              refine ⟨106482644860876663631784995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70988429907251109087856663 106482644860876663631784995)
              ·
                refine ⟨159723967291314995447677493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106482644860876663631784995 159723967291314995447677493)
                ·
                  refine ⟨14974121933560780823219765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159723967291314995447677493 14974121933560780823219765)
                  ·
                    refine ⟨1403823931271323202176853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14974121933560780823219765 1403823931271323202176853)
                    ·
                      rfl

theorem cell23_8201812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_8201812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201812 prefixEnd_8201812 := by exact prefixLift 8201812
  have htrace : WordTrace (prefixWord ++ tailWord_8201812) baseStart_8201812 baseEnd_8201812 := by
    simpa [prefixWord, tailWord_8201812, baseEnd_8201812] using wordTrace_append hprefix tailTrace_8201812
  have hstable : (prefixWord ++ tailWord_8201812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201812).length < 2 ^ (prefixWord ++ tailWord_8201812).sum := by decide
  have hdescent : baseEnd_8201812 < baseStart_8201812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201846 : List Nat := [5, 1, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_8201846 : Nat := 118140960795 + 8201846 * 2 ^ 59
def prefixEnd_8201846 : Nat := 4983230072969 + 3 ^ 40 * 8201846 * 2
def baseEnd_8201846 : Nat := 1403829750718740824501801

theorem tailTrace_8201846 : CollatzResearch.WordTrace tailWord_8201846 prefixEnd_8201846 1403829750718740824501801 := by
  unfold tailWord_8201846
  simp only [CollatzResearch.WordTrace]
  refine ⟨18696618715257511288838087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199430599629413453747606261 18696618715257511288838087)
  ·
    refine ⟨28044928072886266933257131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18696618715257511288838087 28044928072886266933257131)
    ·
      refine ⟨42067392109329400399885697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28044928072886266933257131 42067392109329400399885697)
      ·
        refine ⟨31550544081997050299914273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42067392109329400399885697 31550544081997050299914273)
        ·
          refine ⟨23662908061497787724935705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31550544081997050299914273 23662908061497787724935705)
          ·
            refine ⟨17747181046123340793701779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23662908061497787724935705 17747181046123340793701779)
            ·
              refine ⟨26620771569185011190552669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17747181046123340793701779 26620771569185011190552669)
              ·
                refine ⟨9982789338444379196457251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26620771569185011190552669 9982789338444379196457251)
                ·
                  refine ⟨14974184007666568794685877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9982789338444379196457251 14974184007666568794685877)
                  ·
                    refine ⟨1403829750718740824501801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14974184007666568794685877 1403829750718740824501801)
                    ·
                      rfl

theorem cell23_8201846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_8201846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201846 prefixEnd_8201846 := by exact prefixLift 8201846
  have htrace : WordTrace (prefixWord ++ tailWord_8201846) baseStart_8201846 baseEnd_8201846 := by
    simpa [prefixWord, tailWord_8201846, baseEnd_8201846] using wordTrace_append hprefix tailTrace_8201846
  have hstable : (prefixWord ++ tailWord_8201846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201846).length < 2 ^ (prefixWord ++ tailWord_8201846).sum := by decide
  have hdescent : baseEnd_8201846 < baseStart_8201846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201849 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 4]
def baseStart_8201849 : Nat := 118140960795 + 8201849 * 2 ^ 59
def prefixEnd_8201849 : Nat := 4983230072969 + 3 ^ 40 * 8201849 * 2
def baseEnd_8201849 : Nat := 4211490792598185961767889

theorem tailTrace_8201849 : CollatzResearch.WordTrace tailWord_8201849 prefixEnd_8201849 4211490792598185961767889 := by
  unfold tailWord_8201849
  simp only [CollatzResearch.WordTrace]
  refine ⟨299146008863109312133768601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199430672575406208089179067 299146008863109312133768601)
  ·
    refine ⟨224359506647331984100326451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299146008863109312133768601 224359506647331984100326451)
    ·
      refine ⟨336539259970997976150489677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224359506647331984100326451 336539259970997976150489677)
      ·
        refine ⟨126202222489124241056433629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336539259970997976150489677 126202222489124241056433629)
        ·
          refine ⟨47325833433421590396162611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126202222489124241056433629 47325833433421590396162611)
          ·
            refine ⟨70988750150132385594243917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47325833433421590396162611 70988750150132385594243917)
            ·
              refine ⟨26620781306299644597841469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70988750150132385594243917 26620781306299644597841469)
              ·
                refine ⟨9982792989862366724190551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26620781306299644597841469 9982792989862366724190551)
                ·
                  refine ⟨14974189484793550086285827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9982792989862366724190551 14974189484793550086285827)
                  ·
                    refine ⟨22461284227190325129428741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14974189484793550086285827 22461284227190325129428741)
                    ·
                      refine ⟨4211490792598185961767889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22461284227190325129428741 4211490792598185961767889)
                      ·
                        rfl

theorem cell23_8201849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_8201849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201849 prefixEnd_8201849 := by exact prefixLift 8201849
  have htrace : WordTrace (prefixWord ++ tailWord_8201849) baseStart_8201849 baseEnd_8201849 := by
    simpa [prefixWord, tailWord_8201849, baseEnd_8201849] using wordTrace_append hprefix tailTrace_8201849
  have hstable : (prefixWord ++ tailWord_8201849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201849).length < 2 ^ (prefixWord ++ tailWord_8201849).sum := by decide
  have hdescent : baseEnd_8201849 < baseStart_8201849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201852 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_8201852 : Nat := 118140960795 + 8201852 * 2 ^ 59
def prefixEnd_8201852 : Nat := 4983230072969 + 3 ^ 40 * 8201852 * 2
def baseEnd_8201852 : Nat := 4211492333040149450030375

theorem tailTrace_8201852 : CollatzResearch.WordTrace tailWord_8201852 prefixEnd_8201852 4211492333040149450030375 := by
  unfold tailWord_8201852
  simp only [CollatzResearch.WordTrace]
  refine ⟨149573059141049221823063905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199430745521398962430751873 149573059141049221823063905)
  ·
    refine ⟨112179794355786916367297929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149573059141049221823063905 112179794355786916367297929)
    ·
      refine ⟨84134845766840187275473447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112179794355786916367297929 84134845766840187275473447)
      ·
        refine ⟨126202268650260280913210171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84134845766840187275473447 126202268650260280913210171)
        ·
          refine ⟨189303402975390421369815257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126202268650260280913210171 189303402975390421369815257)
          ·
            refine ⟨141977552231542816027361443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189303402975390421369815257 141977552231542816027361443)
            ·
              refine ⟨212966328347314224041042165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141977552231542816027361443 212966328347314224041042165)
              ·
                refine ⟨19965593282560708503847703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 212966328347314224041042165 19965593282560708503847703)
                ·
                  refine ⟨29948389923841062755771555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19965593282560708503847703 29948389923841062755771555)
                  ·
                    refine ⟨44922584885761594133657333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29948389923841062755771555 44922584885761594133657333)
                    ·
                      refine ⟨4211492333040149450030375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44922584885761594133657333 4211492333040149450030375)
                      ·
                        rfl

theorem cell23_8201852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_8201852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201852 prefixEnd_8201852 := by exact prefixLift 8201852
  have htrace : WordTrace (prefixWord ++ tailWord_8201852) baseStart_8201852 baseEnd_8201852 := by
    simpa [prefixWord, tailWord_8201852, baseEnd_8201852] using wordTrace_append hprefix tailTrace_8201852
  have hstable : (prefixWord ++ tailWord_8201852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201852).length < 2 ^ (prefixWord ++ tailWord_8201852).sum := by decide
  have hdescent : baseEnd_8201852 < baseStart_8201852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201879 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 4]
def baseStart_8201879 : Nat := 118140960795 + 8201879 * 2 ^ 59
def prefixEnd_8201879 : Nat := 4983230072969 + 3 ^ 40 * 8201879 * 2
def baseEnd_8201879 : Nat := 4211506197017820844392751

theorem tailTrace_8201879 : CollatzResearch.WordTrace tailWord_8201879 prefixEnd_8201879 4211506197017820844392751 := by
  unfold tailWord_8201879
  simp only [CollatzResearch.WordTrace]
  refine ⟨299147103053000627257360691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199431402035333751504907127 299147103053000627257360691)
  ·
    refine ⟨448720654579500940886041037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299147103053000627257360691 448720654579500940886041037)
    ·
      refine ⟨168270245467312852832265389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448720654579500940886041037 168270245467312852832265389)
      ·
        refine ⟨63101342050242319812099521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168270245467312852832265389 63101342050242319812099521)
        ·
          refine ⟨47326006537681739859074641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63101342050242319812099521 47326006537681739859074641)
          ·
            refine ⟨35494504903261304894305981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47326006537681739859074641 35494504903261304894305981)
            ·
              refine ⟨13310439338722989335364743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35494504903261304894305981 13310439338722989335364743)
              ·
                refine ⟨19965659008084484003047115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13310439338722989335364743 19965659008084484003047115)
                ·
                  refine ⟨29948488512126726004570673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19965659008084484003047115 29948488512126726004570673)
                  ·
                    refine ⟨22461366384095044503428005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29948488512126726004570673 22461366384095044503428005)
                    ·
                      refine ⟨4211506197017820844392751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22461366384095044503428005 4211506197017820844392751)
                      ·
                        rfl

theorem cell23_8201879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_8201879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201879 prefixEnd_8201879 := by exact prefixLift 8201879
  have htrace : WordTrace (prefixWord ++ tailWord_8201879) baseStart_8201879 baseEnd_8201879 := by
    simpa [prefixWord, tailWord_8201879, baseEnd_8201879] using wordTrace_append hprefix tailTrace_8201879
  have hstable : (prefixWord ++ tailWord_8201879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201879).length < 2 ^ (prefixWord ++ tailWord_8201879).sum := by decide
  have hdescent : baseEnd_8201879 < baseStart_8201879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201889 : List Nat := [1, 2, 3, 3, 2, 1, 4, 7]
def baseStart_8201889 : Nat := 118140960795 + 8201889 * 2 ^ 59
def prefixEnd_8201889 : Nat := 4983230072969 + 3 ^ 40 * 8201889 * 2
def baseEnd_8201889 : Nat := 155981901178680215009915

theorem tailTrace_8201889 : CollatzResearch.WordTrace tailWord_8201889 prefixEnd_8201889 155981901178680215009915 := by
  unfold tailWord_8201889
  simp only [CollatzResearch.WordTrace]
  refine ⟨299147467782964398965224721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199431645188642932643483147 299147467782964398965224721)
  ·
    refine ⟨224360600837223299223918541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299147467782964398965224721 224360600837223299223918541)
    ·
      refine ⟨84135225313958737208969453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224360600837223299223918541 84135225313958737208969453)
      ·
        refine ⟨31550709492734526453363545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84135225313958737208969453 31550709492734526453363545)
        ·
          refine ⟨23663032119550894840022659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31550709492734526453363545 23663032119550894840022659)
          ·
            refine ⟨35494548179326342260033989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23663032119550894840022659 35494548179326342260033989)
            ·
              refine ⟨6655227783623689173756373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35494548179326342260033989 6655227783623689173756373)
              ·
                refine ⟨155981901178680215009915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6655227783623689173756373 155981901178680215009915)
                ·
                  rfl

theorem cell23_8201889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 7].length) (baseStart_8201889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201889 prefixEnd_8201889 := by exact prefixLift 8201889
  have htrace : WordTrace (prefixWord ++ tailWord_8201889) baseStart_8201889 baseEnd_8201889 := by
    simpa [prefixWord, tailWord_8201889, baseEnd_8201889] using wordTrace_append hprefix tailTrace_8201889
  have hstable : (prefixWord ++ tailWord_8201889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201889).length < 2 ^ (prefixWord ++ tailWord_8201889).sum := by decide
  have hdescent : baseEnd_8201889 < baseStart_8201889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201916 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 4, 1, 3]
def baseStart_8201916 : Nat := 118140960795 + 8201916 * 2 ^ 59
def prefixEnd_8201916 : Nat := 4983230072969 + 3 ^ 40 * 8201916 * 2
def baseEnd_8201916 : Nat := 4211525195802037199630081

theorem tailTrace_8201916 : CollatzResearch.WordTrace tailWord_8201916 prefixEnd_8201916 4211525195802037199630081 := by
  unfold tailWord_8201916
  simp only [CollatzResearch.WordTrace]
  refine ⟨149574226276933291288228801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199432301702577721717638401 149574226276933291288228801)
  ·
    refine ⟨112180669707699968466171601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149574226276933291288228801 112180669707699968466171601)
    ·
      refine ⟨84135502280774976349628701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112180669707699968466171601 84135502280774976349628701)
      ·
        refine ⟨31550813355290616131110763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84135502280774976349628701 31550813355290616131110763)
        ·
          refine ⟨47326220032935924196666145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31550813355290616131110763 47326220032935924196666145)
          ·
            refine ⟨35494665024701943147499609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47326220032935924196666145 35494665024701943147499609)
            ·
              refine ⟨26620998768526457360624707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35494665024701943147499609 26620998768526457360624707)
              ·
                refine ⟨39931498152789686040937061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26620998768526457360624707 39931498152789686040937061)
                ·
                  refine ⟨7487155903648066132675699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39931498152789686040937061 7487155903648066132675699)
                  ·
                    refine ⟨11230733855472099199013549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7487155903648066132675699 11230733855472099199013549)
                    ·
                      refine ⟨4211525195802037199630081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11230733855472099199013549 4211525195802037199630081)
                      ·
                        rfl

theorem cell23_8201916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_8201916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201916 prefixEnd_8201916 := by exact prefixLift 8201916
  have htrace : WordTrace (prefixWord ++ tailWord_8201916) baseStart_8201916 baseEnd_8201916 := by
    simpa [prefixWord, tailWord_8201916, baseEnd_8201916] using wordTrace_append hprefix tailTrace_8201916
  have hstable : (prefixWord ++ tailWord_8201916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201916).length < 2 ^ (prefixWord ++ tailWord_8201916).sum := by decide
  have hdescent : baseEnd_8201916 < baseStart_8201916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201956 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 1, 4, 2]
def baseStart_8201956 : Nat := 118140960795 + 8201956 * 2 ^ 59
def prefixEnd_8201956 : Nat := 4983230072969 + 3 ^ 40 * 8201956 * 2
def baseEnd_8201956 : Nat := 4211545735028217043129897

theorem tailTrace_8201956 : CollatzResearch.WordTrace tailWord_8201956 prefixEnd_8201956 4211545735028217043129897 := by
  unfold tailWord_8201956
  simp only [CollatzResearch.WordTrace]
  refine ⟨149574955736860834703956861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199433274315814446271942481 149574955736860834703956861)
  ·
    refine ⟨56090608401322813013983823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149574955736860834703956861 56090608401322813013983823)
    ·
      refine ⟨84135912601984219520975735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56090608401322813013983823 84135912601984219520975735)
      ·
        refine ⟨126203868902976329281463603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84135912601984219520975735 126203868902976329281463603)
        ·
          refine ⟨189305803354464493922195405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126203868902976329281463603 189305803354464493922195405)
          ·
            refine ⟨70989676257924185220823277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189305803354464493922195405 70989676257924185220823277)
            ·
              refine ⟨26621128596721569457808729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70989676257924185220823277 26621128596721569457808729)
              ·
                refine ⟨19965846447541177093356547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26621128596721569457808729 19965846447541177093356547)
                ·
                  refine ⟨29948769671311765640034821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19965846447541177093356547 29948769671311765640034821)
                  ·
                    refine ⟨5615394313370956057506529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29948769671311765640034821 5615394313370956057506529)
                    ·
                      refine ⟨4211545735028217043129897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615394313370956057506529 4211545735028217043129897)
                      ·
                        rfl

theorem cell23_8201956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_8201956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201956 prefixEnd_8201956 := by exact prefixLift 8201956
  have htrace : WordTrace (prefixWord ++ tailWord_8201956) baseStart_8201956 baseEnd_8201956 := by
    simpa [prefixWord, tailWord_8201956, baseEnd_8201956] using wordTrace_append hprefix tailTrace_8201956
  have hstable : (prefixWord ++ tailWord_8201956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201956).length < 2 ^ (prefixWord ++ tailWord_8201956).sum := by decide
  have hdescent : baseEnd_8201956 < baseStart_8201956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201960 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_8201960 : Nat := 118140960795 + 8201960 * 2 ^ 59
def prefixEnd_8201960 : Nat := 4983230072969 + 3 ^ 40 * 8201960 * 2
def baseEnd_8201960 : Nat := 4211547788950835027479879

theorem tailTrace_8201960 : CollatzResearch.WordTrace tailWord_8201960 prefixEnd_8201960 4211547788950835027479879 := by
  unfold tailWord_8201960
  simp only [CollatzResearch.WordTrace]
  refine ⟨149575028682853589045529667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199433371577138118727372889 149575028682853589045529667)
  ·
    refine ⟨224362543024280383568294501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149575028682853589045529667 224362543024280383568294501)
    ·
      refine ⟨42067976817052571919055219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224362543024280383568294501 42067976817052571919055219)
      ·
        refine ⟨63101965225578857878582829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42067976817052571919055219 63101965225578857878582829)
        ·
          refine ⟨23663236959592071704468561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63101965225578857878582829 23663236959592071704468561)
          ·
            refine ⟨17747427719694053778351421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23663236959592071704468561 17747427719694053778351421)
            ·
              refine ⟨6655285394885270166881783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17747427719694053778351421 6655285394885270166881783)
              ·
                refine ⟨9982928092327905250322675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655285394885270166881783 9982928092327905250322675)
                ·
                  refine ⟨14974392138491857875484013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9982928092327905250322675 14974392138491857875484013)
                  ·
                    refine ⟨5615397051934446703306505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14974392138491857875484013 5615397051934446703306505)
                    ·
                      refine ⟨4211547788950835027479879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615397051934446703306505 4211547788950835027479879)
                      ·
                        rfl

theorem cell23_8201960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_8201960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201960 prefixEnd_8201960 := by exact prefixLift 8201960
  have htrace : WordTrace (prefixWord ++ tailWord_8201960) baseStart_8201960 baseEnd_8201960 := by
    simpa [prefixWord, tailWord_8201960, baseEnd_8201960] using wordTrace_append hprefix tailTrace_8201960
  have hstable : (prefixWord ++ tailWord_8201960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201960).length < 2 ^ (prefixWord ++ tailWord_8201960).sum := by decide
  have hdescent : baseEnd_8201960 < baseStart_8201960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8201986 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_8201986 : Nat := 118140960795 + 8201986 * 2 ^ 59
def prefixEnd_8201986 : Nat := 4983230072969 + 3 ^ 40 * 8201986 * 2
def baseEnd_8201986 : Nat := 4211561139447851925754759

theorem tailTrace_8201986 : CollatzResearch.WordTrace tailWord_8201986 prefixEnd_8201986 4211561139447851925754759 := by
  unfold tailWord_8201986
  simp only [CollatzResearch.WordTrace]
  refine ⟨74787751415903246132876453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199434003775741989687670541 74787751415903246132876453)
  ·
    refine ⟨14022703390481858649914335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74787751415903246132876453 14022703390481858649914335)
    ·
      refine ⟨21034055085722787974871503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14022703390481858649914335 21034055085722787974871503)
      ·
        refine ⟨31551082628584181962307255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21034055085722787974871503 31551082628584181962307255)
        ·
          refine ⟨47326623942876272943460883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31551082628584181962307255 47326623942876272943460883)
          ·
            refine ⟨70989935914314409415191325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47326623942876272943460883 70989935914314409415191325)
            ·
              refine ⟨26621225967867903530696747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70989935914314409415191325 26621225967867903530696747)
              ·
                refine ⟨39931838951801855296045121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26621225967867903530696747 39931838951801855296045121)
                ·
                  refine ⟨29948879213851391472033841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39931838951801855296045121 29948879213851391472033841)
                  ·
                    refine ⟨22461659410388543604025381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29948879213851391472033841 22461659410388543604025381)
                    ·
                      refine ⟨4211561139447851925754759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22461659410388543604025381 4211561139447851925754759)
                      ·
                        rfl

theorem cell23_8201986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_8201986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8201986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8201986 prefixEnd_8201986 := by exact prefixLift 8201986
  have htrace : WordTrace (prefixWord ++ tailWord_8201986) baseStart_8201986 baseEnd_8201986 := by
    simpa [prefixWord, tailWord_8201986, baseEnd_8201986] using wordTrace_append hprefix tailTrace_8201986
  have hstable : (prefixWord ++ tailWord_8201986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8201986).length < 2 ^ (prefixWord ++ tailWord_8201986).sum := by decide
  have hdescent : baseEnd_8201986 < baseStart_8201986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8201986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202046 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_8202046 : Nat := 118140960795 + 8202046 * 2 ^ 59
def prefixEnd_8202046 : Nat := 4983230072969 + 3 ^ 40 * 8202046 * 2
def baseEnd_8202046 : Nat := 4211591948287121691004483

theorem tailTrace_8202046 : CollatzResearch.WordTrace tailWord_8202046 prefixEnd_8202046 4211591948287121691004483 := by
  unfold tailWord_8202046
  simp only [CollatzResearch.WordTrace]
  refine ⟨37394149255424451847336249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199435462695597076519126661 37394149255424451847336249)
  ·
    refine ⟨28045611941568338885502187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37394149255424451847336249 28045611941568338885502187)
    ·
      refine ⟨42068417912352508328253281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28045611941568338885502187 42068417912352508328253281)
      ·
        refine ⟨31551313434264381246189961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42068417912352508328253281 31551313434264381246189961)
        ·
          refine ⟨23663485075698285934642471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31551313434264381246189961 23663485075698285934642471)
          ·
            refine ⟨35495227613547428901963707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23663485075698285934642471 35495227613547428901963707)
            ·
              refine ⟨53242841420321143352945561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35495227613547428901963707 53242841420321143352945561)
              ·
                refine ⟨39932131065240857514709171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53242841420321143352945561 39932131065240857514709171)
                ·
                  refine ⟨59898196597861286272063757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39932131065240857514709171 59898196597861286272063757)
                  ·
                    refine ⟨22461823724197982352023909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59898196597861286272063757 22461823724197982352023909)
                    ·
                      refine ⟨4211591948287121691004483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22461823724197982352023909 4211591948287121691004483)
                      ·
                        rfl

theorem cell23_8202046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_8202046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202046 prefixEnd_8202046 := by exact prefixLift 8202046
  have htrace : WordTrace (prefixWord ++ tailWord_8202046) baseStart_8202046 baseEnd_8202046 := by
    simpa [prefixWord, tailWord_8202046, baseEnd_8202046] using wordTrace_append hprefix tailTrace_8202046
  have hstable : (prefixWord ++ tailWord_8202046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202046).length < 2 ^ (prefixWord ++ tailWord_8202046).sum := by decide
  have hdescent : baseEnd_8202046 < baseStart_8202046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202056 : List Nat := [2, 1, 3, 1, 1, 4, 2, 2, 3, 4]
def baseStart_8202056 : Nat := 118140960795 + 8202056 * 2 ^ 59
def prefixEnd_8202056 : Nat := 4983230072969 + 3 ^ 40 * 8202056 * 2
def baseEnd_8202056 : Nat := 1403865694364555550626479

theorem tailTrace_8202056 : CollatzResearch.WordTrace tailWord_8202056 prefixEnd_8202056 1403865694364555550626479 := by
  unfold tailWord_8202056
  simp only [CollatzResearch.WordTrace]
  refine ⟨149576779386679693243277011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199435705848906257657702681 149576779386679693243277011)
  ·
    refine ⟨224365169080019539864915517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149576779386679693243277011 224365169080019539864915517)
    ·
      refine ⟨84136938405007327449343319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224365169080019539864915517 84136938405007327449343319)
      ·
        refine ⟨126205407607510991174014979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84136938405007327449343319 126205407607510991174014979)
        ·
          refine ⟨189308111411266486761022469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126205407607510991174014979 189308111411266486761022469)
          ·
            refine ⟨35495270889612466267691713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189308111411266486761022469 35495270889612466267691713)
            ·
              refine ⟨26621453167209349700768785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35495270889612466267691713 26621453167209349700768785)
              ·
                refine ⟨19966089875407012275576589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26621453167209349700768785 19966089875407012275576589)
                ·
                  refine ⟨7487283703277629603341221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19966089875407012275576589 7487283703277629603341221)
                  ·
                    refine ⟨1403865694364555550626479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7487283703277629603341221 1403865694364555550626479)
                    ·
                      rfl

theorem cell23_8202056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_8202056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202056 prefixEnd_8202056 := by exact prefixLift 8202056
  have htrace : WordTrace (prefixWord ++ tailWord_8202056) baseStart_8202056 baseEnd_8202056 := by
    simpa [prefixWord, tailWord_8202056, baseEnd_8202056] using wordTrace_append hprefix tailTrace_8202056
  have hstable : (prefixWord ++ tailWord_8202056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202056).length < 2 ^ (prefixWord ++ tailWord_8202056).sum := by decide
  have hdescent : baseEnd_8202056 < baseStart_8202056 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202066 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_8202066 : Nat := 118140960795 + 8202066 * 2 ^ 59
def prefixEnd_8202066 : Nat := 4983230072969 + 3 ^ 40 * 8202066 * 2
def baseEnd_8202066 : Nat := 4211602217900211612754391

theorem tailTrace_8202066 : CollatzResearch.WordTrace tailWord_8202066 prefixEnd_8202066 4211602217900211612754391 := by
  unfold tailWord_8202066
  simp only [CollatzResearch.WordTrace]
  refine ⟨74788480875830789548604513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199435949002215438796278701 74788480875830789548604513)
  ·
    refine ⟨56091360656873092161453385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74788480875830789548604513 56091360656873092161453385)
    ·
      refine ⟨42068520492654819121090039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56091360656873092161453385 42068520492654819121090039)
      ·
        refine ⟨63102780738982228681635059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42068520492654819121090039 63102780738982228681635059)
        ·
          refine ⟨94654171108473343022452589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63102780738982228681635059 94654171108473343022452589)
          ·
            refine ⟨35495314165677503633419721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94654171108473343022452589 35495314165677503633419721)
            ·
              refine ⟨26621485624258127725064791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35495314165677503633419721 26621485624258127725064791)
              ·
                refine ⟨39932228436387191587597187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26621485624258127725064791 39932228436387191587597187)
                ·
                  refine ⟨59898342654580787381395781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39932228436387191587597187 59898342654580787381395781)
                  ·
                    refine ⟨11230939247733897634011709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59898342654580787381395781 11230939247733897634011709)
                    ·
                      refine ⟨4211602217900211612754391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11230939247733897634011709 4211602217900211612754391)
                      ·
                        rfl

theorem cell23_8202066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_8202066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202066 prefixEnd_8202066 := by exact prefixLift 8202066
  have htrace : WordTrace (prefixWord ++ tailWord_8202066) baseStart_8202066 baseEnd_8202066 := by
    simpa [prefixWord, tailWord_8202066, baseEnd_8202066] using wordTrace_append hprefix tailTrace_8202066
  have hstable : (prefixWord ++ tailWord_8202066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202066).length < 2 ^ (prefixWord ++ tailWord_8202066).sum := by decide
  have hdescent : baseEnd_8202066 < baseStart_8202066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202069 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 8]
def baseStart_8202069 : Nat := 118140960795 + 8202069 * 2 ^ 59
def prefixEnd_8202069 : Nat := 4983230072969 + 3 ^ 40 * 8202069 * 2
def baseEnd_8202069 : Nat := 467955973149130566779653

theorem tailTrace_8202069 : CollatzResearch.WordTrace tailWord_8202069 prefixEnd_8202069 467955973149130566779653 := by
  unfold tailWord_8202069
  simp only [CollatzResearch.WordTrace]
  refine ⟨299154032922312289706777261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199436021948208193137851507 299154032922312289706777261)
  ·
    refine ⟨112182762345867108640041473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299154032922312289706777261 112182762345867108640041473)
    ·
      refine ⟨84137071759400331480031105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112182762345867108640041473 84137071759400331480031105)
      ·
        refine ⟨63102803819550248610023329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84137071759400331480031105 63102803819550248610023329)
        ·
          refine ⟨47327102864662686457517497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63102803819550248610023329 47327102864662686457517497)
          ·
            refine ⟨35495327148497014843138123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47327102864662686457517497 35495327148497014843138123)
            ·
              refine ⟨53242990722745522264707185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35495327148497014843138123 53242990722745522264707185)
              ·
                refine ⟨39932243042059141698530389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53242990722745522264707185 39932243042059141698530389)
                ·
                  refine ⟨467955973149130566779653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39932243042059141698530389 467955973149130566779653)
                  ·
                    rfl

theorem cell23_8202069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_8202069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202069 prefixEnd_8202069 := by exact prefixLift 8202069
  have htrace : WordTrace (prefixWord ++ tailWord_8202069) baseStart_8202069 baseEnd_8202069 := by
    simpa [prefixWord, tailWord_8202069, baseEnd_8202069] using wordTrace_append hprefix tailTrace_8202069
  have hstable : (prefixWord ++ tailWord_8202069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202069).length < 2 ^ (prefixWord ++ tailWord_8202069).sum := by decide
  have hdescent : baseEnd_8202069 < baseStart_8202069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202083 : List Nat := [1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 3]
def baseStart_8202083 : Nat := 118140960795 + 8202083 * 2 ^ 59
def prefixEnd_8202083 : Nat := 4983230072969 + 3 ^ 40 * 8202083 * 2
def baseEnd_8202083 : Nat := 4211610947071338046241813

theorem tailTrace_8202083 : CollatzResearch.WordTrace tailWord_8202083 prefixEnd_8202083 4211610947071338046241813 := by
  unfold tailWord_8202083
  simp only [CollatzResearch.WordTrace]
  refine ⟨299154543544261570097786903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199436362362841046731857935 299154543544261570097786903)
  ·
    refine ⟨448731815316392355146680355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299154543544261570097786903 448731815316392355146680355)
    ·
      refine ⟨673097722974588532720020533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448731815316392355146680355 673097722974588532720020533)
      ·
        refine ⟨63102911528867674942501925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 673097722974588532720020533 63102911528867674942501925)
        ·
          refine ⟨11831795911662689051719111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63102911528867674942501925 11831795911662689051719111)
          ·
            refine ⟨17747693867494033577578667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11831795911662689051719111 17747693867494033577578667)
            ·
              refine ⟨26621540801241050366368001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17747693867494033577578667 26621540801241050366368001)
              ·
                refine ⟨19966155600930787774776001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26621540801241050366368001 19966155600930787774776001)
                ·
                  refine ⟨14974616700698090831082001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19966155600930787774776001 14974616700698090831082001)
                  ·
                    refine ⟨11230962525523568123311501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14974616700698090831082001 11230962525523568123311501)
                    ·
                      refine ⟨4211610947071338046241813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11230962525523568123311501 4211610947071338046241813)
                      ·
                        rfl

theorem cell23_8202083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_8202083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202083 prefixEnd_8202083 := by exact prefixLift 8202083
  have htrace : WordTrace (prefixWord ++ tailWord_8202083) baseStart_8202083 baseEnd_8202083 := by
    simpa [prefixWord, tailWord_8202083, baseEnd_8202083] using wordTrace_append hprefix tailTrace_8202083
  have hstable : (prefixWord ++ tailWord_8202083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202083).length < 2 ^ (prefixWord ++ tailWord_8202083).sum := by decide
  have hdescent : baseEnd_8202083 < baseStart_8202083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202099 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 3, 5]
def baseStart_8202099 : Nat := 118140960795 + 8202099 * 2 ^ 59
def prefixEnd_8202099 : Nat := 4983230072969 + 3 ^ 40 * 8202099 * 2
def baseEnd_8202099 : Nat := 1403873054253936661213913

theorem tailTrace_8202099 : CollatzResearch.WordTrace tailWord_8202099 prefixEnd_8202099 1403873054253936661213913 := by
  unfold tailWord_8202099
  simp only [CollatzResearch.WordTrace]
  refine ⟨299155127112203604830369351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199436751408135736553579567 299155127112203604830369351)
  ·
    refine ⟨448732690668305407245554027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299155127112203604830369351 448732690668305407245554027)
    ·
      refine ⟨673099036002458110868331041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448732690668305407245554027 673099036002458110868331041)
      ·
        refine ⟨504824277001843583151248281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673099036002458110868331041 504824277001843583151248281)
        ·
          refine ⟨378618207751382687363436211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 504824277001843583151248281 378618207751382687363436211)
          ·
            refine ⟨567927311627074031045154317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378618207751382687363436211 567927311627074031045154317)
            ·
              refine ⟨212972741860152761641932869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 567927311627074031045154317 212972741860152761641932869)
              ·
                refine ⟨39932389098778642807862413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212972741860152761641932869 39932389098778642807862413)
                ·
                  refine ⟨14974645912041991052948405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39932389098778642807862413 14974645912041991052948405)
                  ·
                    refine ⟨1403873054253936661213913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14974645912041991052948405 1403873054253936661213913)
                    ·
                      rfl

theorem cell23_8202099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 5].length) (baseStart_8202099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202099 prefixEnd_8202099 := by exact prefixLift 8202099
  have htrace : WordTrace (prefixWord ++ tailWord_8202099) baseStart_8202099 baseEnd_8202099 := by
    simpa [prefixWord, tailWord_8202099, baseEnd_8202099] using wordTrace_append hprefix tailTrace_8202099
  have hstable : (prefixWord ++ tailWord_8202099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202099).length < 2 ^ (prefixWord ++ tailWord_8202099).sum := by decide
  have hdescent : baseEnd_8202099 < baseStart_8202099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202106 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2]
def baseStart_8202106 : Nat := 118140960795 + 8202106 * 2 ^ 59
def prefixEnd_8202106 : Nat := 4983230072969 + 3 ^ 40 * 8202106 * 2
def baseEnd_8202106 : Nat := 4211622757126391456254207

theorem tailTrace_8202106 : CollatzResearch.WordTrace tailWord_8202106 prefixEnd_8202106 4211622757126391456254207 := by
  unfold tailWord_8202106
  simp only [CollatzResearch.WordTrace]
  refine ⟨74788845605794561256468543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199436921615452163350582781 74788845605794561256468543)
  ·
    refine ⟨112183268408691841884702815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74788845605794561256468543 112183268408691841884702815)
    ·
      refine ⟨168274902613037762827054223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112183268408691841884702815 168274902613037762827054223)
      ·
        refine ⟨252412353919556644240581335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168274902613037762827054223 252412353919556644240581335)
        ·
          refine ⟨378618530879334966360872003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252412353919556644240581335 378618530879334966360872003)
          ·
            refine ⟨567927796319002449541308005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378618530879334966360872003 567927796319002449541308005)
            ·
              refine ⟨106486461809812959288995251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 567927796319002449541308005 106486461809812959288995251)
              ·
                refine ⟨159729692714719438933492877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106486461809812959288995251 159729692714719438933492877)
                ·
                  refine ⟨59898634768019789600059829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159729692714719438933492877 59898634768019789600059829)
                  ·
                    refine ⟨5615497009501855275005609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59898634768019789600059829 5615497009501855275005609)
                    ·
                      refine ⟨4211622757126391456254207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615497009501855275005609 4211622757126391456254207)
                      ·
                        rfl

theorem cell23_8202106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 5, 2].length) (baseStart_8202106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202106 prefixEnd_8202106 := by exact prefixLift 8202106
  have htrace : WordTrace (prefixWord ++ tailWord_8202106) baseStart_8202106 baseEnd_8202106 := by
    simpa [prefixWord, tailWord_8202106, baseEnd_8202106] using wordTrace_append hprefix tailTrace_8202106
  have hstable : (prefixWord ++ tailWord_8202106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202106).length < 2 ^ (prefixWord ++ tailWord_8202106).sum := by decide
  have hdescent : baseEnd_8202106 < baseStart_8202106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202129 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 3, 6]
def baseStart_8202129 : Nat := 118140960795 + 8202129 * 2 ^ 59
def prefixEnd_8202129 : Nat := 4983230072969 + 3 ^ 40 * 8202129 * 2
def baseEnd_8202129 : Nat := 1403878189060481622088867

theorem tailTrace_8202129 : CollatzResearch.WordTrace tailWord_8202129 prefixEnd_8202129 1403878189060481622088867 := by
  unfold tailWord_8202129
  simp only [CollatzResearch.WordTrace]
  refine ⟨299156221302094919953961441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199437480868063279969307627 299156221302094919953961441)
  ·
    refine ⟨224367165976571189965471081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299156221302094919953961441 224367165976571189965471081)
    ·
      refine ⟨168275374482428392474103311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224367165976571189965471081 168275374482428392474103311)
      ·
        refine ⟨252413061723642588711154967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168275374482428392474103311 252413061723642588711154967)
        ·
          refine ⟨378619592585463883066732451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252413061723642588711154967 378619592585463883066732451)
          ·
            refine ⟨567929388878195824600098677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378619592585463883066732451 567929388878195824600098677)
            ·
              refine ⟨53243380207330858556259251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 567929388878195824600098677 53243380207330858556259251)
              ·
                refine ⟨79865070310996287834388877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53243380207330858556259251 79865070310996287834388877)
                ·
                  refine ⟨29949401366623607937895829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79865070310996287834388877 29949401366623607937895829)
                  ·
                    refine ⟨1403878189060481622088867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29949401366623607937895829 1403878189060481622088867)
                    ·
                      rfl

theorem cell23_8202129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_8202129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202129 prefixEnd_8202129 := by exact prefixLift 8202129
  have htrace : WordTrace (prefixWord ++ tailWord_8202129) baseStart_8202129 baseEnd_8202129 := by
    simpa [prefixWord, tailWord_8202129, baseEnd_8202129] using wordTrace_append hprefix tailTrace_8202129
  have hstable : (prefixWord ++ tailWord_8202129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202129).length < 2 ^ (prefixWord ++ tailWord_8202129).sum := by decide
  have hdescent : baseEnd_8202129 < baseStart_8202129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202133 : List Nat := [1, 3, 2, 1, 1, 3, 5, 1, 1, 5]
def baseStart_8202133 : Nat := 118140960795 + 8202133 * 2 ^ 59
def prefixEnd_8202133 : Nat := 4983230072969 + 3 ^ 40 * 8202133 * 2
def baseEnd_8202133 : Nat := 1403878873701354283538861

theorem tailTrace_8202133 : CollatzResearch.WordTrace tailWord_8202133 prefixEnd_8202133 1403878873701354283538861 := by
  unfold tailWord_8202133
  simp only [CollatzResearch.WordTrace]
  refine ⟨299156367194080428637107053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199437578129386952424738035 299156367194080428637107053)
  ·
    refine ⟨112183637697780160738915145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299156367194080428637107053 112183637697780160738915145)
    ·
      refine ⟨84137728273335120554186359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112183637697780160738915145 84137728273335120554186359)
      ·
        refine ⟨126206592410002680831279539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84137728273335120554186359 126206592410002680831279539)
        ·
          refine ⟨189309888615004021246919309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126206592410002680831279539 189309888615004021246919309)
          ·
            refine ⟨70991208230626507967594741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189309888615004021246919309 70991208230626507967594741)
            ·
              refine ⟨6655425771621235121962007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70991208230626507967594741 6655425771621235121962007)
              ·
                refine ⟨9983138657431852682943011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655425771621235121962007 9983138657431852682943011)
                ·
                  refine ⟨14974707986147779024414517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9983138657431852682943011 14974707986147779024414517)
                  ·
                    refine ⟨1403878873701354283538861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14974707986147779024414517 1403878873701354283538861)
                    ·
                      rfl

theorem cell23_8202133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_8202133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202133 prefixEnd_8202133 := by exact prefixLift 8202133
  have htrace : WordTrace (prefixWord ++ tailWord_8202133) baseStart_8202133 baseEnd_8202133 := by
    simpa [prefixWord, tailWord_8202133, baseEnd_8202133] using wordTrace_append hprefix tailTrace_8202133
  have hstable : (prefixWord ++ tailWord_8202133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202133).length < 2 ^ (prefixWord ++ tailWord_8202133).sum := by decide
  have hdescent : baseEnd_8202133 < baseStart_8202133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202140 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 2, 3, 2]
def baseStart_8202140 : Nat := 118140960795 + 8202140 * 2 ^ 59
def prefixEnd_8202140 : Nat := 4983230072969 + 3 ^ 40 * 8202140 * 2
def baseEnd_8202140 : Nat := 4211640215468644323229051

theorem tailTrace_8202140 : CollatzResearch.WordTrace tailWord_8202140 prefixEnd_8202140 4211640215468644323229051 := by
  unfold tailWord_8202140
  simp only [CollatzResearch.WordTrace]
  refine ⟨149578311252527534416305937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199437748336703379221741249 149578311252527534416305937)
  ·
    refine ⟨112183733439395650812229453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149578311252527534416305937 112183733439395650812229453)
    ·
      refine ⟨42068900039773369054586045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112183733439395650812229453 42068900039773369054586045)
      ·
        refine ⟨15775837514915013395469767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42068900039773369054586045 15775837514915013395469767)
        ·
          refine ⟨23663756272372520093204651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15775837514915013395469767 23663756272372520093204651)
          ·
            refine ⟨35495634408558780139806977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23663756272372520093204651 35495634408558780139806977)
            ·
              refine ⟨26621725806419085104855233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35495634408558780139806977 26621725806419085104855233)
              ·
                refine ⟨19966294354814313828641425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26621725806419085104855233 19966294354814313828641425)
                ·
                  refine ⟨14974720766110735371481069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19966294354814313828641425 14974720766110735371481069)
                  ·
                    refine ⟨5615520287291525764305401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14974720766110735371481069 5615520287291525764305401)
                    ·
                      refine ⟨4211640215468644323229051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615520287291525764305401 4211640215468644323229051)
                      ·
                        rfl

theorem cell23_8202140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_8202140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202140 prefixEnd_8202140 := by exact prefixLift 8202140
  have htrace : WordTrace (prefixWord ++ tailWord_8202140) baseStart_8202140 baseEnd_8202140 := by
    simpa [prefixWord, tailWord_8202140, baseEnd_8202140] using wordTrace_append hprefix tailTrace_8202140
  have hstable : (prefixWord ++ tailWord_8202140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202140).length < 2 ^ (prefixWord ++ tailWord_8202140).sum := by decide
  have hdescent : baseEnd_8202140 < baseStart_8202140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202149 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_8202149 : Nat := 118140960795 + 8202149 * 2 ^ 59
def prefixEnd_8202149 : Nat := 4983230072969 + 3 ^ 40 * 8202149 * 2
def baseEnd_8202149 : Nat := 4211644836794534788016509

theorem tailTrace_8202149 : CollatzResearch.WordTrace tailWord_8202149 prefixEnd_8202149 4211644836794534788016509 := by
  unfold tailWord_8202149
  simp only [CollatzResearch.WordTrace]
  refine ⟨299156950762022463369689501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199437967174681642246459667 299156950762022463369689501)
  ·
    refine ⟨112183856535758423763633563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299156950762022463369689501 112183856535758423763633563)
    ·
      refine ⟨168275784803637635645450345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112183856535758423763633563 168275784803637635645450345)
      ·
        refine ⟨126206838602728226734087759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168275784803637635645450345 126206838602728226734087759)
        ·
          refine ⟨189310257904092340101131639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126206838602728226734087759 189310257904092340101131639)
          ·
            refine ⟨283965386856138510151697459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189310257904092340101131639 283965386856138510151697459)
            ·
              refine ⟨425948080284207765227546189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283965386856138510151697459 425948080284207765227546189)
              ·
                refine ⟨159730530106577911960329821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 425948080284207765227546189 159730530106577911960329821)
                ·
                  refine ⟨59898948789966716985123683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159730530106577911960329821 59898948789966716985123683)
                  ·
                    refine ⟨89848423184950075477685525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59898948789966716985123683 89848423184950075477685525)
                    ·
                      refine ⟨4211644836794534788016509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 89848423184950075477685525 4211644836794534788016509)
                      ·
                        rfl

theorem cell23_8202149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_8202149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202149 prefixEnd_8202149 := by exact prefixLift 8202149
  have htrace : WordTrace (prefixWord ++ tailWord_8202149) baseStart_8202149 baseEnd_8202149 := by
    simpa [prefixWord, tailWord_8202149, baseEnd_8202149] using wordTrace_append hprefix tailTrace_8202149
  have hstable : (prefixWord ++ tailWord_8202149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202149).length < 2 ^ (prefixWord ++ tailWord_8202149).sum := by decide
  have hdescent : baseEnd_8202149 < baseStart_8202149 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202173 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_8202173 : Nat := 118140960795 + 8202173 * 2 ^ 59
def prefixEnd_8202173 : Nat := 4983230072969 + 3 ^ 40 * 8202173 * 2
def baseEnd_8202173 : Nat := 4211657160330242694116399

theorem tailTrace_8202173 : CollatzResearch.WordTrace tailWord_8202173 prefixEnd_8202173 4211657160330242694116399 := by
  unfold tailWord_8202173
  simp only [CollatzResearch.WordTrace]
  refine ⟨299157826113935515468563173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199438550742623676979042115 299157826113935515468563173)
  ·
    refine ⟨56092092396362909150355595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299157826113935515468563173 56092092396362909150355595)
    ·
      refine ⟨84138138594544363725533393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56092092396362909150355595 84138138594544363725533393)
      ·
        refine ⟨63103603945908272794150045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84138138594544363725533393 63103603945908272794150045)
        ·
          refine ⟨23663851479715602297806267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63103603945908272794150045 23663851479715602297806267)
          ·
            refine ⟨35495777219573403446709401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23663851479715602297806267 35495777219573403446709401)
            ·
              refine ⟨26621832914680052585032051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35495777219573403446709401 26621832914680052585032051)
              ·
                refine ⟨39932749372020078877548077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26621832914680052585032051 39932749372020078877548077)
                ·
                  refine ⟨14974781014507529579080529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39932749372020078877548077 14974781014507529579080529)
                  ·
                    refine ⟨11231085760880647184310397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14974781014507529579080529 11231085760880647184310397)
                    ·
                      refine ⟨4211657160330242694116399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11231085760880647184310397 4211657160330242694116399)
                      ·
                        rfl

theorem cell23_8202173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_8202173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202173 prefixEnd_8202173 := by exact prefixLift 8202173
  have htrace : WordTrace (prefixWord ++ tailWord_8202173) baseStart_8202173 baseEnd_8202173 := by
    simpa [prefixWord, tailWord_8202173, baseEnd_8202173] using wordTrace_append hprefix tailTrace_8202173
  have hstable : (prefixWord ++ tailWord_8202173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202173).length < 2 ^ (prefixWord ++ tailWord_8202173).sum := by decide
  have hdescent : baseEnd_8202173 < baseStart_8202173 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202176 : List Nat := [2, 1, 1, 2, 3, 2, 5, 7]
def baseStart_8202176 : Nat := 118140960795 + 8202176 * 2 ^ 59
def prefixEnd_8202176 : Nat := 4983230072969 + 3 ^ 40 * 8202176 * 2
def baseEnd_8202176 : Nat := 155987359287859488236255

theorem tailTrace_8202176 : CollatzResearch.WordTrace tailWord_8202176 prefixEnd_8202176 155987359287859488236255 := by
  unfold tailWord_8202176
  simp only [CollatzResearch.WordTrace]
  refine ⟨149578967766462323490461191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199438623688616431320614921 149578967766462323490461191)
  ·
    refine ⟨224368451649693485235691787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149578967766462323490461191 224368451649693485235691787)
    ·
      refine ⟨336552677474540227853537681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224368451649693485235691787 336552677474540227853537681)
      ·
        refine ⟨252414508105905170890153261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336552677474540227853537681 252414508105905170890153261)
        ·
          refine ⟨94655440539714439083807473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252414508105905170890153261 94655440539714439083807473)
          ·
            refine ⟨70991580404785829312855605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94655440539714439083807473 70991580404785829312855605)
            ·
              refine ⟨6655460662948671498080213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70991580404785829312855605 6655460662948671498080213)
              ·
                refine ⟨155987359287859488236255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6655460662948671498080213 155987359287859488236255)
                ·
                  rfl

theorem cell23_8202176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 7].length) (baseStart_8202176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202176 prefixEnd_8202176 := by exact prefixLift 8202176
  have htrace : WordTrace (prefixWord ++ tailWord_8202176) baseStart_8202176 baseEnd_8202176 := by
    simpa [prefixWord, tailWord_8202176, baseEnd_8202176] using wordTrace_append hprefix tailTrace_8202176
  have hstable : (prefixWord ++ tailWord_8202176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202176).length < 2 ^ (prefixWord ++ tailWord_8202176).sum := by decide
  have hdescent : baseEnd_8202176 < baseStart_8202176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202187 : List Nat := [1, 1, 1, 1, 3, 4, 4, 3, 1, 2, 2]
def baseStart_8202187 : Nat := 118140960795 + 8202187 * 2 ^ 59
def prefixEnd_8202187 : Nat := 4983230072969 + 3 ^ 40 * 8202187 * 2
def baseEnd_8202187 : Nat := 4211664349059405639341335

theorem tailTrace_8202187 : CollatzResearch.WordTrace tailWord_8202187 prefixEnd_8202187 4211664349059405639341335 := by
  unfold tailWord_8202187
  simp only [CollatzResearch.WordTrace]
  refine ⟨299158336735884795859572815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199438891157256530573048543 299158336735884795859572815)
  ·
    refine ⟨448737505103827193789359223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299158336735884795859572815 448737505103827193789359223)
    ·
      refine ⟨673106257655740790684038835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448737505103827193789359223 673106257655740790684038835)
      ·
        refine ⟨1009659386483611186026058253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673106257655740790684038835 1009659386483611186026058253)
        ·
          refine ⟨378622269931354194759771845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1009659386483611186026058253 378622269931354194759771845)
          ·
            refine ⟨70991675612128911517457221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378622269931354194759771845 70991675612128911517457221)
            ·
              refine ⟨13310939177274170909523229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70991675612128911517457221 13310939177274170909523229)
              ·
                refine ⟨4991602191477814091071211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13310939177274170909523229 4991602191477814091071211)
                ·
                  refine ⟨7487403287216721136606817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991602191477814091071211 7487403287216721136606817)
                  ·
                    refine ⟨5615552465412540852455113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7487403287216721136606817 5615552465412540852455113)
                    ·
                      refine ⟨4211664349059405639341335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615552465412540852455113 4211664349059405639341335)
                      ·
                        rfl

theorem cell23_8202187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 1, 2, 2].length) (baseStart_8202187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202187 prefixEnd_8202187 := by exact prefixLift 8202187
  have htrace : WordTrace (prefixWord ++ tailWord_8202187) baseStart_8202187 baseEnd_8202187 := by
    simpa [prefixWord, tailWord_8202187, baseEnd_8202187] using wordTrace_append hprefix tailTrace_8202187
  have hstable : (prefixWord ++ tailWord_8202187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202187).length < 2 ^ (prefixWord ++ tailWord_8202187).sum := by decide
  have hdescent : baseEnd_8202187 < baseStart_8202187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202243 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 1, 4, 2]
def baseStart_8202243 : Nat := 118140960795 + 8202243 * 2 ^ 59
def prefixEnd_8202243 : Nat := 4983230072969 + 3 ^ 40 * 8202243 * 2
def baseEnd_8202243 : Nat := 4211693103976057420241077

theorem tailTrace_8202243 : CollatzResearch.WordTrace tailWord_8202243 prefixEnd_8202243 4211693103976057420241077 := by
  unfold tailWord_8202243
  simp only [CollatzResearch.WordTrace]
  refine ⟨299160379223681917423611383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199440252815787944949074255 299160379223681917423611383)
  ·
    refine ⟨448740568835522876135417075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299160379223681917423611383 448740568835522876135417075)
    ·
      refine ⟨673110853253284314203125613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448740568835522876135417075 673110853253284314203125613)
      ·
        refine ⟨252416569969981617826172105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673110853253284314203125613 252416569969981617826172105)
        ·
          refine ⟨189312427477486213369629079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252416569969981617826172105 189312427477486213369629079)
          ·
            refine ⟨283968641216229320054443619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189312427477486213369629079 283968641216229320054443619)
            ·
              refine ⟨425952961824343980081665429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283968641216229320054443619 425952961824343980081665429)
              ·
                refine ⟨19966545085516124066328067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 425952961824343980081665429 19966545085516124066328067)
                ·
                  refine ⟨29949817628274186099492101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19966545085516124066328067 29949817628274186099492101)
                  ·
                    refine ⟨5615590805301409893654769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29949817628274186099492101 5615590805301409893654769)
                    ·
                      refine ⟨4211693103976057420241077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615590805301409893654769 4211693103976057420241077)
                      ·
                        rfl

theorem cell23_8202243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 4, 2].length) (baseStart_8202243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202243 prefixEnd_8202243 := by exact prefixLift 8202243
  have htrace : WordTrace (prefixWord ++ tailWord_8202243) baseStart_8202243 baseEnd_8202243 := by
    simpa [prefixWord, tailWord_8202243, baseEnd_8202243] using wordTrace_append hprefix tailTrace_8202243
  have hstable : (prefixWord ++ tailWord_8202243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202243).length < 2 ^ (prefixWord ++ tailWord_8202243).sum := by decide
  have hdescent : baseEnd_8202243 < baseStart_8202243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202277 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 2, 2, 2]
def baseStart_8202277 : Nat := 118140960795 + 8202277 * 2 ^ 59
def prefixEnd_8202277 : Nat := 4983230072969 + 3 ^ 40 * 8202277 * 2
def baseEnd_8202277 : Nat := 4211710562318310287215921

theorem tailTrace_8202277 : CollatzResearch.WordTrace tailWord_8202277 prefixEnd_8202277 4211710562318310287215921 := by
  unfold tailWord_8202277
  simp only [CollatzResearch.WordTrace]
  refine ⟨299161619305558741230349085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199441079537039160820232723 299161619305558741230349085)
  ·
    refine ⟨112185607239584527961380907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299161619305558741230349085 112185607239584527961380907)
    ·
      refine ⟨168278410859376791942071361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112185607239584527961380907 168278410859376791942071361)
      ·
        refine ⟨126208808144532593956553521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168278410859376791942071361 126208808144532593956553521)
        ·
          refine ⟨94656606108399445467415141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126208808144532593956553521 94656606108399445467415141)
          ·
            refine ⟨17748113645324896025140339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94656606108399445467415141 17748113645324896025140339)
            ·
              refine ⟨26622170467987344037710509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17748113645324896025140339 26622170467987344037710509)
              ·
                refine ⟨9983313925495254014141441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26622170467987344037710509 9983313925495254014141441)
                ·
                  refine ⟨7487485444121440510606081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9983313925495254014141441 7487485444121440510606081)
                  ·
                    refine ⟨5615614083091080382954561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7487485444121440510606081 5615614083091080382954561)
                    ·
                      refine ⟨4211710562318310287215921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615614083091080382954561 4211710562318310287215921)
                      ·
                        rfl

theorem cell23_8202277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_8202277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202277 prefixEnd_8202277 := by exact prefixLift 8202277
  have htrace : WordTrace (prefixWord ++ tailWord_8202277) baseStart_8202277 baseEnd_8202277 := by
    simpa [prefixWord, tailWord_8202277, baseEnd_8202277] using wordTrace_append hprefix tailTrace_8202277
  have hstable : (prefixWord ++ tailWord_8202277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202277).length < 2 ^ (prefixWord ++ tailWord_8202277).sum := by decide
  have hdescent : baseEnd_8202277 < baseStart_8202277 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202350 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2]
def baseStart_8202350 : Nat := 118140960795 + 8202350 * 2 ^ 59
def prefixEnd_8202350 : Nat := 4983230072969 + 3 ^ 40 * 8202350 * 2
def baseEnd_8202350 : Nat := 4211748046406088501603085

theorem tailTrace_8202350 : CollatzResearch.WordTrace tailWord_8202350 prefixEnd_8202350 4211748046406088501603085 := by
  unfold tailWord_8202350
  simp only [CollatzResearch.WordTrace]
  refine ⟨37395535229286784337219563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 199442854556196183131837669 37395535229286784337219563)
  ·
    refine ⟨56093302843930176505829345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37395535229286784337219563 56093302843930176505829345)
    ·
      refine ⟨42069977132947632379372009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56093302843930176505829345 42069977132947632379372009)
      ·
        refine ⟨31552482849710724284529007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42069977132947632379372009 31552482849710724284529007)
        ·
          refine ⟨47328724274566086426793511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31552482849710724284529007 47328724274566086426793511)
          ·
            refine ⟨70993086411849129640190267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47328724274566086426793511 70993086411849129640190267)
            ·
              refine ⟨106489629617773694460285401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70993086411849129640190267 106489629617773694460285401)
              ·
                refine ⟨79867222213330270845214051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106489629617773694460285401 79867222213330270845214051)
                ·
                  refine ⟨119800833319995406267821077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79867222213330270845214051 119800833319995406267821077)
                  ·
                    refine ⟨5615664061874784668804113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119800833319995406267821077 5615664061874784668804113)
                    ·
                      refine ⟨4211748046406088501603085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615664061874784668804113 4211748046406088501603085)
                      ·
                        rfl

theorem cell23_8202350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_8202350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202350 prefixEnd_8202350 := by exact prefixLift 8202350
  have htrace : WordTrace (prefixWord ++ tailWord_8202350) baseStart_8202350 baseEnd_8202350 := by
    simpa [prefixWord, tailWord_8202350, baseEnd_8202350] using wordTrace_append hprefix tailTrace_8202350
  have hstable : (prefixWord ++ tailWord_8202350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202350).length < 2 ^ (prefixWord ++ tailWord_8202350).sum := by decide
  have hdescent : baseEnd_8202350 < baseStart_8202350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202353 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 1, 4, 3]
def baseStart_8202353 : Nat := 118140960795 + 8202353 * 2 ^ 59
def prefixEnd_8202353 : Nat := 4983230072969 + 3 ^ 40 * 8202353 * 2
def baseEnd_8202353 : Nat := 4211749586848051989865571

theorem tailTrace_8202353 : CollatzResearch.WordTrace tailWord_8202353 prefixEnd_8202353 4211749586848051989865571 := by
  unfold tailWord_8202353
  simp only [CollatzResearch.WordTrace]
  refine ⟨299164391253283406210115713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199442927502188937473410475 299164391253283406210115713)
  ·
    refine ⟨224373293439962554657586785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299164391253283406210115713 224373293439962554657586785)
    ·
      refine ⟨168279970079971915993190089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224373293439962554657586785 168279970079971915993190089)
      ·
        refine ⟨126209977559978936994892567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168279970079971915993190089 126209977559978936994892567)
        ·
          refine ⟨189314966339968405492338851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126209977559978936994892567 189314966339968405492338851)
          ·
            refine ⟨283972449509952608238508277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189314966339968405492338851 283972449509952608238508277)
            ·
              refine ⟨26622417141558057022360151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 283972449509952608238508277 26622417141558057022360151)
              ·
                refine ⟨39933625712337085533540227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26622417141558057022360151 39933625712337085533540227)
                ·
                  refine ⟨59900438568505628300310341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39933625712337085533540227 59900438568505628300310341)
                  ·
                    refine ⟨11231332231594805306308189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59900438568505628300310341 11231332231594805306308189)
                    ·
                      refine ⟨4211749586848051989865571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11231332231594805306308189 4211749586848051989865571)
                      ·
                        rfl

theorem cell23_8202353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_8202353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202353 prefixEnd_8202353 := by exact prefixLift 8202353
  have htrace : WordTrace (prefixWord ++ tailWord_8202353) baseStart_8202353 baseEnd_8202353 := by
    simpa [prefixWord, tailWord_8202353, baseEnd_8202353] using wordTrace_append hprefix tailTrace_8202353
  have hstable : (prefixWord ++ tailWord_8202353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202353).length < 2 ^ (prefixWord ++ tailWord_8202353).sum := by decide
  have hdescent : baseEnd_8202353 < baseStart_8202353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202373 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 8]
def baseStart_8202373 : Nat := 118140960795 + 8202373 * 2 ^ 59
def prefixEnd_8202373 : Nat := 4983230072969 + 3 ^ 40 * 8202373 * 2
def baseEnd_8202373 : Nat := 467973317384571323512831

theorem tailTrace_8202373 : CollatzResearch.WordTrace tailWord_8202373 prefixEnd_8202373 467973317384571323512831 := by
  unfold tailWord_8202373
  simp only [CollatzResearch.WordTrace]
  refine ⟨299165120713210949625843773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199443413808807299750562515 299165120713210949625843773)
  ·
    refine ⟨112186920267454106109691415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299165120713210949625843773 112186920267454106109691415)
    ·
      refine ⟨168280380401181159164537123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112186920267454106109691415 168280380401181159164537123)
      ·
        refine ⟨252420570601771738746805685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168280380401181159164537123 252420570601771738746805685)
        ·
          refine ⟨23664428493916100507513033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252420570601771738746805685 23664428493916100507513033)
          ·
            refine ⟨17748321370437075380634775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23664428493916100507513033 17748321370437075380634775)
            ·
              refine ⟨26622482055655613070952163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17748321370437075380634775 26622482055655613070952163)
              ·
                refine ⟨39933723083483419606428245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26622482055655613070952163 39933723083483419606428245)
                ·
                  refine ⟨467973317384571323512831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39933723083483419606428245 467973317384571323512831)
                  ·
                    rfl

theorem cell23_8202373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_8202373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202373 prefixEnd_8202373 := by exact prefixLift 8202373
  have htrace : WordTrace (prefixWord ++ tailWord_8202373) baseStart_8202373 baseEnd_8202373 := by
    simpa [prefixWord, tailWord_8202373, baseEnd_8202373] using wordTrace_append hprefix tailTrace_8202373
  have hstable : (prefixWord ++ tailWord_8202373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202373).length < 2 ^ (prefixWord ++ tailWord_8202373).sum := by decide
  have hdescent : baseEnd_8202373 < baseStart_8202373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202443 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 5]
def baseStart_8202443 : Nat := 118140960795 + 8202443 * 2 ^ 59
def prefixEnd_8202443 : Nat := 4983230072969 + 3 ^ 40 * 8202443 * 2
def baseEnd_8202443 : Nat := 4211795800106956637740157

theorem tailTrace_8202443 : CollatzResearch.WordTrace tailWord_8202443 prefixEnd_8202443 4211795800106956637740157 := by
  unfold tailWord_8202443
  simp only [CollatzResearch.WordTrace]
  refine ⟨299167673822957351580891983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199445115881971567720594655 299167673822957351580891983)
  ·
    refine ⟨448751510734436027371337975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299167673822957351580891983 448751510734436027371337975)
    ·
      refine ⟨673127266101654041057006963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448751510734436027371337975 673127266101654041057006963)
      ·
        refine ⟨1009690899152481061585510445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673127266101654041057006963 1009690899152481061585510445)
        ·
          refine ⟨378634087182180398094566417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1009690899152481061585510445 378634087182180398094566417)
          ·
            refine ⟨283975565386635298570924813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378634087182180398094566417 283975565386635298570924813)
            ·
              refine ⟨106490837019988236964096805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283975565386635298570924813 106490837019988236964096805)
              ·
                refine ⟨19967031941247794430768151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106490837019988236964096805 19967031941247794430768151)
                ·
                  refine ⟨29950547911871691646152227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19967031941247794430768151 29950547911871691646152227)
                  ·
                    refine ⟨44925821867807537469228341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29950547911871691646152227 44925821867807537469228341)
                    ·
                      refine ⟨4211795800106956637740157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44925821867807537469228341 4211795800106956637740157)
                      ·
                        rfl

theorem cell23_8202443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 5].length) (baseStart_8202443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202443 prefixEnd_8202443 := by exact prefixLift 8202443
  have htrace : WordTrace (prefixWord ++ tailWord_8202443) baseStart_8202443 baseEnd_8202443 := by
    simpa [prefixWord, tailWord_8202443, baseEnd_8202443] using wordTrace_append hprefix tailTrace_8202443
  have hstable : (prefixWord ++ tailWord_8202443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202443).length < 2 ^ (prefixWord ++ tailWord_8202443).sum := by decide
  have hdescent : baseEnd_8202443 < baseStart_8202443 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202454 : List Nat := [5, 2, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_8202454 : Nat := 118140960795 + 8202454 * 2 ^ 59
def prefixEnd_8202454 : Nat := 4983230072969 + 3 ^ 40 * 8202454 * 2
def baseEnd_8202454 : Nat := 1403933816131385364900869

theorem tailTrace_8202454 : CollatzResearch.WordTrace tailWord_8202454 prefixEnd_8202454 1403933816131385364900869 := by
  unfold tailWord_8202454
  simp only [CollatzResearch.WordTrace]
  refine ⟨18698004689119843778721401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 199445383350611666973028277 18698004689119843778721401)
  ·
    refine ⟨14023503516839882834041051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18698004689119843778721401 14023503516839882834041051)
    ·
      refine ⟨21035255275259824251061577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14023503516839882834041051 21035255275259824251061577)
      ·
        refine ⟨15776441456444868188296183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21035255275259824251061577 15776441456444868188296183)
        ·
          refine ⟨23664662184667302282444275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15776441456444868188296183 23664662184667302282444275)
          ·
            refine ⟨35496993277000953423666413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23664662184667302282444275 35496993277000953423666413)
            ·
              refine ⟨13311372478875357533874905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35496993277000953423666413 13311372478875357533874905)
              ·
                refine ⟨9983529359156518150406179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13311372478875357533874905 9983529359156518150406179)
                ·
                  refine ⟨14975294038734777225609269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9983529359156518150406179 14975294038734777225609269)
                  ·
                    refine ⟨1403933816131385364900869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14975294038734777225609269 1403933816131385364900869)
                    ·
                      rfl

theorem cell23_8202454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_8202454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202454 prefixEnd_8202454 := by exact prefixLift 8202454
  have htrace : WordTrace (prefixWord ++ tailWord_8202454) baseStart_8202454 baseEnd_8202454 := by
    simpa [prefixWord, tailWord_8202454, baseEnd_8202454] using wordTrace_append hprefix tailTrace_8202454
  have hstable : (prefixWord ++ tailWord_8202454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202454).length < 2 ^ (prefixWord ++ tailWord_8202454).sum := by decide
  have hdescent : baseEnd_8202454 < baseStart_8202454 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202457 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 3, 2, 2]
def baseStart_8202457 : Nat := 118140960795 + 8202457 * 2 ^ 59
def prefixEnd_8202457 : Nat := 4983230072969 + 3 ^ 40 * 8202457 * 2
def baseEnd_8202457 : Nat := 4211802988836119582965093

theorem tailTrace_8202457 : CollatzResearch.WordTrace tailWord_8202457 prefixEnd_8202457 4211802988836119582965093 := by
  unfold tailWord_8202457
  simp only [CollatzResearch.WordTrace]
  refine ⟨299168184444906631971901625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199445456296604421314601083 299168184444906631971901625)
  ·
    refine ⟨224376138333679973978926219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299168184444906631971901625 224376138333679973978926219)
    ·
      refine ⟨336564207500519960968389329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224376138333679973978926219 336564207500519960968389329)
      ·
        refine ⟨252423155625389970726291997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336564207500519960968389329 252423155625389970726291997)
        ·
          refine ⟨94658683359521239022359499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252423155625389970726291997 94658683359521239022359499)
          ·
            refine ⟨141988025039281858533539249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94658683359521239022359499 141988025039281858533539249)
            ·
              refine ⟨106491018779461393900154437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141988025039281858533539249 106491018779461393900154437)
              ·
                refine ⟨19967066021149011356278957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106491018779461393900154437 19967066021149011356278957)
                ·
                  refine ⟨7487649757930879258604609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19967066021149011356278957 7487649757930879258604609)
                  ·
                    refine ⟨5615737318448159443953457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7487649757930879258604609 5615737318448159443953457)
                    ·
                      refine ⟨4211802988836119582965093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615737318448159443953457 4211802988836119582965093)
                      ·
                        rfl

theorem cell23_8202457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 2, 2].length) (baseStart_8202457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202457 prefixEnd_8202457 := by exact prefixLift 8202457
  have htrace : WordTrace (prefixWord ++ tailWord_8202457) baseStart_8202457 baseEnd_8202457 := by
    simpa [prefixWord, tailWord_8202457, baseEnd_8202457] using wordTrace_append hprefix tailTrace_8202457
  have hstable : (prefixWord ++ tailWord_8202457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202457).length < 2 ^ (prefixWord ++ tailWord_8202457).sum := by decide
  have hdescent : baseEnd_8202457 < baseStart_8202457 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202467 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 1, 6]
def baseStart_8202467 : Nat := 118140960795 + 8202467 * 2 ^ 59
def prefixEnd_8202467 : Nat := 4983230072969 + 3 ^ 40 * 8202467 * 2
def baseEnd_8202467 : Nat := 1403936041214221514613349

theorem tailTrace_8202467 : CollatzResearch.WordTrace tailWord_8202467 prefixEnd_8202467 1403936041214221514613349 := by
  unfold tailWord_8202467
  simp only [CollatzResearch.WordTrace]
  refine ⟨299168549174870403679765655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199445699449913602453177103 299168549174870403679765655)
  ·
    refine ⟨448752823762305605519648483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299168549174870403679765655 448752823762305605519648483)
    ·
      refine ⟨673129235643458408279472725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448752823762305605519648483 673129235643458408279472725)
      ·
        refine ⟨7888233230196778222025071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 673129235643458408279472725 7888233230196778222025071)
        ·
          refine ⟨11832349845295167333037607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7888233230196778222025071 11832349845295167333037607)
          ·
            refine ⟨17748524767942750999556411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11832349845295167333037607 17748524767942750999556411)
            ·
              refine ⟨26622787151914126499334617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17748524767942750999556411 26622787151914126499334617)
              ·
                refine ⟨19967090363935594874500963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26622787151914126499334617 19967090363935594874500963)
                ·
                  refine ⟨29950635545903392311751445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19967090363935594874500963 29950635545903392311751445)
                  ·
                    refine ⟨1403936041214221514613349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29950635545903392311751445 1403936041214221514613349)
                    ·
                      rfl

theorem cell23_8202467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 6].length) (baseStart_8202467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202467 prefixEnd_8202467 := by exact prefixLift 8202467
  have htrace : WordTrace (prefixWord ++ tailWord_8202467) baseStart_8202467 baseEnd_8202467 := by
    simpa [prefixWord, tailWord_8202467, baseEnd_8202467] using wordTrace_append hprefix tailTrace_8202467
  have hstable : (prefixWord ++ tailWord_8202467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202467).length < 2 ^ (prefixWord ++ tailWord_8202467).sum := by decide
  have hdescent : baseEnd_8202467 < baseStart_8202467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202507 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 2, 1, 3]
def baseStart_8202507 : Nat := 118140960795 + 8202507 * 2 ^ 59
def prefixEnd_8202507 : Nat := 4983230072969 + 3 ^ 40 * 8202507 * 2
def baseEnd_8202507 : Nat := 4211828662868844387339863

theorem tailTrace_8202507 : CollatzResearch.WordTrace tailWord_8202507 prefixEnd_8202507 4211828662868844387339863 := by
  unfold tailWord_8202507
  simp only [CollatzResearch.WordTrace]
  refine ⟨299170008094725490511221775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199446672063150327007481183 299170008094725490511221775)
  ·
    refine ⟨448755012142088235766832663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299170008094725490511221775 448755012142088235766832663)
    ·
      refine ⟨673132518213132353650248995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448755012142088235766832663 673132518213132353650248995)
      ·
        refine ⟨1009698777319698530475373493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673132518213132353650248995 1009698777319698530475373493)
        ·
          refine ⟨94659260373721737232066265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1009698777319698530475373493 94659260373721737232066265)
          ·
            refine ⟨70994445280291302924049699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94659260373721737232066265 70994445280291302924049699)
            ·
              refine ⟨106491667920436954386074549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70994445280291302924049699 106491667920436954386074549)
              ·
                refine ⟨9983593867540964473694489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106491667920436954386074549 9983593867540964473694489)
                ·
                  refine ⟨7487695400655723355270867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9983593867540964473694489 7487695400655723355270867)
                  ·
                    refine ⟨11231543100983585032906301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7487695400655723355270867 11231543100983585032906301)
                    ·
                      refine ⟨4211828662868844387339863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11231543100983585032906301 4211828662868844387339863)
                      ·
                        rfl

theorem cell23_8202507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 2, 1, 3].length) (baseStart_8202507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202507 prefixEnd_8202507 := by exact prefixLift 8202507
  have htrace : WordTrace (prefixWord ++ tailWord_8202507) baseStart_8202507 baseEnd_8202507 := by
    simpa [prefixWord, tailWord_8202507, baseEnd_8202507] using wordTrace_append hprefix tailTrace_8202507
  have hstable : (prefixWord ++ tailWord_8202507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202507).length < 2 ^ (prefixWord ++ tailWord_8202507).sum := by decide
  have hdescent : baseEnd_8202507 < baseStart_8202507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202517 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 3, 3, 2]
def baseStart_8202517 : Nat := 118140960795 + 8202517 * 2 ^ 59
def prefixEnd_8202517 : Nat := 4983230072969 + 3 ^ 40 * 8202517 * 2
def baseEnd_8202517 : Nat := 4211833797675389348214817

theorem tailTrace_8202517 : CollatzResearch.WordTrace tailWord_8202517 prefixEnd_8202517 4211833797675389348214817 := by
  unfold tailWord_8202517
  simp only [CollatzResearch.WordTrace]
  refine ⟨299170372824689262219085805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199446915216459508146057203 299170372824689262219085805)
  ·
    refine ⟨112188889809258473332157177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299170372824689262219085805 112188889809258473332157177)
    ·
      refine ⟨84141667356943854999117883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112188889809258473332157177 84141667356943854999117883)
      ·
        refine ⟨126212501035415782498676825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84141667356943854999117883 126212501035415782498676825)
        ·
          refine ⟨94659375776561836874007619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126212501035415782498676825 94659375776561836874007619)
          ·
            refine ⟨141989063664842755311011429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94659375776561836874007619 141989063664842755311011429)
            ·
              refine ⟨26622949437158016620814643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141989063664842755311011429 26622949437158016620814643)
              ·
                refine ⟨39934424155737024931221965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26622949437158016620814643 39934424155737024931221965)
                ·
                  refine ⟨14975409058401384349208237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39934424155737024931221965 14975409058401384349208237)
                  ·
                    refine ⟨5615778396900519130953089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14975409058401384349208237 5615778396900519130953089)
                    ·
                      refine ⟨4211833797675389348214817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615778396900519130953089 4211833797675389348214817)
                      ·
                        rfl

theorem cell23_8202517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_8202517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202517 prefixEnd_8202517 := by exact prefixLift 8202517
  have htrace : WordTrace (prefixWord ++ tailWord_8202517) baseStart_8202517 baseEnd_8202517 := by
    simpa [prefixWord, tailWord_8202517, baseEnd_8202517] using wordTrace_append hprefix tailTrace_8202517
  have hstable : (prefixWord ++ tailWord_8202517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202517).length < 2 ^ (prefixWord ++ tailWord_8202517).sum := by decide
  have hdescent : baseEnd_8202517 < baseStart_8202517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202535 : List Nat := [1, 1, 8, 1, 2, 1, 1, 2, 2, 4]
def baseStart_8202535 : Nat := 118140960795 + 8202535 * 2 ^ 59
def prefixEnd_8202535 : Nat := 4983230072969 + 3 ^ 40 * 8202535 * 2
def baseEnd_8202535 : Nat := 1403947680109056759263245

theorem tailTrace_8202535 : CollatzResearch.WordTrace tailWord_8202535 prefixEnd_8202535 1403947680109056759263245 := by
  unfold tailWord_8202535
  simp only [CollatzResearch.WordTrace]
  refine ⟨299171029338624051293241059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199447352892416034195494039 299171029338624051293241059)
  ·
    refine ⟨448756544007936076939861589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299171029338624051293241059 448756544007936076939861589)
    ·
      refine ⟨5258865750093000901639003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 448756544007936076939861589 5258865750093000901639003)
      ·
        refine ⟨7888298625139501352458505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258865750093000901639003 7888298625139501352458505)
        ·
          refine ⟨5916223968854626014343879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7888298625139501352458505 5916223968854626014343879)
          ·
            refine ⟨8874335953281939021515819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916223968854626014343879 8874335953281939021515819)
            ·
              refine ⟨13311503929922908532273729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8874335953281939021515819 13311503929922908532273729)
              ·
                refine ⟨9983627947442181399205297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13311503929922908532273729 9983627947442181399205297)
                ·
                  refine ⟨7487720960581636049403973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9983627947442181399205297 7487720960581636049403973)
                  ·
                    refine ⟨1403947680109056759263245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7487720960581636049403973 1403947680109056759263245)
                    ·
                      rfl

theorem cell23_8202535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_8202535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202535 prefixEnd_8202535 := by exact prefixLift 8202535
  have htrace : WordTrace (prefixWord ++ tailWord_8202535) baseStart_8202535 baseEnd_8202535 := by
    simpa [prefixWord, tailWord_8202535, baseEnd_8202535] using wordTrace_append hprefix tailTrace_8202535
  have hstable : (prefixWord ++ tailWord_8202535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202535).length < 2 ^ (prefixWord ++ tailWord_8202535).sum := by decide
  have hdescent : baseEnd_8202535 < baseStart_8202535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202541 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_8202541 : Nat := 118140960795 + 8202541 * 2 ^ 59
def prefixEnd_8202541 : Nat := 4983230072969 + 3 ^ 40 * 8202541 * 2
def baseEnd_8202541 : Nat := 4211846121211097254314707

theorem tailTrace_8202541 : CollatzResearch.WordTrace tailWord_8202541 prefixEnd_8202541 4211846121211097254314707 := by
  unfold tailWord_8202541
  simp only [CollatzResearch.WordTrace]
  refine ⟨299171248176602314317959477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199447498784401542878639651 299171248176602314317959477)
  ·
    refine ⟨28047304516556466967308701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 299171248176602314317959477 28047304516556466967308701)
    ·
      refine ⟨10517739193708675112740763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28047304516556466967308701 10517739193708675112740763)
      ·
        refine ⟨15776608790563012669111145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10517739193708675112740763 15776608790563012669111145)
        ·
          refine ⟨11832456592922259501833359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15776608790563012669111145 11832456592922259501833359)
          ·
            refine ⟨17748684889383389252750039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11832456592922259501833359 17748684889383389252750039)
            ·
              refine ⟨26623027334075083879125059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17748684889383389252750039 26623027334075083879125059)
              ·
                refine ⟨39934541001112625818687589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26623027334075083879125059 39934541001112625818687589)
                ·
                  refine ⟨7487726437708617341003923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39934541001112625818687589 7487726437708617341003923)
                  ·
                    refine ⟨11231589656562926011505885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7487726437708617341003923 11231589656562926011505885)
                    ·
                      refine ⟨4211846121211097254314707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11231589656562926011505885 4211846121211097254314707)
                      ·
                        rfl

theorem cell23_8202541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_8202541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202541 prefixEnd_8202541 := by exact prefixLift 8202541
  have htrace : WordTrace (prefixWord ++ tailWord_8202541) baseStart_8202541 baseEnd_8202541 := by
    simpa [prefixWord, tailWord_8202541, baseEnd_8202541] using wordTrace_append hprefix tailTrace_8202541
  have hstable : (prefixWord ++ tailWord_8202541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202541).length < 2 ^ (prefixWord ++ tailWord_8202541).sum := by decide
  have hdescent : baseEnd_8202541 < baseStart_8202541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202604 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 7]
def baseStart_8202604 : Nat := 118140960795 + 8202604 * 2 ^ 59
def prefixEnd_8202604 : Nat := 4983230072969 + 3 ^ 40 * 8202604 * 2
def baseEnd_8202604 : Nat := 467986496721370056425213

theorem tailTrace_8202604 : CollatzResearch.WordTrace tailWord_8202604 prefixEnd_8202604 467986496721370056425213 := by
  unfold tailWord_8202604
  simp only [CollatzResearch.WordTrace]
  refine ⟨149586772987687038038751433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199449030650249384051668577 149586772987687038038751433)
  ·
    refine ⟨112190079740765278529063575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149586772987687038038751433 112190079740765278529063575)
    ·
      refine ⟨168285119611147917793595363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112190079740765278529063575 168285119611147917793595363)
      ·
        refine ⟨252427679416721876690393045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168285119611147917793595363 252427679416721876690393045)
        ·
          refine ⟨5916273736329418984931087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 252427679416721876690393045 5916273736329418984931087)
          ·
            refine ⟨8874410604494128477396631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916273736329418984931087 8874410604494128477396631)
            ·
              refine ⟨13311615906741192716094947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8874410604494128477396631 13311615906741192716094947)
              ·
                refine ⟨19967423860111789074142421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13311615906741192716094947 19967423860111789074142421)
                ·
                  refine ⟨467986496721370056425213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19967423860111789074142421 467986496721370056425213)
                  ·
                    rfl

theorem cell23_8202604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_8202604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202604 prefixEnd_8202604 := by exact prefixLift 8202604
  have htrace : WordTrace (prefixWord ++ tailWord_8202604) baseStart_8202604 baseEnd_8202604 := by
    simpa [prefixWord, tailWord_8202604, baseEnd_8202604] using wordTrace_append hprefix tailTrace_8202604
  have hstable : (prefixWord ++ tailWord_8202604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202604).length < 2 ^ (prefixWord ++ tailWord_8202604).sum := by decide
  have hdescent : baseEnd_8202604 < baseStart_8202604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202610 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_8202610 : Nat := 118140960795 + 8202610 * 2 ^ 59
def prefixEnd_8202610 : Nat := 4983230072969 + 3 ^ 40 * 8202610 * 2
def baseEnd_8202610 : Nat := 4211881551376257484351889

theorem tailTrace_8202610 : CollatzResearch.WordTrace tailWord_8202610 prefixEnd_8202610 4211881551376257484351889 := by
  unfold tailWord_8202610
  simp only [CollatzResearch.WordTrace]
  refine ⟨74793441203338084775555321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199449176542234892734814189 74793441203338084775555321)
  ·
    refine ⟨56095080902503563581666491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74793441203338084775555321 56095080902503563581666491)
    ·
      refine ⟨84142621353755345372499737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56095080902503563581666491 84142621353755345372499737)
      ·
        refine ⟨63106966015316509029374803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84142621353755345372499737 63106966015316509029374803)
        ·
          refine ⟨94660449022974763544062205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63106966015316509029374803 94660449022974763544062205)
          ·
            refine ⟨35497668383615536329023327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94660449022974763544062205 35497668383615536329023327)
            ·
              refine ⟨53246502575423304493534991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35497668383615536329023327 53246502575423304493534991)
              ·
                refine ⟨79869753863134956740302487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53246502575423304493534991 79869753863134956740302487)
                ·
                  refine ⟨119804630794702435110453731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79869753863134956740302487 119804630794702435110453731)
                  ·
                    refine ⟨179706946192053652665680597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119804630794702435110453731 179706946192053652665680597)
                    ·
                      refine ⟨4211881551376257484351889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 179706946192053652665680597 4211881551376257484351889)
                      ·
                        rfl

theorem cell23_8202610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_8202610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202610 prefixEnd_8202610 := by exact prefixLift 8202610
  have htrace : WordTrace (prefixWord ++ tailWord_8202610) baseStart_8202610 baseEnd_8202610 := by
    simpa [prefixWord, tailWord_8202610, baseEnd_8202610] using wordTrace_append hprefix tailTrace_8202610
  have hstable : (prefixWord ++ tailWord_8202610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202610).length < 2 ^ (prefixWord ++ tailWord_8202610).sum := by decide
  have hdescent : baseEnd_8202610 < baseStart_8202610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202620 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_8202620 : Nat := 118140960795 + 8202620 * 2 ^ 59
def prefixEnd_8202620 : Nat := 4983230072969 + 3 ^ 40 * 8202620 * 2
def baseEnd_8202620 : Nat := 4211886686182802445226843

theorem tailTrace_8202620 : CollatzResearch.WordTrace tailWord_8202620 prefixEnd_8202620 4211886686182802445226843 := by
  unfold tailWord_8202620
  simp only [CollatzResearch.WordTrace]
  refine ⟨149587064771658055405042657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199449419695544073873390209 149587064771658055405042657)
  ·
    refine ⟨112190298578743541553781993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149587064771658055405042657 112190298578743541553781993)
    ·
      refine ⟨84142723934057656165336495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112190298578743541553781993 84142723934057656165336495)
      ·
        refine ⟨126214085901086484248004743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84142723934057656165336495 126214085901086484248004743)
        ·
          refine ⟨189321128851629726372007115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126214085901086484248004743 189321128851629726372007115)
          ·
            refine ⟨283981693277444589558010673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189321128851629726372007115 283981693277444589558010673)
            ·
              refine ⟨212986269958083442168508005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283981693277444589558010673 212986269958083442168508005)
              ·
                refine ⟨39934925617140645406595251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212986269958083442168508005 39934925617140645406595251)
                ·
                  refine ⟨59902388425710968109892877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39934925617140645406595251 59902388425710968109892877)
                  ·
                    refine ⟨22463395659641613041209829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59902388425710968109892877 22463395659641613041209829)
                    ·
                      refine ⟨4211886686182802445226843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22463395659641613041209829 4211886686182802445226843)
                      ·
                        rfl

theorem cell23_8202620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_8202620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202620 prefixEnd_8202620 := by exact prefixLift 8202620
  have htrace : WordTrace (prefixWord ++ tailWord_8202620) baseStart_8202620 baseEnd_8202620 := by
    simpa [prefixWord, tailWord_8202620, baseEnd_8202620] using wordTrace_append hprefix tailTrace_8202620
  have hstable : (prefixWord ++ tailWord_8202620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202620).length < 2 ^ (prefixWord ++ tailWord_8202620).sum := by decide
  have hdescent : baseEnd_8202620 < baseStart_8202620 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202660 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 8]
def baseStart_8202660 : Nat := 118140960795 + 8202660 * 2 ^ 59
def prefixEnd_8202660 : Nat := 4983230072969 + 3 ^ 40 * 8202660 * 2
def baseEnd_8202660 : Nat := 467989691712109143191851

theorem tailTrace_8202660 : CollatzResearch.WordTrace tailWord_8202660 prefixEnd_8202660 467989691712109143191851 := by
  unfold tailWord_8202660
  simp only [CollatzResearch.WordTrace]
  refine ⟨149587794231585598820770717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199450392308780798427694289 149587794231585598820770717)
  ·
    refine ⟨56095422836844599557789019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149587794231585598820770717 56095422836844599557789019)
    ·
      refine ⟨84143134255266899336683529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56095422836844599557789019 84143134255266899336683529)
      ·
        refine ⟨63107350691450174502512647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84143134255266899336683529 63107350691450174502512647)
        ·
          refine ⟨94661026037175261753768971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63107350691450174502512647 94661026037175261753768971)
          ·
            refine ⟨141991539055762892630653457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94661026037175261753768971 141991539055762892630653457)
            ·
              refine ⟨106493654291822169472990093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141991539055762892630653457 106493654291822169472990093)
              ·
                refine ⟨39935120359433313552371285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106493654291822169472990093 39935120359433313552371285)
                ·
                  refine ⟨467989691712109143191851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39935120359433313552371285 467989691712109143191851)
                  ·
                    rfl

theorem cell23_8202660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_8202660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202660 prefixEnd_8202660 := by exact prefixLift 8202660
  have htrace : WordTrace (prefixWord ++ tailWord_8202660) baseStart_8202660 baseEnd_8202660 := by
    simpa [prefixWord, tailWord_8202660, baseEnd_8202660] using wordTrace_append hprefix tailTrace_8202660
  have hstable : (prefixWord ++ tailWord_8202660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202660).length < 2 ^ (prefixWord ++ tailWord_8202660).sum := by decide
  have hdescent : baseEnd_8202660 < baseStart_8202660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202714 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2]
def baseStart_8202714 : Nat := 118140960795 + 8202714 * 2 ^ 59
def prefixEnd_8202714 : Nat := 4983230072969 + 3 ^ 40 * 8202714 * 2
def baseEnd_8202714 : Nat := 4211934953364325077451411

theorem tailTrace_8202714 : CollatzResearch.WordTrace tailWord_8202714 prefixEnd_8202714 4211934953364325077451411 := by
  unfold tailWord_8202714
  simp only [CollatzResearch.WordTrace]
  refine ⟨74794389501243891216001799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199451705336650376576004797 74794389501243891216001799)
  ·
    refine ⟨112191584251865836824002699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74794389501243891216001799 112191584251865836824002699)
    ·
      refine ⟨168287376377798755236004049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112191584251865836824002699 168287376377798755236004049)
      ·
        refine ⟨126215532283349066427003037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168287376377798755236004049 126215532283349066427003037)
        ·
          refine ⟨47330824606255899910126139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126215532283349066427003037 47330824606255899910126139)
          ·
            refine ⟨70996236909383849865189209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47330824606255899910126139 70996236909383849865189209)
            ·
              refine ⟨53247177682037887398891907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70996236909383849865189209 53247177682037887398891907)
              ·
                refine ⟨79870766523056831098337861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53247177682037887398891907 79870766523056831098337861)
                ·
                  refine ⟨14975768723073155830938349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79870766523056831098337861 14975768723073155830938349)
                  ·
                    refine ⟨5615913271152433436601881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14975768723073155830938349 5615913271152433436601881)
                    ·
                      refine ⟨4211934953364325077451411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615913271152433436601881 4211934953364325077451411)
                      ·
                        rfl

theorem cell23_8202714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2].length) (baseStart_8202714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202714 prefixEnd_8202714 := by exact prefixLift 8202714
  have htrace : WordTrace (prefixWord ++ tailWord_8202714) baseStart_8202714 baseEnd_8202714 := by
    simpa [prefixWord, tailWord_8202714, baseEnd_8202714] using wordTrace_append hprefix tailTrace_8202714
  have hstable : (prefixWord ++ tailWord_8202714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202714).length < 2 ^ (prefixWord ++ tailWord_8202714).sum := by decide
  have hdescent : baseEnd_8202714 < baseStart_8202714 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202721 : List Nat := [1, 2, 3, 1, 2, 2, 1, 6, 1, 1, 3]
def baseStart_8202721 : Nat := 118140960795 + 8202721 * 2 ^ 59
def prefixEnd_8202721 : Nat := 4983230072969 + 3 ^ 40 * 8202721 * 2
def baseEnd_8202721 : Nat := 4211938547728906550063879

theorem tailTrace_8202721 : CollatzResearch.WordTrace tailWord_8202721 prefixEnd_8202721 4211938547728906550063879 := by
  unfold tailWord_8202721
  simp only [CollatzResearch.WordTrace]
  refine ⟨299177813315950205059512017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199451875543966803373008011 299177813315950205059512017)
  ·
    refine ⟨224383359986962653794634013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299177813315950205059512017 224383359986962653794634013)
    ·
      refine ⟨84143759995110995172987755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224383359986962653794634013 84143759995110995172987755)
      ·
        refine ⟨126215639992666492759481633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84143759995110995172987755 126215639992666492759481633)
        ·
          refine ⟨94661729994499869569611225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126215639992666492759481633 94661729994499869569611225)
          ·
            refine ⟨70996297495874902177208419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94661729994499869569611225 70996297495874902177208419)
            ·
              refine ⟨106494446243812353265812629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70996297495874902177208419 106494446243812353265812629)
              ·
                refine ⟨4991927167678704059334967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106494446243812353265812629 4991927167678704059334967)
                ·
                  refine ⟨7487890751518056089002451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991927167678704059334967 7487890751518056089002451)
                  ·
                    refine ⟨11231836127277084133503677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7487890751518056089002451 11231836127277084133503677)
                    ·
                      refine ⟨4211938547728906550063879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11231836127277084133503677 4211938547728906550063879)
                      ·
                        rfl

theorem cell23_8202721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_8202721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202721 prefixEnd_8202721 := by exact prefixLift 8202721
  have htrace : WordTrace (prefixWord ++ tailWord_8202721) baseStart_8202721 baseEnd_8202721 := by
    simpa [prefixWord, tailWord_8202721, baseEnd_8202721] using wordTrace_append hprefix tailTrace_8202721
  have hstable : (prefixWord ++ tailWord_8202721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202721).length < 2 ^ (prefixWord ++ tailWord_8202721).sum := by decide
  have hdescent : baseEnd_8202721 < baseStart_8202721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202744 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 1, 1, 4]
def baseStart_8202744 : Nat := 118140960795 + 8202744 * 2 ^ 59
def prefixEnd_8202744 : Nat := 4983230072969 + 3 ^ 40 * 8202744 * 2
def baseEnd_8202744 : Nat := 4211950357783959960076273

theorem tailTrace_8202744 : CollatzResearch.WordTrace tailWord_8202744 prefixEnd_8202744 4211950357783959960076273 := by
  unfold tailWord_8202744
  simp only [CollatzResearch.WordTrace]
  refine ⟨149589326097433439993799643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199452434796577919991732857 149589326097433439993799643)
  ·
    refine ⟨224383989146150159990699465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149589326097433439993799643 224383989146150159990699465)
    ·
      refine ⟨168287991859612619993024599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224383989146150159990699465 168287991859612619993024599)
      ·
        refine ⟨252431987789418929989536899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168287991859612619993024599 252431987789418929989536899)
        ·
          refine ⟨378647981684128394984305349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252431987789418929989536899 378647981684128394984305349)
          ·
            refine ⟨70996496565774074059557253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 378647981684128394984305349 70996496565774074059557253)
            ·
              refine ⟨13311843106082638886166985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70996496565774074059557253 13311843106082638886166985)
              ·
                refine ⟨9983882329561979164625239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13311843106082638886166985 9983882329561979164625239)
                ·
                  refine ⟨14975823494342968746937859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9983882329561979164625239 14975823494342968746937859)
                  ·
                    refine ⟨22463735241514453120406789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14975823494342968746937859 22463735241514453120406789)
                    ·
                      refine ⟨4211950357783959960076273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22463735241514453120406789 4211950357783959960076273)
                      ·
                        rfl

theorem cell23_8202744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_8202744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202744 prefixEnd_8202744 := by exact prefixLift 8202744
  have htrace : WordTrace (prefixWord ++ tailWord_8202744) baseStart_8202744 baseEnd_8202744 := by
    simpa [prefixWord, tailWord_8202744, baseEnd_8202744] using wordTrace_append hprefix tailTrace_8202744
  have hstable : (prefixWord ++ tailWord_8202744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202744).length < 2 ^ (prefixWord ++ tailWord_8202744).sum := by decide
  have hdescent : baseEnd_8202744 < baseStart_8202744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202757 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_8202757 : Nat := 118140960795 + 8202757 * 2 ^ 59
def prefixEnd_8202757 : Nat := 4983230072969 + 3 ^ 40 * 8202757 * 2
def baseEnd_8202757 : Nat := 4211957033032468409213713

theorem tailTrace_8202757 : CollatzResearch.WordTrace tailWord_8202757 prefixEnd_8202757 4211957033032468409213713 := by
  unfold tailWord_8202757
  simp only [CollatzResearch.WordTrace]
  refine ⟨299179126343819783207822525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199452750895879855471881683 299179126343819783207822525)
  ·
    refine ⟨112192172378932418702933447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299179126343819783207822525 112192172378932418702933447)
    ·
      refine ⟨168288258568398628054400171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112192172378932418702933447 168288258568398628054400171)
      ·
        refine ⟨252432387852597942081600257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168288258568398628054400171 252432387852597942081600257)
        ·
          refine ⟨189324290889448456561200193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252432387852597942081600257 189324290889448456561200193)
          ·
            refine ⟨141993218167086342420900145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189324290889448456561200193 141993218167086342420900145)
            ·
              refine ⟨106494913625314756815675109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141993218167086342420900145 106494913625314756815675109)
              ·
                refine ⟨19967796304746516902939083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106494913625314756815675109 19967796304746516902939083)
                ·
                  refine ⟨29951694457119775354408625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19967796304746516902939083 29951694457119775354408625)
                  ·
                    refine ⟨22463770842839831515806469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29951694457119775354408625 22463770842839831515806469)
                    ·
                      refine ⟨4211957033032468409213713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22463770842839831515806469 4211957033032468409213713)
                      ·
                        rfl

theorem cell23_8202757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_8202757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202757 prefixEnd_8202757 := by exact prefixLift 8202757
  have htrace : WordTrace (prefixWord ++ tailWord_8202757) baseStart_8202757 baseEnd_8202757 := by
    simpa [prefixWord, tailWord_8202757, baseEnd_8202757] using wordTrace_append hprefix tailTrace_8202757
  have hstable : (prefixWord ++ tailWord_8202757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202757).length < 2 ^ (prefixWord ++ tailWord_8202757).sum := by decide
  have hdescent : baseEnd_8202757 < baseStart_8202757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202764 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 1, 1, 5]
def baseStart_8202764 : Nat := 118140960795 + 8202764 * 2 ^ 59
def prefixEnd_8202764 : Nat := 4983230072969 + 3 ^ 40 * 8202764 * 2
def baseEnd_8202764 : Nat := 4211960627397049881826181

theorem tailTrace_8202764 : CollatzResearch.WordTrace tailWord_8202764 prefixEnd_8202764 4211960627397049881826181 := by
  unfold tailWord_8202764
  simp only [CollatzResearch.WordTrace]
  refine ⟨149589690827397211701663673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199452921103196282268884897 149589690827397211701663673)
  ·
    refine ⟨112192268120547908776247755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149589690827397211701663673 112192268120547908776247755)
    ·
      refine ⟨168288402180821863164371633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112192268120547908776247755 168288402180821863164371633)
      ·
        refine ⟨126216301635616397373278725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168288402180821863164371633 126216301635616397373278725)
        ·
          refine ⟨23665556556678074507489761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126216301635616397373278725 23665556556678074507489761)
          ·
            refine ⟨17749167417508555880617321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23665556556678074507489761 17749167417508555880617321)
            ·
              refine ⟨13311875563131416910462991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17749167417508555880617321 13311875563131416910462991)
              ·
                refine ⟨19967813344697125365694487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13311875563131416910462991 19967813344697125365694487)
                ·
                  refine ⟨29951720017045688048541731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19967813344697125365694487 29951720017045688048541731)
                  ·
                    refine ⟨44927580025568532072812597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29951720017045688048541731 44927580025568532072812597)
                    ·
                      refine ⟨4211960627397049881826181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44927580025568532072812597 4211960627397049881826181)
                      ·
                        rfl

theorem cell23_8202764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_8202764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202764 prefixEnd_8202764 := by exact prefixLift 8202764
  have htrace : WordTrace (prefixWord ++ tailWord_8202764) baseStart_8202764 baseEnd_8202764 := by
    simpa [prefixWord, tailWord_8202764, baseEnd_8202764] using wordTrace_append hprefix tailTrace_8202764
  have hstable : (prefixWord ++ tailWord_8202764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202764).length < 2 ^ (prefixWord ++ tailWord_8202764).sum := by decide
  have hdescent : baseEnd_8202764 < baseStart_8202764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202765 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_8202765 : Nat := 118140960795 + 8202765 * 2 ^ 59
def prefixEnd_8202765 : Nat := 4983230072969 + 3 ^ 40 * 8202765 * 2
def baseEnd_8202765 : Nat := 4211961140877704377913677

theorem tailTrace_8202765 : CollatzResearch.WordTrace tailWord_8202765 prefixEnd_8202765 4211961140877704377913677 := by
  unfold tailWord_8202765
  simp only [CollatzResearch.WordTrace]
  refine ⟨299179418127790800574113749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199452945418527200382742499 299179418127790800574113749)
  ·
    refine ⟨7012017612370096888455791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 299179418127790800574113749 7012017612370096888455791)
    ·
      refine ⟨10518026418555145332683687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7012017612370096888455791 10518026418555145332683687)
      ·
        refine ⟨15777039627832717999025531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10518026418555145332683687 15777039627832717999025531)
        ·
          refine ⟨23665559441749076998538297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15777039627832717999025531 23665559441749076998538297)
          ·
            refine ⟨17749169581311807748903723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23665559441749076998538297 17749169581311807748903723)
            ·
              refine ⟨26623754371967711623355585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17749169581311807748903723 26623754371967711623355585)
              ·
                refine ⟨19967815778975783717516689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26623754371967711623355585 19967815778975783717516689)
                ·
                  refine ⟨14975861834231837788137517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19967815778975783717516689 14975861834231837788137517)
                  ·
                    refine ⟨5615948187836939170551569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14975861834231837788137517 5615948187836939170551569)
                    ·
                      refine ⟨4211961140877704377913677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615948187836939170551569 4211961140877704377913677)
                      ·
                        rfl

theorem cell23_8202765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_8202765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202765 prefixEnd_8202765 := by exact prefixLift 8202765
  have htrace : WordTrace (prefixWord ++ tailWord_8202765) baseStart_8202765 baseEnd_8202765 := by
    simpa [prefixWord, tailWord_8202765, baseEnd_8202765] using wordTrace_append hprefix tailTrace_8202765
  have hstable : (prefixWord ++ tailWord_8202765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202765).length < 2 ^ (prefixWord ++ tailWord_8202765).sum := by decide
  have hdescent : baseEnd_8202765 < baseStart_8202765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202772 : List Nat := [2, 4, 3, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_8202772 : Nat := 118140960795 + 8202772 * 2 ^ 59
def prefixEnd_8202772 : Nat := 4983230072969 + 3 ^ 40 * 8202772 * 2
def baseEnd_8202772 : Nat := 4211964735242285850526145

theorem tailTrace_8202772 : CollatzResearch.WordTrace tailWord_8202772 prefixEnd_8202772 4211964735242285850526145 := by
  unfold tailWord_8202772
  simp only [CollatzResearch.WordTrace]
  refine ⟨149589836719382720384809285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199453115625843627179745713 149589836719382720384809285)
  ·
    refine ⟨28048094384884260072151741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149589836719382720384809285 28048094384884260072151741)
    ·
      refine ⟨10518035394331597527056903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28048094384884260072151741 10518035394331597527056903)
      ·
        refine ⟨15777053091497396290585355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10518035394331597527056903 15777053091497396290585355)
        ·
          refine ⟨23665579637246094435878033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15777053091497396290585355 23665579637246094435878033)
          ·
            refine ⟨17749184727934570826908525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23665579637246094435878033 17749184727934570826908525)
            ·
              refine ⟨6655944272975464060090697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17749184727934570826908525 6655944272975464060090697)
              ·
                refine ⟨4991958204731598045068023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6655944272975464060090697 4991958204731598045068023)
                ·
                  refine ⟨7487937307097397067602035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991958204731598045068023 7487937307097397067602035)
                  ·
                    refine ⟨11231905960646095601403053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7487937307097397067602035 11231905960646095601403053)
                    ·
                      refine ⟨4211964735242285850526145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11231905960646095601403053 4211964735242285850526145)
                      ·
                        rfl

theorem cell23_8202772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_8202772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202772 prefixEnd_8202772 := by exact prefixLift 8202772
  have htrace : WordTrace (prefixWord ++ tailWord_8202772) baseStart_8202772 baseEnd_8202772 := by
    simpa [prefixWord, tailWord_8202772, baseEnd_8202772] using wordTrace_append hprefix tailTrace_8202772
  have hstable : (prefixWord ++ tailWord_8202772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202772).length < 2 ^ (prefixWord ++ tailWord_8202772).sum := by decide
  have hdescent : baseEnd_8202772 < baseStart_8202772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202777 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 3, 3, 3]
def baseStart_8202777 : Nat := 118140960795 + 8202777 * 2 ^ 59
def prefixEnd_8202777 : Nat := 4983230072969 + 3 ^ 40 * 8202777 * 2
def baseEnd_8202777 : Nat := 4211967302645558330963621

theorem tailTrace_8202777 : CollatzResearch.WordTrace tailWord_8202777 prefixEnd_8202777 4211967302645558330963621 := by
  unfold tailWord_8202777
  simp only [CollatzResearch.WordTrace]
  refine ⟨299179855803747326623550585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199453237202498217749033723 299179855803747326623550585)
  ·
    refine ⟨224384891852810494967662939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299179855803747326623550585 224384891852810494967662939)
    ·
      refine ⟨336577337779215742451494409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224384891852810494967662939 336577337779215742451494409)
      ·
        refine ⟨252433003334411806838620807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336577337779215742451494409 252433003334411806838620807)
        ·
          refine ⟨378649505001617710257931211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252433003334411806838620807 378649505001617710257931211)
          ·
            refine ⟨567974257502426565386896817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378649505001617710257931211 567974257502426565386896817)
            ·
              refine ⟨425980693126819924040172613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 567974257502426565386896817 425980693126819924040172613)
              ·
                refine ⟨79871379961278735757532365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 425980693126819924040172613 79871379961278735757532365)
                ·
                  refine ⟨29951767485479525909074637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79871379961278735757532365 29951767485479525909074637)
                  ·
                    refine ⟨11231912807054822215902989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29951767485479525909074637 11231912807054822215902989)
                    ·
                      refine ⟨4211967302645558330963621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11231912807054822215902989 4211967302645558330963621)
                      ·
                        rfl

theorem cell23_8202777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_8202777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202777 prefixEnd_8202777 := by exact prefixLift 8202777
  have htrace : WordTrace (prefixWord ++ tailWord_8202777) baseStart_8202777 baseEnd_8202777 := by
    simpa [prefixWord, tailWord_8202777, baseEnd_8202777] using wordTrace_append hprefix tailTrace_8202777
  have hstable : (prefixWord ++ tailWord_8202777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202777).length < 2 ^ (prefixWord ++ tailWord_8202777).sum := by decide
  have hdescent : baseEnd_8202777 < baseStart_8202777 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202778 : List Nat := [3, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2]
def baseStart_8202778 : Nat := 118140960795 + 8202778 * 2 ^ 59
def prefixEnd_8202778 : Nat := 4983230072969 + 3 ^ 40 * 8202778 * 2
def baseEnd_8202778 : Nat := 4211967816126212827051117

theorem tailTrace_8202778 : CollatzResearch.WordTrace tailWord_8202778 prefixEnd_8202778 4211967816126212827051117 := by
  unfold tailWord_8202778
  simp only [CollatzResearch.WordTrace]
  refine ⟨74794973069185925948584247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199453261517829135862891325 74794973069185925948584247)
  ·
    refine ⟨112192459603778888922876371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74794973069185925948584247 112192459603778888922876371)
    ·
      refine ⟨168288689405668333384314557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112192459603778888922876371 168288689405668333384314557)
      ·
        refine ⟨63108258527125625019117959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168288689405668333384314557 63108258527125625019117959)
        ·
          refine ⟨94662387790688437528676939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63108258527125625019117959 94662387790688437528676939)
          ·
            refine ⟨141993581686032656293015409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94662387790688437528676939 141993581686032656293015409)
            ·
              refine ⟨106495186264524492219761557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141993581686032656293015409 106495186264524492219761557)
              ·
                refine ⟨4991961856149585572801323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106495186264524492219761557 4991961856149585572801323)
                ·
                  refine ⟨7487942784224378359201985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991961856149585572801323 7487942784224378359201985)
                  ·
                    refine ⟨5615957088168283769401489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7487942784224378359201985 5615957088168283769401489)
                    ·
                      refine ⟨4211967816126212827051117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615957088168283769401489 4211967816126212827051117)
                      ·
                        rfl

theorem cell23_8202778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2].length) (baseStart_8202778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202778 prefixEnd_8202778 := by exact prefixLift 8202778
  have htrace : WordTrace (prefixWord ++ tailWord_8202778) baseStart_8202778 baseEnd_8202778 := by
    simpa [prefixWord, tailWord_8202778, baseEnd_8202778] using wordTrace_append hprefix tailTrace_8202778
  have hstable : (prefixWord ++ tailWord_8202778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202778).length < 2 ^ (prefixWord ++ tailWord_8202778).sum := by decide
  have hdescent : baseEnd_8202778 < baseStart_8202778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202784 : List Nat := [2, 1, 1, 6, 2, 1, 2, 8]
def baseStart_8202784 : Nat := 118140960795 + 8202784 * 2 ^ 59
def prefixEnd_8202784 : Nat := 4983230072969 + 3 ^ 40 * 8202784 * 2
def baseEnd_8202784 : Nat := 155998922111486659391707

theorem tailTrace_8202784 : CollatzResearch.WordTrace tailWord_8202784 prefixEnd_8202784 155998922111486659391707 := by
  unfold tailWord_8202784
  simp only [CollatzResearch.WordTrace]
  refine ⟨149590055557360983409527703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199453407409814644546036937 149590055557360983409527703)
  ·
    refine ⟨224385083336041475114291555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149590055557360983409527703 224385083336041475114291555)
    ·
      refine ⟨336577625004062212671437333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224385083336041475114291555 336577625004062212671437333)
      ·
        refine ⟨15777076172065416218973625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 336577625004062212671437333 15777076172065416218973625)
        ·
          refine ⟨11832807129049062164230219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15777076172065416218973625 11832807129049062164230219)
          ·
            refine ⟨17749210693573593246345329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11832807129049062164230219 17749210693573593246345329)
            ·
              refine ⟨13311908020180194934758997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17749210693573593246345329 13311908020180194934758997)
              ·
                refine ⟨155998922111486659391707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13311908020180194934758997 155998922111486659391707)
                ·
                  rfl

theorem cell23_8202784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 8].length) (baseStart_8202784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202784 prefixEnd_8202784 := by exact prefixLift 8202784
  have htrace : WordTrace (prefixWord ++ tailWord_8202784) baseStart_8202784 baseEnd_8202784 := by
    simpa [prefixWord, tailWord_8202784, baseEnd_8202784] using wordTrace_append hprefix tailTrace_8202784
  have hstable : (prefixWord ++ tailWord_8202784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202784).length < 2 ^ (prefixWord ++ tailWord_8202784).sum := by decide
  have hdescent : baseEnd_8202784 < baseStart_8202784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202788 : List Nat := [2, 3, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_8202788 : Nat := 118140960795 + 8202788 * 2 ^ 59
def prefixEnd_8202788 : Nat := 4983230072969 + 3 ^ 40 * 8202788 * 2
def baseEnd_8202788 : Nat := 1403990983644252595975357

theorem tailTrace_8202788 : CollatzResearch.WordTrace tailWord_8202788 prefixEnd_8202788 1403990983644252595975357 := by
  unfold tailWord_8202788
  simp only [CollatzResearch.WordTrace]
  refine ⟨149590128503353737751100509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199453504671138317001467345 149590128503353737751100509)
  ·
    refine ⟨56096298188757651656662691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149590128503353737751100509 56096298188757651656662691)
    ·
      refine ⟨84144447283136477484994037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56096298188757651656662691 84144447283136477484994037)
      ·
        refine ⟨7888541932794044764218191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84144447283136477484994037 7888541932794044764218191)
        ·
          refine ⟨11832812899191067146327287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7888541932794044764218191 11832812899191067146327287)
          ·
            refine ⟨17749219348786600719490931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11832812899191067146327287 17749219348786600719490931)
            ·
              refine ⟨26623829023179901079236397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17749219348786600719490931 26623829023179901079236397)
              ·
                refine ⟨9983935883692462904713649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26623829023179901079236397 9983935883692462904713649)
                ·
                  refine ⟨7487951912769347178535237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9983935883692462904713649 7487951912769347178535237)
                  ·
                    refine ⟨1403990983644252595975357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7487951912769347178535237 1403990983644252595975357)
                    ·
                      rfl

theorem cell23_8202788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_8202788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202788 prefixEnd_8202788 := by exact prefixLift 8202788
  have htrace : WordTrace (prefixWord ++ tailWord_8202788) baseStart_8202788 baseEnd_8202788 := by
    simpa [prefixWord, tailWord_8202788, baseEnd_8202788] using wordTrace_append hprefix tailTrace_8202788
  have hstable : (prefixWord ++ tailWord_8202788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202788).length < 2 ^ (prefixWord ++ tailWord_8202788).sum := by decide
  have hdescent : baseEnd_8202788 < baseStart_8202788 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202829 : List Nat := [1, 6, 1, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_8202829 : Nat := 118140960795 + 8202829 * 2 ^ 59
def prefixEnd_8202829 : Nat := 4983230072969 + 3 ^ 40 * 8202829 * 2
def baseEnd_8202829 : Nat := 4211994003639592127513383

theorem tailTrace_8202829 : CollatzResearch.WordTrace tailWord_8202829 prefixEnd_8202829 4211994003639592127513383 := by
  unfold tailWord_8202829
  simp only [CollatzResearch.WordTrace]
  refine ⟨299181752399558939504443541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199454501599705959669629027 299181752399558939504443541)
  ·
    refine ⟨14024144643729325289270791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 299181752399558939504443541 14024144643729325289270791)
    ·
      refine ⟨21036216965593987933906187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14024144643729325289270791 21036216965593987933906187)
      ·
        refine ⟨31554325448390981900859281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21036216965593987933906187 31554325448390981900859281)
        ·
          refine ⟨23665744086293236425644461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31554325448390981900859281 23665744086293236425644461)
          ·
            refine ⟨8874654032359963659616673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23665744086293236425644461 8874654032359963659616673)
            ·
              refine ⟨6655990524269972744712505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8874654032359963659616673 6655990524269972744712505)
              ·
                refine ⟨4991992893202479558534379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6655990524269972744712505 4991992893202479558534379)
                ·
                  refine ⟨7487989339803719337801569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991992893202479558534379 7487989339803719337801569)
                  ·
                    refine ⟨5615992004852789503351177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7487989339803719337801569 5615992004852789503351177)
                    ·
                      refine ⟨4211994003639592127513383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5615992004852789503351177 4211994003639592127513383)
                      ·
                        rfl

theorem cell23_8202829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_8202829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202829 prefixEnd_8202829 := by exact prefixLift 8202829
  have htrace : WordTrace (prefixWord ++ tailWord_8202829) baseStart_8202829 baseEnd_8202829 := by
    simpa [prefixWord, tailWord_8202829, baseEnd_8202829] using wordTrace_append hprefix tailTrace_8202829
  have hstable : (prefixWord ++ tailWord_8202829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202829).length < 2 ^ (prefixWord ++ tailWord_8202829).sum := by decide
  have hdescent : baseEnd_8202829 < baseStart_8202829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202837 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_8202837 : Nat := 118140960795 + 8202837 * 2 ^ 59
def prefixEnd_8202837 : Nat := 4983230072969 + 3 ^ 40 * 8202837 * 2
def baseEnd_8202837 : Nat := 4211998111484828096213345

theorem tailTrace_8202837 : CollatzResearch.WordTrace tailWord_8202837 prefixEnd_8202837 4211998111484828096213345 := by
  unfold tailWord_8202837
  simp only [CollatzResearch.WordTrace]
  refine ⟨299182044183529956870734765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199454696122353304580489843 299182044183529956870734765)
  ·
    refine ⟨112193266568823733826525537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299182044183529956870734765 112193266568823733826525537)
    ·
      refine ⟨84144949926617800369894153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112193266568823733826525537 84144949926617800369894153)
      ·
        refine ⟨63108712444963350277420615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84144949926617800369894153 63108712444963350277420615)
        ·
          refine ⟨94663068667445025416130923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63108712444963350277420615 94663068667445025416130923)
          ·
            refine ⟨141994603001167538124196385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94663068667445025416130923 141994603001167538124196385)
            ·
              refine ⟨106495952250875653593147289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141994603001167538124196385 106495952250875653593147289)
              ·
                refine ⟨79871964188156740194860467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106495952250875653593147289 79871964188156740194860467)
                ·
                  refine ⟨119807946282235110292290701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79871964188156740194860467 119807946282235110292290701)
                  ·
                    refine ⟨44927979855838166359609013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119807946282235110292290701 44927979855838166359609013)
                    ·
                      refine ⟨4211998111484828096213345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44927979855838166359609013 4211998111484828096213345)
                      ·
                        rfl

theorem cell23_8202837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_8202837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202837 prefixEnd_8202837 := by exact prefixLift 8202837
  have htrace : WordTrace (prefixWord ++ tailWord_8202837) baseStart_8202837 baseEnd_8202837 := by
    simpa [prefixWord, tailWord_8202837, baseEnd_8202837] using wordTrace_append hprefix tailTrace_8202837
  have hstable : (prefixWord ++ tailWord_8202837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202837).length < 2 ^ (prefixWord ++ tailWord_8202837).sum := by decide
  have hdescent : baseEnd_8202837 < baseStart_8202837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202851 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 1, 4, 2]
def baseStart_8202851 : Nat := 118140960795 + 8202851 * 2 ^ 59
def prefixEnd_8202851 : Nat := 4983230072969 + 3 ^ 40 * 8202851 * 2
def baseEnd_8202851 : Nat := 4212005300213991041438281

theorem tailTrace_8202851 : CollatzResearch.WordTrace tailWord_8202851 prefixEnd_8202851 4212005300213991041438281 := by
  unfold tailWord_8202851
  simp only [CollatzResearch.WordTrace]
  refine ⟨299182554805479237261744407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199455036536986158174496271 299182554805479237261744407)
  ·
    refine ⟨448773832208218855892616611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299182554805479237261744407 448773832208218855892616611)
    ·
      refine ⟨673160748312328283838924917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448773832208218855892616611 673160748312328283838924917)
      ·
        refine ⟨63108820154280776609899211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 673160748312328283838924917 63108820154280776609899211)
        ·
          refine ⟨94663230231421164914848817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63108820154280776609899211 94663230231421164914848817)
          ·
            refine ⟨70997422673565873686136613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94663230231421164914848817 70997422673565873686136613)
            ·
              refine ⟨13312016751293601316150615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70997422673565873686136613 13312016751293601316150615)
              ·
                refine ⟨19968025126940401974225923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13312016751293601316150615 19968025126940401974225923)
                ·
                  refine ⟨29952037690410602961338885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19968025126940401974225923 29952037690410602961338885)
                  ·
                    refine ⟨5616007066951988055251041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29952037690410602961338885 5616007066951988055251041)
                    ·
                      refine ⟨4212005300213991041438281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5616007066951988055251041 4212005300213991041438281)
                      ·
                        rfl

theorem cell23_8202851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_8202851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202851 prefixEnd_8202851 := by exact prefixLift 8202851
  have htrace : WordTrace (prefixWord ++ tailWord_8202851) baseStart_8202851 baseEnd_8202851 := by
    simpa [prefixWord, tailWord_8202851, baseEnd_8202851] using wordTrace_append hprefix tailTrace_8202851
  have hstable : (prefixWord ++ tailWord_8202851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202851).length < 2 ^ (prefixWord ++ tailWord_8202851).sum := by decide
  have hdescent : baseEnd_8202851 < baseStart_8202851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202885 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 2, 2, 2]
def baseStart_8202885 : Nat := 118140960795 + 8202885 * 2 ^ 59
def prefixEnd_8202885 : Nat := 4983230072969 + 3 ^ 40 * 8202885 * 2
def baseEnd_8202885 : Nat := 4212022758556243908413125

theorem tailTrace_8202885 : CollatzResearch.WordTrace tailWord_8202885 prefixEnd_8202885 4212022758556243908413125 := by
  unfold tailWord_8202885
  simp only [CollatzResearch.WordTrace]
  refine ⟨299183794887356061068482109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199455863258237374045654739 299183794887356061068482109)
  ·
    refine ⟨112193923082758522900680791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299183794887356061068482109 112193923082758522900680791)
    ·
      refine ⟨168290884624137784351021187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112193923082758522900680791 168290884624137784351021187)
      ·
        refine ⟨252436326936206676526531781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168290884624137784351021187 252436326936206676526531781)
        ·
          refine ⟨47331811300538751848724709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252436326936206676526531781 47331811300538751848724709)
          ·
            refine ⟨8874714618851015971635883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47331811300538751848724709 8874714618851015971635883)
            ·
              refine ⟨13312071928276523957453825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8874714618851015971635883 13312071928276523957453825)
              ·
                refine ⟨9984053946207392968090369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13312071928276523957453825 9984053946207392968090369)
                ·
                  refine ⟨7488040459655544726067777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9984053946207392968090369 7488040459655544726067777)
                  ·
                    refine ⟨5616030344741658544550833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7488040459655544726067777 5616030344741658544550833)
                    ·
                      refine ⟨4212022758556243908413125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5616030344741658544550833 4212022758556243908413125)
                      ·
                        rfl

theorem cell23_8202885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 2, 2].length) (baseStart_8202885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202885 prefixEnd_8202885 := by exact prefixLift 8202885
  have htrace : WordTrace (prefixWord ++ tailWord_8202885) baseStart_8202885 baseEnd_8202885 := by
    simpa [prefixWord, tailWord_8202885, baseEnd_8202885] using wordTrace_append hprefix tailTrace_8202885
  have hstable : (prefixWord ++ tailWord_8202885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202885).length < 2 ^ (prefixWord ++ tailWord_8202885).sum := by decide
  have hdescent : baseEnd_8202885 < baseStart_8202885 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202897 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_8202897 : Nat := 118140960795 + 8202897 * 2 ^ 59
def prefixEnd_8202897 : Nat := 4983230072969 + 3 ^ 40 * 8202897 * 2
def baseEnd_8202897 : Nat := 4212028920324097861463069

theorem tailTrace_8202897 : CollatzResearch.WordTrace tailWord_8202897 prefixEnd_8202897 4212028920324097861463069 := by
  unfold tailWord_8202897
  simp only [CollatzResearch.WordTrace]
  refine ⟨299184232563312587117918945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199456155042208391411945963 299184232563312587117918945)
  ·
    refine ⟨224388174422484440338439209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299184232563312587117918945 224388174422484440338439209)
    ·
      refine ⟨168291130816863330253829407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224388174422484440338439209 168291130816863330253829407)
      ·
        refine ⟨252436696225294995380744111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168291130816863330253829407 252436696225294995380744111)
        ·
          refine ⟨378655044337942493071116167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252436696225294995380744111 378655044337942493071116167)
          ·
            refine ⟨567982566506913739606674251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378655044337942493071116167 567982566506913739606674251)
            ·
              refine ⟨851973849760370609410011377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567982566506913739606674251 851973849760370609410011377)
              ·
                refine ⟨638980387320277957057508533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851973849760370609410011377 638980387320277957057508533)
                ·
                  refine ⟨59904411311276058474141425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 638980387320277957057508533 59904411311276058474141425)
                  ·
                    refine ⟨44928308483457043855606069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59904411311276058474141425 44928308483457043855606069)
                    ·
                      refine ⟨4212028920324097861463069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44928308483457043855606069 4212028920324097861463069)
                      ·
                        rfl

theorem cell23_8202897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_8202897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202897 prefixEnd_8202897 := by exact prefixLift 8202897
  have htrace : WordTrace (prefixWord ++ tailWord_8202897) baseStart_8202897 baseEnd_8202897 := by
    simpa [prefixWord, tailWord_8202897, baseEnd_8202897] using wordTrace_append hprefix tailTrace_8202897
  have hstable : (prefixWord ++ tailWord_8202897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202897).length < 2 ^ (prefixWord ++ tailWord_8202897).sum := by decide
  have hdescent : baseEnd_8202897 < baseStart_8202897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202907 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 4]
def baseStart_8202907 : Nat := 118140960795 + 8202907 * 2 ^ 59
def prefixEnd_8202907 : Nat := 4983230072969 + 3 ^ 40 * 8202907 * 2
def baseEnd_8202907 : Nat := 4212034055130642822338023

theorem tailTrace_8202907 : CollatzResearch.WordTrace tailWord_8202907 prefixEnd_8202907 4212034055130642822338023 := by
  unfold tailWord_8202907
  simp only [CollatzResearch.WordTrace]
  refine ⟨299184597293276358825782975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199456398195517572550521983 299184597293276358825782975)
  ·
    refine ⟨448776895939914538238674463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299184597293276358825782975 448776895939914538238674463)
    ·
      refine ⟨673165343909871807358011695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448776895939914538238674463 673165343909871807358011695)
      ·
        refine ⟨1009748015864807711037017543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673165343909871807358011695 1009748015864807711037017543)
        ·
          refine ⟨1514622023797211566555526315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1009748015864807711037017543 1514622023797211566555526315)
          ·
            refine ⟨2271933035695817349833289473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514622023797211566555526315 2271933035695817349833289473)
            ·
              refine ⟨1703949776771863012374967105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2271933035695817349833289473 1703949776771863012374967105)
              ·
                refine ⟨1277962332578897259281225329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1703949776771863012374967105 1277962332578897259281225329)
                ·
                  refine ⟨958471749434172944460918997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1277962332578897259281225329 958471749434172944460918997)
                  ·
                    refine ⟨22464181627363428385802789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 958471749434172944460918997 22464181627363428385802789)
                    ·
                      refine ⟨4212034055130642822338023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22464181627363428385802789 4212034055130642822338023)
                      ·
                        rfl

theorem cell23_8202907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 4].length) (baseStart_8202907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202907 prefixEnd_8202907 := by exact prefixLift 8202907
  have htrace : WordTrace (prefixWord ++ tailWord_8202907) baseStart_8202907 baseEnd_8202907 := by
    simpa [prefixWord, tailWord_8202907, baseEnd_8202907] using wordTrace_append hprefix tailTrace_8202907
  have hstable : (prefixWord ++ tailWord_8202907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202907).length < 2 ^ (prefixWord ++ tailWord_8202907).sum := by decide
  have hdescent : baseEnd_8202907 < baseStart_8202907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202917 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_8202917 : Nat := 118140960795 + 8202917 * 2 ^ 59
def prefixEnd_8202917 : Nat := 4983230072969 + 3 ^ 40 * 8202917 * 2
def baseEnd_8202917 : Nat := 1404013063312395927737659

theorem tailTrace_8202917 : CollatzResearch.WordTrace tailWord_8202917 prefixEnd_8202917 1404013063312395927737659 := by
  unfold tailWord_8202917
  simp only [CollatzResearch.WordTrace]
  refine ⟨299184962023240130533647005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199456641348826753689098003 299184962023240130533647005)
  ·
    refine ⟨112194360758715048950117627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299184962023240130533647005 112194360758715048950117627)
    ·
      refine ⟨168291541138072573425176441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112194360758715048950117627 168291541138072573425176441)
      ·
        refine ⟨126218655853554430068882331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168291541138072573425176441 126218655853554430068882331)
        ·
          refine ⟨189327983780331645103323497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126218655853554430068882331 189327983780331645103323497)
          ·
            refine ⟨141995987835248733827492623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189327983780331645103323497 141995987835248733827492623)
            ·
              refine ⟨212993981752873100741238935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141995987835248733827492623 212993981752873100741238935)
              ·
                refine ⟨319490972629309651111858403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212993981752873100741238935 319490972629309651111858403)
                ·
                  refine ⟨479236458943964476667787605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 319490972629309651111858403 479236458943964476667787605)
                  ·
                    refine ⟨1404013063312395927737659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 479236458943964476667787605 1404013063312395927737659)
                    ·
                      rfl

theorem cell23_8202917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_8202917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202917 prefixEnd_8202917 := by exact prefixLift 8202917
  have htrace : WordTrace (prefixWord ++ tailWord_8202917) baseStart_8202917 baseEnd_8202917 := by
    simpa [prefixWord, tailWord_8202917, baseEnd_8202917] using wordTrace_append hprefix tailTrace_8202917
  have hstable : (prefixWord ++ tailWord_8202917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202917).length < 2 ^ (prefixWord ++ tailWord_8202917).sum := by decide
  have hdescent : baseEnd_8202917 < baseStart_8202917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8202941 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_8202941 : Nat := 118140960795 + 8202941 * 2 ^ 59
def prefixEnd_8202941 : Nat := 4983230072969 + 3 ^ 40 * 8202941 * 2
def baseEnd_8202941 : Nat := 4212051513472895689312867

theorem tailTrace_8202941 : CollatzResearch.WordTrace tailWord_8202941 prefixEnd_8202941 4212051513472895689312867 := by
  unfold tailWord_8202941
  simp only [CollatzResearch.WordTrace]
  refine ⟨299185837375153182632520677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199457224916768788421680451 299185837375153182632520677)
  ·
    refine ⟨56097344507841221743597627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 299185837375153182632520677 56097344507841221743597627)
    ·
      refine ⟨84146016761761832615396441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56097344507841221743597627 84146016761761832615396441)
      ·
        refine ⟨63109512571321374461547331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84146016761761832615396441 63109512571321374461547331)
        ·
          refine ⟨94664268856982061692320997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63109512571321374461547331 94664268856982061692320997)
          ·
            refine ⟨17749550410684136567310187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94664268856982061692320997 17749550410684136567310187)
            ·
              refine ⟨26624325616026204850965281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17749550410684136567310187 26624325616026204850965281)
              ·
                refine ⟨19968244212019653638223961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26624325616026204850965281 19968244212019653638223961)
                ·
                  refine ⟨14976183159014740228667971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19968244212019653638223961 14976183159014740228667971)
                  ·
                    refine ⟨22464274738522110343001957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14976183159014740228667971 22464274738522110343001957)
                    ·
                      refine ⟨4212051513472895689312867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22464274738522110343001957 4212051513472895689312867)
                      ·
                        rfl

theorem cell23_8202941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_8202941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8202941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8202941 prefixEnd_8202941 := by exact prefixLift 8202941
  have htrace : WordTrace (prefixWord ++ tailWord_8202941) baseStart_8202941 baseEnd_8202941 := by
    simpa [prefixWord, tailWord_8202941, baseEnd_8202941] using wordTrace_append hprefix tailTrace_8202941
  have hstable : (prefixWord ++ tailWord_8202941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8202941).length < 2 ^ (prefixWord ++ tailWord_8202941).sum := by decide
  have hdescent : baseEnd_8202941 < baseStart_8202941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8202941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203041 : List Nat := [1, 2, 3, 2, 1, 2, 2, 2, 4, 4]
def baseStart_8203041 : Nat := 118140960795 + 8203041 * 2 ^ 59
def prefixEnd_8203041 : Nat := 4983230072969 + 3 ^ 40 * 8203041 * 2
def baseEnd_8203041 : Nat := 1404034287179448432687469

theorem tailTrace_8203041 : CollatzResearch.WordTrace tailWord_8203041 prefixEnd_8203041 1404034287179448432687469 := by
  unfold tailWord_8203041
  simp only [CollatzResearch.WordTrace]
  refine ⟨299189484674790899711160977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199459656449860599807440651 299189484674790899711160977)
  ·
    refine ⟨224392113506093174783370733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 299189484674790899711160977 224392113506093174783370733)
    ·
      refine ⟨84147042564784940543764025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224392113506093174783370733 84147042564784940543764025)
      ·
        refine ⟨63110281923588705407823019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84147042564784940543764025 63110281923588705407823019)
        ·
          refine ⟨94665422885383058111734529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63110281923588705407823019 94665422885383058111734529)
          ·
            refine ⟨70999067164037293583800897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94665422885383058111734529 70999067164037293583800897)
            ·
              refine ⟨53249300373027970187850673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70999067164037293583800897 53249300373027970187850673)
              ·
                refine ⟨39936975279770977640888005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53249300373027970187850673 39936975279770977640888005)
                ·
                  refine ⟨7488182864957058307666501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39936975279770977640888005 7488182864957058307666501)
                  ·
                    refine ⟨1404034287179448432687469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7488182864957058307666501 1404034287179448432687469)
                    ·
                      rfl

theorem cell23_8203041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_8203041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203041 prefixEnd_8203041 := by exact prefixLift 8203041
  have htrace : WordTrace (prefixWord ++ tailWord_8203041) baseStart_8203041 baseEnd_8203041 := by
    simpa [prefixWord, tailWord_8203041, baseEnd_8203041] using wordTrace_append hprefix tailTrace_8203041
  have hstable : (prefixWord ++ tailWord_8203041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203041).length < 2 ^ (prefixWord ++ tailWord_8203041).sum := by decide
  have hdescent : baseEnd_8203041 < baseStart_8203041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203042 : List Nat := [3, 3, 1, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_8203042 : Nat := 118140960795 + 8203042 * 2 ^ 59
def prefixEnd_8203042 : Nat := 4983230072969 + 3 ^ 40 * 8203042 * 2
def baseEnd_8203042 : Nat := 4212103375018999794149903

theorem tailTrace_8203042 : CollatzResearch.WordTrace tailWord_8203042 prefixEnd_8203042 4212103375018999794149903 := by
  unfold tailWord_8203042
  simp only [CollatzResearch.WordTrace]
  refine ⟨74797380286946819220486845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199459680765191517921298253 74797380286946819220486845)
  ·
    refine ⟨28049017607605057207682567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74797380286946819220486845 28049017607605057207682567)
    ·
      refine ⟨42073526411407585811523851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28049017607605057207682567 42073526411407585811523851)
      ·
        refine ⟨63110289617111378717285777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42073526411407585811523851 63110289617111378717285777)
        ·
          refine ⟨47332717212833534037964333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63110289617111378717285777 47332717212833534037964333)
          ·
            refine ⟨17749768954812575264236625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47332717212833534037964333 17749768954812575264236625)
            ·
              refine ⟨13312326716109431448177469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17749768954812575264236625 13312326716109431448177469)
              ·
                refine ⟨4992122518541036793066551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13312326716109431448177469 4992122518541036793066551)
                ·
                  refine ⟨7488183777811555189599827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992122518541036793066551 7488183777811555189599827)
                  ·
                    refine ⟨11232275666717332784399741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7488183777811555189599827 11232275666717332784399741)
                    ·
                      refine ⟨4212103375018999794149903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11232275666717332784399741 4212103375018999794149903)
                      ·
                        rfl

theorem cell23_8203042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_8203042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203042 prefixEnd_8203042 := by exact prefixLift 8203042
  have htrace : WordTrace (prefixWord ++ tailWord_8203042) baseStart_8203042 baseEnd_8203042 := by
    simpa [prefixWord, tailWord_8203042, baseEnd_8203042] using wordTrace_append hprefix tailTrace_8203042
  have hstable : (prefixWord ++ tailWord_8203042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203042).length < 2 ^ (prefixWord ++ tailWord_8203042).sum := by decide
  have hdescent : baseEnd_8203042 < baseStart_8203042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203048 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_8203048 : Nat := 118140960795 + 8203048 * 2 ^ 59
def prefixEnd_8203048 : Nat := 4983230072969 + 3 ^ 40 * 8203048 * 2
def baseEnd_8203048 : Nat := 4212106455902926770674875

theorem tailTrace_8203048 : CollatzResearch.WordTrace tailWord_8203048 prefixEnd_8203048 4212106455902926770674875 := by
  unfold tailWord_8203048
  simp only [CollatzResearch.WordTrace]
  refine ⟨149594869992882769953332899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199459826657177026604443865 149594869992882769953332899)
  ·
    refine ⟨224392304989324154929999349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149594869992882769953332899 224392304989324154929999349)
    ·
      refine ⟨21036778592749139524687439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224392304989324154929999349 21036778592749139524687439)
      ·
        refine ⟨31555167889123709287031159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21036778592749139524687439 31555167889123709287031159)
        ·
          refine ⟨47332751833685563930546739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31555167889123709287031159 47332751833685563930546739)
          ·
            refine ⟨70999127750528345895820109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47332751833685563930546739 70999127750528345895820109)
            ·
              refine ⟨26624672906448129710932541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70999127750528345895820109 26624672906448129710932541)
              ·
                refine ⟨9984252339918048641599703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26624672906448129710932541 9984252339918048641599703)
                ·
                  refine ⟨14976378509877072962399555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9984252339918048641599703 14976378509877072962399555)
                  ·
                    refine ⟨22464567764815609443599333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14976378509877072962399555 22464567764815609443599333)
                    ·
                      refine ⟨4212106455902926770674875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22464567764815609443599333 4212106455902926770674875)
                      ·
                        rfl

theorem cell23_8203048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_8203048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203048 prefixEnd_8203048 := by exact prefixLift 8203048
  have htrace : WordTrace (prefixWord ++ tailWord_8203048) baseStart_8203048 baseEnd_8203048 := by
    simpa [prefixWord, tailWord_8203048, baseEnd_8203048] using wordTrace_append hprefix tailTrace_8203048
  have hstable : (prefixWord ++ tailWord_8203048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203048).length < 2 ^ (prefixWord ++ tailWord_8203048).sum := by decide
  have hdescent : baseEnd_8203048 < baseStart_8203048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203091 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 2, 7, 2]
def baseStart_8203091 : Nat := 118140960795 + 8203091 * 2 ^ 59
def prefixEnd_8203091 : Nat := 4983230072969 + 3 ^ 40 * 8203091 * 2
def baseEnd_8203091 : Nat := 4212128535571070102437177

theorem tailTrace_8203091 : CollatzResearch.WordTrace tailWord_8203091 prefixEnd_8203091 4212128535571070102437177 := by
  unfold tailWord_8203091
  simp only [CollatzResearch.WordTrace]
  refine ⟨299191308324609758250481127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199460872216406505500320751 299191308324609758250481127)
  ·
    refine ⟨448786962486914637375721691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299191308324609758250481127 448786962486914637375721691)
    ·
      refine ⟨673180443730371956063582537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448786962486914637375721691 673180443730371956063582537)
      ·
        refine ⟨504885332797778967047686903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 673180443730371956063582537 504885332797778967047686903)
        ·
          refine ⟨757327999196668450571530355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504885332797778967047686903 757327999196668450571530355)
          ·
            refine ⟨1135991998795002675857295533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757327999196668450571530355 1135991998795002675857295533)
            ·
              refine ⟨425996999548126003446485825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1135991998795002675857295533 425996999548126003446485825)
              ·
                refine ⟨319497749661094502584864369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425996999548126003446485825 319497749661094502584864369)
                ·
                  refine ⟨239623312245820876938648277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 319497749661094502584864369 239623312245820876938648277)
                  ·
                    refine ⟨5616171380761426803249569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 239623312245820876938648277 5616171380761426803249569)
                    ·
                      refine ⟨4212128535571070102437177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5616171380761426803249569 4212128535571070102437177)
                      ·
                        rfl

theorem cell23_8203091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 7, 2].length) (baseStart_8203091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203091 prefixEnd_8203091 := by exact prefixLift 8203091
  have htrace : WordTrace (prefixWord ++ tailWord_8203091) baseStart_8203091 baseEnd_8203091 := by
    simpa [prefixWord, tailWord_8203091, baseEnd_8203091] using wordTrace_append hprefix tailTrace_8203091
  have hstable : (prefixWord ++ tailWord_8203091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203091).length < 2 ^ (prefixWord ++ tailWord_8203091).sum := by decide
  have hdescent : baseEnd_8203091 < baseStart_8203091 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203098 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3]
def baseStart_8203098 : Nat := 118140960795 + 8203098 * 2 ^ 59
def prefixEnd_8203098 : Nat := 4983230072969 + 3 ^ 40 * 8203098 * 2
def baseEnd_8203098 : Nat := 4212132129935651575049645

theorem tailTrace_8203098 : CollatzResearch.WordTrace tailWord_8203098 prefixEnd_8203098 4212132129935651575049645 := by
  unfold tailWord_8203098
  simp only [CollatzResearch.WordTrace]
  refine ⟨74797890908896099611496487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 199461042423722932297323965 74797890908896099611496487)
  ·
    refine ⟨112196836363344149417244731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74797890908896099611496487 112196836363344149417244731)
    ·
      refine ⟨168295254545016224125867097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112196836363344149417244731 168295254545016224125867097)
      ·
        refine ⟨126221440908762168094400323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168295254545016224125867097 126221440908762168094400323)
        ·
          refine ⟨189332161363143252141600485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126221440908762168094400323 189332161363143252141600485)
          ·
            refine ⟨35499780255589359776550091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189332161363143252141600485 35499780255589359776550091)
            ·
              refine ⟨53249670383384039664825137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35499780255589359776550091 53249670383384039664825137)
              ·
                refine ⟨39937252787538029748618853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53249670383384039664825137 39937252787538029748618853)
                ·
                  refine ⟨7488234897663380577866035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39937252787538029748618853 7488234897663380577866035)
                  ·
                    refine ⟨11232352346495070866799053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7488234897663380577866035 11232352346495070866799053)
                    ·
                      refine ⟨4212132129935651575049645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11232352346495070866799053 4212132129935651575049645)
                      ·
                        rfl

theorem cell23_8203098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3].length) (baseStart_8203098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203098 prefixEnd_8203098 := by exact prefixLift 8203098
  have htrace : WordTrace (prefixWord ++ tailWord_8203098) baseStart_8203098 baseEnd_8203098 := by
    simpa [prefixWord, tailWord_8203098, baseEnd_8203098] using wordTrace_append hprefix tailTrace_8203098
  have hstable : (prefixWord ++ tailWord_8203098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203098).length < 2 ^ (prefixWord ++ tailWord_8203098).sum := by decide
  have hdescent : baseEnd_8203098 < baseStart_8203098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203141 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_8203141 : Nat := 118140960795 + 8203141 * 2 ^ 59
def prefixEnd_8203141 : Nat := 4983230072969 + 3 ^ 40 * 8203141 * 2
def baseEnd_8203141 : Nat := 4212154209603794906811947

theorem tailTrace_8203141 : CollatzResearch.WordTrace tailWord_8203141 prefixEnd_8203141 4212154209603794906811947 := by
  unfold tailWord_8203141
  simp only [CollatzResearch.WordTrace]
  refine ⟨299193131974428616789801277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199462087982952411193200851 299193131974428616789801277)
  ·
    refine ⟨112197424490410731296175479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 299193131974428616789801277 112197424490410731296175479)
    ·
      refine ⟨168296136735616096944263219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112197424490410731296175479 168296136735616096944263219)
      ·
        refine ⟨252444205103424145416394829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168296136735616096944263219 252444205103424145416394829)
        ·
          refine ⟨94666576913784054531148061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252444205103424145416394829 94666576913784054531148061)
          ·
            refine ⟨35499966342669020449180523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94666576913784054531148061 35499966342669020449180523)
            ·
              refine ⟨53249949514003530673770785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35499966342669020449180523 53249949514003530673770785)
              ·
                refine ⟨39937462135502648005328089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53249949514003530673770785 39937462135502648005328089)
                ·
                  refine ⟨29953096601626986003996067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39937462135502648005328089 29953096601626986003996067)
                  ·
                    refine ⟨44929644902440479005994101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29953096601626986003996067 44929644902440479005994101)
                    ·
                      refine ⟨4212154209603794906811947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44929644902440479005994101 4212154209603794906811947)
                      ·
                        rfl

theorem cell23_8203141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_8203141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203141 prefixEnd_8203141 := by exact prefixLift 8203141
  have htrace : WordTrace (prefixWord ++ tailWord_8203141) baseStart_8203141 baseEnd_8203141 := by
    simpa [prefixWord, tailWord_8203141, baseEnd_8203141] using wordTrace_append hprefix tailTrace_8203141
  have hstable : (prefixWord ++ tailWord_8203141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203141).length < 2 ^ (prefixWord ++ tailWord_8203141).sum := by decide
  have hdescent : baseEnd_8203141 < baseStart_8203141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203172 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 2, 2, 2]
def baseStart_8203172 : Nat := 118140960795 + 8203172 * 2 ^ 59
def prefixEnd_8203172 : Nat := 4983230072969 + 3 ^ 40 * 8203172 * 2
def baseEnd_8203172 : Nat := 4212170127504084285524305

theorem tailTrace_8203172 : CollatzResearch.WordTrace tailWord_8203172 prefixEnd_8203172 4212170127504084285524305 := by
  unfold tailWord_8203172
  simp only [CollatzResearch.WordTrace]
  refine ⟨149597131318658154542089885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199462841758210872722786513 149597131318658154542089885)
  ·
    refine ⟨56098924244496807953283707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149597131318658154542089885 56098924244496807953283707)
    ·
      refine ⟨84148386366745211929925561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56098924244496807953283707 84148386366745211929925561)
      ·
        refine ⟨63111289775058908947444171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84148386366745211929925561 63111289775058908947444171)
        ·
          refine ⟨94666934662588363421166257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63111289775058908947444171 94666934662588363421166257)
          ·
            refine ⟨71000200996941272565874693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94666934662588363421166257 71000200996941272565874693)
            ·
              refine ⟨13312537686926488606101505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71000200996941272565874693 13312537686926488606101505)
              ·
                refine ⟨9984403265194866454576129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13312537686926488606101505 9984403265194866454576129)
                ·
                  refine ⟨7488302448896149840932097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9984403265194866454576129 7488302448896149840932097)
                  ·
                    refine ⟨5616226836672112380699073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7488302448896149840932097 5616226836672112380699073)
                    ·
                      refine ⟨4212170127504084285524305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5616226836672112380699073 4212170127504084285524305)
                      ·
                        rfl

theorem cell23_8203172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_8203172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203172 prefixEnd_8203172 := by exact prefixLift 8203172
  have htrace : WordTrace (prefixWord ++ tailWord_8203172) baseStart_8203172 baseEnd_8203172 := by
    simpa [prefixWord, tailWord_8203172, baseEnd_8203172] using wordTrace_append hprefix tailTrace_8203172
  have hstable : (prefixWord ++ tailWord_8203172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203172).length < 2 ^ (prefixWord ++ tailWord_8203172).sum := by decide
  have hdescent : baseEnd_8203172 < baseStart_8203172 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203191 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 4, 5]
def baseStart_8203191 : Nat := 118140960795 + 8203191 * 2 ^ 59
def prefixEnd_8203191 : Nat := 4983230072969 + 3 ^ 40 * 8203191 * 2
def baseEnd_8203191 : Nat := 1404059961212173237062239

theorem tailTrace_8203191 : CollatzResearch.WordTrace tailWord_8203191 prefixEnd_8203191 1404059961212173237062239 := by
  unfold tailWord_8203191
  simp only [CollatzResearch.WordTrace]
  refine ⟨299194955624247475329121427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 199463303749498316886080951 299194955624247475329121427)
  ·
    refine ⟨448792433436371212993682141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299194955624247475329121427 448792433436371212993682141)
    ·
      refine ⟨168297162538639204872630803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 448792433436371212993682141 168297162538639204872630803)
      ·
        refine ⟨252445743807958807308946205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168297162538639204872630803 252445743807958807308946205)
        ·
          refine ⟨94667153927984552740854827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252445743807958807308946205 94667153927984552740854827)
          ·
            refine ⟨142000730891976829111282241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94667153927984552740854827 142000730891976829111282241)
            ·
              refine ⟨106500548168982621833461681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142000730891976829111282241 106500548168982621833461681)
              ·
                refine ⟨79875411126736966375096261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106500548168982621833461681 79875411126736966375096261)
                ·
                  refine ⟨14976639586263181195330549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79875411126736966375096261 14976639586263181195330549)
                  ·
                    refine ⟨1404059961212173237062239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14976639586263181195330549 1404059961212173237062239)
                    ·
                      rfl

theorem cell23_8203191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_8203191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203191 prefixEnd_8203191 := by exact prefixLift 8203191
  have htrace : WordTrace (prefixWord ++ tailWord_8203191) baseStart_8203191 baseEnd_8203191 := by
    simpa [prefixWord, tailWord_8203191, baseEnd_8203191] using wordTrace_append hprefix tailTrace_8203191
  have hstable : (prefixWord ++ tailWord_8203191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203191).length < 2 ^ (prefixWord ++ tailWord_8203191).sum := by decide
  have hdescent : baseEnd_8203191 < baseStart_8203191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203208 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 1, 7]
def baseStart_8203208 : Nat := 118140960795 + 8203208 * 2 ^ 59
def prefixEnd_8203208 : Nat := 4983230072969 + 3 ^ 40 * 8203208 * 2
def baseEnd_8203208 : Nat := 1404062870935882048224713

theorem tailTrace_8203208 : CollatzResearch.WordTrace tailWord_8203208 prefixEnd_8203208 1404062870935882048224713 := by
  unfold tailWord_8203208
  simp only [CollatzResearch.WordTrace]
  refine ⟨149597787832592943616245139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199463717110123924821660185 149597787832592943616245139)
  ·
    refine ⟨224396681748889415424367709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149597787832592943616245139 224396681748889415424367709)
    ·
      refine ⟨84148755655833530784137891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224396681748889415424367709 84148755655833530784137891)
      ·
        refine ⟨126223133483750296176206837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84148755655833530784137891 126223133483750296176206837)
        ·
          refine ⟨11833418764101590266519391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126223133483750296176206837 11833418764101590266519391)
          ·
            refine ⟨17750128146152385399779087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11833418764101590266519391 17750128146152385399779087)
            ·
              refine ⟨26625192219228578099668631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17750128146152385399779087 26625192219228578099668631)
              ·
                refine ⟨39937788328842867149502947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26625192219228578099668631 39937788328842867149502947)
                ·
                  refine ⟨59906682493264300724254421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39937788328842867149502947 59906682493264300724254421)
                  ·
                    refine ⟨1404062870935882048224713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59906682493264300724254421 1404062870935882048224713)
                    ·
                      rfl

theorem cell23_8203208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_8203208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203208 prefixEnd_8203208 := by exact prefixLift 8203208
  have htrace : WordTrace (prefixWord ++ tailWord_8203208) baseStart_8203208 baseEnd_8203208 := by
    simpa [prefixWord, tailWord_8203208, baseEnd_8203208] using wordTrace_append hprefix tailTrace_8203208
  have hstable : (prefixWord ++ tailWord_8203208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203208).length < 2 ^ (prefixWord ++ tailWord_8203208).sum := by decide
  have hdescent : baseEnd_8203208 < baseStart_8203208 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8203272 : List Nat := [2, 1, 3, 2, 1, 3, 3, 3, 1, 4]
def baseStart_8203272 : Nat := 118140960795 + 8203272 * 2 ^ 59
def prefixEnd_8203272 : Nat := 4983230072969 + 3 ^ 40 * 8203272 * 2
def baseEnd_8203272 : Nat := 1404073825189844631424615

theorem tailTrace_8203272 : CollatzResearch.WordTrace tailWord_8203272 prefixEnd_8203272 1404073825189844631424615 := by
  unfold tailWord_8203272
  simp only [CollatzResearch.WordTrace]
  refine ⟨149598954968477013081410035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 199465273291302684108546713 149598954968477013081410035)
  ·
    refine ⟨224398432452715519622115053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149598954968477013081410035 224398432452715519622115053)
    ·
      refine ⟨84149412169768319858293145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224398432452715519622115053 84149412169768319858293145)
      ·
        refine ⟨63112059127326239893719859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84149412169768319858293145 63112059127326239893719859)
        ·
          refine ⟨94668088690989359840579789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63112059127326239893719859 94668088690989359840579789)
          ·
            refine ⟨35500533259121009940217421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94668088690989359840579789 35500533259121009940217421)
            ·
              refine ⟨13312699972170378727581533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35500533259121009940217421 13312699972170378727581533)
              ·
                refine ⟨4992262489563892022843075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13312699972170378727581533 4992262489563892022843075)
                ·
                  refine ⟨7488393734345838034264613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992262489563892022843075 7488393734345838034264613)
                  ·
                    refine ⟨1404073825189844631424615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7488393734345838034264613 1404073825189844631424615)
                    ·
                      rfl

theorem cell23_8203272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_8203272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8203272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8203272 prefixEnd_8203272 := by exact prefixLift 8203272
  have htrace : WordTrace (prefixWord ++ tailWord_8203272) baseStart_8203272 baseEnd_8203272 := by
    simpa [prefixWord, tailWord_8203272, baseEnd_8203272] using wordTrace_append hprefix tailTrace_8203272
  have hstable : (prefixWord ++ tailWord_8203272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8203272).length < 2 ^ (prefixWord ++ tailWord_8203272).sum := by decide
  have hdescent : baseEnd_8203272 < baseStart_8203272 := by decide
  rcases family_descends (prefixWord ++ tailWord_8203272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
