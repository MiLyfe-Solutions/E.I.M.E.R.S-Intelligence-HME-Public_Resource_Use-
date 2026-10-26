import V185TrunkScan23Chunk0363

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2152613 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 5, 3, 2]
def baseStart_2152613 : Nat := 118140960795 + 2152613 * 2 ^ 59
def prefixEnd_2152613 : Nat := 4983230072969 + 3 ^ 40 * 2152613 * 2
def baseEnd_2152613 : Nat := 1105325132116891625437819

theorem tailTrace_2152613 : CollatzResearch.WordTrace tailWord_2152613 prefixEnd_2152613 1105325132116891625437819 := by
  unfold tailWord_2152613
  simp only [CollatzResearch.WordTrace]
  refine ⟨78512246150458212876430493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52341497433638808584286995 78512246150458212876430493)
  ·
    refine ⟨29442092306421829828661435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78512246150458212876430493 29442092306421829828661435)
    ·
      refine ⟨44163138459632744742992153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29442092306421829828661435 44163138459632744742992153)
      ·
        refine ⟨33122353844724558557244115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44163138459632744742992153 33122353844724558557244115)
        ·
          refine ⟨49683530767086837835866173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33122353844724558557244115 49683530767086837835866173)
          ·
            refine ⟨18631324037657564188449815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49683530767086837835866173 18631324037657564188449815)
            ·
              refine ⟨27946986056486346282674723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18631324037657564188449815 27946986056486346282674723)
              ·
                refine ⟨41920479084729519424012085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27946986056486346282674723 41920479084729519424012085)
                ·
                  refine ⟨3930044914193392446001133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41920479084729519424012085 3930044914193392446001133)
                  ·
                    refine ⟨1473766842822522167250425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3930044914193392446001133 1473766842822522167250425)
                    ·
                      refine ⟨1105325132116891625437819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473766842822522167250425 1105325132116891625437819)
                      ·
                        rfl

theorem cell23_2152613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_2152613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152613 prefixEnd_2152613 := by exact prefixLift 2152613
  have htrace : WordTrace (prefixWord ++ tailWord_2152613) baseStart_2152613 baseEnd_2152613 := by
    simpa [prefixWord, tailWord_2152613, baseEnd_2152613] using wordTrace_append hprefix tailTrace_2152613
  have hstable : (prefixWord ++ tailWord_2152613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152613).length < 2 ^ (prefixWord ++ tailWord_2152613).sum := by decide
  have hdescent : baseEnd_2152613 < baseStart_2152613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152626 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2152626 : Nat := 118140960795 + 2152626 * 2 ^ 59
def prefixEnd_2152626 : Nat := 4983230072969 + 3 ^ 40 * 2152626 * 2
def baseEnd_2152626 : Nat := 1105331807365400074575259

theorem tailTrace_2152626 : CollatzResearch.WordTrace tailWord_2152626 prefixEnd_2152626 1105331807365400074575259 := by
  unfold tailWord_2152626
  simp only [CollatzResearch.WordTrace]
  refine ⟨19628180074852779024163433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52341813532940744064435821 19628180074852779024163433)
  ·
    refine ⟨14721135056139584268122575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19628180074852779024163433 14721135056139584268122575)
    ·
      refine ⟨22081702584209376402183863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14721135056139584268122575 22081702584209376402183863)
      ·
        refine ⟨33122553876314064603275795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22081702584209376402183863 33122553876314064603275795)
        ·
          refine ⟨49683830814471096904913693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33122553876314064603275795 49683830814471096904913693)
          ·
            refine ⟨18631436555426661339342635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49683830814471096904913693 18631436555426661339342635)
            ·
              refine ⟨27947154833139992009013953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18631436555426661339342635 27947154833139992009013953)
              ·
                refine ⟨20960366124854994006760465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27947154833139992009013953 20960366124854994006760465)
                ·
                  refine ⟨15720274593641245505070349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20960366124854994006760465 15720274593641245505070349)
                  ·
                    refine ⟨5895102972615467064401381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15720274593641245505070349 5895102972615467064401381)
                    ·
                      refine ⟨1105331807365400074575259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5895102972615467064401381 1105331807365400074575259)
                      ·
                        rfl

theorem cell23_2152626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2152626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152626 prefixEnd_2152626 := by exact prefixLift 2152626
  have htrace : WordTrace (prefixWord ++ tailWord_2152626) baseStart_2152626 baseEnd_2152626 := by
    simpa [prefixWord, tailWord_2152626, baseEnd_2152626] using wordTrace_append hprefix tailTrace_2152626
  have hstable : (prefixWord ++ tailWord_2152626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152626).length < 2 ^ (prefixWord ++ tailWord_2152626).sum := by decide
  have hdescent : baseEnd_2152626 < baseStart_2152626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152641 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2152641 : Nat := 118140960795 + 2152641 * 2 ^ 59
def prefixEnd_2152641 : Nat := 4983230072969 + 3 ^ 40 * 2152641 * 2
def baseEnd_2152641 : Nat := 1105339509575217515887691

theorem tailTrace_2152641 : CollatzResearch.WordTrace tailWord_2152641 prefixEnd_2152641 1105339509575217515887691 := by
  unfold tailWord_2152641
  simp only [CollatzResearch.WordTrace]
  refine ⟨78513267394356773658449777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52342178262904515772299851 78513267394356773658449777)
  ·
    refine ⟨58884950545767580243837333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78513267394356773658449777 58884950545767580243837333)
    ·
      refine ⟨2760232056832855323929875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58884950545767580243837333 2760232056832855323929875)
      ·
        refine ⟨4140348085249282985894813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2760232056832855323929875 4140348085249282985894813)
        ·
          refine ⟨1552630531968481119710555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4140348085249282985894813 1552630531968481119710555)
          ·
            refine ⟨2328945797952721679565833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1552630531968481119710555 2328945797952721679565833)
            ·
              refine ⟨1746709348464541259674375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2328945797952721679565833 1746709348464541259674375)
              ·
                refine ⟨2620064022696811889511563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1746709348464541259674375 2620064022696811889511563)
                ·
                  refine ⟨3930096034045217834267345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2620064022696811889511563 3930096034045217834267345)
                  ·
                    refine ⟨2947572025533913375700509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3930096034045217834267345 2947572025533913375700509)
                    ·
                      refine ⟨1105339509575217515887691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2947572025533913375700509 1105339509575217515887691)
                      ·
                        rfl

theorem cell23_2152641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2152641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152641 prefixEnd_2152641 := by exact prefixLift 2152641
  have htrace : WordTrace (prefixWord ++ tailWord_2152641) baseStart_2152641 baseEnd_2152641 := by
    simpa [prefixWord, tailWord_2152641, baseEnd_2152641] using wordTrace_append hprefix tailTrace_2152641
  have hstable : (prefixWord ++ tailWord_2152641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152641).length < 2 ^ (prefixWord ++ tailWord_2152641).sum := by decide
  have hdescent : baseEnd_2152641 < baseStart_2152641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152666 : List Nat := [3, 1, 1, 2, 2, 1, 3, 3, 7]
def baseStart_2152666 : Nat := 118140960795 + 2152666 * 2 ^ 59
def prefixEnd_2152666 : Nat := 4983230072969 + 3 ^ 40 * 2152666 * 2
def baseEnd_2152666 : Nat := 122816927399064435341675

theorem tailTrace_2152666 : CollatzResearch.WordTrace tailWord_2152666 prefixEnd_2152666 122816927399064435341675 := by
  unfold tailWord_2152666
  simp only [CollatzResearch.WordTrace]
  refine ⟨19628544804816550732027463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52342786146177468618739901 19628544804816550732027463)
  ·
    refine ⟨29442817207224826098041195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19628544804816550732027463 29442817207224826098041195)
    ·
      refine ⟨44164225810837239147061793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29442817207224826098041195 44164225810837239147061793)
      ·
        refine ⟨33123169358127929360296345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44164225810837239147061793 33123169358127929360296345)
        ·
          refine ⟨24842377018595947020222259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33123169358127929360296345 24842377018595947020222259)
          ·
            refine ⟨37263565527893920530333389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24842377018595947020222259 37263565527893920530333389)
            ·
              refine ⟨13973837072960220198875021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37263565527893920530333389 13973837072960220198875021)
              ·
                refine ⟨5240188902360082574578133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13973837072960220198875021 5240188902360082574578133)
                ·
                  refine ⟨122816927399064435341675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5240188902360082574578133 122816927399064435341675)
                  ·
                    rfl

theorem cell23_2152666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_2152666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152666 prefixEnd_2152666 := by exact prefixLift 2152666
  have htrace : WordTrace (prefixWord ++ tailWord_2152666) baseStart_2152666 baseEnd_2152666 := by
    simpa [prefixWord, tailWord_2152666, baseEnd_2152666] using wordTrace_append hprefix tailTrace_2152666
  have hstable : (prefixWord ++ tailWord_2152666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152666).length < 2 ^ (prefixWord ++ tailWord_2152666).sum := by decide
  have hdescent : baseEnd_2152666 < baseStart_2152666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152677 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 1, 4, 2]
def baseStart_2152677 : Nat := 118140960795 + 2152677 * 2 ^ 59
def prefixEnd_2152677 : Nat := 4983230072969 + 3 ^ 40 * 2152677 * 2
def baseEnd_2152677 : Nat := 1105357994878779375037525

theorem tailTrace_2152677 : CollatzResearch.WordTrace tailWord_2152677 prefixEnd_2152677 1105357994878779375037525 := by
  unfold tailWord_2152677
  simp only [CollatzResearch.WordTrace]
  refine ⟨78514580422226351806760285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52343053614817567871173523 78514580422226351806760285)
  ·
    refine ⟨29442967658334881927535107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78514580422226351806760285 29442967658334881927535107)
    ·
      refine ⟨44164451487502322891302661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29442967658334881927535107 44164451487502322891302661)
      ·
        refine ⟨8280834653906685542119249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44164451487502322891302661 8280834653906685542119249)
        ·
          refine ⟨6210625990430014156589437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8280834653906685542119249 6210625990430014156589437)
          ·
            refine ⟨2328984746411255308721039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6210625990430014156589437 2328984746411255308721039)
            ·
              refine ⟨3493477119616882963081559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2328984746411255308721039 3493477119616882963081559)
              ·
                refine ⟨5240215679425324444622339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493477119616882963081559 5240215679425324444622339)
                ·
                  refine ⟨7860323519137986666933509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5240215679425324444622339 7860323519137986666933509)
                  ·
                    refine ⟨1473810659838372500050033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7860323519137986666933509 1473810659838372500050033)
                    ·
                      refine ⟨1105357994878779375037525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473810659838372500050033 1105357994878779375037525)
                      ·
                        rfl

theorem cell23_2152677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_2152677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152677 prefixEnd_2152677 := by exact prefixLift 2152677
  have htrace : WordTrace (prefixWord ++ tailWord_2152677) baseStart_2152677 baseEnd_2152677 := by
    simpa [prefixWord, tailWord_2152677, baseEnd_2152677] using wordTrace_append hprefix tailTrace_2152677
  have hstable : (prefixWord ++ tailWord_2152677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152677).length < 2 ^ (prefixWord ++ tailWord_2152677).sum := by decide
  have hdescent : baseEnd_2152677 < baseStart_2152677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152696 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 6, 5]
def baseStart_2152696 : Nat := 118140960795 + 2152696 * 2 ^ 59
def prefixEnd_2152696 : Nat := 4983230072969 + 3 ^ 40 * 2152696 * 2
def baseEnd_2152696 : Nat := 368455917003738266899979

theorem tailTrace_2152696 : CollatzResearch.WordTrace tailWord_2152696 prefixEnd_2152696 368455917003738266899979 := by
  unfold tailWord_2152696
  simp only [CollatzResearch.WordTrace]
  refine ⟨39257636704578759025850971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52343515606105012034467961 39257636704578759025850971)
  ·
    refine ⟨58886455056868138538776457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39257636704578759025850971 58886455056868138538776457)
    ·
      refine ⟨44164841292651103904082343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58886455056868138538776457 44164841292651103904082343)
      ·
        refine ⟨66247261938976655856123515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44164841292651103904082343 66247261938976655856123515)
        ·
          refine ⟨99370892908464983784185273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66247261938976655856123515 99370892908464983784185273)
          ·
            refine ⟨74528169681348737838138955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99370892908464983784185273 74528169681348737838138955)
            ·
              refine ⟨111792254522023106757208433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74528169681348737838138955 111792254522023106757208433)
              ·
                refine ⟨83844190891517330067906325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111792254522023106757208433 83844190891517330067906325)
                ·
                  refine ⟨3930196448039874846933109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83844190891517330067906325 3930196448039874846933109)
                  ·
                    refine ⟨368455917003738266899979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3930196448039874846933109 368455917003738266899979)
                    ·
                      rfl

theorem cell23_2152696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_2152696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152696 prefixEnd_2152696 := by exact prefixLift 2152696
  have htrace : WordTrace (prefixWord ++ tailWord_2152696) baseStart_2152696 baseEnd_2152696 := by
    simpa [prefixWord, tailWord_2152696, baseEnd_2152696] using wordTrace_append hprefix tailTrace_2152696
  have hstable : (prefixWord ++ tailWord_2152696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152696).length < 2 ^ (prefixWord ++ tailWord_2152696).sum := by decide
  have hdescent : baseEnd_2152696 < baseStart_2152696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152700 : List Nat := [2, 2, 2, 1, 4, 1, 3, 3, 5]
def baseStart_2152700 : Nat := 118140960795 + 2152700 * 2 ^ 59
def prefixEnd_2152700 : Nat := 4983230072969 + 3 ^ 40 * 2152700 * 2
def baseEnd_2152700 : Nat := 122818867214870309449991

theorem tailTrace_2152700 : CollatzResearch.WordTrace tailWord_2152700 prefixEnd_2152700 122818867214870309449991 := by
  unfold tailWord_2152700
  simp only [CollatzResearch.WordTrace]
  refine ⟨39257709650571513367423777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52343612867428684489898369 39257709650571513367423777)
  ·
    refine ⟨29443282237928635025567833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39257709650571513367423777 29443282237928635025567833)
    ·
      refine ⟨22082461678446476269175875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29443282237928635025567833 22082461678446476269175875)
      ·
        refine ⟨33123692517669714403763813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22082461678446476269175875 33123692517669714403763813)
        ·
          refine ⟨6210692347063071450705715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33123692517669714403763813 6210692347063071450705715)
          ·
            refine ⟨9316038520594607176058573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6210692347063071450705715 9316038520594607176058573)
            ·
              refine ⟨3493514445222977691021965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9316038520594607176058573 3493514445222977691021965)
              ·
                refine ⟨1310067916958616634133237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3493514445222977691021965 1310067916958616634133237)
                ·
                  refine ⟨122818867214870309449991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1310067916958616634133237 122818867214870309449991)
                  ·
                    rfl

theorem cell23_2152700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_2152700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152700 prefixEnd_2152700 := by exact prefixLift 2152700
  have htrace : WordTrace (prefixWord ++ tailWord_2152700) baseStart_2152700 baseEnd_2152700 := by
    simpa [prefixWord, tailWord_2152700, baseEnd_2152700] using wordTrace_append hprefix tailTrace_2152700
  have hstable : (prefixWord ++ tailWord_2152700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152700).length < 2 ^ (prefixWord ++ tailWord_2152700).sum := by decide
  have hdescent : baseEnd_2152700 < baseStart_2152700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152713 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 2, 5]
def baseStart_2152713 : Nat := 118140960795 + 2152713 * 2 ^ 59
def prefixEnd_2152713 : Nat := 4983230072969 + 3 ^ 40 * 2152713 * 2
def baseEnd_2152713 : Nat := 368458826727447078062453

theorem tailTrace_2152713 : CollatzResearch.WordTrace tailWord_2152713 prefixEnd_2152713 368458826727447078062453 := by
  unfold tailWord_2152713
  simp only [CollatzResearch.WordTrace]
  refine ⟨78515893450095929955070793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52343928966730619970047195 78515893450095929955070793)
  ·
    refine ⟨58886920087571947466303095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78515893450095929955070793 58886920087571947466303095)
    ·
      refine ⟨88330380131357921199454643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58886920087571947466303095 88330380131357921199454643)
      ·
        refine ⟨132495570197036881799181965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88330380131357921199454643 132495570197036881799181965)
        ·
          refine ⟨49685838823888830674693237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132495570197036881799181965 49685838823888830674693237)
          ·
            refine ⟨4658047389739577875752491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49685838823888830674693237 4658047389739577875752491)
            ·
              refine ⟨6987071084609366813628737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4658047389739577875752491 6987071084609366813628737)
              ·
                refine ⟨5240303313457025110221553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6987071084609366813628737 5240303313457025110221553)
                ·
                  refine ⟨3930227485092768832666165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5240303313457025110221553 3930227485092768832666165)
                  ·
                    refine ⟨368458826727447078062453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3930227485092768832666165 368458826727447078062453)
                    ·
                      rfl

theorem cell23_2152713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_2152713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152713 prefixEnd_2152713 := by exact prefixLift 2152713
  have htrace : WordTrace (prefixWord ++ tailWord_2152713) baseStart_2152713 baseEnd_2152713 := by
    simpa [prefixWord, tailWord_2152713, baseEnd_2152713] using wordTrace_append hprefix tailTrace_2152713
  have hstable : (prefixWord ++ tailWord_2152713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152713).length < 2 ^ (prefixWord ++ tailWord_2152713).sum := by decide
  have hdescent : baseEnd_2152713 < baseStart_2152713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152798 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2152798 : Nat := 118140960795 + 2152798 * 2 ^ 59
def prefixEnd_2152798 : Nat := 4983230072969 + 3 ^ 40 * 2152798 * 2
def baseEnd_2152798 : Nat := 368473375345991133874823

theorem tailTrace_2152798 : CollatzResearch.WordTrace tailWord_2152798 prefixEnd_2152798 368473375345991133874823 := by
  unfold tailWord_2152798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9814874206848498683989381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52345995769858659647943365 9814874206848498683989381)
  ·
    refine ⟨1840288913784093503248009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9814874206848498683989381 1840288913784093503248009)
    ·
      refine ⟨1380216685338070127436007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1840288913784093503248009 1380216685338070127436007)
      ·
        refine ⟨2070325028007105191154011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380216685338070127436007 2070325028007105191154011)
        ·
          refine ⟨3105487542010657786731017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070325028007105191154011 3105487542010657786731017)
          ·
            refine ⟨2329115656507993340048263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3105487542010657786731017 2329115656507993340048263)
            ·
              refine ⟨3493673484761990010072395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2329115656507993340048263 3493673484761990010072395)
              ·
                refine ⟨5240510227142985015108593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493673484761990010072395 5240510227142985015108593)
                ·
                  refine ⟨3930382670357238761331445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5240510227142985015108593 3930382670357238761331445)
                  ·
                    refine ⟨368473375345991133874823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3930382670357238761331445 368473375345991133874823)
                    ·
                      rfl

theorem cell23_2152798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2152798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152798 prefixEnd_2152798 := by exact prefixLift 2152798
  have htrace : WordTrace (prefixWord ++ tailWord_2152798) baseStart_2152798 baseEnd_2152798 := by
    simpa [prefixWord, tailWord_2152798, baseEnd_2152798] using wordTrace_append hprefix tailTrace_2152798
  have hstable : (prefixWord ++ tailWord_2152798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152798).length < 2 ^ (prefixWord ++ tailWord_2152798).sum := by decide
  have hdescent : baseEnd_2152798 < baseStart_2152798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152803 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 3, 5]
def baseStart_2152803 : Nat := 118140960795 + 2152803 * 2 ^ 59
def prefixEnd_2152803 : Nat := 4983230072969 + 3 ^ 40 * 2152803 * 2
def baseEnd_2152803 : Nat := 368474231147081960687315

theorem tailTrace_2152803 : CollatzResearch.WordTrace tailWord_2152803 prefixEnd_2152803 368474231147081960687315 := by
  unfold tailWord_2152803
  simp only [CollatzResearch.WordTrace]
  refine ⟨78519176019769875325847063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52346117346513250217231375 78519176019769875325847063)
  ·
    refine ⟨117778764029654812988770595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78519176019769875325847063 117778764029654812988770595)
    ·
      refine ⟨176668146044482219483155893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117778764029654812988770595 176668146044482219483155893)
      ·
        refine ⟨16562638691670208076545865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176668146044482219483155893 16562638691670208076545865)
        ·
          refine ⟨12421979018752656057409399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16562638691670208076545865 12421979018752656057409399)
          ·
            refine ⟨18632968528128984086114099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12421979018752656057409399 18632968528128984086114099)
            ·
              refine ⟨27949452792193476129171149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18632968528128984086114099 27949452792193476129171149)
              ·
                refine ⟨10481044797072553548439181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27949452792193476129171149 10481044797072553548439181)
                ·
                  refine ⟨3930391798902207580664693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10481044797072553548439181 3930391798902207580664693)
                  ·
                    refine ⟨368474231147081960687315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3930391798902207580664693 368474231147081960687315)
                    ·
                      rfl

theorem cell23_2152803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 5].length) (baseStart_2152803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152803 prefixEnd_2152803 := by exact prefixLift 2152803
  have htrace : WordTrace (prefixWord ++ tailWord_2152803) baseStart_2152803 baseEnd_2152803 := by
    simpa [prefixWord, tailWord_2152803, baseEnd_2152803] using wordTrace_append hprefix tailTrace_2152803
  have hstable : (prefixWord ++ tailWord_2152803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152803).length < 2 ^ (prefixWord ++ tailWord_2152803).sum := by decide
  have hdescent : baseEnd_2152803 < baseStart_2152803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152823 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_2152823 : Nat := 118140960795 + 2152823 * 2 ^ 59
def prefixEnd_2152823 : Nat := 4983230072969 + 3 ^ 40 * 2152823 * 2
def baseEnd_2152823 : Nat := 1105432963054335803811853

theorem tailTrace_2152823 : CollatzResearch.WordTrace tailWord_2152823 prefixEnd_2152823 1105432963054335803811853 := by
  unfold tailWord_2152823
  simp only [CollatzResearch.WordTrace]
  refine ⟨78519905479697418741575123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52346603653131612494383415 78519905479697418741575123)
  ·
    refine ⟨117779858219546128112362685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78519905479697418741575123 117779858219546128112362685)
    ·
      refine ⟨44167446832329798042136007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117779858219546128112362685 44167446832329798042136007)
      ·
        refine ⟨66251170248494697063204011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44167446832329798042136007 66251170248494697063204011)
        ·
          refine ⟨99376755372742045594806017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66251170248494697063204011 99376755372742045594806017)
          ·
            refine ⟨74532566529556534196104513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99376755372742045594806017 74532566529556534196104513)
            ·
              refine ⟨55899424897167400647078385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74532566529556534196104513 55899424897167400647078385)
              ·
                refine ⟨41924568672875550485308789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55899424897167400647078385 41924568672875550485308789)
                ·
                  refine ⟨3930428313082082857997699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41924568672875550485308789 3930428313082082857997699)
                  ·
                    refine ⟨5895642469623124286996549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3930428313082082857997699 5895642469623124286996549)
                    ·
                      refine ⟨1105432963054335803811853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5895642469623124286996549 1105432963054335803811853)
                      ·
                        rfl

theorem cell23_2152823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_2152823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152823 prefixEnd_2152823 := by exact prefixLift 2152823
  have htrace : WordTrace (prefixWord ++ tailWord_2152823) baseStart_2152823 baseEnd_2152823 := by
    simpa [prefixWord, tailWord_2152823, baseEnd_2152823] using wordTrace_append hprefix tailTrace_2152823
  have hstable : (prefixWord ++ tailWord_2152823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152823).length < 2 ^ (prefixWord ++ tailWord_2152823).sum := by decide
  have hdescent : baseEnd_2152823 < baseStart_2152823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152843 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 5]
def baseStart_2152843 : Nat := 118140960795 + 2152843 * 2 ^ 59
def prefixEnd_2152843 : Nat := 4983230072969 + 3 ^ 40 * 2152843 * 2
def baseEnd_2152843 : Nat := 1105443232667425725561761

theorem tailTrace_2152843 : CollatzResearch.WordTrace tailWord_2152843 prefixEnd_2152843 1105443232667425725561761 := by
  unfold tailWord_2152843
  simp only [CollatzResearch.WordTrace]
  refine ⟨78520634939624962157303183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52347089959749974771535455 78520634939624962157303183)
  ·
    refine ⟨117780952409437443235954775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78520634939624962157303183 117780952409437443235954775)
    ·
      refine ⟨176671428614156164853932163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117780952409437443235954775 176671428614156164853932163)
      ·
        refine ⟨265007142921234247280898245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176671428614156164853932163 265007142921234247280898245)
        ·
          refine ⟨49688839297731421365168421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265007142921234247280898245 49688839297731421365168421)
          ·
            refine ⟨9316657368324641505969079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49688839297731421365168421 9316657368324641505969079)
            ·
              refine ⟨13974986052486962258953619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9316657368324641505969079 13974986052486962258953619)
              ·
                refine ⟨20962479078730443388430429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13974986052486962258953619 20962479078730443388430429)
                ·
                  refine ⟨7860929654523916270661411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20962479078730443388430429 7860929654523916270661411)
                  ·
                    refine ⟨11791394481785874405992117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7860929654523916270661411 11791394481785874405992117)
                    ·
                      refine ⟨1105443232667425725561761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11791394481785874405992117 1105443232667425725561761)
                      ·
                        rfl

theorem cell23_2152843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 5].length) (baseStart_2152843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152843 prefixEnd_2152843 := by exact prefixLift 2152843
  have htrace : WordTrace (prefixWord ++ tailWord_2152843) baseStart_2152843 baseEnd_2152843 := by
    simpa [prefixWord, tailWord_2152843, baseEnd_2152843] using wordTrace_append hprefix tailTrace_2152843
  have hstable : (prefixWord ++ tailWord_2152843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152843).length < 2 ^ (prefixWord ++ tailWord_2152843).sum := by decide
  have hdescent : baseEnd_2152843 < baseStart_2152843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152857 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 3, 2, 2]
def baseStart_2152857 : Nat := 118140960795 + 2152857 * 2 ^ 59
def prefixEnd_2152857 : Nat := 4983230072969 + 3 ^ 40 * 2152857 * 2
def baseEnd_2152857 : Nat := 1105450421396588670786697

theorem tailTrace_2152857 : CollatzResearch.WordTrace tailWord_2152857 prefixEnd_2152857 1105450421396588670786697 := by
  unfold tailWord_2152857
  simp only [CollatzResearch.WordTrace]
  refine ⟨78521145561574242548312825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52347430374382828365541883 78521145561574242548312825)
  ·
    refine ⟨58890859171180681911234619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78521145561574242548312825 58890859171180681911234619)
    ·
      refine ⟨88336288756771022866851929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58890859171180681911234619 88336288756771022866851929)
      ·
        refine ⟨66252216567578267150138947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88336288756771022866851929 66252216567578267150138947)
        ·
          refine ⟨99378324851367400725208421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66252216567578267150138947 99378324851367400725208421)
          ·
            refine ⟨18633435909631387635976579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99378324851367400725208421 18633435909631387635976579)
            ·
              refine ⟨27950153864447081453964869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18633435909631387635976579 27950153864447081453964869)
              ·
                refine ⟨5240653849583827772618413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27950153864447081453964869 5240653849583827772618413)
                ·
                  refine ⟨1965245193593935414731905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5240653849583827772618413 1965245193593935414731905)
                  ·
                    refine ⟨1473933895195451561048929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1965245193593935414731905 1473933895195451561048929)
                    ·
                      refine ⟨1105450421396588670786697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1473933895195451561048929 1105450421396588670786697)
                      ·
                        rfl

theorem cell23_2152857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 2, 2].length) (baseStart_2152857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152857 prefixEnd_2152857 := by exact prefixLift 2152857
  have htrace : WordTrace (prefixWord ++ tailWord_2152857) baseStart_2152857 baseEnd_2152857 := by
    simpa [prefixWord, tailWord_2152857, baseEnd_2152857] using wordTrace_append hprefix tailTrace_2152857
  have hstable : (prefixWord ++ tailWord_2152857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152857).length < 2 ^ (prefixWord ++ tailWord_2152857).sum := by decide
  have hdescent : baseEnd_2152857 < baseStart_2152857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152863 : List Nat := [1, 1, 2, 5, 1, 1, 3, 9]
def baseStart_2152863 : Nat := 118140960795 + 2152863 * 2 ^ 59
def prefixEnd_2152863 : Nat := 4983230072969 + 3 ^ 40 * 2152863 * 2
def baseEnd_2152863 : Nat := 40942722306685764715247

theorem tailTrace_2152863 : CollatzResearch.WordTrace tailWord_2152863 prefixEnd_2152863 40942722306685764715247 := by
  unfold tailWord_2152863
  simp only [CollatzResearch.WordTrace]
  refine ⟨78521364399552505573031243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52347576266368337048687495 78521364399552505573031243)
  ·
    refine ⟨117782046599328758359546865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78521364399552505573031243 117782046599328758359546865)
    ·
      refine ⟨88336534949496568769660149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117782046599328758359546865 88336534949496568769660149)
      ·
        refine ⟨8281550151515303322155639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88336534949496568769660149 8281550151515303322155639)
        ·
          refine ⟨12422325227272954983233459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8281550151515303322155639 12422325227272954983233459)
          ·
            refine ⟨18633487840909432474850189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12422325227272954983233459 18633487840909432474850189)
            ·
              refine ⟨6987557940341037178068821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18633487840909432474850189 6987557940341037178068821)
              ·
                refine ⟨40942722306685764715247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6987557940341037178068821 40942722306685764715247)
                ·
                  rfl

theorem cell23_2152863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 9].length) (baseStart_2152863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152863 prefixEnd_2152863 := by exact prefixLift 2152863
  have htrace : WordTrace (prefixWord ++ tailWord_2152863) baseStart_2152863 baseEnd_2152863 := by
    simpa [prefixWord, tailWord_2152863, baseEnd_2152863] using wordTrace_append hprefix tailTrace_2152863
  have hstable : (prefixWord ++ tailWord_2152863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152863).length < 2 ^ (prefixWord ++ tailWord_2152863).sum := by decide
  have hdescent : baseEnd_2152863 < baseStart_2152863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152941 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2152941 : Nat := 118140960795 + 2152941 * 2 ^ 59
def prefixEnd_2152941 : Nat := 4983230072969 + 3 ^ 40 * 2152941 * 2
def baseEnd_2152941 : Nat := 1105493553771566342136311

theorem tailTrace_2152941 : CollatzResearch.WordTrace tailWord_2152941 prefixEnd_2152941 1105493553771566342136311 := by
  unfold tailWord_2152941
  simp only [CollatzResearch.WordTrace]
  refine ⟨78524209293269924894370677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52349472862179949929580451 78524209293269924894370677)
  ·
    refine ⟨7361644621244055458847251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78524209293269924894370677 7361644621244055458847251)
    ·
      refine ⟨11042466931866083188270877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7361644621244055458847251 11042466931866083188270877)
      ·
        refine ⟨4140925099449781195601579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11042466931866083188270877 4140925099449781195601579)
        ·
          refine ⟨6211387649174671793402369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4140925099449781195601579 6211387649174671793402369)
          ·
            refine ⟨4658540736881003845051777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6211387649174671793402369 4658540736881003845051777)
            ·
              refine ⟨3493905552660752883788833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4658540736881003845051777 3493905552660752883788833)
              ·
                refine ⟨2620429164495564662841625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3493905552660752883788833 2620429164495564662841625)
                ·
                  refine ⟨1965321873371673497131219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2620429164495564662841625 1965321873371673497131219)
                  ·
                    refine ⟨2947982810057510245696829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1965321873371673497131219 2947982810057510245696829)
                    ·
                      refine ⟨1105493553771566342136311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2947982810057510245696829 1105493553771566342136311)
                      ·
                        rfl

theorem cell23_2152941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2152941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152941 prefixEnd_2152941 := by exact prefixLift 2152941
  have htrace : WordTrace (prefixWord ++ tailWord_2152941) baseStart_2152941 baseEnd_2152941 := by
    simpa [prefixWord, tailWord_2152941, baseEnd_2152941] using wordTrace_append hprefix tailTrace_2152941
  have hstable : (prefixWord ++ tailWord_2152941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152941).length < 2 ^ (prefixWord ++ tailWord_2152941).sum := by decide
  have hdescent : baseEnd_2152941 < baseStart_2152941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152943 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_2152943 : Nat := 118140960795 + 2152943 * 2 ^ 59
def prefixEnd_2152943 : Nat := 4983230072969 + 3 ^ 40 * 2152943 * 2
def baseEnd_2152943 : Nat := 1105494580732875334311301

theorem tailTrace_2152943 : CollatzResearch.WordTrace tailWord_2152943 prefixEnd_2152943 1105494580732875334311301 := by
  unfold tailWord_2152943
  simp only [CollatzResearch.WordTrace]
  refine ⟨78524282239262679235943483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52349521492841786157295655 78524282239262679235943483)
  ·
    refine ⟨117786423358894018853915225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78524282239262679235943483 117786423358894018853915225)
    ·
      refine ⟨88339817519170514140436419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117786423358894018853915225 88339817519170514140436419)
      ·
        refine ⟨132509726278755771210654629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88339817519170514140436419 132509726278755771210654629)
        ·
          refine ⟨24845573677266707101997743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132509726278755771210654629 24845573677266707101997743)
          ·
            refine ⟨37268360515900060652996615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24845573677266707101997743 37268360515900060652996615)
            ·
              refine ⟨55902540773850090979494923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37268360515900060652996615 55902540773850090979494923)
              ·
                refine ⟨83853811160775136469242385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55902540773850090979494923 83853811160775136469242385)
                ·
                  refine ⟨62890358370581352351931789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83853811160775136469242385 62890358370581352351931789)
                  ·
                    refine ⟨23583884388968007131974421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62890358370581352351931789 23583884388968007131974421)
                    ·
                      refine ⟨1105494580732875334311301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23583884388968007131974421 1105494580732875334311301)
                      ·
                        rfl

theorem cell23_2152943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_2152943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152943 prefixEnd_2152943 := by exact prefixLift 2152943
  have htrace : WordTrace (prefixWord ++ tailWord_2152943) baseStart_2152943 baseEnd_2152943 := by
    simpa [prefixWord, tailWord_2152943, baseEnd_2152943] using wordTrace_append hprefix tailTrace_2152943
  have hstable : (prefixWord ++ tailWord_2152943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152943).length < 2 ^ (prefixWord ++ tailWord_2152943).sum := by decide
  have hdescent : baseEnd_2152943 < baseStart_2152943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152964 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_2152964 : Nat := 118140960795 + 2152964 * 2 ^ 59
def prefixEnd_2152964 : Nat := 4983230072969 + 3 ^ 40 * 2152964 * 2
def baseEnd_2152964 : Nat := 1105505363826619752148705

theorem tailTrace_2152964 : CollatzResearch.WordTrace tailWord_2152964 prefixEnd_2152964 1105505363826619752148705 := by
  unfold tailWord_2152964
  simp only [CollatzResearch.WordTrace]
  refine ⟨39262524086093299911228973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52350032114791066548305297 39262524086093299911228973)
  ·
    refine ⟨14723446532284987466710865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39262524086093299911228973 14723446532284987466710865)
    ·
      refine ⟨11042584899213740600033149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14723446532284987466710865 11042584899213740600033149)
      ·
        refine ⟨4140969337205152725012431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11042584899213740600033149 4140969337205152725012431)
        ·
          refine ⟨6211454005807729087518647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4140969337205152725012431 6211454005807729087518647)
          ·
            refine ⟨9317181008711593631277971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6211454005807729087518647 9317181008711593631277971)
            ·
              refine ⟨13975771513067390446916957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9317181008711593631277971 13975771513067390446916957)
              ·
                refine ⟨5240914317400271417593859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13975771513067390446916957 5240914317400271417593859)
                ·
                  refine ⟨7861371476100407126390789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5240914317400271417593859 7861371476100407126390789)
                  ·
                    refine ⟨1474007151768826336198273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7861371476100407126390789 1474007151768826336198273)
                    ·
                      refine ⟨1105505363826619752148705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1474007151768826336198273 1105505363826619752148705)
                      ·
                        rfl

theorem cell23_2152964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_2152964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152964 prefixEnd_2152964 := by exact prefixLift 2152964
  have htrace : WordTrace (prefixWord ++ tailWord_2152964) baseStart_2152964 baseEnd_2152964 := by
    simpa [prefixWord, tailWord_2152964, baseEnd_2152964] using wordTrace_append hprefix tailTrace_2152964
  have hstable : (prefixWord ++ tailWord_2152964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152964).length < 2 ^ (prefixWord ++ tailWord_2152964).sum := by decide
  have hdescent : baseEnd_2152964 < baseStart_2152964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2152970 : List Nat := [3, 1, 2, 2, 2, 1, 3, 2, 7]
def baseStart_2152970 : Nat := 118140960795 + 2152970 * 2 ^ 59
def prefixEnd_2152970 : Nat := 4983230072969 + 3 ^ 40 * 2152970 * 2
def baseEnd_2152970 : Nat := 122834271634505192074853

theorem tailTrace_2152970 : CollatzResearch.WordTrace tailWord_2152970 prefixEnd_2152970 122834271634505192074853 := by
  unfold tailWord_2152970
  simp only [CollatzResearch.WordTrace]
  refine ⟨19631316752541215711794091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52350178006776575231450909 19631316752541215711794091)
  ·
    refine ⟨29446975128811823567691137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19631316752541215711794091 29446975128811823567691137)
    ·
      refine ⟨22085231346608867675768353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29446975128811823567691137 22085231346608867675768353)
      ·
        refine ⟨16563923509956650756826265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22085231346608867675768353 16563923509956650756826265)
        ·
          refine ⟨12422942632467488067619699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16563923509956650756826265 12422942632467488067619699)
          ·
            refine ⟨18634413948701232101429549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12422942632467488067619699 18634413948701232101429549)
            ·
              refine ⟨6987905230762962038036081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18634413948701232101429549 6987905230762962038036081)
              ·
                refine ⟨5240928923072221528527061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6987905230762962038036081 5240928923072221528527061)
                ·
                  refine ⟨122834271634505192074853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5240928923072221528527061 122834271634505192074853)
                  ·
                    rfl

theorem cell23_2152970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_2152970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2152970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2152970 prefixEnd_2152970 := by exact prefixLift 2152970
  have htrace : WordTrace (prefixWord ++ tailWord_2152970) baseStart_2152970 baseEnd_2152970 := by
    simpa [prefixWord, tailWord_2152970, baseEnd_2152970] using wordTrace_append hprefix tailTrace_2152970
  have hstable : (prefixWord ++ tailWord_2152970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2152970).length < 2 ^ (prefixWord ++ tailWord_2152970).sum := by decide
  have hdescent : baseEnd_2152970 < baseStart_2152970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2152970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153010 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2153010 : Nat := 118140960795 + 2153010 * 2 ^ 59
def prefixEnd_2153010 : Nat := 4983230072969 + 3 ^ 40 * 2153010 * 2
def baseEnd_2153010 : Nat := 1105528983936726572173493

theorem tailTrace_2153010 : CollatzResearch.WordTrace tailWord_2153010 prefixEnd_2153010 1105528983936726572173493 := by
  unfold tailWord_2153010
  simp only [CollatzResearch.WordTrace]
  refine ⟨19631681482504987419658121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52351150620013299785754989 19631681482504987419658121)
  ·
    refine ⟨14723761111878740564743591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19631681482504987419658121 14723761111878740564743591)
    ·
      refine ⟨22085641667818110847115387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14723761111878740564743591 22085641667818110847115387)
      ·
        refine ⟨33128462501727166270673081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22085641667818110847115387 33128462501727166270673081)
        ·
          refine ⟨24846346876295374703004811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33128462501727166270673081 24846346876295374703004811)
          ·
            refine ⟨37269520314443062054507217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24846346876295374703004811 37269520314443062054507217)
            ·
              refine ⟨27952140235832296540880413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37269520314443062054507217 27952140235832296540880413)
              ·
                refine ⟨10482052588437111202830155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27952140235832296540880413 10482052588437111202830155)
                ·
                  refine ⟨15723078882655666804245233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10482052588437111202830155 15723078882655666804245233)
                  ·
                    refine ⟨11792309161991750103183925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15723078882655666804245233 11792309161991750103183925)
                    ·
                      refine ⟨1105528983936726572173493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11792309161991750103183925 1105528983936726572173493)
                      ·
                        rfl

theorem cell23_2153010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2153010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153010 prefixEnd_2153010 := by exact prefixLift 2153010
  have htrace : WordTrace (prefixWord ++ tailWord_2153010) baseStart_2153010 baseEnd_2153010 := by
    simpa [prefixWord, tailWord_2153010, baseEnd_2153010] using wordTrace_append hprefix tailTrace_2153010
  have hstable : (prefixWord ++ tailWord_2153010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153010).length < 2 ^ (prefixWord ++ tailWord_2153010).sum := by decide
  have hdescent : baseEnd_2153010 < baseStart_2153010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153014 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2153014 : Nat := 118140960795 + 2153014 * 2 ^ 59
def prefixEnd_2153014 : Nat := 4983230072969 + 3 ^ 40 * 2153014 * 2
def baseEnd_2153014 : Nat := 1105531037859344556523475

theorem tailTrace_2153014 : CollatzResearch.WordTrace tailWord_2153014 prefixEnd_2153014 1105531037859344556523475 := by
  unfold tailWord_2153014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4907929488875341147611131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52351247881336972241185397 4907929488875341147611131)
  ·
    refine ⟨7361894233313011721416697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4907929488875341147611131 7361894233313011721416697)
    ·
      refine ⟨5521420674984758791062523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7361894233313011721416697 5521420674984758791062523)
      ·
        refine ⟨8282131012477138186593785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5521420674984758791062523 8282131012477138186593785)
        ·
          refine ⟨6211598259357853639945339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8282131012477138186593785 6211598259357853639945339)
          ·
            refine ⟨9317397389036780459918009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6211598259357853639945339 9317397389036780459918009)
            ·
              refine ⟨6988048041777585344938507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9317397389036780459918009 6988048041777585344938507)
              ·
                refine ⟨10482072062666378017407761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6988048041777585344938507 10482072062666378017407761)
                ·
                  refine ⟨7861554046999783513055821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10482072062666378017407761 7861554046999783513055821)
                  ·
                    refine ⟨2948082767624918817395933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7861554046999783513055821 2948082767624918817395933)
                    ·
                      refine ⟨1105531037859344556523475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2948082767624918817395933 1105531037859344556523475)
                      ·
                        rfl

theorem cell23_2153014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2153014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153014 prefixEnd_2153014 := by exact prefixLift 2153014
  have htrace : WordTrace (prefixWord ++ tailWord_2153014) baseStart_2153014 baseEnd_2153014 := by
    simpa [prefixWord, tailWord_2153014, baseEnd_2153014] using wordTrace_append hprefix tailTrace_2153014
  have hstable : (prefixWord ++ tailWord_2153014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153014).length < 2 ^ (prefixWord ++ tailWord_2153014).sum := by decide
  have hdescent : baseEnd_2153014 < baseStart_2153014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153057 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_2153057 : Nat := 118140960795 + 2153057 * 2 ^ 59
def prefixEnd_2153057 : Nat := 4983230072969 + 3 ^ 40 * 2153057 * 2
def baseEnd_2153057 : Nat := 1105553117527487888285777

theorem tailTrace_2153057 : CollatzResearch.WordTrace tailWord_2153057 prefixEnd_2153057 1105553117527487888285777 := by
  unfold tailWord_2153057
  simp only [CollatzResearch.WordTrace]
  refine ⟨78528440160849676705593425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52352293440566451137062283 78528440160849676705593425)
  ·
    refine ⟨58896330120637257529195069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78528440160849676705593425 58896330120637257529195069)
    ·
      refine ⟨22086123795238971573448151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58896330120637257529195069 22086123795238971573448151)
      ·
        refine ⟨33129185692858457360172227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22086123795238971573448151 33129185692858457360172227)
        ·
          refine ⟨49693778539287686040258341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33129185692858457360172227 49693778539287686040258341)
          ·
            refine ⟨9317583476116441132548439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49693778539287686040258341 9317583476116441132548439)
            ·
              refine ⟨13976375214174661698822659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9317583476116441132548439 13976375214174661698822659)
              ·
                refine ⟨20964562821261992548233989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13976375214174661698822659 20964562821261992548233989)
                ·
                  refine ⟨3930855528986623602793873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20964562821261992548233989 3930855528986623602793873)
                  ·
                    refine ⟨2948141646739967702095405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3930855528986623602793873 2948141646739967702095405)
                    ·
                      refine ⟨1105553117527487888285777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2948141646739967702095405 1105553117527487888285777)
                      ·
                        rfl

theorem cell23_2153057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_2153057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153057 prefixEnd_2153057 := by exact prefixLift 2153057
  have htrace : WordTrace (prefixWord ++ tailWord_2153057) baseStart_2153057 baseEnd_2153057 := by
    simpa [prefixWord, tailWord_2153057, baseEnd_2153057] using wordTrace_append hprefix tailTrace_2153057
  have hstable : (prefixWord ++ tailWord_2153057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153057).length < 2 ^ (prefixWord ++ tailWord_2153057).sum := by decide
  have hdescent : baseEnd_2153057 < baseStart_2153057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153060 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 8]
def baseStart_2153060 : Nat := 118140960795 + 2153060 * 2 ^ 59
def prefixEnd_2153060 : Nat := 4983230072969 + 3 ^ 40 * 2153060 * 2
def baseEnd_2153060 : Nat := 122839406441050152949807

theorem tailTrace_2153060 : CollatzResearch.WordTrace tailWord_2153060 prefixEnd_2153060 122839406441050152949807 := by
  unfold tailWord_2153060
  simp only [CollatzResearch.WordTrace]
  refine ⟨39264274789919404108976317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52352366386559205478635089 39264274789919404108976317)
  ·
    refine ⟨14724103046219776540866119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39264274789919404108976317 14724103046219776540866119)
    ·
      refine ⟨22086154569329664811299179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14724103046219776540866119 22086154569329664811299179)
      ·
        refine ⟨33129231853994497216948769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22086154569329664811299179 33129231853994497216948769)
        ·
          refine ⟨24846923890495872912711577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33129231853994497216948769 24846923890495872912711577)
          ·
            refine ⟨18635192917871904684533683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24846923890495872912711577 18635192917871904684533683)
            ·
              refine ⟨27952789376807857026800525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18635192917871904684533683 27952789376807857026800525)
              ·
                refine ⟨10482296016302946385050197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27952789376807857026800525 10482296016302946385050197)
                ·
                  refine ⟨122839406441050152949807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10482296016302946385050197 122839406441050152949807)
                  ·
                    rfl

theorem cell23_2153060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_2153060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153060 prefixEnd_2153060 := by exact prefixLift 2153060
  have htrace : WordTrace (prefixWord ++ tailWord_2153060) baseStart_2153060 baseEnd_2153060 := by
    simpa [prefixWord, tailWord_2153060, baseEnd_2153060] using wordTrace_append hprefix tailTrace_2153060
  have hstable : (prefixWord ++ tailWord_2153060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153060).length < 2 ^ (prefixWord ++ tailWord_2153060).sum := by decide
  have hdescent : baseEnd_2153060 < baseStart_2153060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153100 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_2153100 : Nat := 118140960795 + 2153100 * 2 ^ 59
def prefixEnd_2153100 : Nat := 4983230072969 + 3 ^ 40 * 2153100 * 2
def baseEnd_2153100 : Nat := 1105575197195631220048079

theorem tailTrace_2153100 : CollatzResearch.WordTrace tailWord_2153100 prefixEnd_2153100 1105575197195631220048079 := by
  unfold tailWord_2153100
  simp only [CollatzResearch.WordTrace]
  refine ⟨39265004249846947524704377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52353338999795930032939169 39265004249846947524704377)
  ·
    refine ⟨29448753187385210643528283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39265004249846947524704377 29448753187385210643528283)
    ·
      refine ⟨44173129781077815965292425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29448753187385210643528283 44173129781077815965292425)
      ·
        refine ⟨33129847335808361973969319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44173129781077815965292425 33129847335808361973969319)
        ·
          refine ⟨49694771003712542960953979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33129847335808361973969319 49694771003712542960953979)
          ·
            refine ⟨74542156505568814441430969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49694771003712542960953979 74542156505568814441430969)
            ·
              refine ⟨55906617379176610831073227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74542156505568814441430969 55906617379176610831073227)
              ·
                refine ⟨83859926068764916246609841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55906617379176610831073227 83859926068764916246609841)
                ·
                  refine ⟨62894944551573687184957381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83859926068764916246609841 62894944551573687184957381)
                  ·
                    refine ⟨11792802103420066347179509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62894944551573687184957381 11792802103420066347179509)
                    ·
                      refine ⟨1105575197195631220048079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11792802103420066347179509 1105575197195631220048079)
                      ·
                        rfl

theorem cell23_2153100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_2153100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153100 prefixEnd_2153100 := by exact prefixLift 2153100
  have htrace : WordTrace (prefixWord ++ tailWord_2153100) baseStart_2153100 baseEnd_2153100 := by
    simpa [prefixWord, tailWord_2153100, baseEnd_2153100] using wordTrace_append hprefix tailTrace_2153100
  have hstable : (prefixWord ++ tailWord_2153100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153100).length < 2 ^ (prefixWord ++ tailWord_2153100).sum := by decide
  have hdescent : baseEnd_2153100 < baseStart_2153100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153178 : List Nat := [3, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2]
def baseStart_2153178 : Nat := 118140960795 + 2153178 * 2 ^ 59
def prefixEnd_2153178 : Nat := 4983230072969 + 3 ^ 40 * 2153178 * 2
def baseEnd_2153178 : Nat := 1105615248686681914872721

theorem tailTrace_2153178 : CollatzResearch.WordTrace tailWord_2153178 prefixEnd_2153178 1105615248686681914872721 := by
  unfold tailWord_2153178
  simp only [CollatzResearch.WordTrace]
  refine ⟨19633213348352828592687047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52355235595607542913832125 19633213348352828592687047)
  ·
    refine ⟨29449820022529242889030571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19633213348352828592687047 29449820022529242889030571)
    ·
      refine ⟨44174730033793864333545857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29449820022529242889030571 44174730033793864333545857)
      ·
        refine ⟨33131047525345398250159393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44174730033793864333545857 33131047525345398250159393)
        ·
          refine ⟨24848285644009048687619545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33131047525345398250159393 24848285644009048687619545)
          ·
            refine ⟨18636214233006786515714659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24848285644009048687619545 18636214233006786515714659)
            ·
              refine ⟨27954321349510179773571989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18636214233006786515714659 27954321349510179773571989)
              ·
                refine ⟨1310358813258289676886187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27954321349510179773571989 1310358813258289676886187)
                ·
                  refine ⟨1965538219887434515329281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310358813258289676886187 1965538219887434515329281)
                  ·
                    refine ⟨1474153664915575886496961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1965538219887434515329281 1474153664915575886496961)
                    ·
                      refine ⟨1105615248686681914872721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1474153664915575886496961 1105615248686681914872721)
                      ·
                        rfl

theorem cell23_2153178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_2153178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153178 prefixEnd_2153178 := by exact prefixLift 2153178
  have htrace : WordTrace (prefixWord ++ tailWord_2153178) baseStart_2153178 baseEnd_2153178 := by
    simpa [prefixWord, tailWord_2153178, baseEnd_2153178] using wordTrace_append hprefix tailTrace_2153178
  have hstable : (prefixWord ++ tailWord_2153178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153178).length < 2 ^ (prefixWord ++ tailWord_2153178).sum := by decide
  have hdescent : baseEnd_2153178 < baseStart_2153178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153217 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2153217 : Nat := 118140960795 + 2153217 * 2 ^ 59
def prefixEnd_2153217 : Nat := 4983230072969 + 3 ^ 40 * 2153217 * 2
def baseEnd_2153217 : Nat := 1105635274432207262285041

theorem tailTrace_2153217 : CollatzResearch.WordTrace tailWord_2153217 prefixEnd_2153217 1105635274432207262285041 := by
  unfold tailWord_2153217
  simp only [CollatzResearch.WordTrace]
  refine ⟨78534275840270024031417905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52356183893513349354278603 78534275840270024031417905)
  ·
    refine ⟨58900706880202518023563429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78534275840270024031417905 58900706880202518023563429)
    ·
      refine ⟨11043882540037972129418143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58900706880202518023563429 11043882540037972129418143)
      ·
        refine ⟨16565823810056958194127215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11043882540037972129418143 16565823810056958194127215)
        ·
          refine ⟨24848735715085437291190823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16565823810056958194127215 24848735715085437291190823)
          ·
            refine ⟨37273103572628155936786235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24848735715085437291190823 37273103572628155936786235)
            ·
              refine ⟨55909655358942233905179353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37273103572628155936786235 55909655358942233905179353)
              ·
                refine ⟨41932241519206675428884515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55909655358942233905179353 41932241519206675428884515)
                ·
                  refine ⟨62898362278810013143326773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41932241519206675428884515 62898362278810013143326773)
                  ·
                    refine ⟨5896721463638438732186885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62898362278810013143326773 5896721463638438732186885)
                    ·
                      refine ⟨1105635274432207262285041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5896721463638438732186885 1105635274432207262285041)
                      ·
                        rfl

theorem cell23_2153217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2153217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153217 prefixEnd_2153217 := by exact prefixLift 2153217
  have htrace : WordTrace (prefixWord ++ tailWord_2153217) baseStart_2153217 baseEnd_2153217 := by
    simpa [prefixWord, tailWord_2153217, baseEnd_2153217] using wordTrace_append hprefix tailTrace_2153217
  have hstable : (prefixWord ++ tailWord_2153217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153217).length < 2 ^ (prefixWord ++ tailWord_2153217).sum := by decide
  have hdescent : baseEnd_2153217 < baseStart_2153217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153237 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_2153237 : Nat := 118140960795 + 2153237 * 2 ^ 59
def prefixEnd_2153237 : Nat := 4983230072969 + 3 ^ 40 * 2153237 * 2
def baseEnd_2153237 : Nat := 1105645544045297184034949

theorem tailTrace_2153237 : CollatzResearch.WordTrace tailWord_2153237 prefixEnd_2153237 1105645544045297184034949 := by
  unfold tailWord_2153237
  simp only [CollatzResearch.WordTrace]
  refine ⟨78535005300197567447145965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52356670200131711631430643 78535005300197567447145965)
  ·
    refine ⟨29450626987574087792679737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78535005300197567447145965 29450626987574087792679737)
    ·
      refine ⟨22087970240680565844509803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29450626987574087792679737 22087970240680565844509803)
      ·
        refine ⟨33131955361020848766764705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22087970240680565844509803 33131955361020848766764705)
        ·
          refine ⟨24848966520765636575073529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33131955361020848766764705 24848966520765636575073529)
          ·
            refine ⟨18636724890574227431305147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24848966520765636575073529 18636724890574227431305147)
            ·
              refine ⟨27955087335861341146957721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18636724890574227431305147 27955087335861341146957721)
              ·
                refine ⟨20966315501896005860218291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27955087335861341146957721 20966315501896005860218291)
                ·
                  refine ⟨31449473252844008790327437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20966315501896005860218291 31449473252844008790327437)
                  ·
                    refine ⟨11793552469816503296372789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31449473252844008790327437 11793552469816503296372789)
                    ·
                      refine ⟨1105645544045297184034949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11793552469816503296372789 1105645544045297184034949)
                      ·
                        rfl

theorem cell23_2153237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_2153237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153237 prefixEnd_2153237 := by exact prefixLift 2153237
  have htrace : WordTrace (prefixWord ++ tailWord_2153237) baseStart_2153237 baseEnd_2153237 := by
    simpa [prefixWord, tailWord_2153237, baseEnd_2153237] using wordTrace_append hprefix tailTrace_2153237
  have hstable : (prefixWord ++ tailWord_2153237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153237).length < 2 ^ (prefixWord ++ tailWord_2153237).sum := by decide
  have hdescent : baseEnd_2153237 < baseStart_2153237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153245 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_2153245 : Nat := 118140960795 + 2153245 * 2 ^ 59
def prefixEnd_2153245 : Nat := 4983230072969 + 3 ^ 40 * 2153245 * 2
def baseEnd_2153245 : Nat := 1105649651890533152734913

theorem tailTrace_2153245 : CollatzResearch.WordTrace tailWord_2153245 prefixEnd_2153245 1105649651890533152734913 := by
  unfold tailWord_2153245
  simp only [CollatzResearch.WordTrace]
  refine ⟨78535297084168584813437189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52356864722779056542291459 78535297084168584813437189)
  ·
    refine ⟨14725368203281609652519473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78535297084168584813437189 14725368203281609652519473)
    ·
      refine ⟨11044026152461207239389605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14725368203281609652519473 11044026152461207239389605)
      ·
        refine ⟨2070754903586476357385551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11044026152461207239389605 2070754903586476357385551)
        ·
          refine ⟨3106132355379714536078327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070754903586476357385551 3106132355379714536078327)
          ·
            refine ⟨4659198533069571804117491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3106132355379714536078327 4659198533069571804117491)
            ·
              refine ⟨6988797799604357706176237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4659198533069571804117491 6988797799604357706176237)
              ·
                refine ⟨2620799174851634139816089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6988797799604357706176237 2620799174851634139816089)
                ·
                  refine ⟨1965599381138725604862067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2620799174851634139816089 1965599381138725604862067)
                  ·
                    refine ⟨2948399071708088407293101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1965599381138725604862067 2948399071708088407293101)
                    ·
                      refine ⟨1105649651890533152734913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2948399071708088407293101 1105649651890533152734913)
                      ·
                        rfl

theorem cell23_2153245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_2153245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153245 prefixEnd_2153245 := by exact prefixLift 2153245
  have htrace : WordTrace (prefixWord ++ tailWord_2153245) baseStart_2153245 baseEnd_2153245 := by
    simpa [prefixWord, tailWord_2153245, baseEnd_2153245] using wordTrace_append hprefix tailTrace_2153245
  have hstable : (prefixWord ++ tailWord_2153245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153245).length < 2 ^ (prefixWord ++ tailWord_2153245).sum := by decide
  have hdescent : baseEnd_2153245 < baseStart_2153245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153287 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 3, 7]
def baseStart_2153287 : Nat := 118140960795 + 2153287 * 2 ^ 59
def prefixEnd_2153287 : Nat := 4983230072969 + 3 ^ 40 * 2153287 * 2
def baseEnd_2153287 : Nat := 368557072692673996136573

theorem tailTrace_2153287 : CollatzResearch.WordTrace tailWord_2153287 prefixEnd_2153287 368557072692673996136573 := by
  unfold tailWord_2153287
  simp only [CollatzResearch.WordTrace]
  refine ⟨78536828950016425986466115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52357885966677617324310743 78536828950016425986466115)
  ·
    refine ⟨117805243425024638979699173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78536828950016425986466115 117805243425024638979699173)
    ·
      refine ⟨22088483142192119808693595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117805243425024638979699173 22088483142192119808693595)
      ·
        refine ⟨33132724713288179713040393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22088483142192119808693595 33132724713288179713040393)
        ·
          refine ⟨24849543534966134784780295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33132724713288179713040393 24849543534966134784780295)
          ·
            refine ⟨37274315302449202177170443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24849543534966134784780295 37274315302449202177170443)
            ·
              refine ⟨55911472953673803265755665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37274315302449202177170443 55911472953673803265755665)
              ·
                refine ⟨41933604715255352449316749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55911472953673803265755665 41933604715255352449316749)
                ·
                  refine ⟨15725101768220757168493781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41933604715255352449316749 15725101768220757168493781)
                  ·
                    refine ⟨368557072692673996136573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15725101768220757168493781 368557072692673996136573)
                    ·
                      rfl

theorem cell23_2153287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_2153287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153287 prefixEnd_2153287 := by exact prefixLift 2153287
  have htrace : WordTrace (prefixWord ++ tailWord_2153287) baseStart_2153287 baseEnd_2153287 := by
    simpa [prefixWord, tailWord_2153287, baseEnd_2153287] using wordTrace_append hprefix tailTrace_2153287
  have hstable : (prefixWord ++ tailWord_2153287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153287).length < 2 ^ (prefixWord ++ tailWord_2153287).sum := by decide
  have hdescent : baseEnd_2153287 < baseStart_2153287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153307 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 4]
def baseStart_2153307 : Nat := 118140960795 + 2153307 * 2 ^ 59
def prefixEnd_2153307 : Nat := 4983230072969 + 3 ^ 40 * 2153307 * 2
def baseEnd_2153307 : Nat := 1105681487691111910159627

theorem tailTrace_2153307 : CollatzResearch.WordTrace tailWord_2153307 prefixEnd_2153307 1105681487691111910159627 := by
  unfold tailWord_2153307
  simp only [CollatzResearch.WordTrace]
  refine ⟨78537558409943969402194175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52358372273295979601462783 78537558409943969402194175)
  ·
    refine ⟨117806337614915954103291263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78537558409943969402194175 117806337614915954103291263)
    ·
      refine ⟨176709506422373931154936895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117806337614915954103291263 176709506422373931154936895)
      ·
        refine ⟨265064259633560896732405343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176709506422373931154936895 265064259633560896732405343)
        ·
          refine ⟨397596389450341345098608015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265064259633560896732405343 397596389450341345098608015)
          ·
            refine ⟨596394584175512017647912023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397596389450341345098608015 596394584175512017647912023)
            ·
              refine ⟨894591876263268026471868035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596394584175512017647912023 894591876263268026471868035)
              ·
                refine ⟨1341887814394902039707802053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894591876263268026471868035 1341887814394902039707802053)
                ·
                  refine ⟨251603965199044132445212885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1341887814394902039707802053 251603965199044132445212885)
                  ·
                    refine ⟨5896967934352596854184677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 251603965199044132445212885 5896967934352596854184677)
                    ·
                      refine ⟨1105681487691111910159627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5896967934352596854184677 1105681487691111910159627)
                      ·
                        rfl

theorem cell23_2153307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 4].length) (baseStart_2153307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153307 prefixEnd_2153307 := by exact prefixLift 2153307
  have htrace : WordTrace (prefixWord ++ tailWord_2153307) baseStart_2153307 baseEnd_2153307 := by
    simpa [prefixWord, tailWord_2153307, baseEnd_2153307] using wordTrace_append hprefix tailTrace_2153307
  have hstable : (prefixWord ++ tailWord_2153307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153307).length < 2 ^ (prefixWord ++ tailWord_2153307).sum := by decide
  have hdescent : baseEnd_2153307 < baseStart_2153307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153324 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_2153324 : Nat := 118140960795 + 2153324 * 2 ^ 59
def prefixEnd_2153324 : Nat := 4983230072969 + 3 ^ 40 * 2153324 * 2
def baseEnd_2153324 : Nat := 1105690216862238343647049

theorem tailTrace_2153324 : CollatzResearch.WordTrace tailWord_2153324 prefixEnd_2153324 1105690216862238343647049 := by
  unfold tailWord_2153324
  simp only [CollatzResearch.WordTrace]
  refine ⟨39269089225441190652781513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52358785633921587537042017 39269089225441190652781513)
  ·
    refine ⟨29451816919080892989586135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39269089225441190652781513 29451816919080892989586135)
    ·
      refine ⟨44177725378621339484379203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29451816919080892989586135 44177725378621339484379203)
      ·
        refine ⟨66266588067932009226568805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44177725378621339484379203 66266588067932009226568805)
        ·
          refine ⟨12424985262737251729981651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66266588067932009226568805 12424985262737251729981651)
          ·
            refine ⟨18637477894105877594972477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12424985262737251729981651 18637477894105877594972477)
            ·
              refine ⟨6989054210289704098114679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18637477894105877594972477 6989054210289704098114679)
              ·
                refine ⟨10483581315434556147172019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6989054210289704098114679 10483581315434556147172019)
                ·
                  refine ⟨15725371973151834220758029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10483581315434556147172019 15725371973151834220758029)
                  ·
                    refine ⟨5897014489931937832784261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15725371973151834220758029 5897014489931937832784261)
                    ·
                      refine ⟨1105690216862238343647049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5897014489931937832784261 1105690216862238343647049)
                      ·
                        rfl

theorem cell23_2153324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_2153324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153324 prefixEnd_2153324 := by exact prefixLift 2153324
  have htrace : WordTrace (prefixWord ++ tailWord_2153324) baseStart_2153324 baseEnd_2153324 := by
    simpa [prefixWord, tailWord_2153324, baseEnd_2153324] using wordTrace_append hprefix tailTrace_2153324
  have hstable : (prefixWord ++ tailWord_2153324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153324).length < 2 ^ (prefixWord ++ tailWord_2153324).sum := by decide
  have hdescent : baseEnd_2153324 < baseStart_2153324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153341 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 2, 4, 2]
def baseStart_2153341 : Nat := 118140960795 + 2153341 * 2 ^ 59
def prefixEnd_2153341 : Nat := 4983230072969 + 3 ^ 40 * 2153341 * 2
def baseEnd_2153341 : Nat := 1105698946033364777134471

theorem tailTrace_2153341 : CollatzResearch.WordTrace tailWord_2153341 prefixEnd_2153341 1105698946033364777134471 := by
  unfold tailWord_2153341
  simp only [CollatzResearch.WordTrace]
  refine ⟨78538798491820793208931877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52359198994547195472621251 78538798491820793208931877)
  ·
    refine ⟨14726024717216398726674727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78538798491820793208931877 14726024717216398726674727)
    ·
      refine ⟨22089037075824598090012091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14726024717216398726674727 22089037075824598090012091)
      ·
        refine ⟨33133555613736897135018137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22089037075824598090012091 33133555613736897135018137)
        ·
          refine ⟨24850166710302672851263603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33133555613736897135018137 24850166710302672851263603)
          ·
            refine ⟨37275250065454009276895405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24850166710302672851263603 37275250065454009276895405)
            ·
              refine ⟨13978218774545253478835777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37275250065454009276895405 13978218774545253478835777)
              ·
                refine ⟨10483664080908940109126833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13978218774545253478835777 10483664080908940109126833)
                ·
                  refine ⟨7862748060681705081845125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10483664080908940109126833 7862748060681705081845125)
                  ·
                    refine ⟨1474265261377819702845961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7862748060681705081845125 1474265261377819702845961)
                    ·
                      refine ⟨1105698946033364777134471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1474265261377819702845961 1105698946033364777134471)
                      ·
                        rfl

theorem cell23_2153341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_2153341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153341 prefixEnd_2153341 := by exact prefixLift 2153341
  have htrace : WordTrace (prefixWord ++ tailWord_2153341) baseStart_2153341 baseEnd_2153341 := by
    simpa [prefixWord, tailWord_2153341, baseEnd_2153341] using wordTrace_append hprefix tailTrace_2153341
  have hstable : (prefixWord ++ tailWord_2153341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153341).length < 2 ^ (prefixWord ++ tailWord_2153341).sum := by decide
  have hdescent : baseEnd_2153341 < baseStart_2153341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153351 : List Nat := [1, 1, 4, 2, 3, 1, 1, 3, 3, 4]
def baseStart_2153351 : Nat := 118140960795 + 2153351 * 2 ^ 59
def prefixEnd_2153351 : Nat := 4983230072969 + 3 ^ 40 * 2153351 * 2
def baseEnd_2153351 : Nat := 368568026946636579336475

theorem tailTrace_2153351 : CollatzResearch.WordTrace tailWord_2153351 prefixEnd_2153351 368568026946636579336475 := by
  unfold tailWord_2153351
  simp only [CollatzResearch.WordTrace]
  refine ⟨78539163221784564916795907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52359442147856376611197271 78539163221784564916795907)
  ·
    refine ⟨117808744832676847375193861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78539163221784564916795907 117808744832676847375193861)
    ·
      refine ⟨22089139656126908882848849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117808744832676847375193861 22089139656126908882848849)
      ·
        refine ⟨16566854742095181662136637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22089139656126908882848849 16566854742095181662136637)
        ·
          refine ⟨6212570528285693123301239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16566854742095181662136637 6212570528285693123301239)
          ·
            refine ⟨9318855792428539684951859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6212570528285693123301239 9318855792428539684951859)
            ·
              refine ⟨13978283688642809527427789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9318855792428539684951859 13978283688642809527427789)
              ·
                refine ⟨5241856383241053572785421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13978283688642809527427789 5241856383241053572785421)
                ·
                  refine ⟨1965696143715395089794533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5241856383241053572785421 1965696143715395089794533)
                  ·
                    refine ⟨368568026946636579336475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1965696143715395089794533 368568026946636579336475)
                    ·
                      rfl

theorem cell23_2153351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_2153351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153351 prefixEnd_2153351 := by exact prefixLift 2153351
  have htrace : WordTrace (prefixWord ++ tailWord_2153351) baseStart_2153351 baseEnd_2153351 := by
    simpa [prefixWord, tailWord_2153351, baseEnd_2153351] using wordTrace_append hprefix tailTrace_2153351
  have hstable : (prefixWord ++ tailWord_2153351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153351).length < 2 ^ (prefixWord ++ tailWord_2153351).sum := by decide
  have hdescent : baseEnd_2153351 < baseStart_2153351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153394 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_2153394 : Nat := 118140960795 + 2153394 * 2 ^ 59
def prefixEnd_2153394 : Nat := 4983230072969 + 3 ^ 40 * 2153394 * 2
def baseEnd_2153394 : Nat := 368575386836017689923909

theorem tailTrace_2153394 : CollatzResearch.WordTrace tailWord_2153394 prefixEnd_2153394 368575386836017689923909 := by
  unfold tailWord_2153394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19635182890157195815152809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52360487707085855507074157 19635182890157195815152809)
  ·
    refine ⟨14726387167617896861364607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19635182890157195815152809 14726387167617896861364607)
    ·
      refine ⟨22089580751426845292046911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14726387167617896861364607 22089580751426845292046911)
      ·
        refine ⟨33134371127140267938070367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22089580751426845292046911 33134371127140267938070367)
        ·
          refine ⟨49701556690710401907105551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33134371127140267938070367 49701556690710401907105551)
          ·
            refine ⟨74552335036065602860658327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49701556690710401907105551 74552335036065602860658327)
            ·
              refine ⟨111828502554098404290987491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74552335036065602860658327 111828502554098404290987491)
              ·
                refine ⟨167742753831147606436481237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111828502554098404290987491 167742753831147606436481237)
                ·
                  refine ⟨3931470792917522025855029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 167742753831147606436481237 3931470792917522025855029)
                  ·
                    refine ⟨368575386836017689923909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3931470792917522025855029 368575386836017689923909)
                    ·
                      rfl

theorem cell23_2153394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_2153394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153394 prefixEnd_2153394 := by exact prefixLift 2153394
  have htrace : WordTrace (prefixWord ++ tailWord_2153394) baseStart_2153394 baseEnd_2153394 := by
    simpa [prefixWord, tailWord_2153394, baseEnd_2153394] using wordTrace_append hprefix tailTrace_2153394
  have hstable : (prefixWord ++ tailWord_2153394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153394).length < 2 ^ (prefixWord ++ tailWord_2153394).sum := by decide
  have hdescent : baseEnd_2153394 < baseStart_2153394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153408 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 3, 1, 3]
def baseStart_2153408 : Nat := 118140960795 + 2153408 * 2 ^ 59
def prefixEnd_2153408 : Nat := 4983230072969 + 3 ^ 40 * 2153408 * 2
def baseEnd_2153408 : Nat := 1105733349237216014996663

theorem tailTrace_2153408 : CollatzResearch.WordTrace tailWord_2153408 prefixEnd_2153408 1105733349237216014996663 := by
  unfold tailWord_2153408
  simp only [CollatzResearch.WordTrace]
  refine ⟨39270621091289031825810439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52360828121718709101080585 39270621091289031825810439)
  ·
    refine ⟨58905931636933547738715659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39270621091289031825810439 58905931636933547738715659)
    ·
      refine ⟨88358897455400321608073489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58905931636933547738715659 88358897455400321608073489)
      ·
        refine ⟨66269173091550241206055117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88358897455400321608073489 66269173091550241206055117)
        ·
          refine ⟨24850939909331340452270669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66269173091550241206055117 24850939909331340452270669)
          ·
            refine ⟨9319102465999252669601501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24850939909331340452270669 9319102465999252669601501)
            ·
              refine ⟨3494663424749719751100563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9319102465999252669601501 3494663424749719751100563)
              ·
                refine ⟨5241995137124579626650845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3494663424749719751100563 5241995137124579626650845)
                ·
                  refine ⟨1965748176421717359994067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5241995137124579626650845 1965748176421717359994067)
                  ·
                    refine ⟨2948622264632576039991101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1965748176421717359994067 2948622264632576039991101)
                    ·
                      refine ⟨1105733349237216014996663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2948622264632576039991101 1105733349237216014996663)
                      ·
                        rfl

theorem cell23_2153408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_2153408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153408 prefixEnd_2153408 := by exact prefixLift 2153408
  have htrace : WordTrace (prefixWord ++ tailWord_2153408) baseStart_2153408 baseEnd_2153408 := by
    simpa [prefixWord, tailWord_2153408, baseEnd_2153408] using wordTrace_append hprefix tailTrace_2153408
  have hstable : (prefixWord ++ tailWord_2153408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153408).length < 2 ^ (prefixWord ++ tailWord_2153408).sum := by decide
  have hdescent : baseEnd_2153408 < baseStart_2153408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153424 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 1, 6]
def baseStart_2153424 : Nat := 118140960795 + 2153424 * 2 ^ 59
def prefixEnd_2153424 : Nat := 4983230072969 + 3 ^ 40 * 2153424 * 2
def baseEnd_2153424 : Nat := 368580521642562650798863

theorem tailTrace_2153424 : CollatzResearch.WordTrace tailWord_2153424 prefixEnd_2153424 368580521642562650798863 := by
  unfold tailWord_2153424
  simp only [CollatzResearch.WordTrace]
  refine ⟨39270912875260049192101663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52361217167013398922802217 39270912875260049192101663)
  ·
    refine ⟨58906369312890073788152495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39270912875260049192101663 58906369312890073788152495)
    ·
      refine ⟨88359553969335110682228743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58906369312890073788152495 88359553969335110682228743)
      ·
        refine ⟨132539330954002666023343115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88359553969335110682228743 132539330954002666023343115)
        ·
          refine ⟨198808996431003999035014673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132539330954002666023343115 198808996431003999035014673)
          ·
            refine ⟨149106747323252999276261005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198808996431003999035014673 149106747323252999276261005)
            ·
              refine ⟨55915030246219874728597877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149106747323252999276261005 55915030246219874728597877)
              ·
                refine ⟨5242034085583113255806051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55915030246219874728597877 5242034085583113255806051)
                ·
                  refine ⟨7863051128374669883709077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5242034085583113255806051 7863051128374669883709077)
                  ·
                    refine ⟨368580521642562650798863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7863051128374669883709077 368580521642562650798863)
                    ·
                      rfl

theorem cell23_2153424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_2153424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153424 prefixEnd_2153424 := by exact prefixLift 2153424
  have htrace : WordTrace (prefixWord ++ tailWord_2153424) baseStart_2153424 baseEnd_2153424 := by
    simpa [prefixWord, tailWord_2153424, baseEnd_2153424] using wordTrace_append hprefix tailTrace_2153424
  have hstable : (prefixWord ++ tailWord_2153424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153424).length < 2 ^ (prefixWord ++ tailWord_2153424).sum := by decide
  have hdescent : baseEnd_2153424 < baseStart_2153424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153428 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_2153428 : Nat := 118140960795 + 2153428 * 2 ^ 59
def prefixEnd_2153428 : Nat := 4983230072969 + 3 ^ 40 * 2153428 * 2
def baseEnd_2153428 : Nat := 368581206283435312248857

theorem tailTrace_2153428 : CollatzResearch.WordTrace tailWord_2153428 prefixEnd_2153428 368581206283435312248857 := by
  unfold tailWord_2153428
  simp only [CollatzResearch.WordTrace]
  refine ⟨39270985821252803533674469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52361314428337071378232625 39270985821252803533674469)
  ·
    refine ⟨7363309841484900662563963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39270985821252803533674469 7363309841484900662563963)
    ·
      refine ⟨11044964762227350993845945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7363309841484900662563963 11044964762227350993845945)
      ·
        refine ⟨8283723571670513245384459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11044964762227350993845945 8283723571670513245384459)
        ·
          refine ⟨12425585357505769868076689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8283723571670513245384459 12425585357505769868076689)
          ·
            refine ⟨9319189018129327401057517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12425585357505769868076689 9319189018129327401057517)
            ·
              refine ⟨3494695881798497775396569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9319189018129327401057517 3494695881798497775396569)
              ·
                refine ⟨2621021911348873331547427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3494695881798497775396569 2621021911348873331547427)
                ·
                  refine ⟨3931532867023309997321141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621021911348873331547427 3931532867023309997321141)
                  ·
                    refine ⟨368581206283435312248857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3931532867023309997321141 368581206283435312248857)
                    ·
                      rfl

theorem cell23_2153428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_2153428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153428 prefixEnd_2153428 := by exact prefixLift 2153428
  have htrace : WordTrace (prefixWord ++ tailWord_2153428) baseStart_2153428 baseEnd_2153428 := by
    simpa [prefixWord, tailWord_2153428, baseEnd_2153428] using wordTrace_append hprefix tailTrace_2153428
  have hstable : (prefixWord ++ tailWord_2153428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153428).length < 2 ^ (prefixWord ++ tailWord_2153428).sum := by decide
  have hdescent : baseEnd_2153428 < baseStart_2153428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153431 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 4]
def baseStart_2153431 : Nat := 118140960795 + 2153431 * 2 ^ 59
def prefixEnd_2153431 : Nat := 4983230072969 + 3 ^ 40 * 2153431 * 2
def baseEnd_2153431 : Nat := 1105745159292269425009057

theorem tailTrace_2153431 : CollatzResearch.WordTrace tailWord_2153431 prefixEnd_2153431 1105745159292269425009057 := by
  unfold tailWord_2153431
  simp only [CollatzResearch.WordTrace]
  refine ⟨78542081061494738579708147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52361387374329825719805431 78542081061494738579708147)
  ·
    refine ⟨117813121592242107869562221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78542081061494738579708147 117813121592242107869562221)
    ·
      refine ⟨44179920597090790451085833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117813121592242107869562221 44179920597090790451085833)
      ·
        refine ⟨33134940447818092838314375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44179920597090790451085833 33134940447818092838314375)
        ·
          refine ⟨49702410671727139257471563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33134940447818092838314375 49702410671727139257471563)
          ·
            refine ⟨74553616007590708886207345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49702410671727139257471563 74553616007590708886207345)
            ·
              refine ⟨55915212005693031664655509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74553616007590708886207345 55915212005693031664655509)
              ·
                refine ⟨2621025562766860859280727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55915212005693031664655509 2621025562766860859280727)
                ·
                  refine ⟨3931538344150291288921091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621025562766860859280727 3931538344150291288921091)
                  ·
                    refine ⟨5897307516225436933381637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3931538344150291288921091 5897307516225436933381637)
                    ·
                      refine ⟨1105745159292269425009057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5897307516225436933381637 1105745159292269425009057)
                      ·
                        rfl

theorem cell23_2153431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_2153431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153431 prefixEnd_2153431 := by exact prefixLift 2153431
  have htrace : WordTrace (prefixWord ++ tailWord_2153431) baseStart_2153431 baseEnd_2153431 := by
    simpa [prefixWord, tailWord_2153431, baseEnd_2153431] using wordTrace_append hprefix tailTrace_2153431
  have hstable : (prefixWord ++ tailWord_2153431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153431).length < 2 ^ (prefixWord ++ tailWord_2153431).sum := by decide
  have hdescent : baseEnd_2153431 < baseStart_2153431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153444 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_2153444 : Nat := 118140960795 + 2153444 * 2 ^ 59
def prefixEnd_2153444 : Nat := 4983230072969 + 3 ^ 40 * 2153444 * 2
def baseEnd_2153444 : Nat := 1105751834540777874146497

theorem tailTrace_2153444 : CollatzResearch.WordTrace tailWord_2153444 prefixEnd_2153444 1105751834540777874146497 := by
  unfold tailWord_2153444
  simp only [CollatzResearch.WordTrace]
  refine ⟨39271277605223820899965693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52361703473631761199954257 39271277605223820899965693)
  ·
    refine ⟨14726729101958932837487135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39271277605223820899965693 14726729101958932837487135)
    ·
      refine ⟨22090093652938399256230703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14726729101958932837487135 22090093652938399256230703)
      ·
        refine ⟨33135140479407598884346055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22090093652938399256230703 33135140479407598884346055)
        ·
          refine ⟨49702710719111398326519083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33135140479407598884346055 49702710719111398326519083)
          ·
            refine ⟨74554066078667097489778625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49702710719111398326519083 74554066078667097489778625)
            ·
              refine ⟨55915549559000323117333969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74554066078667097489778625 55915549559000323117333969)
              ·
                refine ⟨41936662169250242338000477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55915549559000323117333969 41936662169250242338000477)
                ·
                  refine ⟨15726248313468840876750179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41936662169250242338000477 15726248313468840876750179)
                  ·
                    refine ⟨23589372470203261315125269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15726248313468840876750179 23589372470203261315125269)
                    ·
                      refine ⟨1105751834540777874146497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23589372470203261315125269 1105751834540777874146497)
                      ·
                        rfl

theorem cell23_2153444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_2153444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153444 prefixEnd_2153444 := by exact prefixLift 2153444
  have htrace : WordTrace (prefixWord ++ tailWord_2153444) baseStart_2153444 baseEnd_2153444 := by
    simpa [prefixWord, tailWord_2153444, baseEnd_2153444] using wordTrace_append hprefix tailTrace_2153444
  have hstable : (prefixWord ++ tailWord_2153444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153444).length < 2 ^ (prefixWord ++ tailWord_2153444).sum := by decide
  have hdescent : baseEnd_2153444 < baseStart_2153444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153454 : List Nat := [4, 1, 2, 1, 15]
def baseStart_2153454 : Nat := 118140960795 + 2153454 * 2 ^ 59
def prefixEnd_2153454 : Nat := 4983230072969 + 3 ^ 40 * 2153454 * 2
def baseEnd_2153454 : Nat := 1516813401025134204419

theorem tailTrace_2153454 : CollatzResearch.WordTrace tailWord_2153454 prefixEnd_2153454 1516813401025134204419 := by
  unfold tailWord_2153454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9817864992551426688474427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52361946626940942338530277 9817864992551426688474427)
  ·
    refine ⟨14726797488827140032711641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9817864992551426688474427 14726797488827140032711641)
    ·
      refine ⟨11045098116620355024533731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14726797488827140032711641 11045098116620355024533731)
      ·
        refine ⟨16567647174930532536800597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11045098116620355024533731 16567647174930532536800597)
        ·
          refine ⟨1516813401025134204419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 16567647174930532536800597 1516813401025134204419)
          ·
            rfl

theorem cell23_2153454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 15].length) (baseStart_2153454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153454 prefixEnd_2153454 := by exact prefixLift 2153454
  have htrace : WordTrace (prefixWord ++ tailWord_2153454) baseStart_2153454 baseEnd_2153454 := by
    simpa [prefixWord, tailWord_2153454, baseEnd_2153454] using wordTrace_append hprefix tailTrace_2153454
  have hstable : (prefixWord ++ tailWord_2153454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153454).length < 2 ^ (prefixWord ++ tailWord_2153454).sum := by decide
  have hdescent : baseEnd_2153454 < baseStart_2153454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153498 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3]
def baseStart_2153498 : Nat := 118140960795 + 2153498 * 2 ^ 59
def prefixEnd_2153498 : Nat := 4983230072969 + 3 ^ 40 * 2153498 * 2
def baseEnd_2153498 : Nat := 1105779562496120662871249

theorem tailTrace_2153498 : CollatzResearch.WordTrace tailWord_2153498 prefixEnd_2153498 1105779562496120662871249 := by
  unfold tailWord_2153498
  simp only [CollatzResearch.WordTrace]
  refine ⟨19636131188063002255599287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52363016501501339348264765 19636131188063002255599287)
  ·
    refine ⟨29454196782094503383398931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19636131188063002255599287 29454196782094503383398931)
    ·
      refine ⟨44181295173141755075098397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29454196782094503383398931 44181295173141755075098397)
      ·
        refine ⟨16567985689928158153161899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44181295173141755075098397 16567985689928158153161899)
        ·
          refine ⟨24851978534892237229742849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16567985689928158153161899 24851978534892237229742849)
          ·
            refine ⟨18638983901169177922307137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24851978534892237229742849 18638983901169177922307137)
            ·
              refine ⟨13979237925876883441730353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18638983901169177922307137 13979237925876883441730353)
              ·
                refine ⟨10484428444407662581297765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13979237925876883441730353 10484428444407662581297765)
                ·
                  refine ⟨1965830333326436733993331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10484428444407662581297765 1965830333326436733993331)
                  ·
                    refine ⟨2948745499989655100989997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1965830333326436733993331 2948745499989655100989997)
                    ·
                      refine ⟨1105779562496120662871249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2948745499989655100989997 1105779562496120662871249)
                      ·
                        rfl

theorem cell23_2153498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_2153498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153498 prefixEnd_2153498 := by exact prefixLift 2153498
  have htrace : WordTrace (prefixWord ++ tailWord_2153498) baseStart_2153498 baseEnd_2153498 := by
    simpa [prefixWord, tailWord_2153498, baseEnd_2153498] using wordTrace_append hprefix tailTrace_2153498
  have hstable : (prefixWord ++ tailWord_2153498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153498).length < 2 ^ (prefixWord ++ tailWord_2153498).sum := by decide
  have hdescent : baseEnd_2153498 < baseStart_2153498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153532 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 2, 1, 3]
def baseStart_2153532 : Nat := 118140960795 + 2153532 * 2 ^ 59
def prefixEnd_2153532 : Nat := 4983230072969 + 3 ^ 40 * 2153532 * 2
def baseEnd_2153532 : Nat := 1105797020838373529846093

theorem tailTrace_2153532 : CollatzResearch.WordTrace tailWord_2153532 prefixEnd_2153532 1105797020838373529846093 := by
  unfold tailWord_2153532
  simp only [CollatzResearch.WordTrace]
  refine ⟨39272882417064416414567425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52363843222752555219423233 39272882417064416414567425)
  ·
    refine ⟨29454661812798312310925569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39272882417064416414567425 29454661812798312310925569)
    ·
      refine ⟨22090996359598734233194177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29454661812798312310925569 22090996359598734233194177)
      ·
        refine ⟨16568247269699050674895633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22090996359598734233194177 16568247269699050674895633)
        ·
          refine ⟨12426185452274288006171725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16568247269699050674895633 12426185452274288006171725)
          ·
            refine ⟨4659819544602858002314397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12426185452274288006171725 4659819544602858002314397)
            ·
              refine ⟨1747432329226071750867899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4659819544602858002314397 1747432329226071750867899)
              ·
                refine ⟨2621148493839107626301849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1747432329226071750867899 2621148493839107626301849)
                ·
                  refine ⟨1965861370379330719726387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2621148493839107626301849 1965861370379330719726387)
                  ·
                    refine ⟨2948792055568996079589581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1965861370379330719726387 2948792055568996079589581)
                    ·
                      refine ⟨1105797020838373529846093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2948792055568996079589581 1105797020838373529846093)
                      ·
                        rfl

theorem cell23_2153532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_2153532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153532 prefixEnd_2153532 := by exact prefixLift 2153532
  have htrace : WordTrace (prefixWord ++ tailWord_2153532) baseStart_2153532 baseEnd_2153532 := by
    simpa [prefixWord, tailWord_2153532, baseEnd_2153532] using wordTrace_append hprefix tailTrace_2153532
  have hstable : (prefixWord ++ tailWord_2153532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153532).length < 2 ^ (prefixWord ++ tailWord_2153532).sum := by decide
  have hdescent : baseEnd_2153532 < baseStart_2153532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153541 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 2, 4, 3]
def baseStart_2153541 : Nat := 118140960795 + 2153541 * 2 ^ 59
def prefixEnd_2153541 : Nat := 4983230072969 + 3 ^ 40 * 2153541 * 2
def baseEnd_2153541 : Nat := 1105801642164263994633551

theorem tailTrace_2153541 : CollatzResearch.WordTrace tailWord_2153541 prefixEnd_2153541 1105801642164263994633551 := by
  unfold tailWord_2153541
  simp only [CollatzResearch.WordTrace]
  refine ⟨78546093091096227366212477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52364062060730818244141651 78546093091096227366212477)
  ·
    refine ⟨29454784909161085262329679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78546093091096227366212477 29454784909161085262329679)
    ·
      refine ⟨44182177363741627893494519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29454784909161085262329679 44182177363741627893494519)
      ·
        refine ⟨66273266045612441840241779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44182177363741627893494519 66273266045612441840241779)
        ·
          refine ⟨99409899068418662760362669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66273266045612441840241779 99409899068418662760362669)
          ·
            refine ⟨37278712150656998535136001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99409899068418662760362669 37278712150656998535136001)
            ·
              refine ⟨27959034112992748901352001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37278712150656998535136001 27959034112992748901352001)
              ·
                refine ⟨20969275584744561676014001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27959034112992748901352001 20969275584744561676014001)
                ·
                  refine ⟨15726956688558421257010501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20969275584744561676014001 15726956688558421257010501)
                  ·
                    refine ⟨2948804379104703985689469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15726956688558421257010501 2948804379104703985689469)
                    ·
                      refine ⟨1105801642164263994633551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2948804379104703985689469 1105801642164263994633551)
                      ·
                        rfl

theorem cell23_2153541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_2153541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153541 prefixEnd_2153541 := by exact prefixLift 2153541
  have htrace : WordTrace (prefixWord ++ tailWord_2153541) baseStart_2153541 baseEnd_2153541 := by
    simpa [prefixWord, tailWord_2153541, baseEnd_2153541] using wordTrace_append hprefix tailTrace_2153541
  have hstable : (prefixWord ++ tailWord_2153541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153541).length < 2 ^ (prefixWord ++ tailWord_2153541).sum := by decide
  have hdescent : baseEnd_2153541 < baseStart_2153541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153578 : List Nat := [3, 1, 3, 2, 2, 1, 3, 1, 7]
def baseStart_2153578 : Nat := 118140960795 + 2153578 * 2 ^ 59
def prefixEnd_2153578 : Nat := 4983230072969 + 3 ^ 40 * 2153578 * 2
def baseEnd_2153578 : Nat := 122868960105386705541209

theorem tailTrace_2153578 : CollatzResearch.WordTrace tailWord_2153578 prefixEnd_2153578 122868960105386705541209 := by
  unfold tailWord_2153578
  simp only [CollatzResearch.WordTrace]
  refine ⟨19636860647990545671327347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52364961727974788456872925 19636860647990545671327347)
  ·
    refine ⟨29455290971985818506991021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19636860647990545671327347 29455290971985818506991021)
    ·
      refine ⟨11045734114494681940121633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29455290971985818506991021 11045734114494681940121633)
      ·
        refine ⟨8284300585871011455091225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11045734114494681940121633 8284300585871011455091225)
        ·
          refine ⟨6213225439403258591318419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8284300585871011455091225 6213225439403258591318419)
          ·
            refine ⟨9319838159104887886977629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6213225439403258591318419 9319838159104887886977629)
            ·
              refine ⟨3494939309664332957616611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9319838159104887886977629 3494939309664332957616611)
              ·
                refine ⟨5242408964496499436424917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3494939309664332957616611 5242408964496499436424917)
                ·
                  refine ⟨122868960105386705541209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5242408964496499436424917 122868960105386705541209)
                  ·
                    rfl

theorem cell23_2153578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_2153578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153578 prefixEnd_2153578 := by exact prefixLift 2153578
  have htrace : WordTrace (prefixWord ++ tailWord_2153578) baseStart_2153578 baseEnd_2153578 := by
    simpa [prefixWord, tailWord_2153578, baseEnd_2153578] using wordTrace_append hprefix tailTrace_2153578
  have hstable : (prefixWord ++ tailWord_2153578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153578).length < 2 ^ (prefixWord ++ tailWord_2153578).sum := by decide
  have hdescent : baseEnd_2153578 < baseStart_2153578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153591 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 4, 5]
def baseStart_2153591 : Nat := 118140960795 + 2153591 * 2 ^ 59
def prefixEnd_2153591 : Nat := 4983230072969 + 3 ^ 40 * 2153591 * 2
def baseEnd_2153591 : Nat := 368609105398996266336107

theorem tailTrace_2153591 : CollatzResearch.WordTrace tailWord_2153591 prefixEnd_2153591 368609105398996266336107 := by
  unfold tailWord_2153591
  simp only [CollatzResearch.WordTrace]
  refine ⟨78547916740915085905532627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52365277827276723937021751 78547916740915085905532627)
  ·
    refine ⟨117821875111372628858298941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78547916740915085905532627 117821875111372628858298941)
    ·
      refine ⟨44183203166764735821862103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117821875111372628858298941 44183203166764735821862103)
      ·
        refine ⟨66274804750147103732793155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44183203166764735821862103 66274804750147103732793155)
        ·
          refine ⟨99412207125220655599189733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66274804750147103732793155 99412207125220655599189733)
          ·
            refine ⟨18639788835978872924848075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99412207125220655599189733 18639788835978872924848075)
            ·
              refine ⟨27959683253968309387272113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18639788835978872924848075 27959683253968309387272113)
              ·
                refine ⟨20969762440476232040454085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27959683253968309387272113 20969762440476232040454085)
                ·
                  refine ⟨3931830457589293507585141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20969762440476232040454085 3931830457589293507585141)
                  ·
                    refine ⟨368609105398996266336107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3931830457589293507585141 368609105398996266336107)
                    ·
                      rfl

theorem cell23_2153591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_2153591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153591 prefixEnd_2153591 := by exact prefixLift 2153591
  have htrace : WordTrace (prefixWord ++ tailWord_2153591) baseStart_2153591 baseEnd_2153591 := by
    simpa [prefixWord, tailWord_2153591, baseEnd_2153591] using wordTrace_append hprefix tailTrace_2153591
  have hstable : (prefixWord ++ tailWord_2153591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153591).length < 2 ^ (prefixWord ++ tailWord_2153591).sum := by decide
  have hdescent : baseEnd_2153591 < baseStart_2153591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153611 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 4]
def baseStart_2153611 : Nat := 118140960795 + 2153611 * 2 ^ 59
def prefixEnd_2153611 : Nat := 4983230072969 + 3 ^ 40 * 2153611 * 2
def baseEnd_2153611 : Nat := 1105837585810078720758229

theorem tailTrace_2153611 : CollatzResearch.WordTrace tailWord_2153611 prefixEnd_2153611 1105837585810078720758229 := by
  unfold tailWord_2153611
  simp only [CollatzResearch.WordTrace]
  refine ⟨78548646200842629321260687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52365764133895086214173791 78548646200842629321260687)
  ·
    refine ⟨117822969301263943981891031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78548646200842629321260687 117822969301263943981891031)
    ·
      refine ⟨176734453951895915972836547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117822969301263943981891031 176734453951895915972836547)
      ·
        refine ⟨265101680927843873959254821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176734453951895915972836547 265101680927843873959254821)
        ·
          refine ⟨49706565173970726367360279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265101680927843873959254821 49706565173970726367360279)
          ·
            refine ⟨74559847760956089551040419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49706565173970726367360279 74559847760956089551040419)
            ·
              refine ⟨111839771641434134326560629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74559847760956089551040419 111839771641434134326560629)
              ·
                refine ⟨10484978591384450093115059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111839771641434134326560629 10484978591384450093115059)
                ·
                  refine ⟨15727467887076675139672589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10484978591384450093115059 15727467887076675139672589)
                  ·
                    refine ⟨5897800457653753177377221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15727467887076675139672589 5897800457653753177377221)
                    ·
                      refine ⟨1105837585810078720758229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5897800457653753177377221 1105837585810078720758229)
                      ·
                        rfl

theorem cell23_2153611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 4].length) (baseStart_2153611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153611 prefixEnd_2153611 := by exact prefixLift 2153611
  have htrace : WordTrace (prefixWord ++ tailWord_2153611) baseStart_2153611 baseEnd_2153611 := by
    simpa [prefixWord, tailWord_2153611, baseEnd_2153611] using wordTrace_append hprefix tailTrace_2153611
  have hstable : (prefixWord ++ tailWord_2153611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153611).length < 2 ^ (prefixWord ++ tailWord_2153611).sum := by decide
  have hdescent : baseEnd_2153611 < baseStart_2153611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153618 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2153618 : Nat := 118140960795 + 2153618 * 2 ^ 59
def prefixEnd_2153618 : Nat := 4983230072969 + 3 ^ 40 * 2153618 * 2
def baseEnd_2153618 : Nat := 1105841180174660193370697

theorem tailTrace_2153618 : CollatzResearch.WordTrace tailWord_2153618 prefixEnd_2153618 1105841180174660193370697 := by
  unfold tailWord_2153618
  simp only [CollatzResearch.WordTrace]
  refine ⟨19637225377954317379191377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52365934341211513011177005 19637225377954317379191377)
  ·
    refine ⟨14727919033465738034393533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19637225377954317379191377 14727919033465738034393533)
    ·
      refine ⟨5522969637549651762897575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14727919033465738034393533 5522969637549651762897575)
      ·
        refine ⟨8284454456324477644346363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5522969637549651762897575 8284454456324477644346363)
        ·
          refine ⟨12426681684486716466519545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8284454456324477644346363 12426681684486716466519545)
          ·
            refine ⟨9320011263365037349889659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12426681684486716466519545 9320011263365037349889659)
            ·
              refine ⟨13980016895047556024834489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9320011263365037349889659 13980016895047556024834489)
              ·
                refine ⟨10485012671285667018625867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13980016895047556024834489 10485012671285667018625867)
                ·
                  refine ⟨15727519006928500527938801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10485012671285667018625867 15727519006928500527938801)
                  ·
                    refine ⟨11795639255196375395954101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15727519006928500527938801 11795639255196375395954101)
                    ·
                      refine ⟨1105841180174660193370697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11795639255196375395954101 1105841180174660193370697)
                      ·
                        rfl

theorem cell23_2153618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2153618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153618 prefixEnd_2153618 := by exact prefixLift 2153618
  have htrace : WordTrace (prefixWord ++ tailWord_2153618) baseStart_2153618 baseEnd_2153618 := by
    simpa [prefixWord, tailWord_2153618, baseEnd_2153618] using wordTrace_append hprefix tailTrace_2153618
  have hstable : (prefixWord ++ tailWord_2153618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153618).length < 2 ^ (prefixWord ++ tailWord_2153618).sum := by decide
  have hdescent : baseEnd_2153618 < baseStart_2153618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153662 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4]
def baseStart_2153662 : Nat := 118140960795 + 2153662 * 2 ^ 59
def prefixEnd_2153662 : Nat := 4983230072969 + 3 ^ 40 * 2153662 * 2
def baseEnd_2153662 : Nat := 1105863773323458021220495

theorem tailTrace_2153662 : CollatzResearch.WordTrace tailWord_2153662 prefixEnd_2153662 1105863773323458021220495 := by
  unfold tailWord_2153662
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818813290457233128920905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52367004215771910020911493 9818813290457233128920905)
  ·
    refine ⟨7364109967842924846690679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9818813290457233128920905 7364109967842924846690679)
    ·
      refine ⟨11046164951764387270036019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7364109967842924846690679 11046164951764387270036019)
      ·
        refine ⟨16569247427646580905054029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11046164951764387270036019 16569247427646580905054029)
        ·
          refine ⟨6213467785367467839395261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16569247427646580905054029 6213467785367467839395261)
          ·
            refine ⟨2330050419512800439773223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6213467785367467839395261 2330050419512800439773223)
            ·
              refine ⟨3495075629269200659659835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330050419512800439773223 3495075629269200659659835)
              ·
                refine ⟨5242613443903800989489753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495075629269200659659835 5242613443903800989489753)
                ·
                  refine ⟨3931960082927850742117315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5242613443903800989489753 3931960082927850742117315)
                  ·
                    refine ⟨5897940124391776113175973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3931960082927850742117315 5897940124391776113175973)
                    ·
                      refine ⟨1105863773323458021220495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5897940124391776113175973 1105863773323458021220495)
                      ·
                        rfl

theorem cell23_2153662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_2153662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153662 prefixEnd_2153662 := by exact prefixLift 2153662
  have htrace : WordTrace (prefixWord ++ tailWord_2153662) baseStart_2153662 baseEnd_2153662 := by
    simpa [prefixWord, tailWord_2153662, baseEnd_2153662] using wordTrace_append hprefix tailTrace_2153662
  have hstable : (prefixWord ++ tailWord_2153662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153662).length < 2 ^ (prefixWord ++ tailWord_2153662).sum := by decide
  have hdescent : baseEnd_2153662 < baseStart_2153662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153671 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_2153671 : Nat := 118140960795 + 2153671 * 2 ^ 59
def prefixEnd_2153671 : Nat := 4983230072969 + 3 ^ 40 * 2153671 * 2
def baseEnd_2153671 : Nat := 1105868394649348486007953

theorem tailTrace_2153671 : CollatzResearch.WordTrace tailWord_2153671 prefixEnd_2153671 1105868394649348486007953 := by
  unfold tailWord_2153671
  simp only [CollatzResearch.WordTrace]
  refine ⟨78550834580625259568444867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52367223053750173045629911 78550834580625259568444867)
  ·
    refine ⟨117826251870937889352667301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78550834580625259568444867 117826251870937889352667301)
    ·
      refine ⟨22092422225800854253625119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117826251870937889352667301 22092422225800854253625119)
      ·
        refine ⟨33138633338701281380437679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22092422225800854253625119 33138633338701281380437679)
        ·
          refine ⟨49707950008051922070656519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33138633338701281380437679 49707950008051922070656519)
          ·
            refine ⟨74561925012077883105984779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49707950008051922070656519 74561925012077883105984779)
            ·
              refine ⟨111842887518116824658977169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74561925012077883105984779 111842887518116824658977169)
              ·
                refine ⟨83882165638587618494232877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111842887518116824658977169 83882165638587618494232877)
                ·
                  refine ⟨31455812114470356935337329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83882165638587618494232877 31455812114470356935337329)
                  ·
                    refine ⟨23591859085852767701502997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31455812114470356935337329 23591859085852767701502997)
                    ·
                      refine ⟨1105868394649348486007953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23591859085852767701502997 1105868394649348486007953)
                      ·
                        rfl

theorem cell23_2153671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_2153671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153671 prefixEnd_2153671 := by exact prefixLift 2153671
  have htrace : WordTrace (prefixWord ++ tailWord_2153671) baseStart_2153671 baseEnd_2153671 := by
    simpa [prefixWord, tailWord_2153671, baseEnd_2153671] using wordTrace_append hprefix tailTrace_2153671
  have hstable : (prefixWord ++ tailWord_2153671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153671).length < 2 ^ (prefixWord ++ tailWord_2153671).sum := by decide
  have hdescent : baseEnd_2153671 < baseStart_2153671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153685 : List Nat := [1, 3, 2, 4, 1, 1, 3, 2, 6]
def baseStart_2153685 : Nat := 118140960795 + 2153685 * 2 ^ 59
def prefixEnd_2153685 : Nat := 4983230072969 + 3 ^ 40 * 2153685 * 2
def baseEnd_2153685 : Nat := 122875064819834603470321

theorem tailTrace_2153685 : CollatzResearch.WordTrace tailWord_2153685 prefixEnd_2153685 122875064819834603470321 := by
  unfold tailWord_2153685
  simp only [CollatzResearch.WordTrace]
  refine ⟨78551345202574539959454509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52367563468383026639636339 78551345202574539959454509)
  ·
    refine ⟨29456754450965452484795441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78551345202574539959454509 29456754450965452484795441)
    ·
      refine ⟨22092565838224089363596581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29456754450965452484795441 22092565838224089363596581)
      ·
        refine ⟨4142356094667016755674359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22092565838224089363596581 4142356094667016755674359)
        ·
          refine ⟨6213534142000525133511539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4142356094667016755674359 6213534142000525133511539)
          ·
            refine ⟨9320301213000787700267309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6213534142000525133511539 9320301213000787700267309)
            ·
              refine ⟨3495112954875295387600241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9320301213000787700267309 3495112954875295387600241)
              ·
                refine ⟨2621334716156471540700181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3495112954875295387600241 2621334716156471540700181)
                ·
                  refine ⟨122875064819834603470321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2621334716156471540700181 122875064819834603470321)
                  ·
                    rfl

theorem cell23_2153685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_2153685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153685 prefixEnd_2153685 := by exact prefixLift 2153685
  have htrace : WordTrace (prefixWord ++ tailWord_2153685) baseStart_2153685 baseEnd_2153685 := by
    simpa [prefixWord, tailWord_2153685, baseEnd_2153685] using wordTrace_append hprefix tailTrace_2153685
  have hstable : (prefixWord ++ tailWord_2153685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153685).length < 2 ^ (prefixWord ++ tailWord_2153685).sum := by decide
  have hdescent : baseEnd_2153685 < baseStart_2153685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153695 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 3, 1, 3]
def baseStart_2153695 : Nat := 118140960795 + 2153695 * 2 ^ 59
def prefixEnd_2153695 : Nat := 4983230072969 + 3 ^ 40 * 2153695 * 2
def baseEnd_2153695 : Nat := 1105880718185056392107843

theorem tailTrace_2153695 : CollatzResearch.WordTrace tailWord_2153695 prefixEnd_2153695 1105880718185056392107843 := by
  unfold tailWord_2153695
  simp only [CollatzResearch.WordTrace]
  refine ⟨78551709932538311667318539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52367806621692207778212359 78551709932538311667318539)
  ·
    refine ⟨117827564898807467500977809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78551709932538311667318539 117827564898807467500977809)
    ·
      refine ⟨88370673674105600625733357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117827564898807467500977809 88370673674105600625733357)
      ·
        refine ⟨33139002627789600234650009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88370673674105600625733357 33139002627789600234650009)
        ·
          refine ⟨24854251970842200175987507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33139002627789600234650009 24854251970842200175987507)
          ·
            refine ⟨37281377956263300263981261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24854251970842200175987507 37281377956263300263981261)
            ·
              refine ⟨13980516733598737598992973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37281377956263300263981261 13980516733598737598992973)
              ·
                refine ⟨5242693775099526599622365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13980516733598737598992973 5242693775099526599622365)
                ·
                  refine ⟨1966010165662322474858387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5242693775099526599622365 1966010165662322474858387)
                  ·
                    refine ⟨2949015248493483712287581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1966010165662322474858387 2949015248493483712287581)
                    ·
                      refine ⟨1105880718185056392107843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2949015248493483712287581 1105880718185056392107843)
                      ·
                        rfl

theorem cell23_2153695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_2153695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153695 prefixEnd_2153695 := by exact prefixLift 2153695
  have htrace : WordTrace (prefixWord ++ tailWord_2153695) baseStart_2153695 baseEnd_2153695 := by
    simpa [prefixWord, tailWord_2153695, baseEnd_2153695] using wordTrace_append hprefix tailTrace_2153695
  have hstable : (prefixWord ++ tailWord_2153695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153695).length < 2 ^ (prefixWord ++ tailWord_2153695).sum := by decide
  have hdescent : baseEnd_2153695 < baseStart_2153695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153715 : List Nat := [1, 1, 1, 2, 2, 6, 2, 2, 1, 5]
def baseStart_2153715 : Nat := 118140960795 + 2153715 * 2 ^ 59
def prefixEnd_2153715 : Nat := 4983230072969 + 3 ^ 40 * 2153715 * 2
def baseEnd_2153715 : Nat := 368630329266048771285917

theorem tailTrace_2153715 : CollatzResearch.WordTrace tailWord_2153715 prefixEnd_2153715 368630329266048771285917 := by
  unfold tailWord_2153715
  simp only [CollatzResearch.WordTrace]
  refine ⟨78552439392465855083046599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52368292928310570055364399 78552439392465855083046599)
  ·
    refine ⟨117828659088698782624569899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78552439392465855083046599 117828659088698782624569899)
    ·
      refine ⟨176742988633048173936854849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117828659088698782624569899 176742988633048173936854849)
      ·
        refine ⟨132557241474786130452641137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176742988633048173936854849 132557241474786130452641137)
        ·
          refine ⟨99417931106089597839480853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132557241474786130452641137 99417931106089597839480853)
          ·
            refine ⟨4660215520597949898725665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99417931106089597839480853 4660215520597949898725665)
            ·
              refine ⟨3495161640448462424044249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4660215520597949898725665 3495161640448462424044249)
              ·
                refine ⟨2621371230336346818033187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3495161640448462424044249 2621371230336346818033187)
                ·
                  refine ⟨3932056845504520227049781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621371230336346818033187 3932056845504520227049781)
                  ·
                    refine ⟨368630329266048771285917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3932056845504520227049781 368630329266048771285917)
                    ·
                      rfl

theorem cell23_2153715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 5].length) (baseStart_2153715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153715 prefixEnd_2153715 := by exact prefixLift 2153715
  have htrace : WordTrace (prefixWord ++ tailWord_2153715) baseStart_2153715 baseEnd_2153715 := by
    simpa [prefixWord, tailWord_2153715, baseEnd_2153715] using wordTrace_append hprefix tailTrace_2153715
  have hstable : (prefixWord ++ tailWord_2153715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153715).length < 2 ^ (prefixWord ++ tailWord_2153715).sum := by decide
  have hdescent : baseEnd_2153715 < baseStart_2153715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153729 : List Nat := [1, 2, 4, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_2153729 : Nat := 118140960795 + 2153729 * 2 ^ 59
def prefixEnd_2153729 : Nat := 4983230072969 + 3 ^ 40 * 2153729 * 2
def baseEnd_2153729 : Nat := 1105898176527309259082687

theorem tailTrace_2153729 : CollatzResearch.WordTrace tailWord_2153729 prefixEnd_2153729 1105898176527309259082687 := by
  unfold tailWord_2153729
  simp only [CollatzResearch.WordTrace]
  refine ⟨78552950014415135474056241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52368633342943423649370827 78552950014415135474056241)
  ·
    refine ⟨58914712510811351605542181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78552950014415135474056241 58914712510811351605542181)
    ·
      refine ⟨11046508595777128426039159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58914712510811351605542181 11046508595777128426039159)
      ·
        refine ⟨16569762893665692639058739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11046508595777128426039159 16569762893665692639058739)
        ·
          refine ⟨24854644340498538958588109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16569762893665692639058739 24854644340498538958588109)
          ·
            refine ⟨9320491627686952109470541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24854644340498538958588109 9320491627686952109470541)
            ·
              refine ⟨3495184360382607041051453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9320491627686952109470541 3495184360382607041051453)
              ·
                refine ⟨1310694135143477640394295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3495184360382607041051453 1310694135143477640394295)
                ·
                  refine ⟨1966041202715216460591443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310694135143477640394295 1966041202715216460591443)
                  ·
                    refine ⟨2949061804072824690887165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1966041202715216460591443 2949061804072824690887165)
                    ·
                      refine ⟨1105898176527309259082687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2949061804072824690887165 1105898176527309259082687)
                      ·
                        rfl

theorem cell23_2153729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_2153729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153729 prefixEnd_2153729 := by exact prefixLift 2153729
  have htrace : WordTrace (prefixWord ++ tailWord_2153729) baseStart_2153729 baseEnd_2153729 := by
    simpa [prefixWord, tailWord_2153729, baseEnd_2153729] using wordTrace_append hprefix tailTrace_2153729
  have hstable : (prefixWord ++ tailWord_2153729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153729).length < 2 ^ (prefixWord ++ tailWord_2153729).sum := by decide
  have hdescent : baseEnd_2153729 < baseStart_2153729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153745 : List Nat := [1, 2, 2, 1, 1, 4, 2, 4, 2, 4]
def baseStart_2153745 : Nat := 118140960795 + 2153745 * 2 ^ 59
def prefixEnd_2153745 : Nat := 4983230072969 + 3 ^ 40 * 2153745 * 2
def baseEnd_2153745 : Nat := 368635464072593732160871

theorem tailTrace_2153745 : CollatzResearch.WordTrace tailWord_2153745 prefixEnd_2153745 368635464072593732160871 := by
  unfold tailWord_2153745
  simp only [CollatzResearch.WordTrace]
  refine ⟨78553533582357170206638689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52369022388238113471092459 78553533582357170206638689)
  ·
    refine ⟨58915150186767877654979017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78553533582357170206638689 58915150186767877654979017)
    ·
      refine ⟨44186362640075908241234263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58915150186767877654979017 44186362640075908241234263)
      ·
        refine ⟨66279543960113862361851395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44186362640075908241234263 66279543960113862361851395)
        ·
          refine ⟨99419315940170793542777093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66279543960113862361851395 99419315940170793542777093)
          ·
            refine ⟨18641121738782023789270705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99419315940170793542777093 18641121738782023789270705)
            ·
              refine ⟨13980841304086517841953029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18641121738782023789270705 13980841304086517841953029)
              ·
                refine ⟨2621407744516222095366193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13980841304086517841953029 2621407744516222095366193)
                ·
                  refine ⟨1966055808387166571524645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2621407744516222095366193 1966055808387166571524645)
                  ·
                    refine ⟨368635464072593732160871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1966055808387166571524645 368635464072593732160871)
                    ·
                      rfl

theorem cell23_2153745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_2153745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153745 prefixEnd_2153745 := by exact prefixLift 2153745
  have htrace : WordTrace (prefixWord ++ tailWord_2153745) baseStart_2153745 baseEnd_2153745 := by
    simpa [prefixWord, tailWord_2153745, baseEnd_2153745] using wordTrace_append hprefix tailTrace_2153745
  have hstable : (prefixWord ++ tailWord_2153745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153745).length < 2 ^ (prefixWord ++ tailWord_2153745).sum := by decide
  have hdescent : baseEnd_2153745 < baseStart_2153745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153789 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2153789 : Nat := 118140960795 + 2153789 * 2 ^ 59
def prefixEnd_2153789 : Nat := 4983230072969 + 3 ^ 40 * 2153789 * 2
def baseEnd_2153789 : Nat := 1105928985366579024332411

theorem tailTrace_2153789 : CollatzResearch.WordTrace tailWord_2153789 prefixEnd_2153789 1105928985366579024332411 := by
  unfold tailWord_2153789
  simp only [CollatzResearch.WordTrace]
  refine ⟨78555138394197765721240421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52370092262798510480826947 78555138394197765721240421)
  ·
    refine ⟨14729088448912081072732579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78555138394197765721240421 14729088448912081072732579)
    ·
      refine ⟨22093632673368121609098869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14729088448912081072732579 22093632673368121609098869)
      ·
        refine ⟨2071278063128261400853019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22093632673368121609098869 2071278063128261400853019)
        ·
          refine ⟨3106917094692392101279529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071278063128261400853019 3106917094692392101279529)
          ·
            refine ⟨2330187821019294075959647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3106917094692392101279529 2330187821019294075959647)
            ·
              refine ⟨3495281731528941113939471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330187821019294075959647 3495281731528941113939471)
              ·
                refine ⟨5242922597293411670909207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495281731528941113939471 5242922597293411670909207)
                ·
                  refine ⟨7864383895940117506363811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5242922597293411670909207 7864383895940117506363811)
                  ·
                    refine ⟨11796575843910176259545717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7864383895940117506363811 11796575843910176259545717)
                    ·
                      refine ⟨1105928985366579024332411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11796575843910176259545717 1105928985366579024332411)
                      ·
                        rfl

theorem cell23_2153789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2153789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153789 prefixEnd_2153789 := by exact prefixLift 2153789
  have htrace : WordTrace (prefixWord ++ tailWord_2153789) baseStart_2153789 baseEnd_2153789 := by
    simpa [prefixWord, tailWord_2153789, baseEnd_2153789] using wordTrace_append hprefix tailTrace_2153789
  have hstable : (prefixWord ++ tailWord_2153789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153789).length < 2 ^ (prefixWord ++ tailWord_2153789).sum := by decide
  have hdescent : baseEnd_2153789 < baseStart_2153789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153808 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 4]
def baseStart_2153808 : Nat := 118140960795 + 2153808 * 2 ^ 59
def prefixEnd_2153808 : Nat := 4983230072969 + 3 ^ 40 * 2153808 * 2
def baseEnd_2153808 : Nat := 1105938741499014449994823

theorem tailTrace_2153808 : CollatzResearch.WordTrace tailWord_2153808 prefixEnd_2153808 1105938741499014449994823 := by
  unfold tailWord_2153808
  simp only [CollatzResearch.WordTrace]
  refine ⟨39277915690564465983091039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52370554254085954644121385 39277915690564465983091039)
  ·
    refine ⟨58916873535846698974636559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39277915690564465983091039 58916873535846698974636559)
    ·
      refine ⟨88375310303770048461954839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58916873535846698974636559 88375310303770048461954839)
      ·
        refine ⟨132562965455655072692932259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88375310303770048461954839 132562965455655072692932259)
        ·
          refine ⟨198844448183482609039398389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132562965455655072692932259 198844448183482609039398389)
          ·
            refine ⟨18641667017201494597443599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 198844448183482609039398389 18641667017201494597443599)
            ·
              refine ⟨27962500525802241896165399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18641667017201494597443599 27962500525802241896165399)
              ·
                refine ⟨41943750788703362844248099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27962500525802241896165399 41943750788703362844248099)
                ·
                  refine ⟨62915626183055044266372149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41943750788703362844248099 62915626183055044266372149)
                  ·
                    refine ⟨5898339954661410399972389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62915626183055044266372149 5898339954661410399972389)
                    ·
                      refine ⟨1105938741499014449994823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5898339954661410399972389 1105938741499014449994823)
                      ·
                        rfl

theorem cell23_2153808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 4].length) (baseStart_2153808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153808 prefixEnd_2153808 := by exact prefixLift 2153808
  have htrace : WordTrace (prefixWord ++ tailWord_2153808) baseStart_2153808 baseEnd_2153808 := by
    simpa [prefixWord, tailWord_2153808, baseEnd_2153808] using wordTrace_append hprefix tailTrace_2153808
  have hstable : (prefixWord ++ tailWord_2153808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153808).length < 2 ^ (prefixWord ++ tailWord_2153808).sum := by decide
  have hdescent : baseEnd_2153808 < baseStart_2153808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153812 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_2153812 : Nat := 118140960795 + 2153812 * 2 ^ 59
def prefixEnd_2153812 : Nat := 4983230072969 + 3 ^ 40 * 2153812 * 2
def baseEnd_2153812 : Nat := 1105940795421632434344805

theorem tailTrace_2153812 : CollatzResearch.WordTrace tailWord_2153812 prefixEnd_2153812 1105940795421632434344805 := by
  unfold tailWord_2153812
  simp only [CollatzResearch.WordTrace]
  refine ⟨39277988636557220324663845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52370651515409627099551793 39277988636557220324663845)
  ·
    refine ⟨7364622869354478810874471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39277988636557220324663845 7364622869354478810874471)
    ·
      refine ⟨11046934304031718216311707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7364622869354478810874471 11046934304031718216311707)
      ·
        refine ⟨16570401456047577324467561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11046934304031718216311707 16570401456047577324467561)
        ·
          refine ⟨12427801092035682993350671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16570401456047577324467561 12427801092035682993350671)
          ·
            refine ⟨18641701638053524490026007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12427801092035682993350671 18641701638053524490026007)
            ·
              refine ⟨27962552457080286735039011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18641701638053524490026007 27962552457080286735039011)
              ·
                refine ⟨41943828685620430102558517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27962552457080286735039011 41943828685620430102558517)
                ·
                  refine ⟨3932233939276915322114861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41943828685620430102558517 3932233939276915322114861)
                  ·
                    refine ⟨1474587727228843245793073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3932233939276915322114861 1474587727228843245793073)
                    ·
                      refine ⟨1105940795421632434344805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1474587727228843245793073 1105940795421632434344805)
                      ·
                        rfl

theorem cell23_2153812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_2153812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153812 prefixEnd_2153812 := by exact prefixLift 2153812
  have htrace : WordTrace (prefixWord ++ tailWord_2153812) baseStart_2153812 baseEnd_2153812 := by
    simpa [prefixWord, tailWord_2153812, baseEnd_2153812] using wordTrace_append hprefix tailTrace_2153812
  have hstable : (prefixWord ++ tailWord_2153812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153812).length < 2 ^ (prefixWord ++ tailWord_2153812).sum := by decide
  have hdescent : baseEnd_2153812 < baseStart_2153812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153818 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_2153818 : Nat := 118140960795 + 2153818 * 2 ^ 59
def prefixEnd_2153818 : Nat := 4983230072969 + 3 ^ 40 * 2153818 * 2
def baseEnd_2153818 : Nat := 368647958768519803623259

theorem tailTrace_2153818 : CollatzResearch.WordTrace tailWord_2153818 prefixEnd_2153818 368647958768519803623259 := by
  unfold tailWord_2153818
  simp only [CollatzResearch.WordTrace]
  refine ⟨19639049027773175918511527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52370797407395135782697405 19639049027773175918511527)
  ·
    refine ⟨29458573541659763877767291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19639049027773175918511527 29458573541659763877767291)
    ·
      refine ⟨44187860312489645816650937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29458573541659763877767291 44187860312489645816650937)
      ·
        refine ⟨33140895234367234362488203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44187860312489645816650937 33140895234367234362488203)
        ·
          refine ⟨49711342851550851543732305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33140895234367234362488203 49711342851550851543732305)
          ·
            refine ⟨37283507138663138657799229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49711342851550851543732305 37283507138663138657799229)
            ·
              refine ⟨13981315176998676996674711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37283507138663138657799229 13981315176998676996674711)
              ·
                refine ⟨20971972765498015495012067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13981315176998676996674711 20971972765498015495012067)
                ·
                  refine ⟨31457959148247023242518101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20971972765498015495012067 31457959148247023242518101)
                  ·
                    refine ⟨368647958768519803623259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31457959148247023242518101 368647958768519803623259)
                    ·
                      rfl

theorem cell23_2153818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_2153818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153818 prefixEnd_2153818 := by exact prefixLift 2153818
  have htrace : WordTrace (prefixWord ++ tailWord_2153818) baseStart_2153818 baseEnd_2153818 := by
    simpa [prefixWord, tailWord_2153818, baseEnd_2153818] using wordTrace_append hprefix tailTrace_2153818
  have hstable : (prefixWord ++ tailWord_2153818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153818).length < 2 ^ (prefixWord ++ tailWord_2153818).sum := by decide
  have hdescent : baseEnd_2153818 < baseStart_2153818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153842 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 1, 4, 2]
def baseStart_2153842 : Nat := 118140960795 + 2153842 * 2 ^ 59
def prefixEnd_2153842 : Nat := 4983230072969 + 3 ^ 40 * 2153842 * 2
def baseEnd_2153842 : Nat := 1105956199841267316969667

theorem tailTrace_2153842 : CollatzResearch.WordTrace tailWord_2153842 prefixEnd_2153842 1105956199841267316969667 := by
  unfold tailWord_2153842
  simp only [CollatzResearch.WordTrace]
  refine ⟨19639267865751438943229945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52371380975337170515279853 19639267865751438943229945)
  ·
    refine ⟨14729450899313579207422459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19639267865751438943229945 14729450899313579207422459)
    ·
      refine ⟨22094176348970368811133689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14729450899313579207422459 22094176348970368811133689)
      ·
        refine ⟨16570632261727776608350267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22094176348970368811133689 16570632261727776608350267)
        ·
          refine ⟨24855948392591664912525401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16570632261727776608350267 24855948392591664912525401)
          ·
            refine ⟨18641961294443748684394051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24855948392591664912525401 18641961294443748684394051)
            ·
              refine ⟨27962941941665623026591077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18641961294443748684394051 27962941941665623026591077)
              ·
                refine ⟨5243051614062304317485827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27962941941665623026591077 5243051614062304317485827)
                ·
                  refine ⟨7864577421093456476228741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5243051614062304317485827 7864577421093456476228741)
                  ·
                    refine ⟨1474608266455023089292889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7864577421093456476228741 1474608266455023089292889)
                    ·
                      refine ⟨1105956199841267316969667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1474608266455023089292889 1105956199841267316969667)
                      ·
                        rfl

theorem cell23_2153842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_2153842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153842 prefixEnd_2153842 := by exact prefixLift 2153842
  have htrace : WordTrace (prefixWord ++ tailWord_2153842) baseStart_2153842 baseEnd_2153842 := by
    simpa [prefixWord, tailWord_2153842, baseEnd_2153842] using wordTrace_append hprefix tailTrace_2153842
  have hstable : (prefixWord ++ tailWord_2153842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153842).length < 2 ^ (prefixWord ++ tailWord_2153842).sum := by decide
  have hdescent : baseEnd_2153842 < baseStart_2153842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153859 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 4, 2, 2]
def baseStart_2153859 : Nat := 118140960795 + 2153859 * 2 ^ 59
def prefixEnd_2153859 : Nat := 4983230072969 + 3 ^ 40 * 2153859 * 2
def baseEnd_2153859 : Nat := 1105964929012393750457089

theorem tailTrace_2153859 : CollatzResearch.WordTrace tailWord_2153859 prefixEnd_2153859 1105964929012393750457089 := by
  unfold tailWord_2153859
  simp only [CollatzResearch.WordTrace]
  refine ⟨78557691503944167676288631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52371794335962778450859087 78557691503944167676288631)
  ·
    refine ⟨117836537255916251514432947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78557691503944167676288631 117836537255916251514432947)
    ·
      refine ⟨176754805883874377271649421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117836537255916251514432947 176754805883874377271649421)
      ·
        refine ⟨66283052206452891476868533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176754805883874377271649421 66283052206452891476868533)
        ·
          refine ⟨6214036144354958575956425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66283052206452891476868533 6214036144354958575956425)
          ·
            refine ⟨4660527108266218931967319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6214036144354958575956425 4660527108266218931967319)
            ·
              refine ⟨6990790662399328397950979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4660527108266218931967319 6990790662399328397950979)
              ·
                refine ⟨10486185993598992596926469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6990790662399328397950979 10486185993598992596926469)
                ·
                  refine ⟨1966159873799811111923713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10486185993598992596926469 1966159873799811111923713)
                  ·
                    refine ⟨1474619905349858333942785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1966159873799811111923713 1474619905349858333942785)
                    ·
                      refine ⟨1105964929012393750457089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1474619905349858333942785 1105964929012393750457089)
                      ·
                        rfl

theorem cell23_2153859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 2, 2].length) (baseStart_2153859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153859 prefixEnd_2153859 := by exact prefixLift 2153859
  have htrace : WordTrace (prefixWord ++ tailWord_2153859) baseStart_2153859 baseEnd_2153859 := by
    simpa [prefixWord, tailWord_2153859, baseEnd_2153859] using wordTrace_append hprefix tailTrace_2153859
  have hstable : (prefixWord ++ tailWord_2153859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153859).length < 2 ^ (prefixWord ++ tailWord_2153859).sum := by decide
  have hdescent : baseEnd_2153859 < baseStart_2153859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153876 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_2153876 : Nat := 118140960795 + 2153876 * 2 ^ 59
def prefixEnd_2153876 : Nat := 4983230072969 + 3 ^ 40 * 2153876 * 2
def baseEnd_2153876 : Nat := 1105973658183520183944511

theorem tailTrace_2153876 : CollatzResearch.WordTrace tailWord_2153876 prefixEnd_2153876 1105973658183520183944511 := by
  unfold tailWord_2153876
  simp only [CollatzResearch.WordTrace]
  refine ⟨39279155772441289789828741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52372207696588386386438321 39279155772441289789828741)
  ·
    refine ⟨7364841707332741835592889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39279155772441289789828741 7364841707332741835592889)
    ·
      refine ⟨5523631280499556376694667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7364841707332741835592889 5523631280499556376694667)
      ·
        refine ⟨8285446920749334565042001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5523631280499556376694667 8285446920749334565042001)
        ·
          refine ⟨6214085190562000923781501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8285446920749334565042001 6214085190562000923781501)
          ·
            refine ⟨2330281946460750346418063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6214085190562000923781501 2330281946460750346418063)
            ·
              refine ⟨3495422919691125519627095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330281946460750346418063 3495422919691125519627095)
              ·
                refine ⟨5243134379536688279440643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495422919691125519627095 5243134379536688279440643)
                ·
                  refine ⟨7864701569305032419160965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5243134379536688279440643 7864701569305032419160965)
                  ·
                    refine ⟨1474631544244693578592681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7864701569305032419160965 1474631544244693578592681)
                    ·
                      refine ⟨1105973658183520183944511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1474631544244693578592681 1105973658183520183944511)
                      ·
                        rfl

theorem cell23_2153876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_2153876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153876 prefixEnd_2153876 := by exact prefixLift 2153876
  have htrace : WordTrace (prefixWord ++ tailWord_2153876) baseStart_2153876 baseEnd_2153876 := by
    simpa [prefixWord, tailWord_2153876, baseEnd_2153876] using wordTrace_append hprefix tailTrace_2153876
  have hstable : (prefixWord ++ tailWord_2153876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153876).length < 2 ^ (prefixWord ++ tailWord_2153876).sum := by decide
  have hdescent : baseEnd_2153876 < baseStart_2153876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153895 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 1, 7]
def baseStart_2153895 : Nat := 118140960795 + 2153895 * 2 ^ 59
def prefixEnd_2153895 : Nat := 4983230072969 + 3 ^ 40 * 2153895 * 2
def baseEnd_2153895 : Nat := 368661138105318536535641

theorem tailTrace_2153895 : CollatzResearch.WordTrace tailWord_2153895 prefixEnd_2153895 368661138105318536535641 := by
  unfold tailWord_2153895
  simp only [CollatzResearch.WordTrace]
  refine ⟨78559004531813745824599139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52372669687875830549732759 78559004531813745824599139)
  ·
    refine ⟨117838506797720618736898709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78559004531813745824599139 117838506797720618736898709)
    ·
      refine ⟨5523680006143154003292127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 117838506797720618736898709 5523680006143154003292127)
      ·
        refine ⟨8285520009214731004938191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5523680006143154003292127 8285520009214731004938191)
        ·
          refine ⟨12428280013822096507407287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8285520009214731004938191 12428280013822096507407287)
          ·
            refine ⟨18642420020733144761110931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12428280013822096507407287 18642420020733144761110931)
            ·
              refine ⟨27963630031099717141666397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18642420020733144761110931 27963630031099717141666397)
              ·
                refine ⟨10486361261662393928124899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27963630031099717141666397 10486361261662393928124899)
                ·
                  refine ⟨15729541892493590892187349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10486361261662393928124899 15729541892493590892187349)
                  ·
                    refine ⟨368661138105318536535641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15729541892493590892187349 368661138105318536535641)
                    ·
                      rfl

theorem cell23_2153895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_2153895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153895 prefixEnd_2153895 := by exact prefixLift 2153895
  have htrace : WordTrace (prefixWord ++ tailWord_2153895) baseStart_2153895 baseEnd_2153895 := by
    simpa [prefixWord, tailWord_2153895, baseEnd_2153895] using wordTrace_append hprefix tailTrace_2153895
  have hstable : (prefixWord ++ tailWord_2153895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153895).length < 2 ^ (prefixWord ++ tailWord_2153895).sum := by decide
  have hdescent : baseEnd_2153895 < baseStart_2153895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153905 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2153905 : Nat := 118140960795 + 2153905 * 2 ^ 59
def prefixEnd_2153905 : Nat := 4983230072969 + 3 ^ 40 * 2153905 * 2
def baseEnd_2153905 : Nat := 1105988549122500570481877

theorem tailTrace_2153905 : CollatzResearch.WordTrace tailWord_2153905 prefixEnd_2153905 1105988549122500570481877 := by
  unfold tailWord_2153905
  simp only [CollatzResearch.WordTrace]
  refine ⟨78559369261777517532463169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52372912841185011688308779 78559369261777517532463169)
  ·
    refine ⟨58919526946333138149347377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78559369261777517532463169 58919526946333138149347377)
    ·
      refine ⟨44189645209749853612010533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58919526946333138149347377 44189645209749853612010533)
      ·
        refine ⟨8285558476828097552251975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44189645209749853612010533 8285558476828097552251975)
        ·
          refine ⟨12428337715242146328377963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8285558476828097552251975 12428337715242146328377963)
          ·
            refine ⟨18642506572863219492566945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12428337715242146328377963 18642506572863219492566945)
            ·
              refine ⟨13981879929647414619425209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18642506572863219492566945 13981879929647414619425209)
              ·
                refine ⟨10486409947235560964568907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13981879929647414619425209 10486409947235560964568907)
                ·
                  refine ⟨15729614920853341446853361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10486409947235560964568907 15729614920853341446853361)
                  ·
                    refine ⟨11797211190640006085140021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15729614920853341446853361 11797211190640006085140021)
                    ·
                      refine ⟨1105988549122500570481877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11797211190640006085140021 1105988549122500570481877)
                      ·
                        rfl

theorem cell23_2153905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2153905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153905 prefixEnd_2153905 := by exact prefixLift 2153905
  have htrace : WordTrace (prefixWord ++ tailWord_2153905) baseStart_2153905 baseEnd_2153905 := by
    simpa [prefixWord, tailWord_2153905, baseEnd_2153905] using wordTrace_append hprefix tailTrace_2153905
  have hstable : (prefixWord ++ tailWord_2153905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153905).length < 2 ^ (prefixWord ++ tailWord_2153905).sum := by decide
  have hdescent : baseEnd_2153905 < baseStart_2153905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153916 : List Nat := [2, 2, 2, 4, 2, 1, 3, 2, 5]
def baseStart_2153916 : Nat := 118140960795 + 2153916 * 2 ^ 59
def prefixEnd_2153916 : Nat := 4983230072969 + 3 ^ 40 * 2153916 * 2
def baseEnd_2153916 : Nat := 122888244156633336382703

theorem tailTrace_2153916 : CollatzResearch.WordTrace tailWord_2153916 prefixEnd_2153916 122888244156633336382703 := by
  unfold tailWord_2153916
  simp only [CollatzResearch.WordTrace]
  refine ⟨39279885232368833205556801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52373180309825110940742401 39279885232368833205556801)
  ·
    refine ⟨29459913924276624904167601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39279885232368833205556801 29459913924276624904167601)
    ·
      refine ⟨22094935443207468678125701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29459913924276624904167601 22094935443207468678125701)
      ·
        refine ⟨4142800395601400377148569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22094935443207468678125701 4142800395601400377148569)
        ·
          refine ⟨3107100296701050282861427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4142800395601400377148569 3107100296701050282861427)
          ·
            refine ⟨4660650445051575424292141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107100296701050282861427 4660650445051575424292141)
            ·
              refine ⟨1747743916894340784109553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4660650445051575424292141 1747743916894340784109553)
              ·
                refine ⟨1310807937670755588082165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1747743916894340784109553 1310807937670755588082165)
                ·
                  refine ⟨122888244156633336382703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1310807937670755588082165 122888244156633336382703)
                  ·
                    rfl

theorem cell23_2153916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_2153916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153916 prefixEnd_2153916 := by exact prefixLift 2153916
  have htrace : WordTrace (prefixWord ++ tailWord_2153916) baseStart_2153916 baseEnd_2153916 := by
    simpa [prefixWord, tailWord_2153916, baseEnd_2153916] using wordTrace_append hprefix tailTrace_2153916
  have hstable : (prefixWord ++ tailWord_2153916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153916).length < 2 ^ (prefixWord ++ tailWord_2153916).sum := by decide
  have hdescent : baseEnd_2153916 < baseStart_2153916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153935 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 3]
def baseStart_2153935 : Nat := 118140960795 + 2153935 * 2 ^ 59
def prefixEnd_2153935 : Nat := 4983230072969 + 3 ^ 40 * 2153935 * 2
def baseEnd_2153935 : Nat := 1106003953542135453106739

theorem tailTrace_2153935 : CollatzResearch.WordTrace tailWord_2153935 prefixEnd_2153935 1106003953542135453106739 := by
  unfold tailWord_2153935
  simp only [CollatzResearch.WordTrace]
  refine ⟨78560463451668832656055259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52373642301112555104036839 78560463451668832656055259)
  ·
    refine ⟨117840695177503248984082889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78560463451668832656055259 117840695177503248984082889)
    ·
      refine ⟨88380521383127436738062167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117840695177503248984082889 88380521383127436738062167)
      ·
        refine ⟨132570782074691155107093251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88380521383127436738062167 132570782074691155107093251)
        ·
          refine ⟨198856173112036732660639877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132570782074691155107093251 198856173112036732660639877)
          ·
            refine ⟨37285532458506887373869977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198856173112036732660639877 37285532458506887373869977)
            ·
              refine ⟨27964149343880165530402483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37285532458506887373869977 27964149343880165530402483)
              ·
                refine ⟨41946224015820248295603725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27964149343880165530402483 41946224015820248295603725)
                ·
                  refine ⟨15729834005932593110851397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41946224015820248295603725 15729834005932593110851397)
                  ·
                    refine ⟨2949343876112361208284637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15729834005932593110851397 2949343876112361208284637)
                    ·
                      refine ⟨1106003953542135453106739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2949343876112361208284637 1106003953542135453106739)
                      ·
                        rfl

theorem cell23_2153935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 3].length) (baseStart_2153935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153935 prefixEnd_2153935 := by exact prefixLift 2153935
  have htrace : WordTrace (prefixWord ++ tailWord_2153935) baseStart_2153935 baseEnd_2153935 := by
    simpa [prefixWord, tailWord_2153935, baseEnd_2153935] using wordTrace_append hprefix tailTrace_2153935
  have hstable : (prefixWord ++ tailWord_2153935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153935).length < 2 ^ (prefixWord ++ tailWord_2153935).sum := by decide
  have hdescent : baseEnd_2153935 < baseStart_2153935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153949 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_2153949 : Nat := 118140960795 + 2153949 * 2 ^ 59
def prefixEnd_2153949 : Nat := 4983230072969 + 3 ^ 40 * 2153949 * 2
def baseEnd_2153949 : Nat := 1106011142271298398331675

theorem tailTrace_2153949 : CollatzResearch.WordTrace tailWord_2153949 prefixEnd_2153949 1106011142271298398331675 := by
  unfold tailWord_2153949
  simp only [CollatzResearch.WordTrace]
  refine ⟨78560974073618113047064901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52373982715745408698043267 78560974073618113047064901)
  ·
    refine ⟨14730182638803396196324669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78560974073618113047064901 14730182638803396196324669)
    ·
      refine ⟨5523818489551273573621751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14730182638803396196324669 5523818489551273573621751)
      ·
        refine ⟨8285727734326910360432627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5523818489551273573621751 8285727734326910360432627)
        ·
          refine ⟨12428591601490365540648941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8285727734326910360432627 12428591601490365540648941)
          ·
            refine ⟨4660721850558887077743353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12428591601490365540648941 4660721850558887077743353)
            ·
              refine ⟨3495541387919165308307515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4660721850558887077743353 3495541387919165308307515)
              ·
                refine ⟨5243312081878747962461273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3495541387919165308307515 5243312081878747962461273)
                ·
                  refine ⟨3932484061409060971845955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5243312081878747962461273 3932484061409060971845955)
                  ·
                    refine ⟨5898726092113591457768933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3932484061409060971845955 5898726092113591457768933)
                    ·
                      refine ⟨1106011142271298398331675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5898726092113591457768933 1106011142271298398331675)
                      ·
                        rfl

theorem cell23_2153949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_2153949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153949 prefixEnd_2153949 := by exact prefixLift 2153949
  have htrace : WordTrace (prefixWord ++ tailWord_2153949) baseStart_2153949 baseEnd_2153949 := by
    simpa [prefixWord, tailWord_2153949, baseEnd_2153949] using wordTrace_append hprefix tailTrace_2153949
  have hstable : (prefixWord ++ tailWord_2153949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153949).length < 2 ^ (prefixWord ++ tailWord_2153949).sum := by decide
  have hdescent : baseEnd_2153949 < baseStart_2153949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2153976 : List Nat := [2, 1, 2, 1, 1, 5, 4, 2, 1, 4]
def baseStart_2153976 : Nat := 118140960795 + 2153976 * 2 ^ 59
def prefixEnd_2153976 : Nat := 4983230072969 + 3 ^ 40 * 2153976 * 2
def baseEnd_2153976 : Nat := 368675002082989930898017

theorem tailTrace_2153976 : CollatzResearch.WordTrace tailWord_2153976 prefixEnd_2153976 368675002082989930898017 := by
  unfold tailWord_2153976
  simp only [CollatzResearch.WordTrace]
  refine ⟨39280979422260148329148891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52374639229680197772198521 39280979422260148329148891)
  ·
    refine ⟨58921469133390222493723337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39280979422260148329148891 58921469133390222493723337)
    ·
      refine ⟨44191101850042666870292503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58921469133390222493723337 44191101850042666870292503)
      ·
        refine ⟨66286652775064000305438755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44191101850042666870292503 66286652775064000305438755)
        ·
          refine ⟨99429979162596000458158133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66286652775064000305438755 99429979162596000458158133)
          ·
            refine ⟨9321560546493375042952325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99429979162596000458158133 9321560546493375042952325)
            ·
              refine ⟨1747792602467507820553561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9321560546493375042952325 1747792602467507820553561)
              ·
                refine ⟨1310844451850630865415171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1747792602467507820553561 1310844451850630865415171)
                ·
                  refine ⟨1966266677775946298122757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1310844451850630865415171 1966266677775946298122757)
                  ·
                    refine ⟨368675002082989930898017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1966266677775946298122757 368675002082989930898017)
                    ·
                      rfl

theorem cell23_2153976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 1, 4].length) (baseStart_2153976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2153976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2153976 prefixEnd_2153976 := by exact prefixLift 2153976
  have htrace : WordTrace (prefixWord ++ tailWord_2153976) baseStart_2153976 baseEnd_2153976 := by
    simpa [prefixWord, tailWord_2153976, baseEnd_2153976] using wordTrace_append hprefix tailTrace_2153976
  have hstable : (prefixWord ++ tailWord_2153976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2153976).length < 2 ^ (prefixWord ++ tailWord_2153976).sum := by decide
  have hdescent : baseEnd_2153976 < baseStart_2153976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2153976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154019 : List Nat := [1, 1, 1, 4, 5, 1, 1, 3, 1, 5]
def baseStart_2154019 : Nat := 118140960795 + 2154019 * 2 ^ 59
def prefixEnd_2154019 : Nat := 4983230072969 + 3 ^ 40 * 2154019 * 2
def baseEnd_2154019 : Nat := 368682361972371041485451

theorem tailTrace_2154019 : CollatzResearch.WordTrace tailWord_2154019 prefixEnd_2154019 368682361972371041485451 := by
  unfold tailWord_2154019
  simp only [CollatzResearch.WordTrace]
  refine ⟨78563527183364515002113111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52375684788909676668075407 78563527183364515002113111)
  ·
    refine ⟨117845290775046772503169667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78563527183364515002113111 117845290775046772503169667)
    ·
      refine ⟨176767936162570158754754501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117845290775046772503169667 176767936162570158754754501)
      ·
        refine ⟨33143988030481904766516469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176767936162570158754754501 33143988030481904766516469)
        ·
          refine ⟨3107248877857678571860919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33143988030481904766516469 3107248877857678571860919)
          ·
            refine ⟨4660873316786517857791379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107248877857678571860919 4660873316786517857791379)
            ·
              refine ⟨6991309975179776786687069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4660873316786517857791379 6991309975179776786687069)
              ·
                refine ⟨2621741240692416295007651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6991309975179776786687069 2621741240692416295007651)
                ·
                  refine ⟨3932611861038624442511477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621741240692416295007651 3932611861038624442511477)
                  ·
                    refine ⟨368682361972371041485451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3932611861038624442511477 368682361972371041485451)
                    ·
                      rfl

theorem cell23_2154019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 3, 1, 5].length) (baseStart_2154019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154019 prefixEnd_2154019 := by exact prefixLift 2154019
  have htrace : WordTrace (prefixWord ++ tailWord_2154019) baseStart_2154019 baseEnd_2154019 := by
    simpa [prefixWord, tailWord_2154019, baseEnd_2154019] using wordTrace_append hprefix tailTrace_2154019
  have hstable : (prefixWord ++ tailWord_2154019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154019).length < 2 ^ (prefixWord ++ tailWord_2154019).sum := by decide
  have hdescent : baseEnd_2154019 < baseStart_2154019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154042 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_2154042 : Nat := 118140960795 + 2154042 * 2 ^ 59
def prefixEnd_2154042 : Nat := 4983230072969 + 3 ^ 40 * 2154042 * 2
def baseEnd_2154042 : Nat := 1106058895972166534468747

theorem tailTrace_2154042 : CollatzResearch.WordTrace tailWord_2154042 prefixEnd_2154042 1106058895972166534468747 := by
  unfold tailWord_2154042
  simp only [CollatzResearch.WordTrace]
  refine ⟨19641091515570297482550095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52376244041520793286800253 19641091515570297482550095)
  ·
    refine ⟨29461637273355446223825143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19641091515570297482550095 29461637273355446223825143)
    ·
      refine ⟨44192455910033169335737715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29461637273355446223825143 44192455910033169335737715)
      ·
        refine ⟨66288683865049754003606573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44192455910033169335737715 66288683865049754003606573)
        ·
          refine ⟨24858256449393657751352465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66288683865049754003606573 24858256449393657751352465)
          ·
            refine ⟨18643692337045243313514349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24858256449393657751352465 18643692337045243313514349)
            ·
              refine ⟨6991384626391966242567881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18643692337045243313514349 6991384626391966242567881)
              ·
                refine ⟨5243538469793974681925911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6991384626391966242567881 5243538469793974681925911)
                ·
                  refine ⟨7865307704690962022888867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5243538469793974681925911 7865307704690962022888867)
                  ·
                    refine ⟨11797961557036443034333301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7865307704690962022888867 11797961557036443034333301)
                    ·
                      refine ⟨1106058895972166534468747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11797961557036443034333301 1106058895972166534468747)
                      ·
                        rfl

theorem cell23_2154042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_2154042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154042 prefixEnd_2154042 := by exact prefixLift 2154042
  have htrace : WordTrace (prefixWord ++ tailWord_2154042) baseStart_2154042 baseEnd_2154042 := by
    simpa [prefixWord, tailWord_2154042, baseEnd_2154042] using wordTrace_append hprefix tailTrace_2154042
  have hstable : (prefixWord ++ tailWord_2154042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154042).length < 2 ^ (prefixWord ++ tailWord_2154042).sum := by decide
  have hdescent : baseEnd_2154042 < baseStart_2154042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154072 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 3, 3, 3]
def baseStart_2154072 : Nat := 118140960795 + 2154072 * 2 ^ 59
def prefixEnd_2154072 : Nat := 4983230072969 + 3 ^ 40 * 2154072 * 2
def baseEnd_2154072 : Nat := 1106074300391801417093609

theorem tailTrace_2154072 : CollatzResearch.WordTrace tailWord_2154072 prefixEnd_2154072 1106074300391801417093609 := by
  unfold tailWord_2154072
  simp only [CollatzResearch.WordTrace]
  refine ⟨39282730126086252526896235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52376973501448336702528313 39282730126086252526896235)
  ·
    refine ⟨58924095189129378790344353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39282730126086252526896235 58924095189129378790344353)
    ·
      refine ⟨44193071391847034092758265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58924095189129378790344353 44193071391847034092758265)
      ·
        refine ⟨33144803543885275569568699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44193071391847034092758265 33144803543885275569568699)
        ·
          refine ⟨49717205315827913354353049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33144803543885275569568699 49717205315827913354353049)
          ·
            refine ⟨37287903986870935015764787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49717205315827913354353049 37287903986870935015764787)
            ·
              refine ⟨55931855980306402523647181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37287903986870935015764787 55931855980306402523647181)
              ·
                refine ⟨20974445992614900946367693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55931855980306402523647181 20974445992614900946367693)
                ·
                  refine ⟨7865417247230587854887885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20974445992614900946367693 7865417247230587854887885)
                  ·
                    refine ⟨2949531467711470445582957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7865417247230587854887885 2949531467711470445582957)
                    ·
                      refine ⟨1106074300391801417093609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2949531467711470445582957 1106074300391801417093609)
                      ·
                        rfl

theorem cell23_2154072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_2154072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154072 prefixEnd_2154072 := by exact prefixLift 2154072
  have htrace : WordTrace (prefixWord ++ tailWord_2154072) baseStart_2154072 baseEnd_2154072 := by
    simpa [prefixWord, tailWord_2154072, baseEnd_2154072] using wordTrace_append hprefix tailTrace_2154072
  have hstable : (prefixWord ++ tailWord_2154072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154072).length < 2 ^ (prefixWord ++ tailWord_2154072).sum := by decide
  have hdescent : baseEnd_2154072 < baseStart_2154072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154076 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2154076 : Nat := 118140960795 + 2154076 * 2 ^ 59
def prefixEnd_2154076 : Nat := 4983230072969 + 3 ^ 40 * 2154076 * 2
def baseEnd_2154076 : Nat := 1106076354314419401443591

theorem tailTrace_2154076 : CollatzResearch.WordTrace tailWord_2154076 prefixEnd_2154076 1106076354314419401443591 := by
  unfold tailWord_2154076
  simp only [CollatzResearch.WordTrace]
  refine ⟨39282803072079006868469041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52377070762772009157958721 39282803072079006868469041)
  ·
    refine ⟨29462102304059255151351781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39282803072079006868469041 29462102304059255151351781)
    ·
      refine ⟨5524144182011110340878459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29462102304059255151351781 5524144182011110340878459)
      ·
        refine ⟨8286216273016665511317689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5524144182011110340878459 8286216273016665511317689)
        ·
          refine ⟨6214662204762499133488267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8286216273016665511317689 6214662204762499133488267)
          ·
            refine ⟨9321993307143748700232401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6214662204762499133488267 9321993307143748700232401)
            ·
              refine ⟨6991494980357811525174301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9321993307143748700232401 6991494980357811525174301)
              ·
                refine ⟨2621810617634179321940363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6991494980357811525174301 2621810617634179321940363)
                ·
                  refine ⟨3932715926451268982910545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2621810617634179321940363 3932715926451268982910545)
                  ·
                    refine ⟨2949536944838451737182909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3932715926451268982910545 2949536944838451737182909)
                    ·
                      refine ⟨1106076354314419401443591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2949536944838451737182909 1106076354314419401443591)
                      ·
                        rfl

theorem cell23_2154076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2154076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154076 prefixEnd_2154076 := by exact prefixLift 2154076
  have htrace : WordTrace (prefixWord ++ tailWord_2154076) baseStart_2154076 baseEnd_2154076 := by
    simpa [prefixWord, tailWord_2154076, baseEnd_2154076] using wordTrace_append hprefix tailTrace_2154076
  have hstable : (prefixWord ++ tailWord_2154076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154076).length < 2 ^ (prefixWord ++ tailWord_2154076).sum := by decide
  have hdescent : baseEnd_2154076 < baseStart_2154076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154089 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 4, 1, 3]
def baseStart_2154089 : Nat := 118140960795 + 2154089 * 2 ^ 59
def prefixEnd_2154089 : Nat := 4983230072969 + 3 ^ 40 * 2154089 * 2
def baseEnd_2154089 : Nat := 1106083029562927850581031

theorem tailTrace_2154089 : CollatzResearch.WordTrace tailWord_2154089 prefixEnd_2154089 1106083029562927850581031 := by
  unfold tailWord_2154089
  simp only [CollatzResearch.WordTrace]
  refine ⟨78566080293110916957161321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52377386862073944638107547 78566080293110916957161321)
  ·
    refine ⟨58924560219833187717870991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78566080293110916957161321 58924560219833187717870991)
    ·
      refine ⟨88386840329749781576806487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58924560219833187717870991 88386840329749781576806487)
      ·
        refine ⟨132580260494624672365209731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88386840329749781576806487 132580260494624672365209731)
        ·
          refine ⟨198870390741937008547814597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132580260494624672365209731 198870390741937008547814597)
          ·
            refine ⟨37288198264113189102715237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198870390741937008547814597 37288198264113189102715237)
            ·
              refine ⟨6991537174521222956759107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37288198264113189102715237 6991537174521222956759107)
              ·
                refine ⟨10487305761781834435138661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6991537174521222956759107 10487305761781834435138661)
                ·
                  refine ⟨1966369830334093956588499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10487305761781834435138661 1966369830334093956588499)
                  ·
                    refine ⟨2949554745501140934882749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1966369830334093956588499 2949554745501140934882749)
                    ·
                      refine ⟨1106083029562927850581031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2949554745501140934882749 1106083029562927850581031)
                      ·
                        rfl

theorem cell23_2154089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 4, 1, 3].length) (baseStart_2154089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154089 prefixEnd_2154089 := by exact prefixLift 2154089
  have htrace : WordTrace (prefixWord ++ tailWord_2154089) baseStart_2154089 baseEnd_2154089 := by
    simpa [prefixWord, tailWord_2154089, baseEnd_2154089] using wordTrace_append hprefix tailTrace_2154089
  have hstable : (prefixWord ++ tailWord_2154089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154089).length < 2 ^ (prefixWord ++ tailWord_2154089).sum := by decide
  have hdescent : baseEnd_2154089 < baseStart_2154089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154192 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 5]
def baseStart_2154192 : Nat := 118140960795 + 2154192 * 2 ^ 59
def prefixEnd_2154192 : Nat := 4983230072969 + 3 ^ 40 * 2154192 * 2
def baseEnd_2154192 : Nat := 1106135918070340947593057

theorem tailTrace_2154192 : CollatzResearch.WordTrace tailWord_2154192 prefixEnd_2154192 1106135918070340947593057 := by
  unfold tailWord_2154192
  simp only [CollatzResearch.WordTrace]
  refine ⟨39284918505868882774080415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52379891341158510365440553 39284918505868882774080415)
  ·
    refine ⟨58927377758803324161120623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39284918505868882774080415 58927377758803324161120623)
    ·
      refine ⟨88391066638204986241680935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58927377758803324161120623 88391066638204986241680935)
      ·
        refine ⟨132586599957307479362521403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88391066638204986241680935 132586599957307479362521403)
        ·
          refine ⟨198879899935961219043782105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132586599957307479362521403 198879899935961219043782105)
          ·
            refine ⟨149159924951970914282836579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198879899935961219043782105 149159924951970914282836579)
            ·
              refine ⟨223739887427956371424254869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149159924951970914282836579 223739887427956371424254869)
              ·
                refine ⟨10487807223185454910511947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 223739887427956371424254869 10487807223185454910511947)
                ·
                  refine ⟨15731710834778182365767921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10487807223185454910511947 15731710834778182365767921)
                  ·
                    refine ⟨11798783126083636774325941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15731710834778182365767921 11798783126083636774325941)
                    ·
                      refine ⟨1106135918070340947593057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11798783126083636774325941 1106135918070340947593057)
                      ·
                        rfl

theorem cell23_2154192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 5].length) (baseStart_2154192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154192 prefixEnd_2154192 := by exact prefixLift 2154192
  have htrace : WordTrace (prefixWord ++ tailWord_2154192) baseStart_2154192 baseEnd_2154192 := by
    simpa [prefixWord, tailWord_2154192, baseEnd_2154192] using wordTrace_append hprefix tailTrace_2154192
  have hstable : (prefixWord ++ tailWord_2154192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154192).length < 2 ^ (prefixWord ++ tailWord_2154192).sum := by decide
  have hdescent : baseEnd_2154192 < baseStart_2154192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154196 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2154196 : Nat := 118140960795 + 2154196 * 2 ^ 59
def prefixEnd_2154196 : Nat := 4983230072969 + 3 ^ 40 * 2154196 * 2
def baseEnd_2154196 : Nat := 1106137971992958931943039

theorem tailTrace_2154196 : CollatzResearch.WordTrace tailWord_2154196 prefixEnd_2154196 1106137971992958931943039 := by
  unfold tailWord_2154196
  simp only [CollatzResearch.WordTrace]
  refine ⟨39284991451861637115653221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52379988602482182820870961 39284991451861637115653221)
  ·
    refine ⟨7365935897224056959184979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39284991451861637115653221 7365935897224056959184979)
    ·
      refine ⟨11048903845836085438777469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7365935897224056959184979 11048903845836085438777469)
      ·
        refine ⟨4143338942188532039541551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11048903845836085438777469 4143338942188532039541551)
        ·
          refine ⟨6215008413282798059312327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4143338942188532039541551 6215008413282798059312327)
          ·
            refine ⟨9322512619924197088968491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6215008413282798059312327 9322512619924197088968491)
            ·
              refine ⟨13983768929886295633452737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9322512619924197088968491 13983768929886295633452737)
              ·
                refine ⟨10487826697414721725089553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13983768929886295633452737 10487826697414721725089553)
                ·
                  refine ⟨7865870023061041293817165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10487826697414721725089553 7865870023061041293817165)
                  ·
                    refine ⟨2949701258647890485181437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7865870023061041293817165 2949701258647890485181437)
                    ·
                      refine ⟨1106137971992958931943039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2949701258647890485181437 1106137971992958931943039)
                      ·
                        rfl

theorem cell23_2154196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2154196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154196 prefixEnd_2154196 := by exact prefixLift 2154196
  have htrace : WordTrace (prefixWord ++ tailWord_2154196) baseStart_2154196 baseEnd_2154196 := by
    simpa [prefixWord, tailWord_2154196, baseEnd_2154196] using wordTrace_append hprefix tailTrace_2154196
  have hstable : (prefixWord ++ tailWord_2154196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154196).length < 2 ^ (prefixWord ++ tailWord_2154196).sum := by decide
  have hdescent : baseEnd_2154196 < baseStart_2154196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154232 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 1, 3, 6]
def baseStart_2154232 : Nat := 118140960795 + 2154232 * 2 ^ 59
def prefixEnd_2154232 : Nat := 4983230072969 + 3 ^ 40 * 2154232 * 2
def baseEnd_2154232 : Nat := 1106156457296520791092873

theorem tailTrace_2154232 : CollatzResearch.WordTrace tailWord_2154232 prefixEnd_2154232 1106156457296520791092873 := by
  unfold tailWord_2154232
  simp only [CollatzResearch.WordTrace]
  refine ⟨39285647965796426189808475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52380863954395234919744633 39285647965796426189808475)
  ·
    refine ⟨58928471948694639284712713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39285647965796426189808475 58928471948694639284712713)
    ·
      refine ⟨44196353961520979463534535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58928471948694639284712713 44196353961520979463534535)
      ·
        refine ⟨66294530942281469195301803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44196353961520979463534535 66294530942281469195301803)
        ·
          refine ⟨99441796413422203792952705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66294530942281469195301803 99441796413422203792952705)
          ·
            refine ⟨74581347310066652844714529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99441796413422203792952705 74581347310066652844714529)
            ·
              refine ⟨55936010482549989633535897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74581347310066652844714529 55936010482549989633535897)
              ·
                refine ⟨41952007861912492225151923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55936010482549989633535897 41952007861912492225151923)
                ·
                  refine ⟨62928011792868738337727885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41952007861912492225151923 62928011792868738337727885)
                  ·
                    refine ⟨23598004422325776876647957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62928011792868738337727885 23598004422325776876647957)
                    ·
                      refine ⟨1106156457296520791092873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23598004422325776876647957 1106156457296520791092873)
                      ·
                        rfl

theorem cell23_2154232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_2154232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154232 prefixEnd_2154232 := by exact prefixLift 2154232
  have htrace : WordTrace (prefixWord ++ tailWord_2154232) baseStart_2154232 baseEnd_2154232 := by
    simpa [prefixWord, tailWord_2154232, baseEnd_2154232] using wordTrace_append hprefix tailTrace_2154232
  have hstable : (prefixWord ++ tailWord_2154232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154232).length < 2 ^ (prefixWord ++ tailWord_2154232).sum := by decide
  have hdescent : baseEnd_2154232 < baseStart_2154232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154239 : List Nat := [1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 3]
def baseStart_2154239 : Nat := 118140960795 + 2154239 * 2 ^ 59
def prefixEnd_2154239 : Nat := 4983230072969 + 3 ^ 40 * 2154239 * 2
def baseEnd_2154239 : Nat := 1106160051661102263705341

theorem tailTrace_2154239 : CollatzResearch.WordTrace tailWord_2154239 prefixEnd_2154239 1106160051661102263705341 := by
  unfold tailWord_2154239
  simp only [CollatzResearch.WordTrace]
  refine ⟨78571551242567492575121771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52381034161711661716747847 78571551242567492575121771)
  ·
    refine ⟨117857326863851238862682657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78571551242567492575121771 117857326863851238862682657)
    ·
      refine ⟨88392995147888429147011993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117857326863851238862682657 88392995147888429147011993)
      ·
        refine ⟨66294746360916321860258995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88392995147888429147011993 66294746360916321860258995)
        ·
          refine ⟨99442119541374482790388493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66294746360916321860258995 99442119541374482790388493)
          ·
            refine ⟨37290794828015431046395685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99442119541374482790388493 37290794828015431046395685)
            ·
              refine ⟨6992024030252893321199191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37290794828015431046395685 6992024030252893321199191)
              ·
                refine ⟨10488036045379339981798787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6992024030252893321199191 10488036045379339981798787)
                ·
                  refine ⟨15732054068069009972698181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10488036045379339981798787 15732054068069009972698181)
                  ·
                    refine ⟨2949760137762939369880909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15732054068069009972698181 2949760137762939369880909)
                    ·
                      refine ⟨1106160051661102263705341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2949760137762939369880909 1106160051661102263705341)
                      ·
                        rfl

theorem cell23_2154239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_2154239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154239 prefixEnd_2154239 := by exact prefixLift 2154239
  have htrace : WordTrace (prefixWord ++ tailWord_2154239) baseStart_2154239 baseEnd_2154239 := by
    simpa [prefixWord, tailWord_2154239, baseEnd_2154239] using wordTrace_append hprefix tailTrace_2154239
  have hstable : (prefixWord ++ tailWord_2154239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154239).length < 2 ^ (prefixWord ++ tailWord_2154239).sum := by decide
  have hdescent : baseEnd_2154239 < baseStart_2154239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154260 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2154260 : Nat := 118140960795 + 2154260 * 2 ^ 59
def prefixEnd_2154260 : Nat := 4983230072969 + 3 ^ 40 * 2154260 * 2
def baseEnd_2154260 : Nat := 1106170834754846681542745

theorem tailTrace_2154260 : CollatzResearch.WordTrace tailWord_2154260 prefixEnd_2154260 1106170834754846681542745 := by
  unfold tailWord_2154260
  simp only [CollatzResearch.WordTrace]
  refine ⟨39286158587745706580818117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52381544783660942107757489 39286158587745706580818117)
  ·
    refine ⟨7366154735202319983903397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39286158587745706580818117 7366154735202319983903397)
    ·
      refine ⟨1381154012850434996981887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7366154735202319983903397 1381154012850434996981887)
      ·
        refine ⟨2071731019275652495472831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381154012850434996981887 2071731019275652495472831)
        ·
          refine ⟨3107596528913478743209247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071731019275652495472831 3107596528913478743209247)
          ·
            refine ⟨4661394793370218114813871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3107596528913478743209247 4661394793370218114813871)
            ·
              refine ⟨6992092190055327172220807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4661394793370218114813871 6992092190055327172220807)
              ·
                refine ⟨10488138285082990758331211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6992092190055327172220807 10488138285082990758331211)
                ·
                  refine ⟨15732207427624486137496817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10488138285082990758331211 15732207427624486137496817)
                  ·
                    refine ⟨11799155570718364603122613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15732207427624486137496817 11799155570718364603122613)
                    ·
                      refine ⟨1106170834754846681542745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11799155570718364603122613 1106170834754846681542745)
                      ·
                        rfl

theorem cell23_2154260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2154260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154260 prefixEnd_2154260 := by exact prefixLift 2154260
  have htrace : WordTrace (prefixWord ++ tailWord_2154260) baseStart_2154260 baseEnd_2154260 := by
    simpa [prefixWord, tailWord_2154260, baseEnd_2154260] using wordTrace_append hprefix tailTrace_2154260
  have hstable : (prefixWord ++ tailWord_2154260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154260).length < 2 ^ (prefixWord ++ tailWord_2154260).sum := by decide
  have hdescent : baseEnd_2154260 < baseStart_2154260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154263 : List Nat := [1, 1, 3, 4, 2, 3, 1, 1, 3, 4]
def baseStart_2154263 : Nat := 118140960795 + 2154263 * 2 ^ 59
def prefixEnd_2154263 : Nat := 4983230072969 + 3 ^ 40 * 2154263 * 2
def baseEnd_2154263 : Nat := 368724125065603389935077

theorem tailTrace_2154263 : CollatzResearch.WordTrace tailWord_2154263 prefixEnd_2154263 368724125065603389935077 := by
  unfold tailWord_2154263
  simp only [CollatzResearch.WordTrace]
  refine ⟨78572426594480544673995443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52381617729653696449330295 78572426594480544673995443)
  ·
    refine ⟨117858639891720817010993165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78572426594480544673995443 117858639891720817010993165)
    ·
      refine ⟨44196989959395306379122437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117858639891720817010993165 44196989959395306379122437)
      ·
        refine ⟨8286935617386619946085457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44196989959395306379122437 8286935617386619946085457)
        ·
          refine ⟨6215201713039964959564093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8286935617386619946085457 6215201713039964959564093)
          ·
            refine ⟨2330700642389986859836535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6215201713039964959564093 2330700642389986859836535)
            ·
              refine ⟨3496050963584980289754803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2330700642389986859836535 3496050963584980289754803)
              ·
                refine ⟨5244076445377470434632205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496050963584980289754803 5244076445377470434632205)
                ·
                  refine ⟨1966528667016551412987077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5244076445377470434632205 1966528667016551412987077)
                  ·
                    refine ⟨368724125065603389935077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1966528667016551412987077 368724125065603389935077)
                    ·
                      rfl

theorem cell23_2154263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 4].length) (baseStart_2154263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154263 prefixEnd_2154263 := by exact prefixLift 2154263
  have htrace : WordTrace (prefixWord ++ tailWord_2154263) baseStart_2154263 baseEnd_2154263 := by
    simpa [prefixWord, tailWord_2154263, baseEnd_2154263] using wordTrace_append hprefix tailTrace_2154263
  have hstable : (prefixWord ++ tailWord_2154263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154263).length < 2 ^ (prefixWord ++ tailWord_2154263).sum := by decide
  have hdescent : baseEnd_2154263 < baseStart_2154263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154276 : List Nat := [2, 3, 1, 3, 2, 2, 1, 3, 6]
def baseStart_2154276 : Nat := 118140960795 + 2154276 * 2 ^ 59
def prefixEnd_2154276 : Nat := 4983230072969 + 3 ^ 40 * 2154276 * 2
def baseEnd_2154276 : Nat := 122908783382813179882519

theorem tailTrace_2154276 : CollatzResearch.WordTrace tailWord_2154276 prefixEnd_2154276 122908783382813179882519 := by
  unfold tailWord_2154276
  simp only [CollatzResearch.WordTrace]
  refine ⟨39286450371716723947109341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52381933828955631929479121 39286450371716723947109341)
  ·
    refine ⟨14732418889393771480166003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39286450371716723947109341 14732418889393771480166003)
    ·
      refine ⟨22098628334090657220249005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14732418889393771480166003 22098628334090657220249005)
      ·
        refine ⟨8286985625283996457593377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22098628334090657220249005 8286985625283996457593377)
        ·
          refine ⟨6215239218962997343195033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8286985625283996457593377 6215239218962997343195033)
          ·
            refine ⟨4661429414222248007396275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6215239218962997343195033 4661429414222248007396275)
            ·
              refine ⟨6992144121333372011094413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4661429414222248007396275 6992144121333372011094413)
              ·
                refine ⟨2622054045500014504160405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6992144121333372011094413 2622054045500014504160405)
                ·
                  refine ⟨122908783382813179882519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2622054045500014504160405 122908783382813179882519)
                  ·
                    rfl

theorem cell23_2154276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_2154276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154276 prefixEnd_2154276 := by exact prefixLift 2154276
  have htrace : WordTrace (prefixWord ++ tailWord_2154276) baseStart_2154276 baseEnd_2154276 := by
    simpa [prefixWord, tailWord_2154276, baseEnd_2154276] using wordTrace_append hprefix tailTrace_2154276
  have hstable : (prefixWord ++ tailWord_2154276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154276).length < 2 ^ (prefixWord ++ tailWord_2154276).sum := by decide
  have hdescent : baseEnd_2154276 < baseStart_2154276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154310 : List Nat := [6, 1, 1, 2, 1, 2, 2, 2, 6]
def baseStart_2154310 : Nat := 118140960795 + 2154310 * 2 ^ 59
def prefixEnd_2154310 : Nat := 4983230072969 + 3 ^ 40 * 2154310 * 2
def baseEnd_2154310 : Nat := 122910723198619053990835

theorem tailTrace_2154310 : CollatzResearch.WordTrace tailWord_2154310 prefixEnd_2154310 122910723198619053990835 := by
  unfold tailWord_2154310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2455441900790945990654887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52382760550206847800637589 2455441900790945990654887)
  ·
    refine ⟨3683162851186418985982331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2455441900790945990654887 3683162851186418985982331)
    ·
      refine ⟨5524744276779628478973497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3683162851186418985982331 5524744276779628478973497)
      ·
        refine ⟨4143558207584721359230123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5524744276779628478973497 4143558207584721359230123)
        ·
          refine ⟨6215337311377082038845185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4143558207584721359230123 6215337311377082038845185)
          ·
            refine ⟨4661502983532811529133889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6215337311377082038845185 4661502983532811529133889)
            ·
              refine ⟨3496127237649608646850417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4661502983532811529133889 3496127237649608646850417)
              ·
                refine ⟨2622095428237206485137813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3496127237649608646850417 2622095428237206485137813)
                ·
                  refine ⟨122910723198619053990835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2622095428237206485137813 122910723198619053990835)
                  ·
                    rfl

theorem cell23_2154310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_2154310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154310 prefixEnd_2154310 := by exact prefixLift 2154310
  have htrace : WordTrace (prefixWord ++ tailWord_2154310) baseStart_2154310 baseEnd_2154310 := by
    simpa [prefixWord, tailWord_2154310, baseEnd_2154310] using wordTrace_append hprefix tailTrace_2154310
  have hstable : (prefixWord ++ tailWord_2154310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154310).length < 2 ^ (prefixWord ++ tailWord_2154310).sum := by decide
  have hdescent : baseEnd_2154310 < baseStart_2154310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154329 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 5]
def baseStart_2154329 : Nat := 118140960795 + 2154329 * 2 ^ 59
def prefixEnd_2154329 : Nat := 4983230072969 + 3 ^ 40 * 2154329 * 2
def baseEnd_2154329 : Nat := 1106206264920006911579927

theorem tailTrace_2154329 : CollatzResearch.WordTrace tailWord_2154329 prefixEnd_2154329 1106206264920006911579927 := by
  unfold tailWord_2154329
  simp only [CollatzResearch.WordTrace]
  refine ⟨78574833812241437945898041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52383222541494291963932027 78574833812241437945898041)
  ·
    refine ⟨58931125359181078459423531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78574833812241437945898041 58931125359181078459423531)
    ·
      refine ⟨88396688038771617689135297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58931125359181078459423531 88396688038771617689135297)
      ·
        refine ⟨66297516029078713266851473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88396688038771617689135297 66297516029078713266851473)
        ·
          refine ⟨49723137021809034950138605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66297516029078713266851473 49723137021809034950138605)
          ·
            refine ⟨18646176383178388106301977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49723137021809034950138605 18646176383178388106301977)
            ·
              refine ⟨13984632287383791079726483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18646176383178388106301977 13984632287383791079726483)
              ·
                refine ⟨20976948431075686619589725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13984632287383791079726483 20976948431075686619589725)
                ·
                  refine ⟨7866355661653382482346147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20976948431075686619589725 7866355661653382482346147)
                  ·
                    refine ⟨11799533492480073723519221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7866355661653382482346147 11799533492480073723519221)
                    ·
                      refine ⟨1106206264920006911579927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11799533492480073723519221 1106206264920006911579927)
                      ·
                        rfl

theorem cell23_2154329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_2154329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154329 prefixEnd_2154329 := by exact prefixLift 2154329
  have htrace : WordTrace (prefixWord ++ tailWord_2154329) baseStart_2154329 baseEnd_2154329 := by
    simpa [prefixWord, tailWord_2154329, baseEnd_2154329] using wordTrace_append hprefix tailTrace_2154329
  have hstable : (prefixWord ++ tailWord_2154329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154329).length < 2 ^ (prefixWord ++ tailWord_2154329).sum := by decide
  have hdescent : baseEnd_2154329 < baseStart_2154329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154336 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 1, 6]
def baseStart_2154336 : Nat := 118140960795 + 2154336 * 2 ^ 59
def prefixEnd_2154336 : Nat := 4983230072969 + 3 ^ 40 * 2154336 * 2
def baseEnd_2154336 : Nat := 368736619761529461397465

theorem tailTrace_2154336 : CollatzResearch.WordTrace tailWord_2154336 prefixEnd_2154336 368736619761529461397465 := by
  unfold tailWord_2154336
  simp only [CollatzResearch.WordTrace]
  refine ⟨39287544561608039070701431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52383392748810718760935241 39287544561608039070701431)
  ·
    refine ⟨58931316842412058606052147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39287544561608039070701431 58931316842412058606052147)
    ·
      refine ⟨88396975263618087909078221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58931316842412058606052147 88396975263618087909078221)
      ·
        refine ⟨33148865723856782965904333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88396975263618087909078221 33148865723856782965904333)
        ·
          refine ⟨12430824646446293612214125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33148865723856782965904333 12430824646446293612214125)
          ·
            refine ⟨4661559242417360104580297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12430824646446293612214125 4661559242417360104580297)
            ·
              refine ⟨3496169431813020078435223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4661559242417360104580297 3496169431813020078435223)
              ·
                refine ⟨5244254147719530117652835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496169431813020078435223 5244254147719530117652835)
                ·
                  refine ⟨7866381221579295176479253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5244254147719530117652835 7866381221579295176479253)
                  ·
                    refine ⟨368736619761529461397465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7866381221579295176479253 368736619761529461397465)
                    ·
                      rfl

theorem cell23_2154336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 1, 6].length) (baseStart_2154336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154336 prefixEnd_2154336 := by exact prefixLift 2154336
  have htrace : WordTrace (prefixWord ++ tailWord_2154336) baseStart_2154336 baseEnd_2154336 := by
    simpa [prefixWord, tailWord_2154336, baseEnd_2154336] using wordTrace_append hprefix tailTrace_2154336
  have hstable : (prefixWord ++ tailWord_2154336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154336).length < 2 ^ (prefixWord ++ tailWord_2154336).sum := by decide
  have hdescent : baseEnd_2154336 < baseStart_2154336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154349 : List Nat := [1, 5, 1, 1, 1, 1, 2, 11]
def baseStart_2154349 : Nat := 118140960795 + 2154349 * 2 ^ 59
def prefixEnd_2154349 : Nat := 4983230072969 + 3 ^ 40 * 2154349 * 2
def baseEnd_2154349 : Nat := 40970982760485067901105

theorem tailTrace_2154349 : CollatzResearch.WordTrace tailWord_2154349 prefixEnd_2154349 40970982760485067901105 := by
  unfold tailWord_2154349
  simp only [CollatzResearch.WordTrace]
  refine ⟨78575563272168981361626101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52383708848112654241084067 78575563272168981361626101)
  ·
    refine ⟨7366459056765842002652447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78575563272168981361626101 7366459056765842002652447)
    ·
      refine ⟨11049688585148763003978671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7366459056765842002652447 11049688585148763003978671)
      ·
        refine ⟨16574532877723144505968007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11049688585148763003978671 16574532877723144505968007)
        ·
          refine ⟨24861799316584716758952011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16574532877723144505968007 24861799316584716758952011)
          ·
            refine ⟨37292698974877075138428017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24861799316584716758952011 37292698974877075138428017)
            ·
              refine ⟨27969524231157806353821013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37292698974877075138428017 27969524231157806353821013)
              ·
                refine ⟨40970982760485067901105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 27969524231157806353821013 40970982760485067901105)
                ·
                  rfl

theorem cell23_2154349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 11].length) (baseStart_2154349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154349 prefixEnd_2154349 := by exact prefixLift 2154349
  have htrace : WordTrace (prefixWord ++ tailWord_2154349) baseStart_2154349 baseEnd_2154349 := by
    simpa [prefixWord, tailWord_2154349, baseEnd_2154349] using wordTrace_append hprefix tailTrace_2154349
  have hstable : (prefixWord ++ tailWord_2154349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154349).length < 2 ^ (prefixWord ++ tailWord_2154349).sum := by decide
  have hdescent : baseEnd_2154349 < baseStart_2154349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154393 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 2, 1, 3]
def baseStart_2154393 : Nat := 118140960795 + 2154393 * 2 ^ 59
def prefixEnd_2154393 : Nat := 4983230072969 + 3 ^ 40 * 2154393 * 2
def baseEnd_2154393 : Nat := 1106239127681894661179633

theorem tailTrace_2154393 : CollatzResearch.WordTrace tailWord_2154393 prefixEnd_2154393 1106239127681894661179633 := by
  unfold tailWord_2154393
  simp only [CollatzResearch.WordTrace]
  refine ⟨78577168084009576876227833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52384778722673051250818555 78577168084009576876227833)
  ·
    refine ⟨58932876063007182657170875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78577168084009576876227833 58932876063007182657170875)
    ·
      refine ⟨88399314094510773985756313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58932876063007182657170875 88399314094510773985756313)
      ·
        refine ⟨66299485570883080489317235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88399314094510773985756313 66299485570883080489317235)
        ·
          refine ⟨99449228356324620733975853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66299485570883080489317235 99449228356324620733975853)
          ·
            refine ⟨37293460633621732775240945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99449228356324620733975853 37293460633621732775240945)
            ·
              refine ⟨27970095475216299581430709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37293460633621732775240945 27970095475216299581430709)
              ·
                refine ⟨2622196450801528085759129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27970095475216299581430709 2622196450801528085759129)
                ·
                  refine ⟨1966647338101146064319347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2622196450801528085759129 1966647338101146064319347)
                  ·
                    refine ⟨2949971007151719096479021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1966647338101146064319347 2949971007151719096479021)
                    ·
                      refine ⟨1106239127681894661179633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2949971007151719096479021 1106239127681894661179633)
                      ·
                        rfl

theorem cell23_2154393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_2154393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154393 prefixEnd_2154393 := by exact prefixLift 2154393
  have htrace : WordTrace (prefixWord ++ tailWord_2154393) baseStart_2154393 baseEnd_2154393 := by
    simpa [prefixWord, tailWord_2154393, baseEnd_2154393] using wordTrace_append hprefix tailTrace_2154393
  have hstable : (prefixWord ++ tailWord_2154393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154393).length < 2 ^ (prefixWord ++ tailWord_2154393).sum := by decide
  have hdescent : baseEnd_2154393 < baseStart_2154393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154409 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 4, 6]
def baseStart_2154409 : Nat := 118140960795 + 2154409 * 2 ^ 59
def prefixEnd_2154409 : Nat := 4983230072969 + 3 ^ 40 * 2154409 * 2
def baseEnd_2154409 : Nat := 368749114457455532859853

theorem tailTrace_2154409 : CollatzResearch.WordTrace tailWord_2154409 prefixEnd_2154409 368749114457455532859853 := by
  unfold tailWord_2154409
  simp only [CollatzResearch.WordTrace]
  refine ⟨78577751651951611608810281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52385167767967741072540187 78577751651951611608810281)
  ·
    refine ⟨58933313738963708706607711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78577751651951611608810281 58933313738963708706607711)
    ·
      refine ⟨88399970608445563059911567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58933313738963708706607711 88399970608445563059911567)
      ·
        refine ⟨132599955912668344589867351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88399970608445563059911567 132599955912668344589867351)
        ·
          refine ⟨198899933869002516884801027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132599955912668344589867351 198899933869002516884801027)
          ·
            refine ⟨298349900803503775327201541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198899933869002516884801027 298349900803503775327201541)
            ·
              refine ⟨55940606400656957873850289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 298349900803503775327201541 55940606400656957873850289)
              ·
                refine ⟨41955454800492718405387717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55940606400656957873850289 41955454800492718405387717)
                ·
                  refine ⟨7866647775092384701010197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41955454800492718405387717 7866647775092384701010197)
                  ·
                    refine ⟨368749114457455532859853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7866647775092384701010197 368749114457455532859853)
                    ·
                      rfl

theorem cell23_2154409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_2154409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154409 prefixEnd_2154409 := by exact prefixLift 2154409
  have htrace : WordTrace (prefixWord ++ tailWord_2154409) baseStart_2154409 baseEnd_2154409 := by
    simpa [prefixWord, tailWord_2154409, baseEnd_2154409] using wordTrace_append hprefix tailTrace_2154409
  have hstable : (prefixWord ++ tailWord_2154409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154409).length < 2 ^ (prefixWord ++ tailWord_2154409).sum := by decide
  have hdescent : baseEnd_2154409 < baseStart_2154409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154446 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4]
def baseStart_2154446 : Nat := 118140960795 + 2154446 * 2 ^ 59
def prefixEnd_2154446 : Nat := 4983230072969 + 3 ^ 40 * 2154446 * 2
def baseEnd_2154446 : Nat := 1106266342156582953816889

theorem tailTrace_2154446 : CollatzResearch.WordTrace tailWord_2154446 prefixEnd_2154446 1106266342156582953816889 := by
  unfold tailWord_2154446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9822387644102195865988399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52386067435211711285271461 9822387644102195865988399)
  ·
    refine ⟨14733581466153293798982599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9822387644102195865988399 14733581466153293798982599)
    ·
      refine ⟨22100372199229940698473899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14733581466153293798982599 22100372199229940698473899)
      ·
        refine ⟨33150558298844911047710849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22100372199229940698473899 33150558298844911047710849)
        ·
          refine ⟨24862918724133683285783137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33150558298844911047710849 24862918724133683285783137)
          ·
            refine ⟨18647189043100262464337353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24862918724133683285783137 18647189043100262464337353)
            ·
              refine ⟨13985391782325196848253015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18647189043100262464337353 13985391782325196848253015)
              ·
                refine ⟨20978087673487795272379523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13985391782325196848253015 20978087673487795272379523)
                ·
                  refine ⟨31467131510231692908569285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20978087673487795272379523 31467131510231692908569285)
                  ·
                    refine ⟨5900087158168442420356741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31467131510231692908569285 5900087158168442420356741)
                    ·
                      refine ⟨1106266342156582953816889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5900087158168442420356741 1106266342156582953816889)
                      ·
                        rfl

theorem cell23_2154446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_2154446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154446 prefixEnd_2154446 := by exact prefixLift 2154446
  have htrace : WordTrace (prefixWord ++ tailWord_2154446) baseStart_2154446 baseEnd_2154446 := by
    simpa [prefixWord, tailWord_2154446, baseEnd_2154446] using wordTrace_append hprefix tailTrace_2154446
  have hstable : (prefixWord ++ tailWord_2154446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154446).length < 2 ^ (prefixWord ++ tailWord_2154446).sum := by decide
  have hdescent : baseEnd_2154446 < baseStart_2154446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154493 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 2, 5, 2]
def baseStart_2154493 : Nat := 118140960795 + 2154493 * 2 ^ 59
def prefixEnd_2154493 : Nat := 4983230072969 + 3 ^ 40 * 2154493 * 2
def baseEnd_2154493 : Nat := 1106290475747344269929173

theorem tailTrace_2154493 : CollatzResearch.WordTrace tailWord_2154493 prefixEnd_2154493 1106290475747344269929173 := by
  unfold tailWord_2154493
  simp only [CollatzResearch.WordTrace]
  refine ⟨78580815383647293954868133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52387210255764862636578755 78580815383647293954868133)
  ·
    refine ⟨14733902884433867616537775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78580815383647293954868133 14733902884433867616537775)
    ·
      refine ⟨22100854326650801424806663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14733902884433867616537775 22100854326650801424806663)
      ·
        refine ⟨33151281489976202137209995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22100854326650801424806663 33151281489976202137209995)
        ·
          refine ⟨49726922234964303205814993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33151281489976202137209995 49726922234964303205814993)
          ·
            refine ⟨37295191676223227404361245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49726922234964303205814993 37295191676223227404361245)
            ·
              refine ⟨13985696878583710276635467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37295191676223227404361245 13985696878583710276635467)
              ·
                refine ⟨20978545317875565414953201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13985696878583710276635467 20978545317875565414953201)
                ·
                  refine ⟨15733908988406674061214901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20978545317875565414953201 15733908988406674061214901)
                  ·
                    refine ⟨1475053967663125693238897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15733908988406674061214901 1475053967663125693238897)
                    ·
                      refine ⟨1106290475747344269929173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475053967663125693238897 1106290475747344269929173)
                      ·
                        rfl

theorem cell23_2154493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_2154493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154493 prefixEnd_2154493 := by exact prefixLift 2154493
  have htrace : WordTrace (prefixWord ++ tailWord_2154493) baseStart_2154493 baseEnd_2154493 := by
    simpa [prefixWord, tailWord_2154493, baseEnd_2154493] using wordTrace_append hprefix tailTrace_2154493
  have hstable : (prefixWord ++ tailWord_2154493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154493).length < 2 ^ (prefixWord ++ tailWord_2154493).sum := by decide
  have hdescent : baseEnd_2154493 < baseStart_2154493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154607 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 3, 1, 3]
def baseStart_2154607 : Nat := 118140960795 + 2154607 * 2 ^ 59
def prefixEnd_2154607 : Nat := 4983230072969 + 3 ^ 40 * 2154607 * 2
def baseEnd_2154607 : Nat := 1106349012541956823903649

theorem tailTrace_2154607 : CollatzResearch.WordTrace tailWord_2154607 prefixEnd_2154607 1106349012541956823903649 := by
  unfold tailWord_2154607
  simp only [CollatzResearch.WordTrace]
  refine ⟨78584973305234291424518075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52389982203489527616345383 78584973305234291424518075)
  ·
    refine ⟨117877459957851437136777113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78584973305234291424518075 117877459957851437136777113)
    ·
      refine ⟨88408094968388577852582835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117877459957851437136777113 88408094968388577852582835)
      ·
        refine ⟨132612142452582866778874253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88408094968388577852582835 132612142452582866778874253)
        ·
          refine ⟨49729553419718575042077845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132612142452582866778874253 49729553419718575042077845)
          ·
            refine ⟨2331072816549308205097399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 49729553419718575042077845 2331072816549308205097399)
            ·
              refine ⟨3496609224823962307646099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331072816549308205097399 3496609224823962307646099)
              ·
                refine ⟨5244913837235943461469149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496609224823962307646099 5244913837235943461469149)
                ·
                  refine ⟨1966842688963478798050931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5244913837235943461469149 1966842688963478798050931)
                  ·
                    refine ⟨2950264033445218197076397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1966842688963478798050931 2950264033445218197076397)
                    ·
                      refine ⟨1106349012541956823903649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2950264033445218197076397 1106349012541956823903649)
                      ·
                        rfl

theorem cell23_2154607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 1, 3].length) (baseStart_2154607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154607 prefixEnd_2154607 := by exact prefixLift 2154607
  have htrace : WordTrace (prefixWord ++ tailWord_2154607) baseStart_2154607 baseEnd_2154607 := by
    simpa [prefixWord, tailWord_2154607, baseEnd_2154607] using wordTrace_append hprefix tailTrace_2154607
  have hstable : (prefixWord ++ tailWord_2154607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154607).length < 2 ^ (prefixWord ++ tailWord_2154607).sum := by decide
  have hdescent : baseEnd_2154607 < baseStart_2154607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154657 : List Nat := [1, 2, 3, 3, 1, 3, 2, 2, 2, 4]
def baseStart_2154657 : Nat := 118140960795 + 2154657 * 2 ^ 59
def prefixEnd_2154657 : Nat := 4983230072969 + 3 ^ 40 * 2154657 * 2
def baseEnd_2154657 : Nat := 368791562191560542759473

theorem tailTrace_2154657 : CollatzResearch.WordTrace tailWord_2154657 prefixEnd_2154657 368791562191560542759473 := by
  unfold tailWord_2154657
  simp only [CollatzResearch.WordTrace]
  refine ⟨78586796955053149963838225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52391197970035433309225483 78586796955053149963838225)
  ·
    refine ⟨58940097716289862472878669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78586796955053149963838225 58940097716289862472878669)
    ·
      refine ⟨22102536643608698427329501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58940097716289862472878669 22102536643608698427329501)
      ·
        refine ⟨8288451241353261910248563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22102536643608698427329501 8288451241353261910248563)
        ·
          refine ⟨12432676862029892865372845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8288451241353261910248563 12432676862029892865372845)
          ·
            refine ⟨4662253823261209824514817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12432676862029892865372845 4662253823261209824514817)
            ·
              refine ⟨3496690367445907368386113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4662253823261209824514817 3496690367445907368386113)
              ·
                refine ⟨2622517775584430526289585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3496690367445907368386113 2622517775584430526289585)
                ·
                  refine ⟨1966888331688322894717189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2622517775584430526289585 1966888331688322894717189)
                  ·
                    refine ⟨368791562191560542759473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1966888331688322894717189 368791562191560542759473)
                    ·
                      rfl

theorem cell23_2154657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_2154657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154657 prefixEnd_2154657 := by exact prefixLift 2154657
  have htrace : WordTrace (prefixWord ++ tailWord_2154657) baseStart_2154657 baseEnd_2154657 := by
    simpa [prefixWord, tailWord_2154657, baseEnd_2154657] using wordTrace_append hprefix tailTrace_2154657
  have hstable : (prefixWord ++ tailWord_2154657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154657).length < 2 ^ (prefixWord ++ tailWord_2154657).sum := by decide
  have hdescent : baseEnd_2154657 < baseStart_2154657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154658 : List Nat := [3, 3, 1, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_2154658 : Nat := 118140960795 + 2154658 * 2 ^ 59
def prefixEnd_2154658 : Nat := 4983230072969 + 3 ^ 40 * 2154658 * 2
def baseEnd_2154658 : Nat := 1106375200055336124365915

theorem tailTrace_2154658 : CollatzResearch.WordTrace tailWord_2154658 prefixEnd_2154658 1106375200055336124365915 := by
  unfold tailWord_2154658
  simp only [CollatzResearch.WordTrace]
  refine ⟨19646708357012381783656157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52391222285366351423083085 19646708357012381783656157)
  ·
    refine ⟨7367515633879643168871059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19646708357012381783656157 7367515633879643168871059)
    ·
      refine ⟨11051273450819464753306589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7367515633879643168871059 11051273450819464753306589)
      ·
        refine ⟨4144227544057299282489971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11051273450819464753306589 4144227544057299282489971)
        ·
          refine ⟨6216341316085948923734957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4144227544057299282489971 6216341316085948923734957)
          ·
            refine ⟨2331127993532230846400609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6216341316085948923734957 2331127993532230846400609)
            ·
              refine ⟨1748345995149173134800457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2331127993532230846400609 1748345995149173134800457)
              ·
                refine ⟨1311259496361879851100343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1748345995149173134800457 1311259496361879851100343)
                ·
                  refine ⟨1966889244542819776650515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311259496361879851100343 1966889244542819776650515)
                  ·
                    refine ⟨2950333866814229664975773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1966889244542819776650515 2950333866814229664975773)
                    ·
                      refine ⟨1106375200055336124365915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2950333866814229664975773 1106375200055336124365915)
                      ·
                        rfl

theorem cell23_2154658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_2154658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154658 prefixEnd_2154658 := by exact prefixLift 2154658
  have htrace : WordTrace (prefixWord ++ tailWord_2154658) baseStart_2154658 baseEnd_2154658 := by
    simpa [prefixWord, tailWord_2154658, baseEnd_2154658] using wordTrace_append hprefix tailTrace_2154658
  have hstable : (prefixWord ++ tailWord_2154658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154658).length < 2 ^ (prefixWord ++ tailWord_2154658).sum := by decide
  have hdescent : baseEnd_2154658 < baseStart_2154658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154680 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 1, 3, 3]
def baseStart_2154680 : Nat := 118140960795 + 2154680 * 2 ^ 59
def prefixEnd_2154680 : Nat := 4983230072969 + 3 ^ 40 * 2154680 * 2
def baseEnd_2154680 : Nat := 1106386496629735038290813

theorem tailTrace_2154680 : CollatzResearch.WordTrace tailWord_2154680 prefixEnd_2154680 1106386496629735038290813 := by
  unfold tailWord_2154680
  simp only [CollatzResearch.WordTrace]
  refine ⟨39293817916984912445962747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52391757222646549927950329 39293817916984912445962747)
  ·
    refine ⟨58940726875477368668944121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39293817916984912445962747 58940726875477368668944121)
    ·
      refine ⟨44205545156608026501708091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58940726875477368668944121 44205545156608026501708091)
      ·
        refine ⟨66308317734912039752562137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44205545156608026501708091 66308317734912039752562137)
        ·
          refine ⟨49731238301184029814421603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66308317734912039752562137 49731238301184029814421603)
          ·
            refine ⟨74596857451776044721632405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49731238301184029814421603 74596857451776044721632405)
            ·
              refine ⟨3496727693052002096326519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74596857451776044721632405 3496727693052002096326519)
              ·
                refine ⟨5245091539578003144489779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496727693052002096326519 5245091539578003144489779)
                ·
                  refine ⟨7867637309367004716734669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5245091539578003144489779 7867637309367004716734669)
                  ·
                    refine ⟨2950363991012626768775501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7867637309367004716734669 2950363991012626768775501)
                    ·
                      refine ⟨1106386496629735038290813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2950363991012626768775501 1106386496629735038290813)
                      ·
                        rfl

theorem cell23_2154680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_2154680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154680 prefixEnd_2154680 := by exact prefixLift 2154680
  have htrace : WordTrace (prefixWord ++ tailWord_2154680) baseStart_2154680 baseEnd_2154680 := by
    simpa [prefixWord, tailWord_2154680, baseEnd_2154680] using wordTrace_append hprefix tailTrace_2154680
  have hstable : (prefixWord ++ tailWord_2154680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154680).length < 2 ^ (prefixWord ++ tailWord_2154680).sum := by decide
  have hdescent : baseEnd_2154680 < baseStart_2154680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154713 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 2, 6]
def baseStart_2154713 : Nat := 118140960795 + 2154713 * 2 ^ 59
def prefixEnd_2154713 : Nat := 4983230072969 + 3 ^ 40 * 2154713 * 2
def baseEnd_2154713 : Nat := 368801147163777803059387

theorem tailTrace_2154713 : CollatzResearch.WordTrace tailWord_2154713 prefixEnd_2154713 368801147163777803059387 := by
  unfold tailWord_2154713
  simp only [CollatzResearch.WordTrace]
  refine ⟨78588839442850271527876793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52392559628566847685251195 78588839442850271527876793)
  ·
    refine ⟨58941629582137703645907595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78588839442850271527876793 58941629582137703645907595)
    ·
      refine ⟨88412444373206555468861393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58941629582137703645907595 88412444373206555468861393)
      ·
        refine ⟨66309333279904916601646045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88412444373206555468861393 66309333279904916601646045)
        ·
          refine ⟨24865999979964343725617267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66309333279904916601646045 24865999979964343725617267)
          ·
            refine ⟨37298999969946515588425901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24865999979964343725617267 37298999969946515588425901)
            ·
              refine ⟨13987124988729943345659713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37298999969946515588425901 13987124988729943345659713)
              ·
                refine ⟨10490343741547457509244785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13987124988729943345659713 10490343741547457509244785)
                ·
                  refine ⟨7867757806160593131933589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10490343741547457509244785 7867757806160593131933589)
                  ·
                    refine ⟨368801147163777803059387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7867757806160593131933589 368801147163777803059387)
                    ·
                      rfl

theorem cell23_2154713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_2154713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154713 prefixEnd_2154713 := by exact prefixLift 2154713
  have htrace : WordTrace (prefixWord ++ tailWord_2154713) baseStart_2154713 baseEnd_2154713 := by
    simpa [prefixWord, tailWord_2154713, baseEnd_2154713] using wordTrace_append hprefix tailTrace_2154713
  have hstable : (prefixWord ++ tailWord_2154713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154713).length < 2 ^ (prefixWord ++ tailWord_2154713).sum := by decide
  have hdescent : baseEnd_2154713 < baseStart_2154713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154737 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 1, 4, 2]
def baseStart_2154737 : Nat := 118140960795 + 2154737 * 2 ^ 59
def prefixEnd_2154737 : Nat := 4983230072969 + 3 ^ 40 * 2154737 * 2
def baseEnd_2154737 : Nat := 1106415765027041315278051

theorem tailTrace_2154737 : CollatzResearch.WordTrace tailWord_2154737 prefixEnd_2154737 1106415765027041315278051 := by
  unfold tailWord_2154737
  simp only [CollatzResearch.WordTrace]
  refine ⟨78589714794763323626750465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52393143196508882417833643 78589714794763323626750465)
  ·
    refine ⟨58942286096072492720062849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78589714794763323626750465 58942286096072492720062849)
    ·
      refine ⟨44206714572054369540047137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58942286096072492720062849 44206714572054369540047137)
      ·
        refine ⟨33155035929040777155035353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44206714572054369540047137 33155035929040777155035353)
        ·
          refine ⟨24866276946780582866276515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33155035929040777155035353 24866276946780582866276515)
          ·
            refine ⟨37299415420170874299414773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24866276946780582866276515 37299415420170874299414773)
            ·
              refine ⟨3496820195641019465570135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37299415420170874299414773 3496820195641019465570135)
              ·
                refine ⟨5245230293461529198355203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3496820195641019465570135 5245230293461529198355203)
                ·
                  refine ⟨7867845440192293797532805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5245230293461529198355203 7867845440192293797532805)
                  ·
                    refine ⟨1475221020036055087037401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7867845440192293797532805 1475221020036055087037401)
                    ·
                      refine ⟨1106415765027041315278051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475221020036055087037401 1106415765027041315278051)
                      ·
                        rfl

theorem cell23_2154737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_2154737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154737 prefixEnd_2154737 := by exact prefixLift 2154737
  have htrace : WordTrace (prefixWord ++ tailWord_2154737) baseStart_2154737 baseEnd_2154737 := by
    simpa [prefixWord, tailWord_2154737, baseEnd_2154737] using wordTrace_append hprefix tailTrace_2154737
  have hstable : (prefixWord ++ tailWord_2154737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154737).length < 2 ^ (prefixWord ++ tailWord_2154737).sum := by decide
  have hdescent : baseEnd_2154737 < baseStart_2154737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154788 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 2, 2, 2]
def baseStart_2154788 : Nat := 118140960795 + 2154788 * 2 ^ 59
def prefixEnd_2154788 : Nat := 4983230072969 + 3 ^ 40 * 2154788 * 2
def baseEnd_2154788 : Nat := 1106441952540420615740317

theorem tailTrace_2154788 : CollatzResearch.WordTrace tailWord_2154788 prefixEnd_2154788 1106441952540420615740317 := by
  unfold tailWord_2154788
  simp only [CollatzResearch.WordTrace]
  refine ⟨39295787458789279668428509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52394383278385706224571345 39295787458789279668428509)
  ·
    refine ⟨14735920297045979875660691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39295787458789279668428509 14735920297045979875660691)
    ·
      refine ⟨22103880445568969813491037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14735920297045979875660691 22103880445568969813491037)
      ·
        refine ⟨8288955167088363680059139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22103880445568969813491037 8288955167088363680059139)
        ·
          refine ⟨12433432750632545520088709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8288955167088363680059139 12433432750632545520088709)
          ·
            refine ⟨2331268640743602285016633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12433432750632545520088709 2331268640743602285016633)
            ·
              refine ⟨1748451480557701713762475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2331268640743602285016633 1748451480557701713762475)
              ·
                refine ⟨2622677220836552570643713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1748451480557701713762475 2622677220836552570643713)
                ·
                  refine ⟨1967007915627414427982785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2622677220836552570643713 1967007915627414427982785)
                  ·
                    refine ⟨1475255936720560820987089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1967007915627414427982785 1475255936720560820987089)
                    ·
                      refine ⟨1106441952540420615740317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475255936720560820987089 1106441952540420615740317)
                      ·
                        rfl

theorem cell23_2154788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_2154788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154788 prefixEnd_2154788 := by exact prefixLift 2154788
  have htrace : WordTrace (prefixWord ++ tailWord_2154788) baseStart_2154788 baseEnd_2154788 := by
    simpa [prefixWord, tailWord_2154788, baseEnd_2154788] using wordTrace_append hprefix tailTrace_2154788
  have hstable : (prefixWord ++ tailWord_2154788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154788).length < 2 ^ (prefixWord ++ tailWord_2154788).sum := by decide
  have hdescent : baseEnd_2154788 < baseStart_2154788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154864 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 3]
def baseStart_2154864 : Nat := 118140960795 + 2154864 * 2 ^ 59
def prefixEnd_2154864 : Nat := 4983230072969 + 3 ^ 40 * 2154864 * 2
def baseEnd_2154864 : Nat := 1106480977070162318389967

theorem tailTrace_2154864 : CollatzResearch.WordTrace tailWord_2154864 prefixEnd_2154864 1106480977070162318389967 := by
  unfold tailWord_2154864
  simp only [CollatzResearch.WordTrace]
  refine ⟨39297173432651612158311823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52396231243535482877749097 39297173432651612158311823)
  ·
    refine ⟨58945760148977418237467735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39297173432651612158311823 58945760148977418237467735)
    ·
      refine ⟨88418640223466127356201603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58945760148977418237467735 88418640223466127356201603)
      ·
        refine ⟨132627960335199191034302405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88418640223466127356201603 132627960335199191034302405)
        ·
          refine ⟨24867742562849848318931701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132627960335199191034302405 24867742562849848318931701)
          ·
            refine ⟨2331350865267173279899847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24867742562849848318931701 2331350865267173279899847)
            ·
              refine ⟨3497026297900759919849771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331350865267173279899847 3497026297900759919849771)
              ·
                refine ⟨5245539446851139879774657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497026297900759919849771 5245539446851139879774657)
                ·
                  refine ⟨3934154585138354909830993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5245539446851139879774657 3934154585138354909830993)
                  ·
                    refine ⟨2950615938853766182373245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3934154585138354909830993 2950615938853766182373245)
                    ·
                      refine ⟨1106480977070162318389967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2950615938853766182373245 1106480977070162318389967)
                      ·
                        rfl

theorem cell23_2154864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 3].length) (baseStart_2154864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154864 prefixEnd_2154864 := by exact prefixLift 2154864
  have htrace : WordTrace (prefixWord ++ tailWord_2154864) baseStart_2154864 baseEnd_2154864 := by
    simpa [prefixWord, tailWord_2154864, baseEnd_2154864] using wordTrace_append hprefix tailTrace_2154864
  have hstable : (prefixWord ++ tailWord_2154864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154864).length < 2 ^ (prefixWord ++ tailWord_2154864).sum := by decide
  have hdescent : baseEnd_2154864 < baseStart_2154864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154904 : List Nat := [2, 1, 2, 5, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2154904 : Nat := 118140960795 + 2154904 * 2 ^ 59
def prefixEnd_2154904 : Nat := 4983230072969 + 3 ^ 40 * 2154904 * 2
def baseEnd_2154904 : Nat := 1106501516296342161889783

theorem tailTrace_2154904 : CollatzResearch.WordTrace tailWord_2154904 prefixEnd_2154904 1106501516296342161889783 := by
  unfold tailWord_2154904
  simp only [CollatzResearch.WordTrace]
  refine ⟨39297902892579155574039883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52397203856772207432053177 39297902892579155574039883)
  ·
    refine ⟨58946854338868733361059825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39297902892579155574039883 58946854338868733361059825)
    ·
      refine ⟨44210140754151550020794869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58946854338868733361059825 44210140754151550020794869)
      ·
        refine ⟨4144700695701707814449519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44210140754151550020794869 4144700695701707814449519)
        ·
          refine ⟨6217051043552561721674279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4144700695701707814449519 6217051043552561721674279)
          ·
            refine ⟨9325576565328842582511419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6217051043552561721674279 9325576565328842582511419)
            ·
              refine ⟨13988364847993263873767129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9325576565328842582511419 13988364847993263873767129)
              ·
                refine ⟨10491273635994947905325347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13988364847993263873767129 10491273635994947905325347)
                ·
                  refine ⟨15736910453992421857988021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10491273635994947905325347 15736910453992421857988021)
                  ·
                    refine ⟨1475335355061789549186377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15736910453992421857988021 1475335355061789549186377)
                    ·
                      refine ⟨1106501516296342161889783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475335355061789549186377 1106501516296342161889783)
                      ·
                        rfl

theorem cell23_2154904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2154904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154904 prefixEnd_2154904 := by exact prefixLift 2154904
  have htrace : WordTrace (prefixWord ++ tailWord_2154904) baseStart_2154904 baseEnd_2154904 := by
    simpa [prefixWord, tailWord_2154904, baseEnd_2154904] using wordTrace_append hprefix tailTrace_2154904
  have hstable : (prefixWord ++ tailWord_2154904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154904).length < 2 ^ (prefixWord ++ tailWord_2154904).sum := by decide
  have hdescent : baseEnd_2154904 < baseStart_2154904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154914 : List Nat := [3, 3, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_2154914 : Nat := 118140960795 + 2154914 * 2 ^ 59
def prefixEnd_2154914 : Nat := 4983230072969 + 3 ^ 40 * 2154914 * 2
def baseEnd_2154914 : Nat := 368835550367629040921579

theorem tailTrace_2154914 : CollatzResearch.WordTrace tailWord_2154914 prefixEnd_2154914 368835550367629040921579 := by
  unfold tailWord_2154914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19649042628780520713985949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52397447010081388570629197 19649042628780520713985949)
  ·
    refine ⟨7368390985792695267744731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19649042628780520713985949 7368390985792695267744731)
    ·
      refine ⟨11052586478689042901617097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7368390985792695267744731 11052586478689042901617097)
      ·
        refine ⟨8289439859016782176212823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11052586478689042901617097 8289439859016782176212823)
        ·
          refine ⟨12434159788525173264319235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8289439859016782176212823 12434159788525173264319235)
          ·
            refine ⟨18651239682787759896478853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12434159788525173264319235 18651239682787759896478853)
            ·
              refine ⟨3497107440522704980589785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18651239682787759896478853 3497107440522704980589785)
              ·
                refine ⟨2622830580392028735442339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3497107440522704980589785 2622830580392028735442339)
                ·
                  refine ⟨3934245870588043103163509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2622830580392028735442339 3934245870588043103163509)
                  ·
                    refine ⟨368835550367629040921579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3934245870588043103163509 368835550367629040921579)
                    ·
                      rfl

theorem cell23_2154914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_2154914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154914 prefixEnd_2154914 := by exact prefixLift 2154914
  have htrace : WordTrace (prefixWord ++ tailWord_2154914) baseStart_2154914 baseEnd_2154914 := by
    simpa [prefixWord, tailWord_2154914, baseEnd_2154914] using wordTrace_append hprefix tailTrace_2154914
  have hstable : (prefixWord ++ tailWord_2154914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154914).length < 2 ^ (prefixWord ++ tailWord_2154914).sum := by decide
  have hdescent : baseEnd_2154914 < baseStart_2154914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154917 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 2, 6, 2]
def baseStart_2154917 : Nat := 118140960795 + 2154917 * 2 ^ 59
def prefixEnd_2154917 : Nat := 4983230072969 + 3 ^ 40 * 2154917 * 2
def baseEnd_2154917 : Nat := 1106508191544850611027223

theorem tailTrace_2154917 : CollatzResearch.WordTrace tailWord_2154917 prefixEnd_2154917 1106508191544850611027223 := by
  unfold tailWord_2154917
  simp only [CollatzResearch.WordTrace]
  refine ⟨78596279934111214368303005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52397519956074142912202003 78596279934111214368303005)
  ·
    refine ⟨29473604975291705388113627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78596279934111214368303005 29473604975291705388113627)
    ·
      refine ⟨44210407462937558082170441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29473604975291705388113627 44210407462937558082170441)
      ·
        refine ⟨33157805597203168561627831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44210407462937558082170441 33157805597203168561627831)
        ·
          refine ⟨49736708395804752842441747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33157805597203168561627831 49736708395804752842441747)
          ·
            refine ⟨74605062593707129263662621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49736708395804752842441747 74605062593707129263662621)
            ·
              refine ⟨27976898472640173473873483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74605062593707129263662621 27976898472640173473873483)
              ·
                refine ⟨41965347708960260210810225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27976898472640173473873483 41965347708960260210810225)
                ·
                  refine ⟨31474010781720195158107669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41965347708960260210810225 31474010781720195158107669)
                  ·
                    refine ⟨1475344255393134148036297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31474010781720195158107669 1475344255393134148036297)
                    ·
                      refine ⟨1106508191544850611027223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475344255393134148036297 1106508191544850611027223)
                      ·
                        rfl

theorem cell23_2154917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_2154917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154917 prefixEnd_2154917 := by exact prefixLift 2154917
  have htrace : WordTrace (prefixWord ++ tailWord_2154917) baseStart_2154917 baseEnd_2154917 := by
    simpa [prefixWord, tailWord_2154917, baseEnd_2154917] using wordTrace_append hprefix tailTrace_2154917
  have hstable : (prefixWord ++ tailWord_2154917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154917).length < 2 ^ (prefixWord ++ tailWord_2154917).sum := by decide
  have hdescent : baseEnd_2154917 < baseStart_2154917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154922 : List Nat := [3, 1, 6, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2154922 : Nat := 118140960795 + 2154922 * 2 ^ 59
def prefixEnd_2154922 : Nat := 4983230072969 + 3 ^ 40 * 2154922 * 2
def baseEnd_2154922 : Nat := 368836919649374363821567

theorem tailTrace_2154922 : CollatzResearch.WordTrace tailWord_2154922 prefixEnd_2154922 368836919649374363821567 := by
  unfold tailWord_2154922
  simp only [CollatzResearch.WordTrace]
  refine ⟨19649115574773275055558755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52397641532728733481490013 19649115574773275055558755)
  ·
    refine ⟨29473673362159912583338133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19649115574773275055558755 29473673362159912583338133)
    ·
      refine ⟨1381578438851245902343975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29473673362159912583338133 1381578438851245902343975)
      ·
        refine ⟨2072367658276868853515963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1381578438851245902343975 2072367658276868853515963)
        ·
          refine ⟨3108551487415303280273945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2072367658276868853515963 3108551487415303280273945)
          ·
            refine ⟨2331413615561477460205459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3108551487415303280273945 2331413615561477460205459)
            ·
              refine ⟨3497120423342216190308189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331413615561477460205459 3497120423342216190308189)
              ·
                refine ⟨1311420158753331071365571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3497120423342216190308189 1311420158753331071365571)
                ·
                  refine ⟨1967130238129996607048357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311420158753331071365571 1967130238129996607048357)
                  ·
                    refine ⟨368836919649374363821567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1967130238129996607048357 368836919649374363821567)
                    ·
                      rfl

theorem cell23_2154922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2154922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154922 prefixEnd_2154922 := by exact prefixLift 2154922
  have htrace : WordTrace (prefixWord ++ tailWord_2154922) baseStart_2154922 baseEnd_2154922 := by
    simpa [prefixWord, tailWord_2154922, baseEnd_2154922] using wordTrace_append hprefix tailTrace_2154922
  have hstable : (prefixWord ++ tailWord_2154922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154922).length < 2 ^ (prefixWord ++ tailWord_2154922).sum := by decide
  have hdescent : baseEnd_2154922 < baseStart_2154922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154937 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 5]
def baseStart_2154937 : Nat := 118140960795 + 2154937 * 2 ^ 59
def prefixEnd_2154937 : Nat := 4983230072969 + 3 ^ 40 * 2154937 * 2
def baseEnd_2154937 : Nat := 1106518461157940532777131

theorem tailTrace_2154937 : CollatzResearch.WordTrace tailWord_2154937 prefixEnd_2154937 1106518461157940532777131 := by
  unfold tailWord_2154937
  simp only [CollatzResearch.WordTrace]
  refine ⟨78597009394038757784031065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52398006262692505189354043 78597009394038757784031065)
  ·
    refine ⟨58947757045529068338023299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78597009394038757784031065 58947757045529068338023299)
    ·
      refine ⟨88421635568293602507034949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58947757045529068338023299 88421635568293602507034949)
      ·
        refine ⟨16579056669055050470069053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88421635568293602507034949 16579056669055050470069053)
        ·
          refine ⟨6217146250895643926275895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16579056669055050470069053 6217146250895643926275895)
          ·
            refine ⟨9325719376343465889413843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6217146250895643926275895 9325719376343465889413843)
            ·
              refine ⟨13988579064515198834120765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9325719376343465889413843 13988579064515198834120765)
              ·
                refine ⟨5245717149193199562795287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13988579064515198834120765 5245717149193199562795287)
                ·
                  refine ⟨7868575723789799344192931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5245717149193199562795287 7868575723789799344192931)
                  ·
                    refine ⟨11802863585684699016289397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7868575723789799344192931 11802863585684699016289397)
                    ·
                      refine ⟨1106518461157940532777131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11802863585684699016289397 1106518461157940532777131)
                      ·
                        rfl

theorem cell23_2154937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_2154937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154937 prefixEnd_2154937 := by exact prefixLift 2154937
  have htrace : WordTrace (prefixWord ++ tailWord_2154937) baseStart_2154937 baseEnd_2154937 := by
    simpa [prefixWord, tailWord_2154937, baseEnd_2154937] using wordTrace_append hprefix tailTrace_2154937
  have hstable : (prefixWord ++ tailWord_2154937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154937).length < 2 ^ (prefixWord ++ tailWord_2154937).sum := by decide
  have hdescent : baseEnd_2154937 < baseStart_2154937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154951 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 3, 2, 2]
def baseStart_2154951 : Nat := 118140960795 + 2154951 * 2 ^ 59
def prefixEnd_2154951 : Nat := 4983230072969 + 3 ^ 40 * 2154951 * 2
def baseEnd_2154951 : Nat := 1106525649887103478002067

theorem tailTrace_2154951 : CollatzResearch.WordTrace tailWord_2154951 prefixEnd_2154951 1106525649887103478002067 := by
  unfold tailWord_2154951
  simp only [CollatzResearch.WordTrace]
  refine ⟨78597520015988038175040707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52398346677325358783360471 78597520015988038175040707)
  ·
    refine ⟨117896280023982057262561061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78597520015988038175040707 117896280023982057262561061)
    ·
      refine ⟨22105552504496635736730199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117896280023982057262561061 22105552504496635736730199)
      ·
        refine ⟨33158328756744953605095299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22105552504496635736730199 33158328756744953605095299)
        ·
          refine ⟨49737493135117430407642949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33158328756744953605095299 49737493135117430407642949)
          ·
            refine ⟨9325779962834518201433053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49737493135117430407642949 9325779962834518201433053)
            ·
              refine ⟨3497167486062944325537395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9325779962834518201433053 3497167486062944325537395)
              ·
                refine ⟨5245751229094416488306093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497167486062944325537395 5245751229094416488306093)
                ·
                  refine ⟨1967156710910406183114785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5245751229094416488306093 1967156710910406183114785)
                  ·
                    refine ⟨1475367533182804637336089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1967156710910406183114785 1475367533182804637336089)
                    ·
                      refine ⟨1106525649887103478002067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475367533182804637336089 1106525649887103478002067)
                      ·
                        rfl

theorem cell23_2154951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_2154951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154951 prefixEnd_2154951 := by exact prefixLift 2154951
  have htrace : WordTrace (prefixWord ++ tailWord_2154951) baseStart_2154951 baseEnd_2154951 := by
    simpa [prefixWord, tailWord_2154951, baseEnd_2154951] using wordTrace_append hprefix tailTrace_2154951
  have hstable : (prefixWord ++ tailWord_2154951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154951).length < 2 ^ (prefixWord ++ tailWord_2154951).sum := by decide
  have hdescent : baseEnd_2154951 < baseStart_2154951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2154984 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 1, 3, 3]
def baseStart_2154984 : Nat := 118140960795 + 2154984 * 2 ^ 59
def prefixEnd_2154984 : Nat := 4983230072969 + 3 ^ 40 * 2154984 * 2
def baseEnd_2154984 : Nat := 1106542594748701848889415

theorem tailTrace_2154984 : CollatzResearch.WordTrace tailWord_2154984 prefixEnd_2154984 1106542594748701848889415 := by
  unfold tailWord_2154984
  simp only [CollatzResearch.WordTrace]
  refine ⟨39299361812434242405496003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52399149083245656540661337 39299361812434242405496003)
  ·
    refine ⟨58949042718651363608244005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39299361812434242405496003 58949042718651363608244005)
    ·
      refine ⟨11052945509747130676545751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58949042718651363608244005 11052945509747130676545751)
      ·
        refine ⟨16579418264620696014818627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11052945509747130676545751 16579418264620696014818627)
        ·
          refine ⟨24869127396931044022227941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16579418264620696014818627 24869127396931044022227941)
          ·
            refine ⟨4662961386924570754167739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24869127396931044022227941 4662961386924570754167739)
            ·
              refine ⟨6994442080386856131251609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4662961386924570754167739 6994442080386856131251609)
              ·
                refine ⟨5245831560290142098438707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6994442080386856131251609 5245831560290142098438707)
                ·
                  refine ⟨7868747340435213147658061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5245831560290142098438707 7868747340435213147658061)
                  ·
                    refine ⟨2950780252663204930371773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7868747340435213147658061 2950780252663204930371773)
                    ·
                      refine ⟨1106542594748701848889415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2950780252663204930371773 1106542594748701848889415)
                      ·
                        rfl

theorem cell23_2154984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_2154984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2154984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2154984 prefixEnd_2154984 := by exact prefixLift 2154984
  have htrace : WordTrace (prefixWord ++ tailWord_2154984) baseStart_2154984 baseEnd_2154984 := by
    simpa [prefixWord, tailWord_2154984, baseEnd_2154984] using wordTrace_append hprefix tailTrace_2154984
  have hstable : (prefixWord ++ tailWord_2154984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2154984).length < 2 ^ (prefixWord ++ tailWord_2154984).sum := by decide
  have hdescent : baseEnd_2154984 < baseStart_2154984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2154984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155027 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 3]
def baseStart_2155027 : Nat := 118140960795 + 2155027 * 2 ^ 59
def prefixEnd_2155027 : Nat := 4983230072969 + 3 ^ 40 * 2155027 * 2
def baseEnd_2155027 : Nat := 1106564674416845180651717

theorem tailTrace_2155027 : CollatzResearch.WordTrace tailWord_2155027 prefixEnd_2155027 1106564674416845180651717 := by
  unfold tailWord_2155027
  simp only [CollatzResearch.WordTrace]
  refine ⟨78600291963712703154807335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52400194642475135436538223 78600291963712703154807335)
  ·
    refine ⟨117900437945569054732211003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78600291963712703154807335 117900437945569054732211003)
    ·
      refine ⟨176850656918353582098316505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117900437945569054732211003 176850656918353582098316505)
      ·
        refine ⟨132637992688765186573737379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176850656918353582098316505 132637992688765186573737379)
        ·
          refine ⟨198956989033147779860606069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132637992688765186573737379 198956989033147779860606069)
          ·
            refine ⟨18652217721857604361931819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 198956989033147779860606069 18652217721857604361931819)
            ·
              refine ⟨27978326582786406542897729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18652217721857604361931819 27978326582786406542897729)
              ·
                refine ⟨20983744937089804907173297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27978326582786406542897729 20983744937089804907173297)
                ·
                  refine ⟨15737808702817353680379973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20983744937089804907173297 15737808702817353680379973)
                  ·
                    refine ⟨2950839131778253815071245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15737808702817353680379973 2950839131778253815071245)
                    ·
                      refine ⟨1106564674416845180651717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2950839131778253815071245 1106564674416845180651717)
                      ·
                        rfl

theorem cell23_2155027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 3].length) (baseStart_2155027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155027 prefixEnd_2155027 := by exact prefixLift 2155027
  have htrace : WordTrace (prefixWord ++ tailWord_2155027) baseStart_2155027 baseEnd_2155027 := by
    simpa [prefixWord, tailWord_2155027, baseEnd_2155027] using wordTrace_append hprefix tailTrace_2155027
  have hstable : (prefixWord ++ tailWord_2155027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155027).length < 2 ^ (prefixWord ++ tailWord_2155027).sum := by decide
  have hdescent : baseEnd_2155027 < baseStart_2155027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155028 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_2155028 : Nat := 118140960795 + 2155028 * 2 ^ 59
def prefixEnd_2155028 : Nat := 4983230072969 + 3 ^ 40 * 2155028 * 2
def baseEnd_2155028 : Nat := 1106565187897499676739213

theorem tailTrace_2155028 : CollatzResearch.WordTrace tailWord_2155028 prefixEnd_2155028 1106565187897499676739213 := by
  unfold tailWord_2155028
  simp only [CollatzResearch.WordTrace]
  refine ⟨39300164218354540162796869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52400218957806053550395825 39300164218354540162796869)
  ·
    refine ⟨7368780790941476280524413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39300164218354540162796869 7368780790941476280524413)
    ·
      refine ⟨2763292796603053605196655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7368780790941476280524413 2763292796603053605196655)
      ·
        refine ⟨4144939194904580407794983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2763292796603053605196655 4144939194904580407794983)
        ·
          refine ⟨6217408792356870611692475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4144939194904580407794983 6217408792356870611692475)
          ·
            refine ⟨9326113188535305917538713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6217408792356870611692475 9326113188535305917538713)
            ·
              refine ⟨6994584891401479438154035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9326113188535305917538713 6994584891401479438154035)
              ·
                refine ⟨10491877337102219157231053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6994584891401479438154035 10491877337102219157231053)
                ·
                  refine ⟨3934454001413332183961645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10491877337102219157231053 3934454001413332183961645)
                  ·
                    refine ⟨1475420250529999568985617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3934454001413332183961645 1475420250529999568985617)
                    ·
                      refine ⟨1106565187897499676739213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475420250529999568985617 1106565187897499676739213)
                      ·
                        rfl

theorem cell23_2155028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_2155028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155028 prefixEnd_2155028 := by exact prefixLift 2155028
  have htrace : WordTrace (prefixWord ++ tailWord_2155028) baseStart_2155028 baseEnd_2155028 := by
    simpa [prefixWord, tailWord_2155028, baseEnd_2155028] using wordTrace_append hprefix tailTrace_2155028
  have hstable : (prefixWord ++ tailWord_2155028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155028).length < 2 ^ (prefixWord ++ tailWord_2155028).sum := by decide
  have hdescent : baseEnd_2155028 < baseStart_2155028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155041 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 4, 2, 2]
def baseStart_2155041 : Nat := 118140960795 + 2155041 * 2 ^ 59
def prefixEnd_2155041 : Nat := 4983230072969 + 3 ^ 40 * 2155041 * 2
def baseEnd_2155041 : Nat := 1106571863146008125876653

theorem tailTrace_2155041 : CollatzResearch.WordTrace tailWord_2155041 prefixEnd_2155041 1106571863146008125876653 := by
  unfold tailWord_2155041
  simp only [CollatzResearch.WordTrace]
  refine ⟨78600802585661983545816977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52400535057107989030544651 78600802585661983545816977)
  ·
    refine ⟨58950601939246487659362733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78600802585661983545816977 58950601939246487659362733)
    ·
      refine ⟨22106475727217432872261025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58950601939246487659362733 22106475727217432872261025)
      ·
        refine ⟨16579856795413074654195769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22106475727217432872261025 16579856795413074654195769)
        ·
          refine ⟨12434892596559805990646827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16579856795413074654195769 12434892596559805990646827)
          ·
            refine ⟨18652338894839708985970241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12434892596559805990646827 18652338894839708985970241)
            ·
              refine ⟨13989254171129781739477681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18652338894839708985970241 13989254171129781739477681)
              ·
                refine ⟨10491940628347336304608261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13989254171129781739477681 10491940628347336304608261)
                ·
                  refine ⟨1967238867815125557114049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10491940628347336304608261 1967238867815125557114049)
                  ·
                    refine ⟨1475429150861344167835537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1967238867815125557114049 1475429150861344167835537)
                    ·
                      refine ⟨1106571863146008125876653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475429150861344167835537 1106571863146008125876653)
                      ·
                        rfl

theorem cell23_2155041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_2155041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155041 prefixEnd_2155041 := by exact prefixLift 2155041
  have htrace : WordTrace (prefixWord ++ tailWord_2155041) baseStart_2155041 baseEnd_2155041 := by
    simpa [prefixWord, tailWord_2155041, baseEnd_2155041] using wordTrace_append hprefix tailTrace_2155041
  have hstable : (prefixWord ++ tailWord_2155041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155041).length < 2 ^ (prefixWord ++ tailWord_2155041).sum := by decide
  have hdescent : baseEnd_2155041 < baseStart_2155041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155058 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2]
def baseStart_2155058 : Nat := 118140960795 + 2155058 * 2 ^ 59
def prefixEnd_2155058 : Nat := 4983230072969 + 3 ^ 40 * 2155058 * 2
def baseEnd_2155058 : Nat := 1106580592317134559364075

theorem tailTrace_2155058 : CollatzResearch.WordTrace tailWord_2155058 prefixEnd_2155058 1106580592317134559364075 := by
  unfold tailWord_2155058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19650355656650098862296457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52400948417733596966123885 19650355656650098862296457)
  ·
    refine ⟨14737766742487574146722343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19650355656650098862296457 14737766742487574146722343)
    ·
      refine ⟨22106650113731361220083515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14737766742487574146722343 22106650113731361220083515)
      ·
        refine ⟨33159975170597041830125273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22106650113731361220083515 33159975170597041830125273)
        ·
          refine ⟨24869981377947781372593955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33159975170597041830125273 24869981377947781372593955)
          ·
            refine ⟨37304972066921672058890933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24869981377947781372593955 37304972066921672058890933)
            ·
              refine ⟨3497341131273906755521025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37304972066921672058890933 3497341131273906755521025)
              ·
                refine ⟨2623005848455430066640769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3497341131273906755521025 2623005848455430066640769)
                ·
                  refine ⟨1967254386341572549980577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2623005848455430066640769 1967254386341572549980577)
                  ·
                    refine ⟨1475440789756179412485433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1967254386341572549980577 1475440789756179412485433)
                    ·
                      refine ⟨1106580592317134559364075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475440789756179412485433 1106580592317134559364075)
                      ·
                        rfl

theorem cell23_2155058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2].length) (baseStart_2155058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155058 prefixEnd_2155058 := by exact prefixLift 2155058
  have htrace : WordTrace (prefixWord ++ tailWord_2155058) baseStart_2155058 baseEnd_2155058 := by
    simpa [prefixWord, tailWord_2155058, baseEnd_2155058] using wordTrace_append hprefix tailTrace_2155058
  have hstable : (prefixWord ++ tailWord_2155058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155058).length < 2 ^ (prefixWord ++ tailWord_2155058).sum := by decide
  have hdescent : baseEnd_2155058 < baseStart_2155058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155064 : List Nat := [2, 1, 2, 1, 4, 1, 1, 6, 5]
def baseStart_2155064 : Nat := 118140960795 + 2155064 * 2 ^ 59
def prefixEnd_2155064 : Nat := 4983230072969 + 3 ^ 40 * 2155064 * 2
def baseEnd_2155064 : Nat := 122953741466784615098783

theorem tailTrace_2155064 : CollatzResearch.WordTrace tailWord_2155064 prefixEnd_2155064 122953741466784615098783 := by
  unfold tailWord_2155064
  simp only [CollatzResearch.WordTrace]
  refine ⟨39300820732289329236952123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52401094309719105649269497 39300820732289329236952123)
  ·
    refine ⟨58951231098433993855428185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39300820732289329236952123 58951231098433993855428185)
    ·
      refine ⟨44213423323825495391571139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58951231098433993855428185 44213423323825495391571139)
      ·
        refine ⟨66320134985738243087356709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44213423323825495391571139 66320134985738243087356709)
        ·
          refine ⟨12435025309825920578879383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66320134985738243087356709 12435025309825920578879383)
          ·
            refine ⟨18652537964738880868319075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12435025309825920578879383 18652537964738880868319075)
            ·
              refine ⟨27978806947108321302478613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18652537964738880868319075 27978806947108321302478613)
              ·
                refine ⟨1311506575645702561053685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 27978806947108321302478613 1311506575645702561053685)
                ·
                  refine ⟨122953741466784615098783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1311506575645702561053685 122953741466784615098783)
                  ·
                    rfl

theorem cell23_2155064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 5].length) (baseStart_2155064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155064 prefixEnd_2155064 := by exact prefixLift 2155064
  have htrace : WordTrace (prefixWord ++ tailWord_2155064) baseStart_2155064 baseEnd_2155064 := by
    simpa [prefixWord, tailWord_2155064, baseEnd_2155064] using wordTrace_append hprefix tailTrace_2155064
  have hstable : (prefixWord ++ tailWord_2155064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155064).length < 2 ^ (prefixWord ++ tailWord_2155064).sum := by decide
  have hdescent : baseEnd_2155064 < baseStart_2155064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155077 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_2155077 : Nat := 118140960795 + 2155077 * 2 ^ 59
def prefixEnd_2155077 : Nat := 4983230072969 + 3 ^ 40 * 2155077 * 2
def baseEnd_2155077 : Nat := 368863449483189995008829

theorem tailTrace_2155077 : CollatzResearch.WordTrace tailWord_2155077 prefixEnd_2155077 368863449483189995008829 := by
  unfold tailWord_2155077
  simp only [CollatzResearch.WordTrace]
  refine ⟨78602115613531561694127485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52401410409021041129418323 78602115613531561694127485)
  ·
    refine ⟨29475793355074335635297807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78602115613531561694127485 29475793355074335635297807)
    ·
      refine ⟨44213690032611503452946711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29475793355074335635297807 44213690032611503452946711)
      ·
        refine ⟨66320535048917255179420067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44213690032611503452946711 66320535048917255179420067)
        ·
          refine ⟨99480802573375882769130101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66320535048917255179420067 99480802573375882769130101)
          ·
            refine ⟨9326325241253989009605947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99480802573375882769130101 9326325241253989009605947)
            ·
              refine ⟨13989487861880983514408921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9326325241253989009605947 13989487861880983514408921)
              ·
                refine ⟨10492115896410737635806691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13989487861880983514408921 10492115896410737635806691)
                ·
                  refine ⟨15738173844616106453710037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10492115896410737635806691 15738173844616106453710037)
                  ·
                    refine ⟨368863449483189995008829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15738173844616106453710037 368863449483189995008829)
                    ·
                      rfl

theorem cell23_2155077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_2155077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155077 prefixEnd_2155077 := by exact prefixLift 2155077
  have htrace : WordTrace (prefixWord ++ tailWord_2155077) baseStart_2155077 baseEnd_2155077 := by
    simpa [prefixWord, tailWord_2155077, baseEnd_2155077] using wordTrace_append hprefix tailTrace_2155077
  have hstable : (prefixWord ++ tailWord_2155077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155077).length < 2 ^ (prefixWord ++ tailWord_2155077).sum := by decide
  have hdescent : baseEnd_2155077 < baseStart_2155077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155127 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 6]
def baseStart_2155127 : Nat := 118140960795 + 2155127 * 2 ^ 59
def prefixEnd_2155127 : Nat := 4983230072969 + 3 ^ 40 * 2155127 * 2
def baseEnd_2155127 : Nat := 1106616022482294789401257

theorem tailTrace_2155127 : CollatzResearch.WordTrace tailWord_2155127 prefixEnd_2155127 1106616022482294789401257 := by
  unfold tailWord_2155127
  simp only [CollatzResearch.WordTrace]
  refine ⟨78603939263350420233447635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52402626175566946822298423 78603939263350420233447635)
  ·
    refine ⟨117905908895025630350171453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78603939263350420233447635 117905908895025630350171453)
    ·
      refine ⟨44214715835634611381314295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117905908895025630350171453 44214715835634611381314295)
      ·
        refine ⟨66322073753451917071971443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44214715835634611381314295 66322073753451917071971443)
        ·
          refine ⟨99483110630177875607957165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66322073753451917071971443 99483110630177875607957165)
          ·
            refine ⟨37306166486316703352983937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99483110630177875607957165 37306166486316703352983937)
            ·
              refine ⟨27979624864737527514737953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37306166486316703352983937 27979624864737527514737953)
              ·
                refine ⟨20984718648553145636053465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27979624864737527514737953 20984718648553145636053465)
                ·
                  refine ⟨15738538986414859227040099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20984718648553145636053465 15738538986414859227040099)
                  ·
                    refine ⟨23607808479622288840560149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15738538986414859227040099 23607808479622288840560149)
                    ·
                      refine ⟨1106616022482294789401257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23607808479622288840560149 1106616022482294789401257)
                      ·
                        rfl

theorem cell23_2155127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_2155127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155127 prefixEnd_2155127 := by exact prefixLift 2155127
  have htrace : WordTrace (prefixWord ++ tailWord_2155127) baseStart_2155127 baseEnd_2155127 := by
    simpa [prefixWord, tailWord_2155127, baseEnd_2155127] using wordTrace_append hprefix tailTrace_2155127
  have hstable : (prefixWord ++ tailWord_2155127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155127).length < 2 ^ (prefixWord ++ tailWord_2155127).sum := by decide
  have hdescent : baseEnd_2155127 < baseStart_2155127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155157 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_2155157 : Nat := 118140960795 + 2155157 * 2 ^ 59
def prefixEnd_2155157 : Nat := 4983230072969 + 3 ^ 40 * 2155157 * 2
def baseEnd_2155157 : Nat := 1106631426901929672026119

theorem tailTrace_2155157 : CollatzResearch.WordTrace tailWord_2155157 prefixEnd_2155157 1106631426901929672026119 := by
  unfold tailWord_2155157
  simp only [CollatzResearch.WordTrace]
  refine ⟨78605033453241735357039725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52403355635494490238026483 78605033453241735357039725)
  ·
    refine ⟨29476887544965650758889897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78605033453241735357039725 29476887544965650758889897)
    ·
      refine ⟨22107665658724238069167423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29476887544965650758889897 22107665658724238069167423)
      ·
        refine ⟨33161498488086357103751135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22107665658724238069167423 33161498488086357103751135)
        ·
          refine ⟨49742247732129535655626703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33161498488086357103751135 49742247732129535655626703)
          ·
            refine ⟨74613371598194303483440055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49742247732129535655626703 74613371598194303483440055)
            ·
              refine ⟨111920057397291455225160083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74613371598194303483440055 111920057397291455225160083)
              ·
                refine ⟨167880086095937182837740125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111920057397291455225160083 167880086095937182837740125)
                ·
                  refine ⟨62955032285976443564152547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167880086095937182837740125 62955032285976443564152547)
                  ·
                    refine ⟨94432548428964665346228821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62955032285976443564152547 94432548428964665346228821)
                    ·
                      refine ⟨1106631426901929672026119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 94432548428964665346228821 1106631426901929672026119)
                      ·
                        rfl

theorem cell23_2155157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_2155157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155157 prefixEnd_2155157 := by exact prefixLift 2155157
  have htrace : WordTrace (prefixWord ++ tailWord_2155157) baseStart_2155157 baseEnd_2155157 := by
    simpa [prefixWord, tailWord_2155157, baseEnd_2155157] using wordTrace_append hprefix tailTrace_2155157
  have hstable : (prefixWord ++ tailWord_2155157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155157).length < 2 ^ (prefixWord ++ tailWord_2155157).sum := by decide
  have hdescent : baseEnd_2155157 < baseStart_2155157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155177 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_2155177 : Nat := 118140960795 + 2155177 * 2 ^ 59
def prefixEnd_2155177 : Nat := 4983230072969 + 3 ^ 40 * 2155177 * 2
def baseEnd_2155177 : Nat := 1106641696515019593776027

theorem tailTrace_2155177 : CollatzResearch.WordTrace tailWord_2155177 prefixEnd_2155177 1106641696515019593776027 := by
  unfold tailWord_2155177
  simp only [CollatzResearch.WordTrace]
  refine ⟨78605762913169278772767785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52403841942112852515178523 78605762913169278772767785)
  ·
    refine ⟨58954322184876959079575839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78605762913169278772767785 58954322184876959079575839)
    ·
      refine ⟨88431483277315438619363759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58954322184876959079575839 88431483277315438619363759)
      ·
        refine ⟨132647224915973157929045639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88431483277315438619363759 132647224915973157929045639)
        ·
          refine ⟨198970837373959736893568459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132647224915973157929045639 198970837373959736893568459)
          ·
            refine ⟨298456256060939605340352689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198970837373959736893568459 298456256060939605340352689)
            ·
              refine ⟨223842192045704704005264517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298456256060939605340352689 223842192045704704005264517)
              ·
                refine ⟨41970411008569632000987097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223842192045704704005264517 41970411008569632000987097)
                ·
                  refine ⟨31477808256427224000740323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41970411008569632000987097 31477808256427224000740323)
                  ·
                    refine ⟨47216712384640836001110485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31477808256427224000740323 47216712384640836001110485)
                    ·
                      refine ⟨1106641696515019593776027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47216712384640836001110485 1106641696515019593776027)
                      ·
                        rfl

theorem cell23_2155177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_2155177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155177 prefixEnd_2155177 := by exact prefixLift 2155177
  have htrace : WordTrace (prefixWord ++ tailWord_2155177) baseStart_2155177 baseEnd_2155177 := by
    simpa [prefixWord, tailWord_2155177, baseEnd_2155177] using wordTrace_append hprefix tailTrace_2155177
  have hstable : (prefixWord ++ tailWord_2155177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155177).length < 2 ^ (prefixWord ++ tailWord_2155177).sum := by decide
  have hdescent : baseEnd_2155177 < baseStart_2155177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155198 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_2155198 : Nat := 118140960795 + 2155198 * 2 ^ 59
def prefixEnd_2155198 : Nat := 4983230072969 + 3 ^ 40 * 2155198 * 2
def baseEnd_2155198 : Nat := 1106652479608764011613431

theorem tailTrace_2155198 : CollatzResearch.WordTrace tailWord_2155198 prefixEnd_2155198 1106652479608764011613431 := by
  unfold tailWord_2155198
  simp only [CollatzResearch.WordTrace]
  refine ⟨9825816105761649919910281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52404352564062132906188165 9825816105761649919910281)
  ·
    refine ⟨7369362079321237439932711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9825816105761649919910281 7369362079321237439932711)
    ·
      refine ⟨11054043118981856159899067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7369362079321237439932711 11054043118981856159899067)
      ·
        refine ⟨16581064678472784239848601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11054043118981856159899067 16581064678472784239848601)
        ·
          refine ⟨12435798508854588179886451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16581064678472784239848601 12435798508854588179886451)
          ·
            refine ⟨18653697763281882269829677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12435798508854588179886451 18653697763281882269829677)
            ·
              refine ⟨6995136661230705851186129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18653697763281882269829677 6995136661230705851186129)
              ·
                refine ⟨5246352495923029388389597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6995136661230705851186129 5246352495923029388389597)
                ·
                  refine ⟨1967382185971136020646099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5246352495923029388389597 1967382185971136020646099)
                  ·
                    refine ⟨2951073278956704030969149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1967382185971136020646099 2951073278956704030969149)
                    ·
                      refine ⟨1106652479608764011613431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2951073278956704030969149 1106652479608764011613431)
                      ·
                        rfl

theorem cell23_2155198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_2155198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155198 prefixEnd_2155198 := by exact prefixLift 2155198
  have htrace : WordTrace (prefixWord ++ tailWord_2155198) baseStart_2155198 baseEnd_2155198 := by
    simpa [prefixWord, tailWord_2155198, baseEnd_2155198] using wordTrace_append hprefix tailTrace_2155198
  have hstable : (prefixWord ++ tailWord_2155198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155198).length < 2 ^ (prefixWord ++ tailWord_2155198).sum := by decide
  have hdescent : baseEnd_2155198 < baseStart_2155198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155208 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 2, 3, 2]
def baseStart_2155208 : Nat := 118140960795 + 2155208 * 2 ^ 59
def prefixEnd_2155208 : Nat := 4983230072969 + 3 ^ 40 * 2155208 * 2
def baseEnd_2155208 : Nat := 1106657614415308972488385

theorem tailTrace_2155208 : CollatzResearch.WordTrace tailWord_2155208 prefixEnd_2155208 1106657614415308972488385 := by
  unfold tailWord_2155208
  simp only [CollatzResearch.WordTrace]
  refine ⟨39303446788028485533573139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52404595717371314044764185 39303446788028485533573139)
  ·
    refine ⟨58955170182042728300359709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39303446788028485533573139 58955170182042728300359709)
    ·
      refine ⟨22108188818266023112634891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58955170182042728300359709 22108188818266023112634891)
      ·
        refine ⟨33162283227399034668952337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22108188818266023112634891 33162283227399034668952337)
        ·
          refine ⟨24871712420549276001714253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33162283227399034668952337 24871712420549276001714253)
          ·
            refine ⟨9326892157705978500642845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24871712420549276001714253 9326892157705978500642845)
            ·
              refine ⟨3497584559139741937741067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9326892157705978500642845 3497584559139741937741067)
              ·
                refine ⟨5246376838709612906611601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497584559139741937741067 5246376838709612906611601)
                ·
                  refine ⟨3934782629032209679958701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5246376838709612906611601 3934782629032209679958701)
                  ·
                    refine ⟨1475543485887078629984513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3934782629032209679958701 1475543485887078629984513)
                    ·
                      refine ⟨1106657614415308972488385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475543485887078629984513 1106657614415308972488385)
                      ·
                        rfl

theorem cell23_2155208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 2, 3, 2].length) (baseStart_2155208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155208 prefixEnd_2155208 := by exact prefixLift 2155208
  have htrace : WordTrace (prefixWord ++ tailWord_2155208) baseStart_2155208 baseEnd_2155208 := by
    simpa [prefixWord, tailWord_2155208, baseEnd_2155208] using wordTrace_append hprefix tailTrace_2155208
  have hstable : (prefixWord ++ tailWord_2155208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155208).length < 2 ^ (prefixWord ++ tailWord_2155208).sum := by decide
  have hdescent : baseEnd_2155208 < baseStart_2155208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155218 : List Nat := [3, 2, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_2155218 : Nat := 118140960795 + 2155218 * 2 ^ 59
def prefixEnd_2155218 : Nat := 4983230072969 + 3 ^ 40 * 2155218 * 2
def baseEnd_2155218 : Nat := 368887583073951311121113

theorem tailTrace_2155218 : CollatzResearch.WordTrace tailWord_2155218 prefixEnd_2155218 368887583073951311121113 := by
  unfold tailWord_2155218
  simp only [CollatzResearch.WordTrace]
  refine ⟨19651814576505185693752577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52404838870680495183340205 19651814576505185693752577)
  ·
    refine ⟨14738860932378889270314433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19651814576505185693752577 14738860932378889270314433)
    ·
      refine ⟨11054145699284166952735825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14738860932378889270314433 11054145699284166952735825)
      ·
        refine ⟨8290609274463125214551869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11054145699284166952735825 8290609274463125214551869)
        ·
          refine ⟨3108978477923671955456951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8290609274463125214551869 3108978477923671955456951)
          ·
            refine ⟨4663467716885507933185427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3108978477923671955456951 4663467716885507933185427)
            ·
              refine ⟨6995201575328261899778141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4663467716885507933185427 6995201575328261899778141)
              ·
                refine ⟨2623200590748098212416803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6995201575328261899778141 2623200590748098212416803)
                ·
                  refine ⟨3934800886122147318625205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2623200590748098212416803 3934800886122147318625205)
                  ·
                    refine ⟨368887583073951311121113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3934800886122147318625205 368887583073951311121113)
                    ·
                      rfl

theorem cell23_2155218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_2155218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155218 prefixEnd_2155218 := by exact prefixLift 2155218
  have htrace : WordTrace (prefixWord ++ tailWord_2155218) baseStart_2155218 baseEnd_2155218 := by
    simpa [prefixWord, tailWord_2155218, baseEnd_2155218] using wordTrace_append hprefix tailTrace_2155218
  have hstable : (prefixWord ++ tailWord_2155218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155218).length < 2 ^ (prefixWord ++ tailWord_2155218).sum := by decide
  have hdescent : baseEnd_2155218 < baseStart_2155218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155231 : List Nat := [1, 1, 2, 3, 2, 4, 1, 1, 4, 4]
def baseStart_2155231 : Nat := 118140960795 + 2155231 * 2 ^ 59
def prefixEnd_2155231 : Nat := 4983230072969 + 3 ^ 40 * 2155231 * 2
def baseEnd_2155231 : Nat := 368889808156787460833593

theorem tailTrace_2155231 : CollatzResearch.WordTrace tailWord_2155231 prefixEnd_2155231 368889808156787460833593 := by
  unfold tailWord_2155231
  simp only [CollatzResearch.WordTrace]
  refine ⟨78607732454973645995233547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52405154969982430663489031 78607732454973645995233547)
  ·
    refine ⟨117911598682460468992850321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78607732454973645995233547 117911598682460468992850321)
    ·
      refine ⟨88433699011845351744637741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117911598682460468992850321 88433699011845351744637741)
      ·
        refine ⟨33162637129442006904239153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88433699011845351744637741 33162637129442006904239153)
        ·
          refine ⟨24871977847081505178179365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33162637129442006904239153 24871977847081505178179365)
          ·
            refine ⟨4663495846327782220908631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24871977847081505178179365 4663495846327782220908631)
            ·
              refine ⟨6995243769491673331362947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4663495846327782220908631 6995243769491673331362947)
              ·
                refine ⟨10492865654237509997044421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6995243769491673331362947 10492865654237509997044421)
                ·
                  refine ⟨1967412310169533124445829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10492865654237509997044421 1967412310169533124445829)
                  ·
                    refine ⟨368889808156787460833593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1967412310169533124445829 368889808156787460833593)
                    ·
                      rfl

theorem cell23_2155231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 4].length) (baseStart_2155231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155231 prefixEnd_2155231 := by exact prefixLift 2155231
  have htrace : WordTrace (prefixWord ++ tailWord_2155231) baseStart_2155231 baseEnd_2155231 := by
    simpa [prefixWord, tailWord_2155231, baseEnd_2155231] using wordTrace_append hprefix tailTrace_2155231
  have hstable : (prefixWord ++ tailWord_2155231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155231).length < 2 ^ (prefixWord ++ tailWord_2155231).sum := by decide
  have hdescent : baseEnd_2155231 < baseStart_2155231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155248 : List Nat := [2, 1, 1, 1, 3, 1, 7, 1, 2, 4]
def baseStart_2155248 : Nat := 118140960795 + 2155248 * 2 ^ 59
def prefixEnd_2155248 : Nat := 4983230072969 + 3 ^ 40 * 2155248 * 2
def baseEnd_2155248 : Nat := 368892717880496271996067

theorem tailTrace_2155248 : CollatzResearch.WordTrace tailWord_2155248 prefixEnd_2155248 368892717880496271996067 := by
  unfold tailWord_2155248
  simp only [CollatzResearch.WordTrace]
  refine ⟨39304176247956028949301199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52405568330608038599068265 39304176247956028949301199)
  ·
    refine ⟨58956264371934043423951799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39304176247956028949301199 58956264371934043423951799)
    ·
      refine ⟨88434396557901065135927699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58956264371934043423951799 88434396557901065135927699)
      ·
        refine ⟨132651594836851597703891549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88434396557901065135927699 132651594836851597703891549)
        ·
          refine ⟨49744348063819349138959331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132651594836851597703891549 49744348063819349138959331)
          ·
            refine ⟨74616522095729023708438997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49744348063819349138959331 74616522095729023708438997)
            ·
              refine ⟨1748824736618648993166539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 74616522095729023708438997 1748824736618648993166539)
              ·
                refine ⟨2623237104927973489749809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1748824736618648993166539 2623237104927973489749809)
                ·
                  refine ⟨1967427828695980117312357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2623237104927973489749809 1967427828695980117312357)
                  ·
                    refine ⟨368892717880496271996067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1967427828695980117312357 368892717880496271996067)
                    ·
                      rfl

theorem cell23_2155248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 2, 4].length) (baseStart_2155248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155248 prefixEnd_2155248 := by exact prefixLift 2155248
  have htrace : WordTrace (prefixWord ++ tailWord_2155248) baseStart_2155248 baseEnd_2155248 := by
    simpa [prefixWord, tailWord_2155248, baseEnd_2155248] using wordTrace_append hprefix tailTrace_2155248
  have hstable : (prefixWord ++ tailWord_2155248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155248).length < 2 ^ (prefixWord ++ tailWord_2155248).sum := by decide
  have hdescent : baseEnd_2155248 < baseStart_2155248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155252 : List Nat := [2, 6, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2155252 : Nat := 118140960795 + 2155252 * 2 ^ 59
def prefixEnd_2155252 : Nat := 4983230072969 + 3 ^ 40 * 2155252 * 2
def baseEnd_2155252 : Nat := 368893402521368933446061

theorem tailTrace_2155252 : CollatzResearch.WordTrace tailWord_2155252 prefixEnd_2155252 368893402521368933446061 := by
  unfold tailWord_2155252
  simp only [CollatzResearch.WordTrace]
  refine ⟨39304249193948783290874005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52405665591931711054498673 39304249193948783290874005)
  ·
    refine ⟨1842386680966349216759719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39304249193948783290874005 1842386680966349216759719)
    ·
      refine ⟨2763580021449523825139579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1842386680966349216759719 2763580021449523825139579)
      ·
        refine ⟨4145370032174285737709369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2763580021449523825139579 4145370032174285737709369)
        ·
          refine ⟨3109027524130714303282027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4145370032174285737709369 3109027524130714303282027)
          ·
            refine ⟨4663541286196071454923041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3109027524130714303282027 4663541286196071454923041)
            ·
              refine ⟨3497655964647053591192281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4663541286196071454923041 3497655964647053591192281)
              ·
                refine ⟨2623241973485290193394211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3497655964647053591192281 2623241973485290193394211)
                ·
                  refine ⟨3934862960227935290091317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2623241973485290193394211 3934862960227935290091317)
                  ·
                    refine ⟨368893402521368933446061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3934862960227935290091317 368893402521368933446061)
                    ·
                      rfl

theorem cell23_2155252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2155252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155252 prefixEnd_2155252 := by exact prefixLift 2155252
  have htrace : WordTrace (prefixWord ++ tailWord_2155252) baseStart_2155252 baseEnd_2155252 := by
    simpa [prefixWord, tailWord_2155252, baseEnd_2155252] using wordTrace_append hprefix tailTrace_2155252
  have hstable : (prefixWord ++ tailWord_2155252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155252).length < 2 ^ (prefixWord ++ tailWord_2155252).sum := by decide
  have hdescent : baseEnd_2155252 < baseStart_2155252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155272 : List Nat := [2, 1, 3, 2, 2, 2, 3, 3, 1, 2, 2]
def baseStart_2155272 : Nat := 118140960795 + 2155272 * 2 ^ 59
def prefixEnd_2155272 : Nat := 4983230072969 + 3 ^ 40 * 2155272 * 2
def baseEnd_2155272 : Nat := 1106690477177196722088091

theorem tailTrace_2155272 : CollatzResearch.WordTrace tailWord_2155272 prefixEnd_2155272 1106690477177196722088091 := by
  unfold tailWord_2155272
  simp only [CollatzResearch.WordTrace]
  refine ⟨39304613923912554998738035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52406151898550073331650713 39304613923912554998738035)
  ·
    refine ⟨58956920885868832498107053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39304613923912554998738035 58956920885868832498107053)
    ·
      refine ⟨22108845332200812186790145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58956920885868832498107053 22108845332200812186790145)
      ·
        refine ⟨16581633999150609140092609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22108845332200812186790145 16581633999150609140092609)
        ·
          refine ⟨12436225499362956855069457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16581633999150609140092609 12436225499362956855069457)
          ·
            refine ⟨9327169124522217641302093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12436225499362956855069457 9327169124522217641302093)
            ·
              refine ⟨3497688421695831615488285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9327169124522217641302093 3497688421695831615488285)
              ·
                refine ⟨1311633158135936855808107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3497688421695831615488285 1311633158135936855808107)
                ·
                  refine ⟨1967449737203905283712161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311633158135936855808107 1967449737203905283712161)
                  ·
                    refine ⟨1475587302902928962784121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1967449737203905283712161 1475587302902928962784121)
                    ·
                      refine ⟨1106690477177196722088091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475587302902928962784121 1106690477177196722088091)
                      ·
                        rfl

theorem cell23_2155272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_2155272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155272 prefixEnd_2155272 := by exact prefixLift 2155272
  have htrace : WordTrace (prefixWord ++ tailWord_2155272) baseStart_2155272 baseEnd_2155272 := by
    simpa [prefixWord, tailWord_2155272, baseEnd_2155272] using wordTrace_append hprefix tailTrace_2155272
  have hstable : (prefixWord ++ tailWord_2155272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155272).length < 2 ^ (prefixWord ++ tailWord_2155272).sum := by decide
  have hdescent : baseEnd_2155272 < baseStart_2155272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155288 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2155288 : Nat := 118140960795 + 2155288 * 2 ^ 59
def prefixEnd_2155288 : Nat := 4983230072969 + 3 ^ 40 * 2155288 * 2
def baseEnd_2155288 : Nat := 1106698692867668659488017

theorem tailTrace_2155288 : CollatzResearch.WordTrace tailWord_2155288 prefixEnd_2155288 1106698692867668659488017 := by
  unfold tailWord_2155288
  simp only [CollatzResearch.WordTrace]
  refine ⟨39304905707883572365029259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52406540943844763153372345 39304905707883572365029259)
  ·
    refine ⟨58957358561825358547543889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39304905707883572365029259 58957358561825358547543889)
    ·
      refine ⟨44218018921369018910657917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58957358561825358547543889 44218018921369018910657917)
      ·
        refine ⟨16581757095513382091496719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44218018921369018910657917 16581757095513382091496719)
        ·
          refine ⟨24872635643270073137245079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16581757095513382091496719 24872635643270073137245079)
          ·
            refine ⟨37308953464905109705867619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24872635643270073137245079 37308953464905109705867619)
            ·
              refine ⟨55963430197357664558801429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37308953464905109705867619 55963430197357664558801429)
              ·
                refine ⟨2623285790501140526193817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55963430197357664558801429 2623285790501140526193817)
                ·
                  refine ⟨1967464342875855394645363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2623285790501140526193817 1967464342875855394645363)
                  ·
                    refine ⟨2951196514313783091968045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1967464342875855394645363 2951196514313783091968045)
                    ·
                      refine ⟨1106698692867668659488017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2951196514313783091968045 1106698692867668659488017)
                      ·
                        rfl

theorem cell23_2155288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2155288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155288 prefixEnd_2155288 := by exact prefixLift 2155288
  have htrace : WordTrace (prefixWord ++ tailWord_2155288) baseStart_2155288 baseEnd_2155288 := by
    simpa [prefixWord, tailWord_2155288, baseEnd_2155288] using wordTrace_append hprefix tailTrace_2155288
  have hstable : (prefixWord ++ tailWord_2155288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155288).length < 2 ^ (prefixWord ++ tailWord_2155288).sum := by decide
  have hdescent : baseEnd_2155288 < baseStart_2155288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155309 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2155309 : Nat := 118140960795 + 2155309 * 2 ^ 59
def prefixEnd_2155309 : Nat := 4983230072969 + 3 ^ 40 * 2155309 * 2
def baseEnd_2155309 : Nat := 1106709475961413077325421

theorem tailTrace_2155309 : CollatzResearch.WordTrace tailWord_2155309 prefixEnd_2155309 1106709475961413077325421 := by
  unfold tailWord_2155309
  simp only [CollatzResearch.WordTrace]
  refine ⟨78610577348691065316572981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52407051565794043544381987 78610577348691065316572981)
  ·
    refine ⟨7369741626439787373428717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78610577348691065316572981 7369741626439787373428717)
    ·
      refine ⟨2763653109914920265035769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7369741626439787373428717 2763653109914920265035769)
      ·
        refine ⟨2072739832436190198776827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2763653109914920265035769 2072739832436190198776827)
        ·
          refine ⟨3109109748654285298165241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2072739832436190198776827 3109109748654285298165241)
          ·
            refine ⟨2331832311490713973623931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3109109748654285298165241 2331832311490713973623931)
            ·
              refine ⟨3497748467236070960435897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2331832311490713973623931 3497748467236070960435897)
              ·
                refine ⟨2623311350427053220326923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3497748467236070960435897 2623311350427053220326923)
                ·
                  refine ⟨3934967025640579830490385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2623311350427053220326923 3934967025640579830490385)
                  ·
                    refine ⟨2951225269230434872867789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3934967025640579830490385 2951225269230434872867789)
                    ·
                      refine ⟨1106709475961413077325421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2951225269230434872867789 1106709475961413077325421)
                      ·
                        rfl

theorem cell23_2155309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2155309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155309 prefixEnd_2155309 := by exact prefixLift 2155309
  have htrace : WordTrace (prefixWord ++ tailWord_2155309) baseStart_2155309 baseEnd_2155309 := by
    simpa [prefixWord, tailWord_2155309, baseEnd_2155309] using wordTrace_append hprefix tailTrace_2155309
  have hstable : (prefixWord ++ tailWord_2155309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155309).length < 2 ^ (prefixWord ++ tailWord_2155309).sum := by decide
  have hdescent : baseEnd_2155309 < baseStart_2155309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155315 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 1, 3, 2]
def baseStart_2155315 : Nat := 118140960795 + 2155315 * 2 ^ 59
def prefixEnd_2155315 : Nat := 4983230072969 + 3 ^ 40 * 2155315 * 2
def baseEnd_2155315 : Nat := 1106712556845340053850393

theorem tailTrace_2155315 : CollatzResearch.WordTrace tailWord_2155315 prefixEnd_2155315 1106712556845340053850393 := by
  unfold tailWord_2155315
  simp only [CollatzResearch.WordTrace]
  refine ⟨78610796186669328341291399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52407197457779552227527599 78610796186669328341291399)
  ·
    refine ⟨117916194280003992511937099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78610796186669328341291399 117916194280003992511937099)
    ·
      refine ⟨176874291420005988767905649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117916194280003992511937099 176874291420005988767905649)
      ·
        refine ⟨132655718565004491575929237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176874291420005988767905649 132655718565004491575929237)
        ·
          refine ⟨6218236807734585542621683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 132655718565004491575929237 6218236807734585542621683)
          ·
            refine ⟨9327355211601878313932525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6218236807734585542621683 9327355211601878313932525)
            ·
              refine ⟨3497758204350704367724697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9327355211601878313932525 3497758204350704367724697)
              ·
                refine ⟨2623318653263028275793523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3497758204350704367724697 2623318653263028275793523)
                ·
                  refine ⟨3934977979894542413690285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2623318653263028275793523 3934977979894542413690285)
                  ·
                    refine ⟨1475616742460453405133857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3934977979894542413690285 1475616742460453405133857)
                    ·
                      refine ⟨1106712556845340053850393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475616742460453405133857 1106712556845340053850393)
                      ·
                        rfl

theorem cell23_2155315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 1, 3, 2].length) (baseStart_2155315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155315 prefixEnd_2155315 := by exact prefixLift 2155315
  have htrace : WordTrace (prefixWord ++ tailWord_2155315) baseStart_2155315 baseEnd_2155315 := by
    simpa [prefixWord, tailWord_2155315, baseEnd_2155315] using wordTrace_append hprefix tailTrace_2155315
  have hstable : (prefixWord ++ tailWord_2155315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155315).length < 2 ^ (prefixWord ++ tailWord_2155315).sum := by decide
  have hdescent : baseEnd_2155315 < baseStart_2155315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155328 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 6, 2, 2]
def baseStart_2155328 : Nat := 118140960795 + 2155328 * 2 ^ 59
def prefixEnd_2155328 : Nat := 4983230072969 + 3 ^ 40 * 2155328 * 2
def baseEnd_2155328 : Nat := 1106719232093848502987833

theorem tailTrace_2155328 : CollatzResearch.WordTrace tailWord_2155328 prefixEnd_2155328 1106719232093848502987833 := by
  unfold tailWord_2155328
  simp only [CollatzResearch.WordTrace]
  refine ⟨39305635167811115780757319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52407513557081487707676425 39305635167811115780757319)
  ·
    refine ⟨58958452751716673671135979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39305635167811115780757319 58958452751716673671135979)
    ·
      refine ⟨88437679127575010506703969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58958452751716673671135979 88437679127575010506703969)
      ·
        refine ⟨66328259345681257880027977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88437679127575010506703969 66328259345681257880027977)
        ·
          refine ⟨49746194509260943410020983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66328259345681257880027977 49746194509260943410020983)
          ·
            refine ⟨74619291763891415115031475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49746194509260943410020983 74619291763891415115031475)
            ·
              refine ⟨111928937645837122672547213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74619291763891415115031475 111928937645837122672547213)
              ·
                refine ⟨41973351617188921002205205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111928937645837122672547213 41973351617188921002205205)
                ·
                  refine ⟨1967500857055730671978369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 41973351617188921002205205 1967500857055730671978369)
                  ·
                    refine ⟨1475625642791798003983777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1967500857055730671978369 1475625642791798003983777)
                    ·
                      refine ⟨1106719232093848502987833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475625642791798003983777 1106719232093848502987833)
                      ·
                        rfl

theorem cell23_2155328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 6, 2, 2].length) (baseStart_2155328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155328 prefixEnd_2155328 := by exact prefixLift 2155328
  have htrace : WordTrace (prefixWord ++ tailWord_2155328) baseStart_2155328 baseEnd_2155328 := by
    simpa [prefixWord, tailWord_2155328, baseEnd_2155328] using wordTrace_append hprefix tailTrace_2155328
  have hstable : (prefixWord ++ tailWord_2155328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155328).length < 2 ^ (prefixWord ++ tailWord_2155328).sum := by decide
  have hdescent : baseEnd_2155328 < baseStart_2155328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155344 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 7]
def baseStart_2155344 : Nat := 118140960795 + 2155344 * 2 ^ 59
def prefixEnd_2155344 : Nat := 4983230072969 + 3 ^ 40 * 2155344 * 2
def baseEnd_2155344 : Nat := 1106727447784320440387759

theorem tailTrace_2155344 : CollatzResearch.WordTrace tailWord_2155344 prefixEnd_2155344 1106727447784320440387759 := by
  unfold tailWord_2155344
  simp only [CollatzResearch.WordTrace]
  refine ⟨39305926951782133147048543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52407902602376177529398057 39305926951782133147048543)
  ·
    refine ⟨58958890427673199720572815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39305926951782133147048543 58958890427673199720572815)
    ·
      refine ⟨88438335641509799580859223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58958890427673199720572815 88438335641509799580859223)
      ·
        refine ⟨132657503462264699371288835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88438335641509799580859223 132657503462264699371288835)
        ·
          refine ⟨198986255193397049056933253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132657503462264699371288835 198986255193397049056933253)
          ·
            refine ⟨37309922848761946698174985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198986255193397049056933253 37309922848761946698174985)
            ·
              refine ⟨27982442136571460023631239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37309922848761946698174985 27982442136571460023631239)
              ·
                refine ⟨41973663204857190035446859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27982442136571460023631239 41973663204857190035446859)
                ·
                  refine ⟨62960494807285785053170289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41973663204857190035446859 62960494807285785053170289)
                  ·
                    refine ⟨47220371105464338789877717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62960494807285785053170289 47220371105464338789877717)
                    ·
                      refine ⟨1106727447784320440387759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47220371105464338789877717 1106727447784320440387759)
                      ·
                        rfl

theorem cell23_2155344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_2155344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155344 prefixEnd_2155344 := by exact prefixLift 2155344
  have htrace : WordTrace (prefixWord ++ tailWord_2155344) baseStart_2155344 baseEnd_2155344 := by
    simpa [prefixWord, tailWord_2155344, baseEnd_2155344] using wordTrace_append hprefix tailTrace_2155344
  have hstable : (prefixWord ++ tailWord_2155344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155344).length < 2 ^ (prefixWord ++ tailWord_2155344).sum := by decide
  have hdescent : baseEnd_2155344 < baseStart_2155344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155362 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_2155362 : Nat := 118140960795 + 2155362 * 2 ^ 59
def prefixEnd_2155362 : Nat := 4983230072969 + 3 ^ 40 * 2155362 * 2
def baseEnd_2155362 : Nat := 1106736690436101369962677

theorem tailTrace_2155362 : CollatzResearch.WordTrace tailWord_2155362 prefixEnd_2155362 1106736690436101369962677 := by
  unfold tailWord_2155362
  simp only [CollatzResearch.WordTrace]
  refine ⟨19653127604374763842063085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52408340278332703578834893 19653127604374763842063085)
  ·
    refine ⟨7369922851640536440773657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19653127604374763842063085 7369922851640536440773657)
    ·
      refine ⟨5527442138730402330580243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7369922851640536440773657 5527442138730402330580243)
      ·
        refine ⟨8291163208095603495870365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5527442138730402330580243 8291163208095603495870365)
        ·
          refine ⟨3109186203035851310951387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8291163208095603495870365 3109186203035851310951387)
          ·
            refine ⟨4663779304553776966427081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3109186203035851310951387 4663779304553776966427081)
            ·
              refine ⟨3497834478415332724820311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4663779304553776966427081 3497834478415332724820311)
              ·
                refine ⟨5246751717622999087230467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3497834478415332724820311 5246751717622999087230467)
                ·
                  refine ⟨7870127576434498630845701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5246751717622999087230467 7870127576434498630845701)
                  ·
                    refine ⟨1475648920581468493283569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7870127576434498630845701 1475648920581468493283569)
                    ·
                      refine ⟨1106736690436101369962677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475648920581468493283569 1106736690436101369962677)
                      ·
                        rfl

theorem cell23_2155362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_2155362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155362 prefixEnd_2155362 := by exact prefixLift 2155362
  have htrace : WordTrace (prefixWord ++ tailWord_2155362) baseStart_2155362 baseEnd_2155362 := by
    simpa [prefixWord, tailWord_2155362, baseEnd_2155362] using wordTrace_append hprefix tailTrace_2155362
  have hstable : (prefixWord ++ tailWord_2155362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155362).length < 2 ^ (prefixWord ++ tailWord_2155362).sum := by decide
  have hdescent : baseEnd_2155362 < baseStart_2155362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155428 : List Nat := [2, 3, 1, 2, 1, 2, 1, 4, 3, 4]
def baseStart_2155428 : Nat := 118140960795 + 2155428 * 2 ^ 59
def prefixEnd_2155428 : Nat := 4983230072969 + 3 ^ 40 * 2155428 * 2
def baseEnd_2155428 : Nat := 368923526719766037245791

theorem tailTrace_2155428 : CollatzResearch.WordTrace tailWord_2155428 prefixEnd_2155428 368923526719766037245791 := by
  unfold tailWord_2155428
  simp only [CollatzResearch.WordTrace]
  refine ⟨39307458817629974320077469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52409945090173299093436625 39307458817629974320077469)
  ·
    refine ⟨14740297056611240370029051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39307458817629974320077469 14740297056611240370029051)
    ·
      refine ⟨22110445584916860555043577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14740297056611240370029051 22110445584916860555043577)
      ·
        refine ⟨16582834188687645416282683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22110445584916860555043577 16582834188687645416282683)
        ·
          refine ⟨24874251283031468124424025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16582834188687645416282683 24874251283031468124424025)
          ·
            refine ⟨18655688462273601093318019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24874251283031468124424025 18655688462273601093318019)
            ·
              refine ⟨27983532693410401639977029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18655688462273601093318019 27983532693410401639977029)
              ·
                refine ⟨5246912380014450307495693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27983532693410401639977029 5246912380014450307495693)
                ·
                  refine ⟨1967592142505418865310885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5246912380014450307495693 1967592142505418865310885)
                  ·
                    refine ⟨368923526719766037245791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1967592142505418865310885 368923526719766037245791)
                    ·
                      rfl

theorem cell23_2155428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_2155428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155428 prefixEnd_2155428 := by exact prefixLift 2155428
  have htrace : WordTrace (prefixWord ++ tailWord_2155428) baseStart_2155428 baseEnd_2155428 := by
    simpa [prefixWord, tailWord_2155428, baseEnd_2155428] using wordTrace_append hprefix tailTrace_2155428
  have hstable : (prefixWord ++ tailWord_2155428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155428).length < 2 ^ (prefixWord ++ tailWord_2155428).sum := by decide
  have hdescent : baseEnd_2155428 < baseStart_2155428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155451 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 3]
def baseStart_2155451 : Nat := 118140960795 + 2155451 * 2 ^ 59
def prefixEnd_2155451 : Nat := 4983230072969 + 3 ^ 40 * 2155451 * 2
def baseEnd_2155451 : Nat := 1106782390214351521749767

theorem tailTrace_2155451 : CollatzResearch.WordTrace tailWord_2155451 prefixEnd_2155451 1106782390214351521749767 := by
  unfold tailWord_2155451
  simp only [CollatzResearch.WordTrace]
  refine ⟨78615756514176623568242207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52410504342784415712161471 78615756514176623568242207)
  ·
    refine ⟨117923634771264935352363311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78615756514176623568242207 117923634771264935352363311)
    ·
      refine ⟨176885452156897403028544967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117923634771264935352363311 176885452156897403028544967)
      ·
        refine ⟨265328178235346104542817451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176885452156897403028544967 265328178235346104542817451)
        ·
          refine ⟨397992267353019156814226177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265328178235346104542817451 397992267353019156814226177)
          ·
            refine ⟨298494200514764367610669633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397992267353019156814226177 298494200514764367610669633)
            ·
              refine ⟨223870650386073275708002225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298494200514764367610669633 223870650386073275708002225)
              ·
                refine ⟨167902987789554956781001669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223870650386073275708002225 167902987789554956781001669)
                ·
                  refine ⟨31481810210541554396437813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167902987789554956781001669 31481810210541554396437813)
                  ·
                    refine ⟨2951419707238270724666045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31481810210541554396437813 2951419707238270724666045)
                    ·
                      refine ⟨1106782390214351521749767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2951419707238270724666045 1106782390214351521749767)
                      ·
                        rfl

theorem cell23_2155451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5, 3].length) (baseStart_2155451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155451 prefixEnd_2155451 := by exact prefixLift 2155451
  have htrace : WordTrace (prefixWord ++ tailWord_2155451) baseStart_2155451 baseEnd_2155451 := by
    simpa [prefixWord, tailWord_2155451, baseEnd_2155451] using wordTrace_append hprefix tailTrace_2155451
  have hstable : (prefixWord ++ tailWord_2155451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155451).length < 2 ^ (prefixWord ++ tailWord_2155451).sum := by decide
  have hdescent : baseEnd_2155451 < baseStart_2155451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155559 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_2155559 : Nat := 118140960795 + 2155559 * 2 ^ 59
def prefixEnd_2155559 : Nat := 4983230072969 + 3 ^ 40 * 2155559 * 2
def baseEnd_2155559 : Nat := 1106837846125037099199271

theorem tailTrace_2155559 : CollatzResearch.WordTrace tailWord_2155559 prefixEnd_2155559 1106837846125037099199271 := by
  unfold tailWord_2155559
  simp only [CollatzResearch.WordTrace]
  refine ⟨78619695597785358013173731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52413130398523572008782487 78619695597785358013173731)
  ·
    refine ⟨117929543396678037019760597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78619695597785358013173731 117929543396678037019760597)
    ·
      refine ⟨2763973673359641492650639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 117929543396678037019760597 2763973673359641492650639)
      ·
        refine ⟨4145960510039462238975959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2763973673359641492650639 4145960510039462238975959)
        ·
          refine ⟨6218940765059193358463939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4145960510039462238975959 6218940765059193358463939)
          ·
            refine ⟨9328411147588790037695909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6218940765059193358463939 9328411147588790037695909)
            ·
              refine ⟨1749077090172898132067983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9328411147588790037695909 1749077090172898132067983)
              ·
                refine ⟨2623615635259347198101975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749077090172898132067983 2623615635259347198101975)
                ·
                  refine ⟨3935423452889020797152963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2623615635259347198101975 3935423452889020797152963)
                  ·
                    refine ⟨5903135179333531195729445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3935423452889020797152963 5903135179333531195729445)
                    ·
                      refine ⟨1106837846125037099199271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5903135179333531195729445 1106837846125037099199271)
                      ·
                        rfl

theorem cell23_2155559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_2155559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155559 prefixEnd_2155559 := by exact prefixLift 2155559
  have htrace : WordTrace (prefixWord ++ tailWord_2155559) baseStart_2155559 baseEnd_2155559 := by
    simpa [prefixWord, tailWord_2155559, baseEnd_2155559] using wordTrace_append hprefix tailTrace_2155559
  have hstable : (prefixWord ++ tailWord_2155559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155559).length < 2 ^ (prefixWord ++ tailWord_2155559).sum := by decide
  have hdescent : baseEnd_2155559 < baseStart_2155559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155615 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 3, 4, 2]
def baseStart_2155615 : Nat := 118140960795 + 2155615 * 2 ^ 59
def prefixEnd_2155615 : Nat := 4983230072969 + 3 ^ 40 * 2155615 * 2
def baseEnd_2155615 : Nat := 1106866601041688880099013

theorem tailTrace_2155615 : CollatzResearch.WordTrace tailWord_2155615 prefixEnd_2155615 1106866601041688880099013 := by
  unfold tailWord_2155615
  simp only [CollatzResearch.WordTrace]
  refine ⟨78621738085582479577212299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52414492057054986384808199 78621738085582479577212299)
  ·
    refine ⟨117932607128373719365818449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78621738085582479577212299 117932607128373719365818449)
    ·
      refine ⟨88449455346280289524363837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117932607128373719365818449 88449455346280289524363837)
      ·
        refine ⟨33168545754855108571636439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88449455346280289524363837 33168545754855108571636439)
        ·
          refine ⟨49752818632282662857454659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33168545754855108571636439 49752818632282662857454659)
          ·
            refine ⟨74629227948423994286181989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49752818632282662857454659 74629227948423994286181989)
            ·
              refine ⟨13992980240329498928659123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74629227948423994286181989 13992980240329498928659123)
              ·
                refine ⟨20989470360494248392988685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13992980240329498928659123 20989470360494248392988685)
                ·
                  refine ⟨7871051385185343147370757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20989470360494248392988685 7871051385185343147370757)
                  ·
                    refine ⟨1475822134722251840132017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7871051385185343147370757 1475822134722251840132017)
                    ·
                      refine ⟨1106866601041688880099013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475822134722251840132017 1106866601041688880099013)
                      ·
                        rfl

theorem cell23_2155615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 4, 2].length) (baseStart_2155615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155615 prefixEnd_2155615 := by exact prefixLift 2155615
  have htrace : WordTrace (prefixWord ++ tailWord_2155615) baseStart_2155615 baseEnd_2155615 := by
    simpa [prefixWord, tailWord_2155615, baseEnd_2155615] using wordTrace_append hprefix tailTrace_2155615
  have hstable : (prefixWord ++ tailWord_2155615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155615).length < 2 ^ (prefixWord ++ tailWord_2155615).sum := by decide
  have hdescent : baseEnd_2155615 < baseStart_2155615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155632 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 4, 2, 2]
def baseStart_2155632 : Nat := 118140960795 + 2155632 * 2 ^ 59
def prefixEnd_2155632 : Nat := 4983230072969 + 3 ^ 40 * 2155632 * 2
def baseEnd_2155632 : Nat := 1106875330212815313586435

theorem tailTrace_2155632 : CollatzResearch.WordTrace tailWord_2155632 prefixEnd_2155632 1106875330212815313586435 := by
  unfold tailWord_2155632
  simp only [CollatzResearch.WordTrace]
  refine ⟨39311179063260445740290575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52414905417680594320387433 39311179063260445740290575)
  ·
    refine ⟨58966768594890668610435863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39311179063260445740290575 58966768594890668610435863)
    ·
      refine ⟨88450152892336002915653795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58966768594890668610435863 88450152892336002915653795)
      ·
        refine ⟨132675229338504004373480693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88450152892336002915653795 132675229338504004373480693)
        ·
          refine ⟨12438302750484750410013815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132675229338504004373480693 12438302750484750410013815)
          ·
            refine ⟨18657454125727125615020723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12438302750484750410013815 18657454125727125615020723)
            ·
              refine ⟨27986181188590688422531085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18657454125727125615020723 27986181188590688422531085)
              ·
                refine ⟨10494817945721508158449157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27986181188590688422531085 10494817945721508158449157)
                ·
                  refine ⟨1967778364822782779709217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10494817945721508158449157 1967778364822782779709217)
                  ·
                    refine ⟨1475833773617087084781913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1967778364822782779709217 1475833773617087084781913)
                    ·
                      refine ⟨1106875330212815313586435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475833773617087084781913 1106875330212815313586435)
                      ·
                        rfl

theorem cell23_2155632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4, 2, 2].length) (baseStart_2155632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155632 prefixEnd_2155632 := by exact prefixLift 2155632
  have htrace : WordTrace (prefixWord ++ tailWord_2155632) baseStart_2155632 baseEnd_2155632 := by
    simpa [prefixWord, tailWord_2155632, baseEnd_2155632] using wordTrace_append hprefix tailTrace_2155632
  have hstable : (prefixWord ++ tailWord_2155632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155632).length < 2 ^ (prefixWord ++ tailWord_2155632).sum := by decide
  have hdescent : baseEnd_2155632 < baseStart_2155632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155685 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_2155685 : Nat := 118140960795 + 2155685 * 2 ^ 59
def prefixEnd_2155685 : Nat := 4983230072969 + 3 ^ 40 * 2155685 * 2
def baseEnd_2155685 : Nat := 368967514895834535407897

theorem tailTrace_2155685 : CollatzResearch.WordTrace tailWord_2155685 prefixEnd_2155685 368967514895834535407897 := by
  unfold tailWord_2155685
  simp only [CollatzResearch.WordTrace]
  refine ⟨78624291195328881532260509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52416194130219254354840339 78624291195328881532260509)
  ·
    refine ⟨29484109198248330574597691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78624291195328881532260509 29484109198248330574597691)
    ·
      refine ⟨44226163797372495861896537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29484109198248330574597691 44226163797372495861896537)
      ·
        refine ⟨33169622848029371896422403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44226163797372495861896537 33169622848029371896422403)
        ·
          refine ⟨49754434272044057844633605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33169622848029371896422403 49754434272044057844633605)
          ·
            refine ⟨9328956426008260845868801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49754434272044057844633605 9328956426008260845868801)
            ·
              refine ⟨6996717319506195634401601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9328956426008260845868801 6996717319506195634401601)
              ·
                refine ⟨5247537989629646725801201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6996717319506195634401601 5247537989629646725801201)
                ·
                  refine ⟨3935653492222235044350901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5247537989629646725801201 3935653492222235044350901)
                  ·
                    refine ⟨368967514895834535407897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3935653492222235044350901 368967514895834535407897)
                    ·
                      rfl

theorem cell23_2155685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_2155685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155685 prefixEnd_2155685 := by exact prefixLift 2155685
  have htrace : WordTrace (prefixWord ++ tailWord_2155685) baseStart_2155685 baseEnd_2155685 := by
    simpa [prefixWord, tailWord_2155685, baseEnd_2155685] using wordTrace_append hprefix tailTrace_2155685
  have hstable : (prefixWord ++ tailWord_2155685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155685).length < 2 ^ (prefixWord ++ tailWord_2155685).sum := by decide
  have hdescent : baseEnd_2155685 < baseStart_2155685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155722 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_2155722 : Nat := 118140960795 + 2155722 * 2 ^ 59
def prefixEnd_2155722 : Nat := 4983230072969 + 3 ^ 40 * 2155722 * 2
def baseEnd_2155722 : Nat := 1106921543471719961461021

theorem tailTrace_2155722 : CollatzResearch.WordTrace tailWord_2155722 prefixEnd_2155722 1106921543471719961461021 := by
  unfold tailWord_2155722
  simp only [CollatzResearch.WordTrace]
  refine ⟨19656410174048709212839355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52417093797463224567571613 19656410174048709212839355)
  ·
    refine ⟨29484615261073063819259033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19656410174048709212839355 29484615261073063819259033)
    ·
      refine ⟨22113461445804797864444275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29484615261073063819259033 22113461445804797864444275)
      ·
        refine ⟨33170192168707196796666413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22113461445804797864444275 33170192168707196796666413)
        ·
          refine ⟨12438822063265198798749905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33170192168707196796666413 12438822063265198798749905)
          ·
            refine ⟨9329116547448899099062429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12438822063265198798749905 9329116547448899099062429)
            ·
              refine ⟨3498418705293337162148411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9329116547448899099062429 3498418705293337162148411)
              ·
                refine ⟨5247628057940005743222617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498418705293337162148411 5247628057940005743222617)
                ·
                  refine ⟨3935721043455004307416963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5247628057940005743222617 3935721043455004307416963)
                  ·
                    refine ⟨5903581565182506461125445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3935721043455004307416963 5903581565182506461125445)
                    ·
                      refine ⟨1106921543471719961461021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5903581565182506461125445 1106921543471719961461021)
                      ·
                        rfl

theorem cell23_2155722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_2155722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155722 prefixEnd_2155722 := by exact prefixLift 2155722
  have htrace : WordTrace (prefixWord ++ tailWord_2155722) baseStart_2155722 baseEnd_2155722 := by
    simpa [prefixWord, tailWord_2155722, baseEnd_2155722] using wordTrace_append hprefix tailTrace_2155722
  have hstable : (prefixWord ++ tailWord_2155722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155722).length < 2 ^ (prefixWord ++ tailWord_2155722).sum := by decide
  have hdescent : baseEnd_2155722 < baseStart_2155722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155745 : List Nat := [1, 2, 3, 1, 3, 3, 1, 1, 8]
def baseStart_2155745 : Nat := 118140960795 + 2155745 * 2 ^ 59
def prefixEnd_2155745 : Nat := 4983230072969 + 3 ^ 40 * 2155745 * 2
def baseEnd_2155745 : Nat := 122992594836308152385935

theorem tailTrace_2155745 : CollatzResearch.WordTrace tailWord_2155745 prefixEnd_2155745 122992594836308152385935 := by
  unfold tailWord_2155745
  simp only [CollatzResearch.WordTrace]
  refine ⟨78626479575111511779444689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52417653050074341186296459 78626479575111511779444689)
  ·
    refine ⟨58969859681333633834583517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78626479575111511779444689 58969859681333633834583517)
    ·
      refine ⟨22113697380500112687968819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58969859681333633834583517 22113697380500112687968819)
      ·
        refine ⟨33170546070750169031953229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22113697380500112687968819 33170546070750169031953229)
        ·
          refine ⟨12438954776531313386982461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33170546070750169031953229 12438954776531313386982461)
          ·
            refine ⟨4664608041199242520118423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12438954776531313386982461 4664608041199242520118423)
            ·
              refine ⟨6996912061798863780177635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4664608041199242520118423 6996912061798863780177635)
              ·
                refine ⟨10495368092698295670266453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6996912061798863780177635 10495368092698295670266453)
                ·
                  refine ⟨122992594836308152385935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10495368092698295670266453 122992594836308152385935)
                  ·
                    rfl

theorem cell23_2155745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 1, 8].length) (baseStart_2155745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155745 prefixEnd_2155745 := by exact prefixLift 2155745
  have htrace : WordTrace (prefixWord ++ tailWord_2155745) baseStart_2155745 baseEnd_2155745 := by
    simpa [prefixWord, tailWord_2155745, baseEnd_2155745] using wordTrace_append hprefix tailTrace_2155745
  have hstable : (prefixWord ++ tailWord_2155745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155745).length < 2 ^ (prefixWord ++ tailWord_2155745).sum := by decide
  have hdescent : baseEnd_2155745 < baseStart_2155745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155749 : List Nat := [1, 3, 1, 4, 3, 1, 2, 1, 3, 4]
def baseStart_2155749 : Nat := 118140960795 + 2155749 * 2 ^ 59
def prefixEnd_2155749 : Nat := 4983230072969 + 3 ^ 40 * 2155749 * 2
def baseEnd_2155749 : Nat := 368978469149797118607799

theorem tailTrace_2155749 : CollatzResearch.WordTrace tailWord_2155749 prefixEnd_2155749 368978469149797118607799 := by
  unfold tailWord_2155749
  simp only [CollatzResearch.WordTrace]
  refine ⟨78626625467097020462590301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52417750311398013641726867 78626625467097020462590301)
  ·
    refine ⟨29484984550161382673471363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78626625467097020462590301 29484984550161382673471363)
    ·
      refine ⟨44227476825242074010207045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29484984550161382673471363 44227476825242074010207045)
      ·
        refine ⟨8292651904732888876913821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44227476825242074010207045 8292651904732888876913821)
        ·
          refine ⟨3109744464274833328842683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8292651904732888876913821 3109744464274833328842683)
          ·
            refine ⟨4664616696412249993264025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3109744464274833328842683 4664616696412249993264025)
            ·
              refine ⟨3498462522309187494948019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4664616696412249993264025 3498462522309187494948019)
              ·
                refine ⟨5247693783463781242422029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3498462522309187494948019 5247693783463781242422029)
                ·
                  refine ⟨1967885168798917965908261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5247693783463781242422029 1967885168798917965908261)
                  ·
                    refine ⟨368978469149797118607799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1967885168798917965908261 368978469149797118607799)
                    ·
                      rfl

theorem cell23_2155749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_2155749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155749 prefixEnd_2155749 := by exact prefixLift 2155749
  have htrace : WordTrace (prefixWord ++ tailWord_2155749) baseStart_2155749 baseEnd_2155749 := by
    simpa [prefixWord, tailWord_2155749, baseEnd_2155749] using wordTrace_append hprefix tailTrace_2155749
  have hstable : (prefixWord ++ tailWord_2155749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155749).length < 2 ^ (prefixWord ++ tailWord_2155749).sum := by decide
  have hdescent : baseEnd_2155749 < baseStart_2155749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155795 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 4]
def baseStart_2155795 : Nat := 118140960795 + 2155795 * 2 ^ 59
def prefixEnd_2155795 : Nat := 4983230072969 + 3 ^ 40 * 2155795 * 2
def baseEnd_2155795 : Nat := 1106959027559498175848185

theorem tailTrace_2155795 : CollatzResearch.WordTrace tailWord_2155795 prefixEnd_2155795 1106959027559498175848185 := by
  unfold tailWord_2155795
  simp only [CollatzResearch.WordTrace]
  refine ⟨78628303224930370318764839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52418868816620246879176559 78628303224930370318764839)
  ·
    refine ⟨117942454837395555478147259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78628303224930370318764839 117942454837395555478147259)
    ·
      refine ⟨176913682256093333217220889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117942454837395555478147259 176913682256093333217220889)
      ·
        refine ⟨132685261692069999912915667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176913682256093333217220889 132685261692069999912915667)
        ·
          refine ⟨199027892538104999869373501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132685261692069999912915667 199027892538104999869373501)
          ·
            refine ⟨74635459701789374951015063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199027892538104999869373501 74635459701789374951015063)
            ·
              refine ⟨111953189552684062426522595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74635459701789374951015063 111953189552684062426522595)
              ·
                refine ⟨167929784329026093639783893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111953189552684062426522595 167929784329026093639783893)
                ·
                  refine ⟨3935854320211549069682435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 167929784329026093639783893 3935854320211549069682435)
                  ·
                    refine ⟨5903781480317323604523653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3935854320211549069682435 5903781480317323604523653)
                    ·
                      refine ⟨1106959027559498175848185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5903781480317323604523653 1106959027559498175848185)
                      ·
                        rfl

theorem cell23_2155795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_2155795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155795 prefixEnd_2155795 := by exact prefixLift 2155795
  have htrace : WordTrace (prefixWord ++ tailWord_2155795) baseStart_2155795 baseEnd_2155795 := by
    simpa [prefixWord, tailWord_2155795, baseEnd_2155795] using wordTrace_append hprefix tailTrace_2155795
  have hstable : (prefixWord ++ tailWord_2155795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155795).length < 2 ^ (prefixWord ++ tailWord_2155795).sum := by decide
  have hdescent : baseEnd_2155795 < baseStart_2155795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155799 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 2, 3, 2]
def baseStart_2155799 : Nat := 118140960795 + 2155799 * 2 ^ 59
def prefixEnd_2155799 : Nat := 4983230072969 + 3 ^ 40 * 2155799 * 2
def baseEnd_2155799 : Nat := 1106961081482116160198167

theorem tailTrace_2155799 : CollatzResearch.WordTrace tailWord_2155799 prefixEnd_2155799 1106961081482116160198167 := by
  unfold tailWord_2155799
  simp only [CollatzResearch.WordTrace]
  refine ⟨78628449116915879001910451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52418966077943919334606967 78628449116915879001910451)
  ·
    refine ⟨117942673675373818502865677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78628449116915879001910451 117942673675373818502865677)
    ·
      refine ⟨44228502628265181938574629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117942673675373818502865677 44228502628265181938574629)
      ·
        refine ⟨8292844242799721613482743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44228502628265181938574629 8292844242799721613482743)
        ·
          refine ⟨12439266364199582420224115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8292844242799721613482743 12439266364199582420224115)
          ·
            refine ⟨18658899546299373630336173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12439266364199582420224115 18658899546299373630336173)
            ·
              refine ⟨6997087329862265111376065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18658899546299373630336173 6997087329862265111376065)
              ·
                refine ⟨5247815497396698833532049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6997087329862265111376065 5247815497396698833532049)
                ·
                  refine ⟨3935861623047524125149037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5247815497396698833532049 3935861623047524125149037)
                  ·
                    refine ⟨1475948108642821546930889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3935861623047524125149037 1475948108642821546930889)
                    ·
                      refine ⟨1106961081482116160198167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475948108642821546930889 1106961081482116160198167)
                      ·
                        rfl

theorem cell23_2155799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_2155799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155799 prefixEnd_2155799 := by exact prefixLift 2155799
  have htrace : WordTrace (prefixWord ++ tailWord_2155799) baseStart_2155799 baseEnd_2155799 := by
    simpa [prefixWord, tailWord_2155799, baseEnd_2155799] using wordTrace_append hprefix tailTrace_2155799
  have hstable : (prefixWord ++ tailWord_2155799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155799).length < 2 ^ (prefixWord ++ tailWord_2155799).sum := by decide
  have hdescent : baseEnd_2155799 < baseStart_2155799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155812 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2155812 : Nat := 118140960795 + 2155812 * 2 ^ 59
def prefixEnd_2155812 : Nat := 4983230072969 + 3 ^ 40 * 2155812 * 2
def baseEnd_2155812 : Nat := 1106967756730624609335607

theorem tailTrace_2155812 : CollatzResearch.WordTrace tailWord_2155812 prefixEnd_2155812 1106967756730624609335607 := by
  unfold tailWord_2155812
  simp only [CollatzResearch.WordTrace]
  refine ⟨39314461632934391111066845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52419282177245854814755793 39314461632934391111066845)
  ·
    refine ⟨14742923112350396666650067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39314461632934391111066845 14742923112350396666650067)
    ·
      refine ⟨22114384668525594999975101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14742923112350396666650067 22114384668525594999975101)
      ·
        refine ⟨8292894250697098124990663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22114384668525594999975101 8292894250697098124990663)
        ·
          refine ⟨12439341376045647187485995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8292894250697098124990663 12439341376045647187485995)
          ·
            refine ⟨18659012064068470781228993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12439341376045647187485995 18659012064068470781228993)
            ·
              refine ⟨13994259048051353085921745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18659012064068470781228993 13994259048051353085921745)
              ·
                refine ⟨10495694286038514814441309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13994259048051353085921745 10495694286038514814441309)
                ·
                  refine ⟨3935885357264443055415491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10495694286038514814441309 3935885357264443055415491)
                  ·
                    refine ⟨5903828035896664583123237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3935885357264443055415491 5903828035896664583123237)
                    ·
                      refine ⟨1106967756730624609335607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5903828035896664583123237 1106967756730624609335607)
                      ·
                        rfl

theorem cell23_2155812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2155812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155812 prefixEnd_2155812 := by exact prefixLift 2155812
  have htrace : WordTrace (prefixWord ++ tailWord_2155812) baseStart_2155812 baseEnd_2155812 := by
    simpa [prefixWord, tailWord_2155812, baseEnd_2155812] using wordTrace_append hprefix tailTrace_2155812
  have hstable : (prefixWord ++ tailWord_2155812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155812).length < 2 ^ (prefixWord ++ tailWord_2155812).sum := by decide
  have hdescent : baseEnd_2155812 < baseStart_2155812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155829 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_2155829 : Nat := 118140960795 + 2155829 * 2 ^ 59
def prefixEnd_2155829 : Nat := 4983230072969 + 3 ^ 40 * 2155829 * 2
def baseEnd_2155829 : Nat := 1106976485901751042823029

theorem tailTrace_2155829 : CollatzResearch.WordTrace tailWord_2155829 prefixEnd_2155829 1106976485901751042823029 := by
  unfold tailWord_2155829
  simp only [CollatzResearch.WordTrace]
  refine ⟨78629543306807194125502541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52419695537871462750335027 78629543306807194125502541)
  ·
    refine ⟨29486078740052697797063453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78629543306807194125502541 29486078740052697797063453)
    ·
      refine ⟨11057279527519761673898795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29486078740052697797063453 11057279527519761673898795)
      ·
        refine ⟨16585919291279642510848193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11057279527519761673898795 16585919291279642510848193)
        ·
          refine ⟨12439439468459731883136145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16585919291279642510848193 12439439468459731883136145)
          ·
            refine ⟨9329579601344798912352109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12439439468459731883136145 9329579601344798912352109)
            ·
              refine ⟨3498592350504299592132041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9329579601344798912352109 3498592350504299592132041)
              ·
                refine ⟨2623944262878224694099031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3498592350504299592132041 2623944262878224694099031)
                ·
                  refine ⟨3935916394317337041148547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2623944262878224694099031 3935916394317337041148547)
                  ·
                    refine ⟨5903874591476005561722821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3935916394317337041148547 5903874591476005561722821)
                    ·
                      refine ⟨1106976485901751042823029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5903874591476005561722821 1106976485901751042823029)
                      ·
                        rfl

theorem cell23_2155829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_2155829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155829 prefixEnd_2155829 := by exact prefixLift 2155829
  have htrace : WordTrace (prefixWord ++ tailWord_2155829) baseStart_2155829 baseEnd_2155829 := by
    simpa [prefixWord, tailWord_2155829, baseEnd_2155829] using wordTrace_append hprefix tailTrace_2155829
  have hstable : (prefixWord ++ tailWord_2155829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155829).length < 2 ^ (prefixWord ++ tailWord_2155829).sum := by decide
  have hdescent : baseEnd_2155829 < baseStart_2155829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155863 : List Nat := [1, 1, 3, 2, 3, 3, 1, 4, 1, 2, 2]
def baseStart_2155863 : Nat := 118140960795 + 2155863 * 2 ^ 59
def prefixEnd_2155863 : Nat := 4983230072969 + 3 ^ 40 * 2155863 * 2
def baseEnd_2155863 : Nat := 1106993944244003909797873

theorem tailTrace_2155863 : CollatzResearch.WordTrace tailWord_2155863 prefixEnd_2155863 1106993944244003909797873 := by
  unfold tailWord_2155863
  simp only [CollatzResearch.WordTrace]
  refine ⟨78630783388684017932240243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52420522259122678621493495 78630783388684017932240243)
  ·
    refine ⟨117946175083026026898360365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78630783388684017932240243 117946175083026026898360365)
    ·
      refine ⟨44229815656134760086885137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117946175083026026898360365 44229815656134760086885137)
      ·
        refine ⟨33172361742101070065163853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44229815656134760086885137 33172361742101070065163853)
        ·
          refine ⟨12439635653287901274436445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33172361742101070065163853 12439635653287901274436445)
          ·
            refine ⟨4664863369982962977913667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12439635653287901274436445 4664863369982962977913667)
            ·
              refine ⟨6997295054974444466870501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4664863369982962977913667 6997295054974444466870501)
              ·
                refine ⟨1311992822807708337538219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6997295054974444466870501 1311992822807708337538219)
                ·
                  refine ⟨1967989234211562506307329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1311992822807708337538219 1967989234211562506307329)
                  ·
                    refine ⟨1475991925658671879730497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1967989234211562506307329 1475991925658671879730497)
                    ·
                      refine ⟨1106993944244003909797873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1475991925658671879730497 1106993944244003909797873)
                      ·
                        rfl

theorem cell23_2155863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_2155863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155863 prefixEnd_2155863 := by exact prefixLift 2155863
  have htrace : WordTrace (prefixWord ++ tailWord_2155863) baseStart_2155863 baseEnd_2155863 := by
    simpa [prefixWord, tailWord_2155863, baseEnd_2155863] using wordTrace_append hprefix tailTrace_2155863
  have hstable : (prefixWord ++ tailWord_2155863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155863).length < 2 ^ (prefixWord ++ tailWord_2155863).sum := by decide
  have hdescent : baseEnd_2155863 < baseStart_2155863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155865 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 2, 7]
def baseStart_2155865 : Nat := 118140960795 + 2155865 * 2 ^ 59
def prefixEnd_2155865 : Nat := 4983230072969 + 3 ^ 40 * 2155865 * 2
def baseEnd_2155865 : Nat := 368998323735104300657621

theorem tailTrace_2155865 : CollatzResearch.WordTrace tailWord_2155865 prefixEnd_2155865 368998323735104300657621 := by
  unfold tailWord_2155865
  simp only [CollatzResearch.WordTrace]
  refine ⟨78630856334676772273813049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52420570889784514849208699 78630856334676772273813049)
  ·
    refine ⟨58973142251007579205359787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78630856334676772273813049 58973142251007579205359787)
    ·
      refine ⟨88459713376511368808039681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58973142251007579205359787 88459713376511368808039681)
      ·
        refine ⟨66344785032383526606029761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88459713376511368808039681 66344785032383526606029761)
        ·
          refine ⟨49758588774287644954522321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66344785032383526606029761 49758588774287644954522321)
          ·
            refine ⟨37318941580715733715891741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49758588774287644954522321 37318941580715733715891741)
            ·
              refine ⟨13994603092768400143459403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37318941580715733715891741 13994603092768400143459403)
              ·
                refine ⟨20991904639152600215189105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13994603092768400143459403 20991904639152600215189105)
                ·
                  refine ⟨15743928479364450161391829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20991904639152600215189105 15743928479364450161391829)
                  ·
                    refine ⟨368998323735104300657621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15743928479364450161391829 368998323735104300657621)
                    ·
                      rfl

theorem cell23_2155865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_2155865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155865 prefixEnd_2155865 := by exact prefixLift 2155865
  have htrace : WordTrace (prefixWord ++ tailWord_2155865) baseStart_2155865 baseEnd_2155865 := by
    simpa [prefixWord, tailWord_2155865, baseEnd_2155865] using wordTrace_append hprefix tailTrace_2155865
  have hstable : (prefixWord ++ tailWord_2155865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155865).length < 2 ^ (prefixWord ++ tailWord_2155865).sum := by decide
  have hdescent : baseEnd_2155865 < baseStart_2155865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155886 : List Nat := [4, 1, 2, 4, 1, 1, 3, 7]
def baseStart_2155886 : Nat := 118140960795 + 2155886 * 2 ^ 59
def prefixEnd_2155886 : Nat := 4983230072969 + 3 ^ 40 * 2155886 * 2
def baseEnd_2155886 : Nat := 41000213122187308141121

theorem tailTrace_2155886 : CollatzResearch.WordTrace tailWord_2155886 prefixEnd_2155886 41000213122187308141121 := by
  unfold tailWord_2155886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9828952783450086607540939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52421081511733795240218341 9828952783450086607540939)
  ·
    refine ⟨14743429175175129911311409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9828952783450086607540939 14743429175175129911311409)
    ·
      refine ⟨11057571881381347433483557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14743429175175129911311409 11057571881381347433483557)
      ·
        refine ⟨2073294727759002643778167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11057571881381347433483557 2073294727759002643778167)
        ·
          refine ⟨3109942091638503965667251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2073294727759002643778167 3109942091638503965667251)
          ·
            refine ⟨4664913137457755948500877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3109942091638503965667251 4664913137457755948500877)
            ·
              refine ⟨1749342426546658480687829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4664913137457755948500877 1749342426546658480687829)
              ·
                refine ⟨41000213122187308141121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1749342426546658480687829 41000213122187308141121)
                ·
                  rfl

theorem cell23_2155886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_2155886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155886 prefixEnd_2155886 := by exact prefixLift 2155886
  have htrace : WordTrace (prefixWord ++ tailWord_2155886) baseStart_2155886 baseEnd_2155886 := by
    simpa [prefixWord, tailWord_2155886, baseEnd_2155886] using wordTrace_append hprefix tailTrace_2155886
  have hstable : (prefixWord ++ tailWord_2155886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155886).length < 2 ^ (prefixWord ++ tailWord_2155886).sum := by decide
  have hdescent : baseEnd_2155886 < baseStart_2155886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155889 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 3, 3, 2]
def baseStart_2155889 : Nat := 118140960795 + 2155889 * 2 ^ 59
def prefixEnd_2155889 : Nat := 4983230072969 + 3 ^ 40 * 2155889 * 2
def baseEnd_2155889 : Nat := 1107007294741020808072753

theorem tailTrace_2155889 : CollatzResearch.WordTrace tailWord_2155889 prefixEnd_2155889 1107007294741020808072753 := by
  unfold tailWord_2155889
  simp only [CollatzResearch.WordTrace]
  refine ⟨78631731686589824372686721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52421154457726549581791147 78631731686589824372686721)
  ·
    refine ⟨58973798764942368279515041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78631731686589824372686721 58973798764942368279515041)
    ·
      refine ⟨44230349073706776209636281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58973798764942368279515041 44230349073706776209636281)
      ·
        refine ⟨33172761805280082157227211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44230349073706776209636281 33172761805280082157227211)
        ·
          refine ⟨49759142707920123235840817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33172761805280082157227211 49759142707920123235840817)
          ·
            refine ⟨37319357030940092426880613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49759142707920123235840817 37319357030940092426880613)
            ·
              refine ⟨6997379443301267330040115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37319357030940092426880613 6997379443301267330040115)
              ·
                refine ⟨10496069164951900995060173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6997379443301267330040115 10496069164951900995060173)
                ·
                  refine ⟨3936025936856962873147565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10496069164951900995060173 3936025936856962873147565)
                  ·
                    refine ⟨1476009726321361077430337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3936025936856962873147565 1476009726321361077430337)
                    ·
                      refine ⟨1107007294741020808072753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1476009726321361077430337 1107007294741020808072753)
                      ·
                        rfl

theorem cell23_2155889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_2155889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155889 prefixEnd_2155889 := by exact prefixLift 2155889
  have htrace : WordTrace (prefixWord ++ tailWord_2155889) baseStart_2155889 baseEnd_2155889 := by
    simpa [prefixWord, tailWord_2155889, baseEnd_2155889] using wordTrace_append hprefix tailTrace_2155889
  have hstable : (prefixWord ++ tailWord_2155889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155889).length < 2 ^ (prefixWord ++ tailWord_2155889).sum := by decide
  have hdescent : baseEnd_2155889 < baseStart_2155889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155895 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 1, 8]
def baseStart_2155895 : Nat := 118140960795 + 2155895 * 2 ^ 59
def prefixEnd_2155895 : Nat := 4983230072969 + 3 ^ 40 * 2155895 * 2
def baseEnd_2155895 : Nat := 369003458541649261532575

theorem tailTrace_2155895 : CollatzResearch.WordTrace tailWord_2155895 prefixEnd_2155895 369003458541649261532575 := by
  unfold tailWord_2155895
  simp only [CollatzResearch.WordTrace]
  refine ⟨78631950524568087397405139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52421300349712058264936759 78631950524568087397405139)
  ·
    refine ⟨117947925786852131096107709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78631950524568087397405139 117947925786852131096107709)
    ·
      refine ⟨44230472170069549161040391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117947925786852131096107709 44230472170069549161040391)
      ·
        refine ⟨66345708255104323741560587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44230472170069549161040391 66345708255104323741560587)
        ·
          refine ⟨99518562382656485612340881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66345708255104323741560587 99518562382656485612340881)
          ·
            refine ⟨74638921786992364209255661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99518562382656485612340881 74638921786992364209255661)
            ·
              refine ⟨27989595670122136578470873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74638921786992364209255661 27989595670122136578470873)
              ·
                refine ⟨20992196752591602433853155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27989595670122136578470873 20992196752591602433853155)
                ·
                  refine ⟨31488295128887403650779733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20992196752591602433853155 31488295128887403650779733)
                  ·
                    refine ⟨369003458541649261532575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31488295128887403650779733 369003458541649261532575)
                    ·
                      rfl

theorem cell23_2155895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_2155895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155895 prefixEnd_2155895 := by exact prefixLift 2155895
  have htrace : WordTrace (prefixWord ++ tailWord_2155895) baseStart_2155895 baseEnd_2155895 := by
    simpa [prefixWord, tailWord_2155895, baseEnd_2155895] using wordTrace_append hprefix tailTrace_2155895
  have hstable : (prefixWord ++ tailWord_2155895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155895).length < 2 ^ (prefixWord ++ tailWord_2155895).sum := by decide
  have hdescent : baseEnd_2155895 < baseStart_2155895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155912 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 2, 6]
def baseStart_2155912 : Nat := 118140960795 + 2155912 * 2 ^ 59
def prefixEnd_2155912 : Nat := 4983230072969 + 3 ^ 40 * 2155912 * 2
def baseEnd_2155912 : Nat := 369006368265358072695049

theorem tailTrace_2155912 : CollatzResearch.WordTrace tailWord_2155912 prefixEnd_2155912 369006368265358072695049 := by
  unfold tailWord_2155912
  simp only [CollatzResearch.WordTrace]
  refine ⟨39316285282753249650386995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52421713710337666200515993 39316285282753249650386995)
  ·
    refine ⟨58974427924129874475580493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39316285282753249650386995 58974427924129874475580493)
    ·
      refine ⟨22115410471548702928342685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58974427924129874475580493 22115410471548702928342685)
      ·
        refine ⟨8293278926830763598128507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22115410471548702928342685 8293278926830763598128507)
        ·
          refine ⟨12439918390246145397192761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8293278926830763598128507 12439918390246145397192761)
          ·
            refine ⟨9329938792684609047894571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12439918390246145397192761 9329938792684609047894571)
            ·
              refine ⟨13994908189026913571841857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9329938792684609047894571 13994908189026913571841857)
              ·
                refine ⟨10496181141770185178881393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13994908189026913571841857 10496181141770185178881393)
                ·
                  refine ⟨7872135856327638884161045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10496181141770185178881393 7872135856327638884161045)
                  ·
                    refine ⟨369006368265358072695049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7872135856327638884161045 369006368265358072695049)
                    ·
                      rfl

theorem cell23_2155912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_2155912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155912 prefixEnd_2155912 := by exact prefixLift 2155912
  have htrace : WordTrace (prefixWord ++ tailWord_2155912) baseStart_2155912 baseEnd_2155912 := by
    simpa [prefixWord, tailWord_2155912, baseEnd_2155912] using wordTrace_append hprefix tailTrace_2155912
  have hstable : (prefixWord ++ tailWord_2155912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155912).length < 2 ^ (prefixWord ++ tailWord_2155912).sum := by decide
  have hdescent : baseEnd_2155912 < baseStart_2155912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155913 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 2, 1, 3]
def baseStart_2155913 : Nat := 118140960795 + 2155913 * 2 ^ 59
def prefixEnd_2155913 : Nat := 4983230072969 + 3 ^ 40 * 2155913 * 2
def baseEnd_2155913 : Nat := 1107019618276728714172643

theorem tailTrace_2155913 : CollatzResearch.WordTrace tailWord_2155913 prefixEnd_2155913 1107019618276728714172643 := by
  unfold tailWord_2155913
  simp only [CollatzResearch.WordTrace]
  refine ⟨78632607038502876471560393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52421738025668584314373595 78632607038502876471560393)
  ·
    refine ⟨58974455278877157353670295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78632607038502876471560393 58974455278877157353670295)
    ·
      refine ⟨88461682918315736030505443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58974455278877157353670295 88461682918315736030505443)
      ·
        refine ⟨132692524377473604045758165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88461682918315736030505443 132692524377473604045758165)
        ·
          refine ⟨3109981040097037594822457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 132692524377473604045758165 3109981040097037594822457)
          ·
            refine ⟨2332485780072778196116843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3109981040097037594822457 2332485780072778196116843)
            ·
              refine ⟨3498728670109167294175265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2332485780072778196116843 3498728670109167294175265)
              ·
                refine ⟨2624046502581875470631449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3498728670109167294175265 2624046502581875470631449)
                ·
                  refine ⟨1968034876936406602973587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2624046502581875470631449 1968034876936406602973587)
                  ·
                    refine ⟨2952052315404609904460381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1968034876936406602973587 2952052315404609904460381)
                    ·
                      refine ⟨1107019618276728714172643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2952052315404609904460381 1107019618276728714172643)
                      ·
                        rfl

theorem cell23_2155913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 1, 3].length) (baseStart_2155913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155913 prefixEnd_2155913 := by exact prefixLift 2155913
  have htrace : WordTrace (prefixWord ++ tailWord_2155913) baseStart_2155913 baseEnd_2155913 := by
    simpa [prefixWord, tailWord_2155913, baseEnd_2155913] using wordTrace_append hprefix tailTrace_2155913
  have hstable : (prefixWord ++ tailWord_2155913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155913).length < 2 ^ (prefixWord ++ tailWord_2155913).sum := by decide
  have hdescent : baseEnd_2155913 < baseStart_2155913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155952 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 3]
def baseStart_2155952 : Nat := 118140960795 + 2155952 * 2 ^ 59
def prefixEnd_2155952 : Nat := 4983230072969 + 3 ^ 40 * 2155952 * 2
def baseEnd_2155952 : Nat := 1107039644022254061584963

theorem tailTrace_2155952 : CollatzResearch.WordTrace tailWord_2155952 prefixEnd_2155952 1107039644022254061584963 := by
  unfold tailWord_2155952
  simp only [CollatzResearch.WordTrace]
  refine ⟨39317014742680793066115055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52422686323574390754820073 39317014742680793066115055)
  ·
    refine ⟨58975522114021189599172583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39317014742680793066115055 58975522114021189599172583)
    ·
      refine ⟨88463283171031784398758875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58975522114021189599172583 88463283171031784398758875)
      ·
        refine ⟨132694924756547676598138313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88463283171031784398758875 132694924756547676598138313)
        ·
          refine ⟨99521193567410757448603735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132694924756547676598138313 99521193567410757448603735)
          ·
            refine ⟨149281790351116136172905603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99521193567410757448603735 149281790351116136172905603)
            ·
              refine ⟨223922685526674204259358405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149281790351116136172905603 223922685526674204259358405)
              ·
                refine ⟨41985503536251413298629701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223922685526674204259358405 41985503536251413298629701)
                ·
                  refine ⟨7872281913047139993493069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41985503536251413298629701 7872281913047139993493069)
                  ·
                    refine ⟨2952105717392677497559901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7872281913047139993493069 2952105717392677497559901)
                    ·
                      refine ⟨1107039644022254061584963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2952105717392677497559901 1107039644022254061584963)
                      ·
                        rfl

theorem cell23_2155952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 3].length) (baseStart_2155952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155952 prefixEnd_2155952 := by exact prefixLift 2155952
  have htrace : WordTrace (prefixWord ++ tailWord_2155952) baseStart_2155952 baseEnd_2155952 := by
    simpa [prefixWord, tailWord_2155952, baseEnd_2155952] using wordTrace_append hprefix tailTrace_2155952
  have hstable : (prefixWord ++ tailWord_2155952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155952).length < 2 ^ (prefixWord ++ tailWord_2155952).sum := by decide
  have hdescent : baseEnd_2155952 < baseStart_2155952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155976 : List Nat := [2, 1, 3, 1, 3, 1, 5, 2, 5]
def baseStart_2155976 : Nat := 118140960795 + 2155976 * 2 ^ 59
def prefixEnd_2155976 : Nat := 4983230072969 + 3 ^ 40 * 2155976 * 2
def baseEnd_2155976 : Nat := 123005774173106885298317

theorem tailTrace_2155976 : CollatzResearch.WordTrace tailWord_2155976 prefixEnd_2155976 123005774173106885298317 := by
  unfold tailWord_2155976
  simp only [CollatzResearch.WordTrace]
  refine ⟨39317452418637319115551891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52423269891516425487402521 39317452418637319115551891)
  ·
    refine ⟨58976178627955978673327837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39317452418637319115551891 58976178627955978673327837)
    ·
      refine ⟨22116066985483492002497939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58976178627955978673327837 22116066985483492002497939)
      ·
        refine ⟨33174100478225238003746909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22116066985483492002497939 33174100478225238003746909)
        ·
          refine ⟨12440287679334464251405091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33174100478225238003746909 12440287679334464251405091)
          ·
            refine ⟨18660431519001696377107637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12440287679334464251405091 18660431519001696377107637)
            ·
              refine ⟨1749415454906409035353841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18660431519001696377107637 1749415454906409035353841)
              ·
                refine ⟨1312061591179806776515381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1749415454906409035353841 1312061591179806776515381)
                ·
                  refine ⟨123005774173106885298317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1312061591179806776515381 123005774173106885298317)
                  ·
                    rfl

theorem cell23_2155976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2, 5].length) (baseStart_2155976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155976 prefixEnd_2155976 := by exact prefixLift 2155976
  have htrace : WordTrace (prefixWord ++ tailWord_2155976) baseStart_2155976 baseEnd_2155976 := by
    simpa [prefixWord, tailWord_2155976, baseEnd_2155976] using wordTrace_append hprefix tailTrace_2155976
  have hstable : (prefixWord ++ tailWord_2155976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155976).length < 2 ^ (prefixWord ++ tailWord_2155976).sum := by decide
  have hdescent : baseEnd_2155976 < baseStart_2155976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155982 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7]
def baseStart_2155982 : Nat := 118140960795 + 2155982 * 2 ^ 59
def prefixEnd_2155982 : Nat := 4983230072969 + 3 ^ 40 * 2155982 * 2
def baseEnd_2155982 : Nat := 1107055048441888944209825

theorem tailTrace_2155982 : CollatzResearch.WordTrace tailWord_2155982 prefixEnd_2155982 1107055048441888944209825 := by
  unfold tailWord_2155982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9829390459406612656977775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52423415783501934170548133 9829390459406612656977775)
  ·
    refine ⟨14744085689109918985466663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9829390459406612656977775 14744085689109918985466663)
    ·
      refine ⟨22116128533664878478199995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14744085689109918985466663 22116128533664878478199995)
      ·
        refine ⟨33174192800497317717299993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22116128533664878478199995 33174192800497317717299993)
        ·
          refine ⟨24880644600372988287974995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33174192800497317717299993 24880644600372988287974995)
          ·
            refine ⟨37320966900559482431962493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24880644600372988287974995 37320966900559482431962493)
            ·
              refine ⟨13995362587709805911985935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37320966900559482431962493 13995362587709805911985935)
              ·
                refine ⟨20993043881564708867978903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13995362587709805911985935 20993043881564708867978903)
                ·
                  refine ⟨31489565822347063301968355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20993043881564708867978903 31489565822347063301968355)
                  ·
                    refine ⟨47234348733520594952952533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31489565822347063301968355 47234348733520594952952533)
                    ·
                      refine ⟨1107055048441888944209825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47234348733520594952952533 1107055048441888944209825)
                      ·
                        rfl

theorem cell23_2155982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_2155982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155982 prefixEnd_2155982 := by exact prefixLift 2155982
  have htrace : WordTrace (prefixWord ++ tailWord_2155982) baseStart_2155982 baseEnd_2155982 := by
    simpa [prefixWord, tailWord_2155982, baseEnd_2155982] using wordTrace_append hprefix tailTrace_2155982
  have hstable : (prefixWord ++ tailWord_2155982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155982).length < 2 ^ (prefixWord ++ tailWord_2155982).sum := by decide
  have hdescent : baseEnd_2155982 < baseStart_2155982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2155992 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2155992 : Nat := 118140960795 + 2155992 * 2 ^ 59
def prefixEnd_2155992 : Nat := 4983230072969 + 3 ^ 40 * 2155992 * 2
def baseEnd_2155992 : Nat := 1107060183248433905084779

theorem tailTrace_2155992 : CollatzResearch.WordTrace tailWord_2155992 prefixEnd_2155992 1107060183248433905084779 := by
  unfold tailWord_2155992
  simp only [CollatzResearch.WordTrace]
  refine ⟨39317744202608336481843115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52423658936811115309124153 39317744202608336481843115)
  ·
    refine ⟨58976616303912504722764673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39317744202608336481843115 58976616303912504722764673)
    ·
      refine ⟨44232462227934378542073505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58976616303912504722764673 44232462227934378542073505)
      ·
        refine ⟨33174346670950783906555129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44232462227934378542073505 33174346670950783906555129)
        ·
          refine ⟨24880760003213087929916347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33174346670950783906555129 24880760003213087929916347)
          ·
            refine ⟨37321140004819631894874521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24880760003213087929916347 37321140004819631894874521)
            ·
              refine ⟨27990855003614723921155891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37321140004819631894874521 27990855003614723921155891)
              ·
                refine ⟨41986282505422085881733837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27990855003614723921155891 41986282505422085881733837)
                ·
                  refine ⟨15744855939533282205650189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41986282505422085881733837 15744855939533282205650189)
                  ·
                    refine ⟨5904320977324980827118821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15744855939533282205650189 5904320977324980827118821)
                    ·
                      refine ⟨1107060183248433905084779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5904320977324980827118821 1107060183248433905084779)
                      ·
                        rfl

theorem cell23_2155992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2155992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2155992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2155992 prefixEnd_2155992 := by exact prefixLift 2155992
  have htrace : WordTrace (prefixWord ++ tailWord_2155992) baseStart_2155992 baseEnd_2155992 := by
    simpa [prefixWord, tailWord_2155992, baseEnd_2155992] using wordTrace_append hprefix tailTrace_2155992
  have hstable : (prefixWord ++ tailWord_2155992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2155992).length < 2 ^ (prefixWord ++ tailWord_2155992).sum := by decide
  have hdescent : baseEnd_2155992 < baseStart_2155992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2155992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156116 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_2156116 : Nat := 118140960795 + 2156116 * 2 ^ 59
def prefixEnd_2156116 : Nat := 4983230072969 + 3 ^ 40 * 2156116 * 2
def baseEnd_2156116 : Nat := 1107123854849591419934209

theorem tailTrace_2156116 : CollatzResearch.WordTrace tailWord_2156116 prefixEnd_2156116 1107123854849591419934209 := by
  unfold tailWord_2156116
  simp only [CollatzResearch.WordTrace]
  refine ⟨39320005528383721070600101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52426674037844961427466801 39320005528383721070600101)
  ·
    refine ⟨7372501036571947700737519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39320005528383721070600101 7372501036571947700737519)
    ·
      refine ⟨11058751554857921551106279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7372501036571947700737519 11058751554857921551106279)
      ·
        refine ⟨16588127332286882326659419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11058751554857921551106279 16588127332286882326659419)
        ·
          refine ⟨24882190998430323489989129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16588127332286882326659419 24882190998430323489989129)
          ·
            refine ⟨18661643248822742617491847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24882190998430323489989129 18661643248822742617491847)
            ·
              refine ⟨27992464873234113926237771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18661643248822742617491847 27992464873234113926237771)
              ·
                refine ⟨41988697309851170889356657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27992464873234113926237771 41988697309851170889356657)
                ·
                  refine ⟨31491522982388378167017493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41988697309851170889356657 31491522982388378167017493)
                  ·
                    refine ⟨1476165139799455226578945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31491522982388378167017493 1476165139799455226578945)
                    ·
                      refine ⟨1107123854849591419934209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1476165139799455226578945 1107123854849591419934209)
                      ·
                        rfl

theorem cell23_2156116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_2156116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156116 prefixEnd_2156116 := by exact prefixLift 2156116
  have htrace : WordTrace (prefixWord ++ tailWord_2156116) baseStart_2156116 baseEnd_2156116 := by
    simpa [prefixWord, tailWord_2156116, baseEnd_2156116] using wordTrace_append hprefix tailTrace_2156116
  have hstable : (prefixWord ++ tailWord_2156116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156116).length < 2 ^ (prefixWord ++ tailWord_2156116).sum := by decide
  have hdescent : baseEnd_2156116 < baseStart_2156116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156129 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_2156129 : Nat := 118140960795 + 2156129 * 2 ^ 59
def prefixEnd_2156129 : Nat := 4983230072969 + 3 ^ 40 * 2156129 * 2
def baseEnd_2156129 : Nat := 1107130530098099869071649

theorem tailTrace_2156129 : CollatzResearch.WordTrace tailWord_2156129 prefixEnd_2156129 1107130530098099869071649 := by
  unfold tailWord_2156129
  simp only [CollatzResearch.WordTrace]
  refine ⟨78640485205720345361423441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52426990137146896907615627 78640485205720345361423441)
  ·
    refine ⟨58980363904290259021067581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78640485205720345361423441 58980363904290259021067581)
    ·
      refine ⟨22117636464108847132900343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58980363904290259021067581 22117636464108847132900343)
      ·
        refine ⟨33176454696163270699350515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22117636464108847132900343 33176454696163270699350515)
        ·
          refine ⟨49764682044244906049025773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33176454696163270699350515 49764682044244906049025773)
          ·
            refine ⟨18661755766591839768384665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49764682044244906049025773 18661755766591839768384665)
            ·
              refine ⟨13996316824943879826288499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18661755766591839768384665 13996316824943879826288499)
              ·
                refine ⟨20994475237415819739432749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13996316824943879826288499 20994475237415819739432749)
                ·
                  refine ⟨7872928214030932402287281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20994475237415819739432749 7872928214030932402287281)
                  ·
                    refine ⟨5904696160523199301715461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7872928214030932402287281 5904696160523199301715461)
                    ·
                      refine ⟨1107130530098099869071649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5904696160523199301715461 1107130530098099869071649)
                      ·
                        rfl

theorem cell23_2156129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_2156129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156129 prefixEnd_2156129 := by exact prefixLift 2156129
  have htrace : WordTrace (prefixWord ++ tailWord_2156129) baseStart_2156129 baseEnd_2156129 := by
    simpa [prefixWord, tailWord_2156129, baseEnd_2156129] using wordTrace_append hprefix tailTrace_2156129
  have hstable : (prefixWord ++ tailWord_2156129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156129).length < 2 ^ (prefixWord ++ tailWord_2156129).sum := by decide
  have hdescent : baseEnd_2156129 < baseStart_2156129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156136 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2156136 : Nat := 118140960795 + 2156136 * 2 ^ 59
def prefixEnd_2156136 : Nat := 4983230072969 + 3 ^ 40 * 2156136 * 2
def baseEnd_2156136 : Nat := 1107134124462681341684117

theorem tailTrace_2156136 : CollatzResearch.WordTrace tailWord_2156136 prefixEnd_2156136 1107134124462681341684117 := by
  unfold tailWord_2156136
  simp only [CollatzResearch.WordTrace]
  refine ⟨39320370258347492778464131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52427160344463323704618841 39320370258347492778464131)
  ·
    refine ⟨58980555387521239167696197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39320370258347492778464131 58980555387521239167696197)
    ·
      refine ⟨11058854135160232343943037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58980555387521239167696197 11058854135160232343943037)
      ·
        refine ⟨4147070300685087128978639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11058854135160232343943037 4147070300685087128978639)
        ·
          refine ⟨6220605451027630693467959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4147070300685087128978639 6220605451027630693467959)
          ·
            refine ⟨9330908176541446040201939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6220605451027630693467959 9330908176541446040201939)
            ·
              refine ⟨13996362264812169060302909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9330908176541446040201939 13996362264812169060302909)
              ·
                refine ⟨5248635849304563397613591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13996362264812169060302909 5248635849304563397613591)
                ·
                  refine ⟨7872953773956845096420387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5248635849304563397613591 7872953773956845096420387)
                  ·
                    refine ⟨11809430660935267644630581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7872953773956845096420387 11809430660935267644630581)
                    ·
                      refine ⟨1107134124462681341684117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11809430660935267644630581 1107134124462681341684117)
                      ·
                        rfl

theorem cell23_2156136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2156136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156136 prefixEnd_2156136 := by exact prefixLift 2156136
  have htrace : WordTrace (prefixWord ++ tailWord_2156136) baseStart_2156136 baseEnd_2156136 := by
    simpa [prefixWord, tailWord_2156136, baseEnd_2156136] using wordTrace_append hprefix tailTrace_2156136
  have hstable : (prefixWord ++ tailWord_2156136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156136).length < 2 ^ (prefixWord ++ tailWord_2156136).sum := by decide
  have hdescent : baseEnd_2156136 < baseStart_2156136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156170 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2156170 : Nat := 118140960795 + 2156170 * 2 ^ 59
def prefixEnd_2156170 : Nat := 4983230072969 + 3 ^ 40 * 2156170 * 2
def baseEnd_2156170 : Nat := 1107151582804934208658961

theorem tailTrace_2156170 : CollatzResearch.WordTrace tailWord_2156170 prefixEnd_2156170 1107151582804934208658961 := by
  unfold tailWord_2156170
  simp only [CollatzResearch.WordTrace]
  refine ⟨19660495149642952340916491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52427987065714539575777309 19660495149642952340916491)
  ·
    refine ⟨29490742724464428511374737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19660495149642952340916491 29490742724464428511374737)
    ·
      refine ⟨22118057043348321383531053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29490742724464428511374737 22118057043348321383531053)
      ·
        refine ⟨8294271391255620518824145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22118057043348321383531053 8294271391255620518824145)
        ·
          refine ⟨6220703543441715389118109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8294271391255620518824145 6220703543441715389118109)
          ·
            refine ⟨2332763828790643270919291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6220703543441715389118109 2332763828790643270919291)
            ·
              refine ⟨3499145743185964906378937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2332763828790643270919291 3499145743185964906378937)
              ·
                refine ⟨2624359307389473679784203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3499145743185964906378937 2624359307389473679784203)
                ·
                  refine ⟨3936538961084210519676305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2624359307389473679784203 3936538961084210519676305)
                  ·
                    refine ⟨2952404220813157889757229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3936538961084210519676305 2952404220813157889757229)
                    ·
                      refine ⟨1107151582804934208658961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2952404220813157889757229 1107151582804934208658961)
                      ·
                        rfl

theorem cell23_2156170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2156170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156170 prefixEnd_2156170 := by exact prefixLift 2156170
  have htrace : WordTrace (prefixWord ++ tailWord_2156170) baseStart_2156170 baseEnd_2156170 := by
    simpa [prefixWord, tailWord_2156170, baseEnd_2156170] using wordTrace_append hprefix tailTrace_2156170
  have hstable : (prefixWord ++ tailWord_2156170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156170).length < 2 ^ (prefixWord ++ tailWord_2156170).sum := by decide
  have hdescent : baseEnd_2156170 < baseStart_2156170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156223 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 1, 4, 2]
def baseStart_2156223 : Nat := 118140960795 + 2156223 * 2 ^ 59
def prefixEnd_2156223 : Nat := 4983230072969 + 3 ^ 40 * 2156223 * 2
def baseEnd_2156223 : Nat := 1107178797279622501296217

theorem tailTrace_2156223 : CollatzResearch.WordTrace tailWord_2156223 prefixEnd_2156223 1107178797279622501296217 := by
  unfold tailWord_2156223
  simp only [CollatzResearch.WordTrace]
  refine ⟨78643913667379799415345323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52429275778253199610230215 78643913667379799415345323)
  ·
    refine ⟨117965870501069699123017985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78643913667379799415345323 117965870501069699123017985)
    ·
      refine ⟨88474402875802274342263489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117965870501069699123017985 88474402875802274342263489)
      ·
        refine ⟨66355802156851705756697617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88474402875802274342263489 66355802156851705756697617)
        ·
          refine ⟨49766851617638779317523213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66355802156851705756697617 49766851617638779317523213)
          ·
            refine ⟨18662569356614542244071205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49766851617638779317523213 18662569356614542244071205)
            ·
              refine ⟨3499231754365226670763351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18662569356614542244071205 3499231754365226670763351)
              ·
                refine ⟨5248847631547840006145027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3499231754365226670763351 5248847631547840006145027)
                ·
                  refine ⟨7873271447321760009217541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5248847631547840006145027 7873271447321760009217541)
                  ·
                    refine ⟨1476238396372830001728289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7873271447321760009217541 1476238396372830001728289)
                    ·
                      refine ⟨1107178797279622501296217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1476238396372830001728289 1107178797279622501296217)
                      ·
                        rfl

theorem cell23_2156223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 4, 2].length) (baseStart_2156223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156223 prefixEnd_2156223 := by exact prefixLift 2156223
  have htrace : WordTrace (prefixWord ++ tailWord_2156223) baseStart_2156223 baseEnd_2156223 := by
    simpa [prefixWord, tailWord_2156223, baseEnd_2156223] using wordTrace_append hprefix tailTrace_2156223
  have hstable : (prefixWord ++ tailWord_2156223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156223).length < 2 ^ (prefixWord ++ tailWord_2156223).sum := by decide
  have hdescent : baseEnd_2156223 < baseStart_2156223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156229 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 7]
def baseStart_2156229 : Nat := 118140960795 + 2156229 * 2 ^ 59
def prefixEnd_2156229 : Nat := 4983230072969 + 3 ^ 40 * 2156229 * 2
def baseEnd_2156229 : Nat := 123020208684838830869021

theorem tailTrace_2156229 : CollatzResearch.WordTrace tailWord_2156229 prefixEnd_2156229 123020208684838830869021 := by
  unfold tailWord_2156229
  simp only [CollatzResearch.WordTrace]
  refine ⟨78644132505358062440063741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52429421670238708293375827 78644132505358062440063741)
  ·
    refine ⟨29491549689509273415023903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78644132505358062440063741 29491549689509273415023903)
    ·
      refine ⟨44237324534263910122535855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29491549689509273415023903 44237324534263910122535855)
      ·
        refine ⟨66355986801395865183803783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44237324534263910122535855 66355986801395865183803783)
        ·
          refine ⟨99533980202093797775705675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66355986801395865183803783 99533980202093797775705675)
          ·
            refine ⟨149300970303140696663558513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99533980202093797775705675 149300970303140696663558513)
            ·
              refine ⟨111975727727355522497668885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149300970303140696663558513 111975727727355522497668885)
              ·
                refine ⟨5248862237219790117078229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111975727727355522497668885 5248862237219790117078229)
                ·
                  refine ⟨123020208684838830869021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5248862237219790117078229 123020208684838830869021)
                  ·
                    rfl

theorem cell23_2156229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_2156229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156229 prefixEnd_2156229 := by exact prefixLift 2156229
  have htrace : WordTrace (prefixWord ++ tailWord_2156229) baseStart_2156229 baseEnd_2156229 := by
    simpa [prefixWord, tailWord_2156229, baseEnd_2156229] using wordTrace_append hprefix tailTrace_2156229
  have hstable : (prefixWord ++ tailWord_2156229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156229).length < 2 ^ (prefixWord ++ tailWord_2156229).sum := by decide
  have hdescent : baseEnd_2156229 < baseStart_2156229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156244 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2156244 : Nat := 118140960795 + 2156244 * 2 ^ 59
def prefixEnd_2156244 : Nat := 4983230072969 + 3 ^ 40 * 2156244 * 2
def baseEnd_2156244 : Nat := 1107189580373366919133621

theorem tailTrace_2156244 : CollatzResearch.WordTrace tailWord_2156244 prefixEnd_2156244 1107189580373366919133621 := by
  unfold tailWord_2156244
  simp only [CollatzResearch.WordTrace]
  refine ⟨39322339800151860000929893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52429786400202480001239857 39322339800151860000929893)
  ·
    refine ⟨7372938712528473750174355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39322339800151860000929893 7372938712528473750174355)
    ·
      refine ⟨11059408068792710625261533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7372938712528473750174355 11059408068792710625261533)
      ·
        refine ⟨4147278025797266484473075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11059408068792710625261533 4147278025797266484473075)
        ·
          refine ⟨6220917038695899726709613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4147278025797266484473075 6220917038695899726709613)
          ·
            refine ⟨2332843889510962397516105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6220917038695899726709613 2332843889510962397516105)
            ·
              refine ⟨1749632917133221798137079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2332843889510962397516105 1749632917133221798137079)
              ·
                refine ⟨2624449375699832697205619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1749632917133221798137079 2624449375699832697205619)
                ·
                  refine ⟨3936674063549749045808429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2624449375699832697205619 3936674063549749045808429)
                  ·
                    refine ⟨1476252773831155892178161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3936674063549749045808429 1476252773831155892178161)
                    ·
                      refine ⟨1107189580373366919133621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1476252773831155892178161 1107189580373366919133621)
                      ·
                        rfl

theorem cell23_2156244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2156244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156244 prefixEnd_2156244 := by exact prefixLift 2156244
  have htrace : WordTrace (prefixWord ++ tailWord_2156244) baseStart_2156244 baseEnd_2156244 := by
    simpa [prefixWord, tailWord_2156244, baseEnd_2156244] using wordTrace_append hprefix tailTrace_2156244
  have hstable : (prefixWord ++ tailWord_2156244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156244).length < 2 ^ (prefixWord ++ tailWord_2156244).sum := by decide
  have hdescent : baseEnd_2156244 < baseStart_2156244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156256 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 3]
def baseStart_2156256 : Nat := 118140960795 + 2156256 * 2 ^ 59
def prefixEnd_2156256 : Nat := 4983230072969 + 3 ^ 40 * 2156256 * 2
def baseEnd_2156256 : Nat := 1107195742141220872183565

theorem tailTrace_2156256 : CollatzResearch.WordTrace tailWord_2156256 prefixEnd_2156256 1107195742141220872183565 := by
  unfold tailWord_2156256
  simp only [CollatzResearch.WordTrace]
  refine ⟨39322558638130123025648311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52430078184173497367531081 39322558638130123025648311)
  ·
    refine ⟨58983837957195184538472467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39322558638130123025648311 58983837957195184538472467)
    ·
      refine ⟨88475756935792776807708701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58983837957195184538472467 88475756935792776807708701)
      ·
        refine ⟨33178408850922291302890763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88475756935792776807708701 33178408850922291302890763)
        ·
          refine ⟨49767613276383436954336145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33178408850922291302890763 49767613276383436954336145)
          ·
            refine ⟨37325709957287577715752109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49767613276383436954336145 37325709957287577715752109)
            ·
              refine ⟨13997141233982841643407041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37325709957287577715752109 13997141233982841643407041)
              ·
                refine ⟨10497855925487131232555281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13997141233982841643407041 10497855925487131232555281)
                ·
                  refine ⟨7873391944115348424416461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10497855925487131232555281 7873391944115348424416461)
                  ·
                    refine ⟨2952521979043255659156173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7873391944115348424416461 2952521979043255659156173)
                    ·
                      refine ⟨1107195742141220872183565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2952521979043255659156173 1107195742141220872183565)
                      ·
                        rfl

theorem cell23_2156256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_2156256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156256 prefixEnd_2156256 := by exact prefixLift 2156256
  have htrace : WordTrace (prefixWord ++ tailWord_2156256) baseStart_2156256 baseEnd_2156256 := by
    simpa [prefixWord, tailWord_2156256, baseEnd_2156256] using wordTrace_append hprefix tailTrace_2156256
  have hstable : (prefixWord ++ tailWord_2156256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156256).length < 2 ^ (prefixWord ++ tailWord_2156256).sum := by decide
  have hdescent : baseEnd_2156256 < baseStart_2156256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156296 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 1, 3, 4]
def baseStart_2156296 : Nat := 118140960795 + 2156296 * 2 ^ 59
def prefixEnd_2156296 : Nat := 4983230072969 + 3 ^ 40 * 2156296 * 2
def baseEnd_2156296 : Nat := 1107216281367400715683381

theorem tailTrace_2156296 : CollatzResearch.WordTrace tailWord_2156296 prefixEnd_2156296 1107216281367400715683381 := by
  unfold tailWord_2156296
  simp only [CollatzResearch.WordTrace]
  refine ⟨39323288098057666441376371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52431050797410221921835161 39323288098057666441376371)
  ·
    refine ⟨58984932147086499662064557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39323288098057666441376371 58984932147086499662064557)
    ·
      refine ⟨22119349555157437373274209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58984932147086499662064557 22119349555157437373274209)
      ·
        refine ⟨16589512166368078029955657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22119349555157437373274209 16589512166368078029955657)
        ·
          refine ⟨12442134124776058522466743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16589512166368078029955657 12442134124776058522466743)
          ·
            refine ⟨18663201187164087783700115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12442134124776058522466743 18663201187164087783700115)
            ·
              refine ⟨27994801780746131675550173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18663201187164087783700115 27994801780746131675550173)
              ·
                refine ⟨10498050667779799378331315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27994801780746131675550173 10498050667779799378331315)
                ·
                  refine ⟨15747076001669699067496973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10498050667779799378331315 15747076001669699067496973)
                  ·
                    refine ⟨5905153500626137150311365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15747076001669699067496973 5905153500626137150311365)
                    ·
                      refine ⟨1107216281367400715683381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5905153500626137150311365 1107216281367400715683381)
                      ·
                        rfl

theorem cell23_2156296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_2156296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156296 prefixEnd_2156296 := by exact prefixLift 2156296
  have htrace : WordTrace (prefixWord ++ tailWord_2156296) baseStart_2156296 baseEnd_2156296 := by
    simpa [prefixWord, tailWord_2156296, baseEnd_2156296] using wordTrace_append hprefix tailTrace_2156296
  have hstable : (prefixWord ++ tailWord_2156296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156296).length < 2 ^ (prefixWord ++ tailWord_2156296).sum := by decide
  have hdescent : baseEnd_2156296 < baseStart_2156296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156323 : List Nat := [1, 1, 1, 4, 2, 1, 5, 1, 3, 4]
def baseStart_2156323 : Nat := 118140960795 + 2156323 * 2 ^ 59
def prefixEnd_2156323 : Nat := 4983230072969 + 3 ^ 40 * 2156323 * 2
def baseEnd_2156323 : Nat := 369076715115024036681919

theorem tailTrace_2156323 : CollatzResearch.WordTrace tailWord_2156323 prefixEnd_2156323 369076715115024036681919 := by
  unfold tailWord_2156323
  simp only [CollatzResearch.WordTrace]
  refine ⟨78647560967017516493985623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52431707311345010995990415 78647560967017516493985623)
  ·
    refine ⟨117971341450526274740978435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78647560967017516493985623 117971341450526274740978435)
    ·
      refine ⟨176957012175789412111467653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117971341450526274740978435 176957012175789412111467653)
      ·
        refine ⟨33179439782960514770900185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176957012175789412111467653 33179439782960514770900185)
        ·
          refine ⟨24884579837220386078175139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33179439782960514770900185 24884579837220386078175139)
          ·
            refine ⟨37326869755830579117262709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24884579837220386078175139 37326869755830579117262709)
            ·
              refine ⟨3499394039609116792243379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37326869755830579117262709 3499394039609116792243379)
              ·
                refine ⟨5249091059413675188365069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3499394039609116792243379 5249091059413675188365069)
                ·
                  refine ⟨1968409147280128195636901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5249091059413675188365069 1968409147280128195636901)
                  ·
                    refine ⟨369076715115024036681919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1968409147280128195636901 369076715115024036681919)
                    ·
                      rfl

theorem cell23_2156323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3, 4].length) (baseStart_2156323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156323 prefixEnd_2156323 := by exact prefixLift 2156323
  have htrace : WordTrace (prefixWord ++ tailWord_2156323) baseStart_2156323 baseEnd_2156323 := by
    simpa [prefixWord, tailWord_2156323, baseEnd_2156323] using wordTrace_append hprefix tailTrace_2156323
  have hstable : (prefixWord ++ tailWord_2156323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156323).length < 2 ^ (prefixWord ++ tailWord_2156323).sum := by decide
  have hdescent : baseEnd_2156323 < baseStart_2156323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156350 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_2156350 : Nat := 118140960795 + 2156350 * 2 ^ 59
def prefixEnd_2156350 : Nat := 4983230072969 + 3 ^ 40 * 2156350 * 2
def baseEnd_2156350 : Nat := 1107244009322743504408133

theorem tailTrace_2156350 : CollatzResearch.WordTrace tailWord_2156350 prefixEnd_2156350 1107244009322743504408133 := by
  unfold tailWord_2156350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9831068217239962513152313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52432363825279800070145669 9831068217239962513152313)
  ·
    refine ⟨7373301162929971884864235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9831068217239962513152313 7373301162929971884864235)
    ·
      refine ⟨11059951744394957827296353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7373301162929971884864235 11059951744394957827296353)
      ·
        refine ⟨8294963808296218370472265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11059951744394957827296353 8294963808296218370472265)
        ·
          refine ⟨6221222856222163777854199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8294963808296218370472265 6221222856222163777854199)
          ·
            refine ⟨9331834284333245666781299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6221222856222163777854199 9331834284333245666781299)
            ·
              refine ⟨13997751426499868500171949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9331834284333245666781299 13997751426499868500171949)
              ·
                refine ⟨5249156784937450687564481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13997751426499868500171949 5249156784937450687564481)
                ·
                  refine ⟨3936867588703088015673361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5249156784937450687564481 3936867588703088015673361)
                  ·
                    refine ⟨2952650691527316011755021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3936867588703088015673361 2952650691527316011755021)
                    ·
                      refine ⟨1107244009322743504408133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2952650691527316011755021 1107244009322743504408133)
                      ·
                        rfl

theorem cell23_2156350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_2156350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156350 prefixEnd_2156350 := by exact prefixLift 2156350
  have htrace : WordTrace (prefixWord ++ tailWord_2156350) baseStart_2156350 baseEnd_2156350 := by
    simpa [prefixWord, tailWord_2156350, baseEnd_2156350] using wordTrace_append hprefix tailTrace_2156350
  have hstable : (prefixWord ++ tailWord_2156350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156350).length < 2 ^ (prefixWord ++ tailWord_2156350).sum := by decide
  have hdescent : baseEnd_2156350 < baseStart_2156350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156403 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 4]
def baseStart_2156403 : Nat := 118140960795 + 2156403 * 2 ^ 59
def prefixEnd_2156403 : Nat := 4983230072969 + 3 ^ 40 * 2156403 * 2
def baseEnd_2156403 : Nat := 1107271223797431797045389

theorem tailTrace_2156403 : CollatzResearch.WordTrace tailWord_2156403 prefixEnd_2156403 1107271223797431797045389 := by
  unfold tailWord_2156403
  simp only [CollatzResearch.WordTrace]
  refine ⟨78650478806727690156897863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52433652537818460104598575 78650478806727690156897863)
  ·
    refine ⟨117975718210091535235346795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78650478806727690156897863 117975718210091535235346795)
    ·
      refine ⟨176963577315137302853020193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117975718210091535235346795 176963577315137302853020193)
      ·
        refine ⟨132722682986352977139765145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176963577315137302853020193 132722682986352977139765145)
        ·
          refine ⟨99542012239764732854823859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132722682986352977139765145 99542012239764732854823859)
          ·
            refine ⟨149313018359647099282235789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99542012239764732854823859 149313018359647099282235789)
            ·
              refine ⟨55992381884867662230838421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149313018359647099282235789 55992381884867662230838421)
              ·
                refine ⟨2624642900853171667070551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 55992381884867662230838421 2624642900853171667070551)
                ·
                  refine ⟨3936964351279757500605827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2624642900853171667070551 3936964351279757500605827)
                  ·
                    refine ⟨5905446526919636250908741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3936964351279757500605827 5905446526919636250908741)
                    ·
                      refine ⟨1107271223797431797045389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5905446526919636250908741 1107271223797431797045389)
                      ·
                        rfl

theorem cell23_2156403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 1, 1, 4].length) (baseStart_2156403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156403 prefixEnd_2156403 := by exact prefixLift 2156403
  have htrace : WordTrace (prefixWord ++ tailWord_2156403) baseStart_2156403 baseEnd_2156403 := by
    simpa [prefixWord, tailWord_2156403, baseEnd_2156403] using wordTrace_append hprefix tailTrace_2156403
  have hstable : (prefixWord ++ tailWord_2156403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156403).length < 2 ^ (prefixWord ++ tailWord_2156403).sum := by decide
  have hdescent : baseEnd_2156403 < baseStart_2156403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156413 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_2156413 : Nat := 118140960795 + 2156413 * 2 ^ 59
def prefixEnd_2156413 : Nat := 4983230072969 + 3 ^ 40 * 2156413 * 2
def baseEnd_2156413 : Nat := 369092119534658919306781

theorem tailTrace_2156413 : CollatzResearch.WordTrace tailWord_2156413 prefixEnd_2156413 369092119534658919306781 := by
  unfold tailWord_2156413
  simp only [CollatzResearch.WordTrace]
  refine ⟨78650843536691461864761893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52433895691127641243174595 78650843536691461864761893)
  ·
    refine ⟨14747033163129649099642855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78650843536691461864761893 14747033163129649099642855)
    ·
      refine ⟨22120549744694473649464283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14747033163129649099642855 22120549744694473649464283)
      ·
        refine ⟨33180824617041710474196425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22120549744694473649464283 33180824617041710474196425)
        ·
          refine ⟨24885618462781282855647319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33180824617041710474196425 24885618462781282855647319)
          ·
            refine ⟨37328427694171924283470979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24885618462781282855647319 37328427694171924283470979)
            ·
              refine ⟨55992641541257886425206469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37328427694171924283470979 55992641541257886425206469)
              ·
                refine ⟨10498620288985853704726213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55992641541257886425206469 10498620288985853704726213)
                ·
                  refine ⟨1968491304184847569636165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10498620288985853704726213 1968491304184847569636165)
                  ·
                    refine ⟨369092119534658919306781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1968491304184847569636165 369092119534658919306781)
                    ·
                      rfl

theorem cell23_2156413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_2156413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156413 prefixEnd_2156413 := by exact prefixLift 2156413
  have htrace : WordTrace (prefixWord ++ tailWord_2156413) baseStart_2156413 baseEnd_2156413 := by
    simpa [prefixWord, tailWord_2156413, baseEnd_2156413] using wordTrace_append hprefix tailTrace_2156413
  have hstable : (prefixWord ++ tailWord_2156413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156413).length < 2 ^ (prefixWord ++ tailWord_2156413).sum := by decide
  have hdescent : baseEnd_2156413 < baseStart_2156413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156417 : List Nat := [1, 2, 4, 4, 1, 1, 1, 3, 1, 5]
def baseStart_2156417 : Nat := 118140960795 + 2156417 * 2 ^ 59
def prefixEnd_2156417 : Nat := 4983230072969 + 3 ^ 40 * 2156417 * 2
def baseEnd_2156417 : Nat := 369092804175531580756775

theorem tailTrace_2156417 : CollatzResearch.WordTrace tailWord_2156417 prefixEnd_2156417 369092804175531580756775 := by
  unfold tailWord_2156417
  simp only [CollatzResearch.WordTrace]
  refine ⟨78650989428676970547907505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52433992952451313698605003 78650989428676970547907505)
  ·
    refine ⟨58988242071507727910930629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78650989428676970547907505 58988242071507727910930629)
    ·
      refine ⟨11060295388407698983299493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58988242071507727910930629 11060295388407698983299493)
      ·
        refine ⟨2073805385326443559368655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11060295388407698983299493 2073805385326443559368655)
        ·
          refine ⟨3110708077989665339052983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2073805385326443559368655 3110708077989665339052983)
          ·
            refine ⟨4666062116984498008579475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110708077989665339052983 4666062116984498008579475)
            ·
              refine ⟨6999093175476747012869213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4666062116984498008579475 6999093175476747012869213)
              ·
                refine ⟨2624659940803780129825955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6999093175476747012869213 2624659940803780129825955)
                ·
                  refine ⟨3936989911205670194738933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2624659940803780129825955 3936989911205670194738933)
                  ·
                    refine ⟨369092804175531580756775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3936989911205670194738933 369092804175531580756775)
                    ·
                      rfl

theorem cell23_2156417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_2156417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156417 prefixEnd_2156417 := by exact prefixLift 2156417
  have htrace : WordTrace (prefixWord ++ tailWord_2156417) baseStart_2156417 baseEnd_2156417 := by
    simpa [prefixWord, tailWord_2156417, baseEnd_2156417] using wordTrace_append hprefix tailTrace_2156417
  have hstable : (prefixWord ++ tailWord_2156417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156417).length < 2 ^ (prefixWord ++ tailWord_2156417).sum := by decide
  have hdescent : baseEnd_2156417 < baseStart_2156417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156437 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 3, 2, 2]
def baseStart_2156437 : Nat := 118140960795 + 2156437 * 2 ^ 59
def prefixEnd_2156437 : Nat := 4983230072969 + 3 ^ 40 * 2156437 * 2
def baseEnd_2156437 : Nat := 1107288682139684664020233

theorem tailTrace_2156437 : CollatzResearch.WordTrace tailWord_2156437 prefixEnd_2156437 1107288682139684664020233 := by
  unfold tailWord_2156437
  simp only [CollatzResearch.WordTrace]
  refine ⟨78651718888604513963635565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52434479259069675975757043 78651718888604513963635565)
  ·
    refine ⟨29494394583226692736363337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78651718888604513963635565 29494394583226692736363337)
    ·
      refine ⟨22120795937420019552272503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29494394583226692736363337 22120795937420019552272503)
      ·
        refine ⟨33181193906130029328408755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22120795937420019552272503 33181193906130029328408755)
        ·
          refine ⟨49771790859195043992613133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33181193906130029328408755 49771790859195043992613133)
          ·
            refine ⟨18664421572198141497229925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49771790859195043992613133 18664421572198141497229925)
            ·
              refine ⟨3499579044787151530730611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18664421572198141497229925 3499579044787151530730611)
              ·
                refine ⟨5249368567180727296095917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3499579044787151530730611 5249368567180727296095917)
                ·
                  refine ⟨1968513212692772736035969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5249368567180727296095917 1968513212692772736035969)
                  ·
                    refine ⟨1476384909519579552026977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1968513212692772736035969 1476384909519579552026977)
                    ·
                      refine ⟨1107288682139684664020233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1476384909519579552026977 1107288682139684664020233)
                      ·
                        rfl

theorem cell23_2156437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_2156437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156437 prefixEnd_2156437 := by exact prefixLift 2156437
  have htrace : WordTrace (prefixWord ++ tailWord_2156437) baseStart_2156437 baseEnd_2156437 := by
    simpa [prefixWord, tailWord_2156437, baseEnd_2156437] using wordTrace_append hprefix tailTrace_2156437
  have hstable : (prefixWord ++ tailWord_2156437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156437).length < 2 ^ (prefixWord ++ tailWord_2156437).sum := by decide
  have hdescent : baseEnd_2156437 < baseStart_2156437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156447 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 1, 6]
def baseStart_2156447 : Nat := 118140960795 + 2156447 * 2 ^ 59
def prefixEnd_2156447 : Nat := 4983230072969 + 3 ^ 40 * 2156447 * 2
def baseEnd_2156447 : Nat := 369097938982076541631729

theorem tailTrace_2156447 : CollatzResearch.WordTrace tailWord_2156447 prefixEnd_2156447 369097938982076541631729 := by
  unfold tailWord_2156447
  simp only [CollatzResearch.WordTrace]
  refine ⟨78652083618568285671499595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52434722412378857114333063 78652083618568285671499595)
  ·
    refine ⟨117978125427852428507249393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78652083618568285671499595 117978125427852428507249393)
    ·
      refine ⟨88483594070889321380437045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117978125427852428507249393 88483594070889321380437045)
      ·
        refine ⟨8295336944145873879415973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88483594070889321380437045 8295336944145873879415973)
        ·
          refine ⟨1555375677027351352390495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8295336944145873879415973 1555375677027351352390495)
          ·
            refine ⟨2333063515541027028585743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1555375677027351352390495 2333063515541027028585743)
            ·
              refine ⟨3499595273311540542878615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2333063515541027028585743 3499595273311540542878615)
              ·
                refine ⟨5249392909967310814317923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3499595273311540542878615 5249392909967310814317923)
                ·
                  refine ⟨7874089364950966221476885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5249392909967310814317923 7874089364950966221476885)
                  ·
                    refine ⟨369097938982076541631729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7874089364950966221476885 369097938982076541631729)
                    ·
                      rfl

theorem cell23_2156447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 1, 6].length) (baseStart_2156447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156447 prefixEnd_2156447 := by exact prefixLift 2156447
  have htrace : WordTrace (prefixWord ++ tailWord_2156447) baseStart_2156447 baseEnd_2156447 := by
    simpa [prefixWord, tailWord_2156447, baseEnd_2156447] using wordTrace_append hprefix tailTrace_2156447
  have hstable : (prefixWord ++ tailWord_2156447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156447).length < 2 ^ (prefixWord ++ tailWord_2156447).sum := by decide
  have hdescent : baseEnd_2156447 < baseStart_2156447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156450 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_2156450 : Nat := 118140960795 + 2156450 * 2 ^ 59
def prefixEnd_2156450 : Nat := 4983230072969 + 3 ^ 40 * 2156450 * 2
def baseEnd_2156450 : Nat := 1107295357388193113157673

theorem tailTrace_2156450 : CollatzResearch.WordTrace tailWord_2156450 prefixEnd_2156450 1107295357388193113157673 := by
  unfold tailWord_2156450
  simp only [CollatzResearch.WordTrace]
  refine ⟨19663048259389354295964701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52434795358371611455905869 19663048259389354295964701)
  ·
    refine ⟨7373643097271007860986763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19663048259389354295964701 7373643097271007860986763)
    ·
      refine ⟨11060464645906511791480145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7373643097271007860986763 11060464645906511791480145)
      ·
        refine ⟨8295348484429883843610109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11060464645906511791480145 8295348484429883843610109)
        ·
          refine ⟨3110755681661206441353791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8295348484429883843610109 3110755681661206441353791)
          ·
            refine ⟨4666133522491809662030687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110755681661206441353791 4666133522491809662030687)
            ·
              refine ⟨6999200283737714493046031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4666133522491809662030687 6999200283737714493046031)
              ·
                refine ⟨10498800425606571739569047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6999200283737714493046031 10498800425606571739569047)
                ·
                  refine ⟨15748200638409857609353571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10498800425606571739569047 15748200638409857609353571)
                  ·
                    refine ⟨23622300957614786414030357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15748200638409857609353571 23622300957614786414030357)
                    ·
                      refine ⟨1107295357388193113157673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23622300957614786414030357 1107295357388193113157673)
                      ·
                        rfl

theorem cell23_2156450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_2156450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156450 prefixEnd_2156450 := by exact prefixLift 2156450
  have htrace : WordTrace (prefixWord ++ tailWord_2156450) baseStart_2156450 baseEnd_2156450 := by
    simpa [prefixWord, tailWord_2156450, baseEnd_2156450] using wordTrace_append hprefix tailTrace_2156450
  have hstable : (prefixWord ++ tailWord_2156450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156450).length < 2 ^ (prefixWord ++ tailWord_2156450).sum := by decide
  have hdescent : baseEnd_2156450 < baseStart_2156450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156508 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2156508 : Nat := 118140960795 + 2156508 * 2 ^ 59
def prefixEnd_2156508 : Nat := 4983230072969 + 3 ^ 40 * 2156508 * 2
def baseEnd_2156508 : Nat := 1107325139266153886232407

theorem tailTrace_2156508 : CollatzResearch.WordTrace tailWord_2156508 prefixEnd_2156508 1107325139266153886232407 := by
  unfold tailWord_2156508
  simp only [CollatzResearch.WordTrace]
  refine ⟨39327154235673646544735089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52436205647564862059646785 39327154235673646544735089)
  ·
    refine ⟨29495365676755234908551317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39327154235673646544735089 29495365676755234908551317)
    ·
      refine ⟨1382595266097901636338343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29495365676755234908551317 1382595266097901636338343)
      ·
        refine ⟨2073892899146852454507515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1382595266097901636338343 2073892899146852454507515)
        ·
          refine ⟨3110839348720278681761273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2073892899146852454507515 3110839348720278681761273)
          ·
            refine ⟨2333129511540209011320955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3110839348720278681761273 2333129511540209011320955)
            ·
              refine ⟨3499694267310313516981433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2333129511540209011320955 3499694267310313516981433)
              ·
                refine ⟨2624770700482735137736075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3499694267310313516981433 2624770700482735137736075)
                ·
                  refine ⟨3937156050724102706604113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2624770700482735137736075 3937156050724102706604113)
                  ·
                    refine ⟨2952867038043077029953085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3937156050724102706604113 2952867038043077029953085)
                    ·
                      refine ⟨1107325139266153886232407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2952867038043077029953085 1107325139266153886232407)
                      ·
                        rfl

theorem cell23_2156508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2156508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156508 prefixEnd_2156508 := by exact prefixLift 2156508
  have htrace : WordTrace (prefixWord ++ tailWord_2156508) baseStart_2156508 baseEnd_2156508 := by
    simpa [prefixWord, tailWord_2156508, baseEnd_2156508] using wordTrace_append hprefix tailTrace_2156508
  have hstable : (prefixWord ++ tailWord_2156508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156508).length < 2 ^ (prefixWord ++ tailWord_2156508).sum := by decide
  have hdescent : baseEnd_2156508 < baseStart_2156508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156513 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_2156513 : Nat := 118140960795 + 2156513 * 2 ^ 59
def prefixEnd_2156513 : Nat := 4983230072969 + 3 ^ 40 * 2156513 * 2
def baseEnd_2156513 : Nat := 1107327706669426366669883

theorem tailTrace_2156513 : CollatzResearch.WordTrace tailWord_2156513 prefixEnd_2156513 1107327706669426366669883 := by
  unfold tailWord_2156513
  simp only [CollatzResearch.WordTrace]
  refine ⟨78654490836329178943402193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52436327224219452628934795 78654490836329178943402193)
  ·
    refine ⟨58990868127246884207551645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78654490836329178943402193 58990868127246884207551645)
    ·
      refine ⟨22121575547717581577831867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58990868127246884207551645 22121575547717581577831867)
      ·
        refine ⟨33182363321576372366747801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22121575547717581577831867 33182363321576372366747801)
        ·
          refine ⟨24886772491182279275060851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33182363321576372366747801 24886772491182279275060851)
          ·
            refine ⟨37330158736773418912591277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24886772491182279275060851 37330158736773418912591277)
            ·
              refine ⟨13998809526290032092221729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37330158736773418912591277 13998809526290032092221729)
              ·
                refine ⟨10499107144717524069166297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13998809526290032092221729 10499107144717524069166297)
                ·
                  refine ⟨7874330358538143051874723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10499107144717524069166297 7874330358538143051874723)
                  ·
                    refine ⟨11811495537807214577812085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7874330358538143051874723 11811495537807214577812085)
                    ·
                      refine ⟨1107327706669426366669883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11811495537807214577812085 1107327706669426366669883)
                      ·
                        rfl

theorem cell23_2156513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_2156513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156513 prefixEnd_2156513 := by exact prefixLift 2156513
  have htrace : WordTrace (prefixWord ++ tailWord_2156513) baseStart_2156513 baseEnd_2156513 := by
    simpa [prefixWord, tailWord_2156513, baseEnd_2156513] using wordTrace_append hprefix tailTrace_2156513
  have hstable : (prefixWord ++ tailWord_2156513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156513).length < 2 ^ (prefixWord ++ tailWord_2156513).sum := by decide
  have hdescent : baseEnd_2156513 < baseStart_2156513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156543 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 3]
def baseStart_2156543 : Nat := 118140960795 + 2156543 * 2 ^ 59
def prefixEnd_2156543 : Nat := 4983230072969 + 3 ^ 40 * 2156543 * 2
def baseEnd_2156543 : Nat := 1107343111089061249294745

theorem tailTrace_2156543 : CollatzResearch.WordTrace tailWord_2156543 prefixEnd_2156543 1107343111089061249294745 := by
  unfold tailWord_2156543
  simp only [CollatzResearch.WordTrace]
  refine ⟨78655585026220494066994283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52437056684146996044662855 78655585026220494066994283)
  ·
    refine ⟨117983377539330741100491425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78655585026220494066994283 117983377539330741100491425)
    ·
      refine ⟨88487533154498055825368569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117983377539330741100491425 88487533154498055825368569)
      ·
        refine ⟨66365649865873541869026427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88487533154498055825368569 66365649865873541869026427)
        ·
          refine ⟨99548474798810312803539641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66365649865873541869026427 99548474798810312803539641)
          ·
            refine ⟨74661356099107734602654731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99548474798810312803539641 74661356099107734602654731)
            ·
              refine ⟨111992034148661601903982097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74661356099107734602654731 111992034148661601903982097)
              ·
                refine ⟨83994025611496201427986573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111992034148661601903982097 83994025611496201427986573)
                ·
                  refine ⟨31497759604311075535494965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83994025611496201427986573 31497759604311075535494965)
                  ·
                    refine ⟨2952914962904163331452653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31497759604311075535494965 2952914962904163331452653)
                    ·
                      refine ⟨1107343111089061249294745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2952914962904163331452653 1107343111089061249294745)
                      ·
                        rfl

theorem cell23_2156543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_2156543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156543 prefixEnd_2156543 := by exact prefixLift 2156543
  have htrace : WordTrace (prefixWord ++ tailWord_2156543) baseStart_2156543 baseEnd_2156543 := by
    simpa [prefixWord, tailWord_2156543, baseEnd_2156543] using wordTrace_append hprefix tailTrace_2156543
  have hstable : (prefixWord ++ tailWord_2156543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156543).length < 2 ^ (prefixWord ++ tailWord_2156543).sum := by decide
  have hdescent : baseEnd_2156543 < baseStart_2156543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156563 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 4, 5]
def baseStart_2156563 : Nat := 118140960795 + 2156563 * 2 ^ 59
def prefixEnd_2156563 : Nat := 4983230072969 + 3 ^ 40 * 2156563 * 2
def baseEnd_2156563 : Nat := 369117793567383723681551

theorem tailTrace_2156563 : CollatzResearch.WordTrace tailWord_2156563 prefixEnd_2156563 369117793567383723681551 := by
  unfold tailWord_2156563
  simp only [CollatzResearch.WordTrace]
  refine ⟨78656314486148037482722343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52437542990765358321814895 78656314486148037482722343)
  ·
    refine ⟨117984471729222056224083515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78656314486148037482722343 117984471729222056224083515)
    ·
      refine ⟨176976707593833084336125273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117984471729222056224083515 176976707593833084336125273)
      ·
        refine ⟨132732530695374813252093955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176976707593833084336125273 132732530695374813252093955)
        ·
          refine ⟨199098796043062219878140933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132732530695374813252093955 199098796043062219878140933)
          ·
            refine ⟨37331024258074166227151425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199098796043062219878140933 37331024258074166227151425)
            ·
              refine ⟨27998268193555624670363569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37331024258074166227151425 27998268193555624670363569)
              ·
                refine ⟨20998701145166718502772677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27998268193555624670363569 20998701145166718502772677)
                ·
                  refine ⟨3937256464718759719269877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20998701145166718502772677 3937256464718759719269877)
                  ·
                    refine ⟨369117793567383723681551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3937256464718759719269877 369117793567383723681551)
                    ·
                      rfl

theorem cell23_2156563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 4, 5].length) (baseStart_2156563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156563 prefixEnd_2156563 := by exact prefixLift 2156563
  have htrace : WordTrace (prefixWord ++ tailWord_2156563) baseStart_2156563 baseEnd_2156563 := by
    simpa [prefixWord, tailWord_2156563, baseEnd_2156563] using wordTrace_append hprefix tailTrace_2156563
  have hstable : (prefixWord ++ tailWord_2156563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156563).length < 2 ^ (prefixWord ++ tailWord_2156563).sum := by decide
  have hdescent : baseEnd_2156563 < baseStart_2156563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156613 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_2156613 : Nat := 118140960795 + 2156613 * 2 ^ 59
def prefixEnd_2156613 : Nat := 4983230072969 + 3 ^ 40 * 2156613 * 2
def baseEnd_2156613 : Nat := 1107379054734875975419423

theorem tailTrace_2156613 : CollatzResearch.WordTrace tailWord_2156613 prefixEnd_2156613 1107379054734875975419423 := by
  unfold tailWord_2156613
  simp only [CollatzResearch.WordTrace]
  refine ⟨78658138135966896022042493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52438758757311264014694995 78658138135966896022042493)
  ·
    refine ⟨29496801800987586008265935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78658138135966896022042493 29496801800987586008265935)
    ·
      refine ⟨44245202701481379012398903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29496801800987586008265935 44245202701481379012398903)
      ·
        refine ⟨66367804052222068518598355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44245202701481379012398903 66367804052222068518598355)
        ·
          refine ⟨99551706078333102777897533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66367804052222068518598355 99551706078333102777897533)
          ·
            refine ⟨37331889779374913541711575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99551706078333102777897533 37331889779374913541711575)
            ·
              refine ⟨55997834669062370312567363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37331889779374913541711575 55997834669062370312567363)
              ·
                refine ⟨83996752003593555468851045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55997834669062370312567363 83996752003593555468851045)
                ·
                  refine ⟨15749391000673791650409571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83996752003593555468851045 15749391000673791650409571)
                  ·
                    refine ⟨23624086501010687475614357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15749391000673791650409571 23624086501010687475614357)
                    ·
                      refine ⟨1107379054734875975419423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23624086501010687475614357 1107379054734875975419423)
                      ·
                        rfl

theorem cell23_2156613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_2156613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156613 prefixEnd_2156613 := by exact prefixLift 2156613
  have htrace : WordTrace (prefixWord ++ tailWord_2156613) baseStart_2156613 baseEnd_2156613 := by
    simpa [prefixWord, tailWord_2156613, baseEnd_2156613] using wordTrace_append hprefix tailTrace_2156613
  have hstable : (prefixWord ++ tailWord_2156613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156613).length < 2 ^ (prefixWord ++ tailWord_2156613).sum := by decide
  have hdescent : baseEnd_2156613 < baseStart_2156613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156620 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 1, 4, 3]
def baseStart_2156620 : Nat := 118140960795 + 2156620 * 2 ^ 59
def prefixEnd_2156620 : Nat := 4983230072969 + 3 ^ 40 * 2156620 * 2
def baseEnd_2156620 : Nat := 1107382649099457448031891

theorem tailTrace_2156620 : CollatzResearch.WordTrace tailWord_2156620 prefixEnd_2156620 1107382649099457448031891 := by
  unfold tailWord_2156620
  simp only [CollatzResearch.WordTrace]
  refine ⟨39329196723470768108773657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52438928964627690811698209 39329196723470768108773657)
  ·
    refine ⟨29496897542603076081580243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39329196723470768108773657 29496897542603076081580243)
    ·
      refine ⟨44245346313904614122370365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29496897542603076081580243 44245346313904614122370365)
      ·
        refine ⟨16592004867714230295888887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44245346313904614122370365 16592004867714230295888887)
        ·
          refine ⟨24888007301571345443833331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16592004867714230295888887 24888007301571345443833331)
          ·
            refine ⟨37332010952357018165749997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24888007301571345443833331 37332010952357018165749997)
            ·
              refine ⟨13999504107133881812156249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37332010952357018165749997 13999504107133881812156249)
              ·
                refine ⟨10499628080350411359117187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13999504107133881812156249 10499628080350411359117187)
                ·
                  refine ⟨15749442120525617038675781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10499628080350411359117187 15749442120525617038675781)
                  ·
                    refine ⟨2953020397598553194751709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15749442120525617038675781 2953020397598553194751709)
                    ·
                      refine ⟨1107382649099457448031891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2953020397598553194751709 1107382649099457448031891)
                      ·
                        rfl

theorem cell23_2156620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_2156620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156620 prefixEnd_2156620 := by exact prefixLift 2156620
  have htrace : WordTrace (prefixWord ++ tailWord_2156620) baseStart_2156620 baseEnd_2156620 := by
    simpa [prefixWord, tailWord_2156620, baseEnd_2156620] using wordTrace_append hprefix tailTrace_2156620
  have hstable : (prefixWord ++ tailWord_2156620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156620).length < 2 ^ (prefixWord ++ tailWord_2156620).sum := by decide
  have hdescent : baseEnd_2156620 < baseStart_2156620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156644 : List Nat := [2, 3, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_2156644 : Nat := 118140960795 + 2156644 * 2 ^ 59
def prefixEnd_2156644 : Nat := 4983230072969 + 3 ^ 40 * 2156644 * 2
def baseEnd_2156644 : Nat := 369131657545055118043927

theorem tailTrace_2156644 : CollatzResearch.WordTrace tailWord_2156644 prefixEnd_2156644 369131657545055118043927 := by
  unfold tailWord_2156644
  simp only [CollatzResearch.WordTrace]
  refine ⟨39329634399427294158210493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52439512532569725544280657 39329634399427294158210493)
  ·
    refine ⟨14748612899785235309328935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39329634399427294158210493 14748612899785235309328935)
    ·
      refine ⟨22122919349677852963993403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14748612899785235309328935 22122919349677852963993403)
      ·
        refine ⟨33184379024516779445990105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22122919349677852963993403 33184379024516779445990105)
        ·
          refine ⟨24888284268387584584492579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33184379024516779445990105 24888284268387584584492579)
          ·
            refine ⟨37332426402581376876738869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24888284268387584584492579 37332426402581376876738869)
            ·
              refine ⟨3499914975242004082194269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37332426402581376876738869 3499914975242004082194269)
              ·
                refine ⟨1312468115715751530822851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3499914975242004082194269 1312468115715751530822851)
                ·
                  refine ⟨1968702173573627296234277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1312468115715751530822851 1968702173573627296234277)
                  ·
                    refine ⟨369131657545055118043927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1968702173573627296234277 369131657545055118043927)
                    ·
                      rfl

theorem cell23_2156644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_2156644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156644 prefixEnd_2156644 := by exact prefixLift 2156644
  have htrace : WordTrace (prefixWord ++ tailWord_2156644) baseStart_2156644 baseEnd_2156644 := by
    simpa [prefixWord, tailWord_2156644, baseEnd_2156644] using wordTrace_append hprefix tailTrace_2156644
  have hstable : (prefixWord ++ tailWord_2156644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156644).length < 2 ^ (prefixWord ++ tailWord_2156644).sum := by decide
  have hdescent : baseEnd_2156644 < baseStart_2156644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156704 : List Nat := [2, 1, 1, 4, 2, 3, 3, 1, 1, 5]
def baseStart_2156704 : Nat := 118140960795 + 2156704 * 2 ^ 59
def prefixEnd_2156704 : Nat := 4983230072969 + 3 ^ 40 * 2156704 * 2
def baseEnd_2156704 : Nat := 369141927158145039793835

theorem tailTrace_2156704 : CollatzResearch.WordTrace tailWord_2156704 prefixEnd_2156704 369141927158145039793835 := by
  unfold tailWord_2156704
  simp only [CollatzResearch.WordTrace]
  refine ⟨39330728589318609281802583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52440971452424812375736777 39330728589318609281802583)
  ·
    refine ⟨58996092883977913922703875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39330728589318609281802583 58996092883977913922703875)
    ·
      refine ⟨88494139325966870884055813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58996092883977913922703875 88494139325966870884055813)
      ·
        refine ⟨16592651123618788290760465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88494139325966870884055813 16592651123618788290760465)
        ·
          refine ⟨12444488342714091218070349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16592651123618788290760465 12444488342714091218070349)
          ·
            refine ⟨4666683128517784206776381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12444488342714091218070349 4666683128517784206776381)
            ·
              refine ⟨1750006173194169077541143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4666683128517784206776381 1750006173194169077541143)
              ·
                refine ⟨2625009259791253616311715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750006173194169077541143 2625009259791253616311715)
                ·
                  refine ⟨3937513889686880424467573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2625009259791253616311715 3937513889686880424467573)
                  ·
                    refine ⟨369141927158145039793835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3937513889686880424467573 369141927158145039793835)
                    ·
                      rfl

theorem cell23_2156704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 1, 1, 5].length) (baseStart_2156704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156704 prefixEnd_2156704 := by exact prefixLift 2156704
  have htrace : WordTrace (prefixWord ++ tailWord_2156704) baseStart_2156704 baseEnd_2156704 := by
    simpa [prefixWord, tailWord_2156704, baseEnd_2156704] using wordTrace_append hprefix tailTrace_2156704
  have hstable : (prefixWord ++ tailWord_2156704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156704).length < 2 ^ (prefixWord ++ tailWord_2156704).sum := by decide
  have hdescent : baseEnd_2156704 < baseStart_2156704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156727 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 3]
def baseStart_2156727 : Nat := 118140960795 + 2156727 * 2 ^ 59
def prefixEnd_2156727 : Nat := 4983230072969 + 3 ^ 40 * 2156727 * 2
def baseEnd_2156727 : Nat := 1107437591529488529393899

theorem tailTrace_2156727 : CollatzResearch.WordTrace tailWord_2156727 prefixEnd_2156727 1107437591529488529393899 := by
  unfold tailWord_2156727
  simp only [CollatzResearch.WordTrace]
  refine ⟨78662296057553893491692435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52441530705035928994461623 78662296057553893491692435)
  ·
    refine ⟨117993444086330840237538653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78662296057553893491692435 117993444086330840237538653)
    ·
      refine ⟨44247541532374065089076995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117993444086330840237538653 44247541532374065089076995)
      ·
        refine ⟨66371312298561097633615493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44247541532374065089076995 66371312298561097633615493)
        ·
          refine ⟨12444621055980205806302905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66371312298561097633615493 12444621055980205806302905)
          ·
            refine ⟨9333465791985154354727179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12444621055980205806302905 9333465791985154354727179)
            ·
              refine ⟨14000198687977731532090769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9333465791985154354727179 14000198687977731532090769)
              ·
                refine ⟨10500149015983298649068077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14000198687977731532090769 10500149015983298649068077)
                ·
                  refine ⟨3937555880993736993400529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10500149015983298649068077 3937555880993736993400529)
                  ·
                    refine ⟨2953166910745302745050397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3937555880993736993400529 2953166910745302745050397)
                    ·
                      refine ⟨1107437591529488529393899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2953166910745302745050397 1107437591529488529393899)
                      ·
                        rfl

theorem cell23_2156727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_2156727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156727 prefixEnd_2156727 := by exact prefixLift 2156727
  have htrace : WordTrace (prefixWord ++ tailWord_2156727) baseStart_2156727 baseEnd_2156727 := by
    simpa [prefixWord, tailWord_2156727, baseEnd_2156727] using wordTrace_append hprefix tailTrace_2156727
  have hstable : (prefixWord ++ tailWord_2156727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156727).length < 2 ^ (prefixWord ++ tailWord_2156727).sum := by decide
  have hdescent : baseEnd_2156727 < baseStart_2156727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156730 : List Nat := [3, 1, 1, 1, 2, 2, 5, 8]
def baseStart_2156730 : Nat := 118140960795 + 2156730 * 2 ^ 59
def prefixEnd_2156730 : Nat := 4983230072969 + 3 ^ 40 * 2156730 * 2
def baseEnd_2156730 : Nat := 41016264147090815468755

theorem tailTrace_2156730 : CollatzResearch.WordTrace tailWord_2156730 prefixEnd_2156730 41016264147090815468755 := by
  unfold tailWord_2156730
  simp only [CollatzResearch.WordTrace]
  refine ⟨19665601369135756251012911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52441603651028683336034429 19665601369135756251012911)
  ·
    refine ⟨29498402053703634376519367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19665601369135756251012911 29498402053703634376519367)
    ·
      refine ⟨44247603080555451564779051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29498402053703634376519367 44247603080555451564779051)
      ·
        refine ⟨66371404620833177347168577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44247603080555451564779051 66371404620833177347168577)
        ·
          refine ⟨49778553465624883010376433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66371404620833177347168577 49778553465624883010376433)
          ·
            refine ⟨37333915099218662257782325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49778553465624883010376433 37333915099218662257782325)
            ·
              refine ⟨3500054540551749586667093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37333915099218662257782325 3500054540551749586667093)
              ·
                refine ⟨41016264147090815468755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3500054540551749586667093 41016264147090815468755)
                ·
                  rfl

theorem cell23_2156730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 8].length) (baseStart_2156730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156730 prefixEnd_2156730 := by exact prefixLift 2156730
  have htrace : WordTrace (prefixWord ++ tailWord_2156730) baseStart_2156730 baseEnd_2156730 := by
    simpa [prefixWord, tailWord_2156730, baseEnd_2156730] using wordTrace_append hprefix tailTrace_2156730
  have hstable : (prefixWord ++ tailWord_2156730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156730).length < 2 ^ (prefixWord ++ tailWord_2156730).sum := by decide
  have hdescent : baseEnd_2156730 < baseStart_2156730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156734 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_2156734 : Nat := 118140960795 + 2156734 * 2 ^ 59
def prefixEnd_2156734 : Nat := 4983230072969 + 3 ^ 40 * 2156734 * 2
def baseEnd_2156734 : Nat := 369147061964690000668789

theorem tailTrace_2156734 : CollatzResearch.WordTrace tailWord_2156734 prefixEnd_2156734 369147061964690000668789 := by
  unfold tailWord_2156734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9832818921066066710899657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52441700912352355791464837 9832818921066066710899657)
  ·
    refine ⟨7374614190799550033174743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9832818921066066710899657 7374614190799550033174743)
    ·
      refine ⟨11061921286199325049762115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7374614190799550033174743 11061921286199325049762115)
      ·
        refine ⟨16592881929298987574643173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11061921286199325049762115 16592881929298987574643173)
        ·
          refine ⟨3111165361743560170245595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16592881929298987574643173 3111165361743560170245595)
          ·
            refine ⟨4666748042615340255368393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111165361743560170245595 4666748042615340255368393)
            ·
              refine ⟨3500061031961505191526295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4666748042615340255368393 3500061031961505191526295)
              ·
                refine ⟨5250091547942257787289443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3500061031961505191526295 5250091547942257787289443)
                ·
                  refine ⟨7875137321913386680934165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5250091547942257787289443 7875137321913386680934165)
                  ·
                    refine ⟨369147061964690000668789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7875137321913386680934165 369147061964690000668789)
                    ·
                      rfl

theorem cell23_2156734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_2156734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156734 prefixEnd_2156734 := by exact prefixLift 2156734
  have htrace : WordTrace (prefixWord ++ tailWord_2156734) baseStart_2156734 baseEnd_2156734 := by
    simpa [prefixWord, tailWord_2156734, baseEnd_2156734] using wordTrace_append hprefix tailTrace_2156734
  have hstable : (prefixWord ++ tailWord_2156734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156734).length < 2 ^ (prefixWord ++ tailWord_2156734).sum := by decide
  have hdescent : baseEnd_2156734 < baseStart_2156734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156758 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_2156758 : Nat := 118140960795 + 2156758 * 2 ^ 59
def prefixEnd_2156758 : Nat := 4983230072969 + 3 ^ 40 * 2156758 * 2
def baseEnd_2156758 : Nat := 1107453509429777908106257

theorem tailTrace_2156758 : CollatzResearch.WordTrace tailWord_2156758 prefixEnd_2156758 1107453509429777908106257 := by
  unfold tailWord_2156758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4916464170027599111629433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52442284480294390524047285 4916464170027599111629433)
  ·
    refine ⟨3687348127520699333722075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4916464170027599111629433 3687348127520699333722075)
    ·
      refine ⟨5531022191281049000583113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3687348127520699333722075 5531022191281049000583113)
      ·
        refine ⟨4148266643460786750437335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5531022191281049000583113 4148266643460786750437335)
        ·
          refine ⟨6222399965191180125656003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148266643460786750437335 6222399965191180125656003)
          ·
            refine ⟨9333599947786770188484005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6222399965191180125656003 9333599947786770188484005)
            ·
              refine ⟨1750049990210019410340751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9333599947786770188484005 1750049990210019410340751)
              ·
                refine ⟨2625074985315029115511127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750049990210019410340751 2625074985315029115511127)
                ·
                  refine ⟨3937612477972543673266691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2625074985315029115511127 3937612477972543673266691)
                  ·
                    refine ⟨5906418716958815509900037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3937612477972543673266691 5906418716958815509900037)
                    ·
                      refine ⟨1107453509429777908106257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5906418716958815509900037 1107453509429777908106257)
                      ·
                        rfl

theorem cell23_2156758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_2156758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156758 prefixEnd_2156758 := by exact prefixLift 2156758
  have htrace : WordTrace (prefixWord ++ tailWord_2156758) baseStart_2156758 baseEnd_2156758 := by
    simpa [prefixWord, tailWord_2156758, baseEnd_2156758] using wordTrace_append hprefix tailTrace_2156758
  have hstable : (prefixWord ++ tailWord_2156758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156758).length < 2 ^ (prefixWord ++ tailWord_2156758).sum := by decide
  have hdescent : baseEnd_2156758 < baseStart_2156758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156764 : List Nat := [2, 2, 5, 2, 1, 1, 10]
def baseStart_2156764 : Nat := 118140960795 + 2156764 * 2 ^ 59
def prefixEnd_2156764 : Nat := 4983230072969 + 3 ^ 40 * 2156764 * 2
def baseEnd_2156764 : Nat := 13672303584119813390509

theorem tailTrace_2156764 : CollatzResearch.WordTrace tailWord_2156764 prefixEnd_2156764 13672303584119813390509 := by
  unfold tailWord_2156764
  simp only [CollatzResearch.WordTrace]
  refine ⟨39331822779209924405394673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52442430372279899207192897 39331822779209924405394673)
  ·
    refine ⟨29498867084407443304046005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39331822779209924405394673 29498867084407443304046005)
    ·
      refine ⟨2765518789163197809754313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29498867084407443304046005 2765518789163197809754313)
      ·
        refine ⟨2074139091872398357315735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2765518789163197809754313 2074139091872398357315735)
        ·
          refine ⟨3111208637808597535973603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2074139091872398357315735 3111208637808597535973603)
          ·
            refine ⟨4666812956712896303960405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111208637808597535973603 4666812956712896303960405)
            ·
              refine ⟨13672303584119813390509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4666812956712896303960405 13672303584119813390509)
              ·
                rfl

theorem cell23_2156764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 10].length) (baseStart_2156764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156764 prefixEnd_2156764 := by exact prefixLift 2156764
  have htrace : WordTrace (prefixWord ++ tailWord_2156764) baseStart_2156764 baseEnd_2156764 := by
    simpa [prefixWord, tailWord_2156764, baseEnd_2156764] using wordTrace_append hprefix tailTrace_2156764
  have hstable : (prefixWord ++ tailWord_2156764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156764).length < 2 ^ (prefixWord ++ tailWord_2156764).sum := by decide
  have hdescent : baseEnd_2156764 < baseStart_2156764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156801 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_2156801 : Nat := 118140960795 + 2156801 * 2 ^ 59
def prefixEnd_2156801 : Nat := 4983230072969 + 3 ^ 40 * 2156801 * 2
def baseEnd_2156801 : Nat := 1107475589097921239868559

theorem tailTrace_2156801 : CollatzResearch.WordTrace tailWord_2156801 prefixEnd_2156801 1107475589097921239868559 := by
  unfold tailWord_2156801
  simp only [CollatzResearch.WordTrace]
  refine ⟨78664995059285804129886257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52443330039523869419924171 78664995059285804129886257)
  ·
    refine ⟨58998746294464353097414693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78664995059285804129886257 58998746294464353097414693)
    ·
      refine ⟨11062264930212066205765255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58998746294464353097414693 11062264930212066205765255)
      ·
        refine ⟨16593397395318099308647883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11062264930212066205765255 16593397395318099308647883)
        ·
          refine ⟨24890096092977148962971825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16593397395318099308647883 24890096092977148962971825)
          ·
            refine ⟨18667572069732861722228869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24890096092977148962971825 18667572069732861722228869)
            ·
              refine ⟨3500169763074911572917913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18667572069732861722228869 3500169763074911572917913)
              ·
                refine ⟨2625127322306183679688435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3500169763074911572917913 2625127322306183679688435)
                ·
                  refine ⟨3937690983459275519532653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2625127322306183679688435 3937690983459275519532653)
                  ·
                    refine ⟨1476634118797228319824745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3937690983459275519532653 1476634118797228319824745)
                    ·
                      refine ⟨1107475589097921239868559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1476634118797228319824745 1107475589097921239868559)
                      ·
                        rfl

theorem cell23_2156801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_2156801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156801 prefixEnd_2156801 := by exact prefixLift 2156801
  have htrace : WordTrace (prefixWord ++ tailWord_2156801) baseStart_2156801 baseEnd_2156801 := by
    simpa [prefixWord, tailWord_2156801, baseEnd_2156801] using wordTrace_append hprefix tailTrace_2156801
  have hstable : (prefixWord ++ tailWord_2156801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156801).length < 2 ^ (prefixWord ++ tailWord_2156801).sum := by decide
  have hdescent : baseEnd_2156801 < baseStart_2156801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156814 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2]
def baseStart_2156814 : Nat := 118140960795 + 2156814 * 2 ^ 59
def prefixEnd_2156814 : Nat := 4983230072969 + 3 ^ 40 * 2156814 * 2
def baseEnd_2156814 : Nat := 1107482264346429689005999

theorem tailTrace_2156814 : CollatzResearch.WordTrace tailWord_2156814 prefixEnd_2156814 1107482264346429689005999 := by
  unfold tailWord_2156814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9833183651029838418763687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52443646138825804900072997 9833183651029838418763687)
  ·
    refine ⟨14749775476544757628145531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9833183651029838418763687 14749775476544757628145531)
    ·
      refine ⟨22124663214817136442218297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14749775476544757628145531 22124663214817136442218297)
      ·
        refine ⟨16593497411112852331663723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22124663214817136442218297 16593497411112852331663723)
        ·
          refine ⟨24890246116669278497495585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16593497411112852331663723 24890246116669278497495585)
          ·
            refine ⟨18667684587501958873121689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24890246116669278497495585 18667684587501958873121689)
            ·
              refine ⟨14000763440626469154841267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18667684587501958873121689 14000763440626469154841267)
              ·
                refine ⟨21001145160939703732261901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14000763440626469154841267 21001145160939703732261901)
                ·
                  refine ⟨7875429435352388899598213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21001145160939703732261901 7875429435352388899598213)
                  ·
                    refine ⟨1476643019128572918674665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7875429435352388899598213 1476643019128572918674665)
                    ·
                      refine ⟨1107482264346429689005999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1476643019128572918674665 1107482264346429689005999)
                      ·
                        rfl

theorem cell23_2156814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_2156814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156814 prefixEnd_2156814 := by exact prefixLift 2156814
  have htrace : WordTrace (prefixWord ++ tailWord_2156814) baseStart_2156814 baseEnd_2156814 := by
    simpa [prefixWord, tailWord_2156814, baseEnd_2156814] using wordTrace_append hprefix tailTrace_2156814
  have hstable : (prefixWord ++ tailWord_2156814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156814).length < 2 ^ (prefixWord ++ tailWord_2156814).sum := by decide
  have hdescent : baseEnd_2156814 < baseStart_2156814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156817 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_2156817 : Nat := 118140960795 + 2156817 * 2 ^ 59
def prefixEnd_2156817 : Nat := 4983230072969 + 3 ^ 40 * 2156817 * 2
def baseEnd_2156817 : Nat := 1107483804788393177268485

theorem tailTrace_2156817 : CollatzResearch.WordTrace tailWord_2156817 prefixEnd_2156817 1107483804788393177268485 := by
  unfold tailWord_2156817
  simp only [CollatzResearch.WordTrace]
  refine ⟨78665578627227838862468705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52443719084818559241645803 78665578627227838862468705)
  ·
    refine ⟨58999183970420879146851529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78665578627227838862468705 58999183970420879146851529)
    ·
      refine ⟨44249387977815659360138647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58999183970420879146851529 44249387977815659360138647)
      ·
        refine ⟨66374081966723489040207971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44249387977815659360138647 66374081966723489040207971)
        ·
          refine ⟨99561122950085233560311957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66374081966723489040207971 99561122950085233560311957)
          ·
            refine ⟨4666927638285245323139623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99561122950085233560311957 4666927638285245323139623)
            ·
              refine ⟨7000391457427867984709435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4666927638285245323139623 7000391457427867984709435)
              ·
                refine ⟨10500587186141801977064153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7000391457427867984709435 10500587186141801977064153)
                ·
                  refine ⟨7875440389606351482798115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10500587186141801977064153 7875440389606351482798115)
                  ·
                    refine ⟨11813160584409527224197173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7875440389606351482798115 11813160584409527224197173)
                    ·
                      refine ⟨1107483804788393177268485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11813160584409527224197173 1107483804788393177268485)
                      ·
                        rfl

theorem cell23_2156817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_2156817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156817 prefixEnd_2156817 := by exact prefixLift 2156817
  have htrace : WordTrace (prefixWord ++ tailWord_2156817) baseStart_2156817 baseEnd_2156817 := by
    simpa [prefixWord, tailWord_2156817, baseEnd_2156817] using wordTrace_append hprefix tailTrace_2156817
  have hstable : (prefixWord ++ tailWord_2156817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156817).length < 2 ^ (prefixWord ++ tailWord_2156817).sum := by decide
  have hdescent : baseEnd_2156817 < baseStart_2156817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156831 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 4, 2, 2]
def baseStart_2156831 : Nat := 118140960795 + 2156831 * 2 ^ 59
def prefixEnd_2156831 : Nat := 4983230072969 + 3 ^ 40 * 2156831 * 2
def baseEnd_2156831 : Nat := 1107490993517556122493421

theorem tailTrace_2156831 : CollatzResearch.WordTrace tailWord_2156831 prefixEnd_2156831 1107490993517556122493421 := by
  unfold tailWord_2156831
  simp only [CollatzResearch.WordTrace]
  refine ⟨78666089249177119253478347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52444059499451412835652231 78666089249177119253478347)
  ·
    refine ⟨117999133873765678880217521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78666089249177119253478347 117999133873765678880217521)
    ·
      refine ⟨88499350405324259160163141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117999133873765678880217521 88499350405324259160163141)
      ·
        refine ⟨16593628200998298592530589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88499350405324259160163141 16593628200998298592530589)
        ·
          refine ⟨6222610575374361972198971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16593628200998298592530589 6222610575374361972198971)
          ·
            refine ⟨9333915863061542958298457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6222610575374361972198971 9333915863061542958298457)
            ·
              refine ⟨7000436897296157218723843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9333915863061542958298457 7000436897296157218723843)
              ·
                refine ⟨10500655345944235828085765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7000436897296157218723843 10500655345944235828085765)
                ·
                  refine ⟨1968872877364544217766081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10500655345944235828085765 1968872877364544217766081)
                  ·
                    refine ⟨1476654658023408163324561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1968872877364544217766081 1476654658023408163324561)
                    ·
                      refine ⟨1107490993517556122493421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1476654658023408163324561 1107490993517556122493421)
                      ·
                        rfl

theorem cell23_2156831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_2156831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156831 prefixEnd_2156831 := by exact prefixLift 2156831
  have htrace : WordTrace (prefixWord ++ tailWord_2156831) baseStart_2156831 baseEnd_2156831 := by
    simpa [prefixWord, tailWord_2156831, baseEnd_2156831] using wordTrace_append hprefix tailTrace_2156831
  have hstable : (prefixWord ++ tailWord_2156831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156831).length < 2 ^ (prefixWord ++ tailWord_2156831).sum := by decide
  have hdescent : baseEnd_2156831 < baseStart_2156831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156842 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_2156842 : Nat := 118140960795 + 2156842 * 2 ^ 59
def prefixEnd_2156842 : Nat := 4983230072969 + 3 ^ 40 * 2156842 * 2
def baseEnd_2156842 : Nat := 1107496641804755579455871

theorem tailTrace_2156842 : CollatzResearch.WordTrace tailWord_2156842 prefixEnd_2156842 1107496641804755579455871 := by
  unfold tailWord_2156842
  simp only [CollatzResearch.WordTrace]
  refine ⟨19666622613034317033032195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52444326968091512088085853 19666622613034317033032195)
  ·
    refine ⟨29499933919551475549548293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19666622613034317033032195 29499933919551475549548293)
    ·
      refine ⟨5531237609915901665540305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29499933919551475549548293 5531237609915901665540305)
      ·
        refine ⟨4148428207436926249155229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5531237609915901665540305 4148428207436926249155229)
        ·
          refine ⟨1555660577788847343433211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4148428207436926249155229 1555660577788847343433211)
          ·
            refine ⟨2333490866683271015149817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1555660577788847343433211 2333490866683271015149817)
            ·
              refine ⟨1750118150012453261362363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2333490866683271015149817 1750118150012453261362363)
              ·
                refine ⟨2625177225018679892043545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750118150012453261362363 2625177225018679892043545)
                ·
                  refine ⟨1968882918764009919032659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2625177225018679892043545 1968882918764009919032659)
                  ·
                    refine ⟨2953324378146014878548989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1968882918764009919032659 2953324378146014878548989)
                    ·
                      refine ⟨1107496641804755579455871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2953324378146014878548989 1107496641804755579455871)
                      ·
                        rfl

theorem cell23_2156842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_2156842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156842 prefixEnd_2156842 := by exact prefixLift 2156842
  have htrace : WordTrace (prefixWord ++ tailWord_2156842) baseStart_2156842 baseEnd_2156842 := by
    simpa [prefixWord, tailWord_2156842, baseEnd_2156842] using wordTrace_append hprefix tailTrace_2156842
  have hstable : (prefixWord ++ tailWord_2156842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156842).length < 2 ^ (prefixWord ++ tailWord_2156842).sum := by decide
  have hdescent : baseEnd_2156842 < baseStart_2156842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156847 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 3]
def baseStart_2156847 : Nat := 118140960795 + 2156847 * 2 ^ 59
def prefixEnd_2156847 : Nat := 4983230072969 + 3 ^ 40 * 2156847 * 2
def baseEnd_2156847 : Nat := 1107499209208028059893347

theorem tailTrace_2156847 : CollatzResearch.WordTrace tailWord_2156847 prefixEnd_2156847 1107499209208028059893347 := by
  unfold tailWord_2156847
  simp only [CollatzResearch.WordTrace]
  refine ⟨78666672817119153986060795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52444448544746102657373863 78666672817119153986060795)
  ·
    refine ⟨118000009225678730979091193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78666672817119153986060795 118000009225678730979091193)
    ·
      refine ⟨88500006919259048234318395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118000009225678730979091193 88500006919259048234318395)
      ·
        refine ⟨132750010378888572351477593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88500006919259048234318395 132750010378888572351477593)
        ·
          refine ⟨99562507784166429263608195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132750010378888572351477593 99562507784166429263608195)
          ·
            refine ⟨149343761676249643895412293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99562507784166429263608195 149343761676249643895412293)
            ·
              refine ⟨28001955314296808230389805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149343761676249643895412293 28001955314296808230389805)
              ·
                refine ⟨10500733242861303086396177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28001955314296808230389805 10500733242861303086396177)
                ·
                  refine ⟨7875549932145977314797133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10500733242861303086396177 7875549932145977314797133)
                  ·
                    refine ⟨2953331224554741493048925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7875549932145977314797133 2953331224554741493048925)
                    ·
                      refine ⟨1107499209208028059893347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2953331224554741493048925 1107499209208028059893347)
                      ·
                        rfl

theorem cell23_2156847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 3].length) (baseStart_2156847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156847 prefixEnd_2156847 := by exact prefixLift 2156847
  have htrace : WordTrace (prefixWord ++ tailWord_2156847) baseStart_2156847 baseEnd_2156847 := by
    simpa [prefixWord, tailWord_2156847, baseEnd_2156847] using wordTrace_append hprefix tailTrace_2156847
  have hstable : (prefixWord ++ tailWord_2156847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156847).length < 2 ^ (prefixWord ++ tailWord_2156847).sum := by decide
  have hdescent : baseEnd_2156847 < baseStart_2156847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156867 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 2, 5]
def baseStart_2156867 : Nat := 118140960795 + 2156867 * 2 ^ 59
def prefixEnd_2156867 : Nat := 4983230072969 + 3 ^ 40 * 2156867 * 2
def baseEnd_2156867 : Nat := 369169826273705993881085

theorem tailTrace_2156867 : CollatzResearch.WordTrace tailWord_2156867 prefixEnd_2156867 369169826273705993881085 := by
  unfold tailWord_2156867
  simp only [CollatzResearch.WordTrace]
  refine ⟨78667402277046697401788855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52444934851364464934525903 78667402277046697401788855)
  ·
    refine ⟨118001103415570046102683283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78667402277046697401788855 118001103415570046102683283)
    ·
      refine ⟨177001655123355069154024925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118001103415570046102683283 177001655123355069154024925)
      ·
        refine ⟨66375620671258150932759347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177001655123355069154024925 66375620671258150932759347)
        ·
          refine ⟨99563431006887226399139021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66375620671258150932759347 99563431006887226399139021)
          ·
            refine ⟨37336286627582709899677133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99563431006887226399139021 37336286627582709899677133)
            ·
              refine ⟨14001107485343516212378925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37336286627582709899677133 14001107485343516212378925)
              ·
                refine ⟨5250415307003818579642097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14001107485343516212378925 5250415307003818579642097)
                ·
                  refine ⟨3937811480252863934731573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5250415307003818579642097 3937811480252863934731573)
                  ·
                    refine ⟨369169826273705993881085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3937811480252863934731573 369169826273705993881085)
                    ·
                      rfl

theorem cell23_2156867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 5].length) (baseStart_2156867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156867 prefixEnd_2156867 := by exact prefixLift 2156867
  have htrace : WordTrace (prefixWord ++ tailWord_2156867) baseStart_2156867 baseEnd_2156867 := by
    simpa [prefixWord, tailWord_2156867, baseEnd_2156867] using wordTrace_append hprefix tailTrace_2156867
  have hstable : (prefixWord ++ tailWord_2156867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156867).length < 2 ^ (prefixWord ++ tailWord_2156867).sum := by decide
  have hdescent : baseEnd_2156867 < baseStart_2156867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156884 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_2156884 : Nat := 118140960795 + 2156884 * 2 ^ 59
def prefixEnd_2156884 : Nat := 4983230072969 + 3 ^ 40 * 2156884 * 2
def baseEnd_2156884 : Nat := 369172735997414805043559

theorem tailTrace_2156884 : CollatzResearch.WordTrace tailWord_2156884 prefixEnd_2156884 369172735997414805043559 := by
  unfold tailWord_2156884
  simp only [CollatzResearch.WordTrace]
  refine ⟨39334011158992554652578853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52445348211990072870105137 39334011158992554652578853)
  ·
    refine ⟨7375127092311103997358535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39334011158992554652578853 7375127092311103997358535)
    ·
      refine ⟨11062690638466655996037803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7375127092311103997358535 11062690638466655996037803)
      ·
        refine ⟨16594035957699983994056705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11062690638466655996037803 16594035957699983994056705)
        ·
          refine ⟨12445526968274987995542529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16594035957699983994056705 12445526968274987995542529)
          ·
            refine ⟨9334145226206240996656897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12445526968274987995542529 9334145226206240996656897)
            ·
              refine ⟨7000608919654680747492673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9334145226206240996656897 7000608919654680747492673)
              ·
                refine ⟨5250456689741010560619505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7000608919654680747492673 5250456689741010560619505)
                ·
                  refine ⟨3937842517305757920464629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5250456689741010560619505 3937842517305757920464629)
                  ·
                    refine ⟨369172735997414805043559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3937842517305757920464629 369172735997414805043559)
                    ·
                      rfl

theorem cell23_2156884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_2156884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156884 prefixEnd_2156884 := by exact prefixLift 2156884
  have htrace : WordTrace (prefixWord ++ tailWord_2156884) baseStart_2156884 baseEnd_2156884 := by
    simpa [prefixWord, tailWord_2156884, baseEnd_2156884] using wordTrace_append hprefix tailTrace_2156884
  have hstable : (prefixWord ++ tailWord_2156884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156884).length < 2 ^ (prefixWord ++ tailWord_2156884).sum := by decide
  have hdescent : baseEnd_2156884 < baseStart_2156884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156907 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 3]
def baseStart_2156907 : Nat := 118140960795 + 2156907 * 2 ^ 59
def prefixEnd_2156907 : Nat := 4983230072969 + 3 ^ 40 * 2156907 * 2
def baseEnd_2156907 : Nat := 1107530018047297825143071

theorem tailTrace_2156907 : CollatzResearch.WordTrace tailWord_2156907 prefixEnd_2156907 1107530018047297825143071 := by
  unfold tailWord_2156907
  simp only [CollatzResearch.WordTrace]
  refine ⟨78668861196901784233244975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52445907464601189488829983 78668861196901784233244975)
  ·
    refine ⟨118003291795352676349867463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78668861196901784233244975 118003291795352676349867463)
    ·
      refine ⟨177004937693029014524801195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118003291795352676349867463 177004937693029014524801195)
      ·
        refine ⟨265507406539543521787201793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177004937693029014524801195 265507406539543521787201793)
        ·
          refine ⟨199130554904657641340401345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265507406539543521787201793 199130554904657641340401345)
          ·
            refine ⟨149347916178493231005301009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199130554904657641340401345 149347916178493231005301009)
            ·
              refine ⟨112010937133869923253975757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149347916178493231005301009 112010937133869923253975757)
              ·
                refine ⟨42004101425201221220240909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112010937133869923253975757 42004101425201221220240909)
                ·
                  refine ⟨15751538034450457957590341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42004101425201221220240909 15751538034450457957590341)
                  ·
                    refine ⟨2953413381459460867048189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15751538034450457957590341 2953413381459460867048189)
                    ·
                      refine ⟨1107530018047297825143071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2953413381459460867048189 1107530018047297825143071)
                      ·
                        rfl

theorem cell23_2156907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 3].length) (baseStart_2156907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156907 prefixEnd_2156907 := by exact prefixLift 2156907
  have htrace : WordTrace (prefixWord ++ tailWord_2156907) baseStart_2156907 baseEnd_2156907 := by
    simpa [prefixWord, tailWord_2156907, baseEnd_2156907] using wordTrace_append hprefix tailTrace_2156907
  have hstable : (prefixWord ++ tailWord_2156907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156907).length < 2 ^ (prefixWord ++ tailWord_2156907).sum := by decide
  have hdescent : baseEnd_2156907 < baseStart_2156907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156914 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_2156914 : Nat := 118140960795 + 2156914 * 2 ^ 59
def prefixEnd_2156914 : Nat := 4983230072969 + 3 ^ 40 * 2156914 * 2
def baseEnd_2156914 : Nat := 369177870803959765918513

theorem tailTrace_2156914 : CollatzResearch.WordTrace tailWord_2156914 prefixEnd_2156914 369177870803959765918513 := by
  unfold tailWord_2156914
  simp only [CollatzResearch.WordTrace]
  refine ⟨19667279126969106107187449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52446077671917616285833197 19667279126969106107187449)
  ·
    refine ⟨14750459345226829580390587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19667279126969106107187449 14750459345226829580390587)
    ·
      refine ⟨22125689017840244370585881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14750459345226829580390587 22125689017840244370585881)
      ·
        refine ⟨16594266763380183277939411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22125689017840244370585881 16594266763380183277939411)
        ·
          refine ⟨24891400145070274916909117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16594266763380183277939411 24891400145070274916909117)
          ·
            refine ⟨9334275054401353093840919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24891400145070274916909117 9334275054401353093840919)
            ·
              refine ⟨14001412581602029640761379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9334275054401353093840919 14001412581602029640761379)
              ·
                refine ⟨21002118872403044461142069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14001412581602029640761379 21002118872403044461142069)
                ·
                  refine ⟨1968948644287785418232069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21002118872403044461142069 1968948644287785418232069)
                  ·
                    refine ⟨369177870803959765918513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1968948644287785418232069 369177870803959765918513)
                    ·
                      rfl

theorem cell23_2156914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_2156914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156914 prefixEnd_2156914 := by exact prefixLift 2156914
  have htrace : WordTrace (prefixWord ++ tailWord_2156914) baseStart_2156914 baseEnd_2156914 := by
    simpa [prefixWord, tailWord_2156914, baseEnd_2156914] using wordTrace_append hprefix tailTrace_2156914
  have hstable : (prefixWord ++ tailWord_2156914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156914).length < 2 ^ (prefixWord ++ tailWord_2156914).sum := by decide
  have hdescent : baseEnd_2156914 < baseStart_2156914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156924 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_2156924 : Nat := 118140960795 + 2156924 * 2 ^ 59
def prefixEnd_2156924 : Nat := 4983230072969 + 3 ^ 40 * 2156924 * 2
def baseEnd_2156924 : Nat := 1107538747218424258630493

theorem tailTrace_2156924 : CollatzResearch.WordTrace tailWord_2156924 prefixEnd_2156924 1107538747218424258630493 := by
  unfold tailWord_2156924
  simp only [CollatzResearch.WordTrace]
  refine ⟨39334740618920098068306913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52446320825226797424409217 39334740618920098068306913)
  ·
    refine ⟨29501055464190073551230185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39334740618920098068306913 29501055464190073551230185)
    ·
      refine ⟨22125791598142555163422639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29501055464190073551230185 22125791598142555163422639)
      ·
        refine ⟨33188687397213832745133959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22125791598142555163422639 33188687397213832745133959)
        ·
          refine ⟨49783031095820749117700939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33188687397213832745133959 49783031095820749117700939)
          ·
            refine ⟨74674546643731123676551409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49783031095820749117700939 74674546643731123676551409)
            ·
              refine ⟨56005909982798342757413557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74674546643731123676551409 56005909982798342757413557)
              ·
                refine ⟨5250554060887344633507521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56005909982798342757413557 5250554060887344633507521)
                ·
                  refine ⟨3937915545665508475130641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5250554060887344633507521 3937915545665508475130641)
                  ·
                    refine ⟨2953436659249131356347981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3937915545665508475130641 2953436659249131356347981)
                    ·
                      refine ⟨1107538747218424258630493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2953436659249131356347981 1107538747218424258630493)
                      ·
                        rfl

theorem cell23_2156924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_2156924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156924 prefixEnd_2156924 := by exact prefixLift 2156924
  have htrace : WordTrace (prefixWord ++ tailWord_2156924) baseStart_2156924 baseEnd_2156924 := by
    simpa [prefixWord, tailWord_2156924, baseEnd_2156924] using wordTrace_append hprefix tailTrace_2156924
  have hstable : (prefixWord ++ tailWord_2156924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156924).length < 2 ^ (prefixWord ++ tailWord_2156924).sum := by decide
  have hdescent : baseEnd_2156924 < baseStart_2156924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2156948 : List Nat := [2, 4, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2156948 : Nat := 118140960795 + 2156948 * 2 ^ 59
def prefixEnd_2156948 : Nat := 4983230072969 + 3 ^ 40 * 2156948 * 2
def baseEnd_2156948 : Nat := 369183690251377388243461

theorem tailTrace_2156948 : CollatzResearch.WordTrace tailWord_2156948 prefixEnd_2156948 369183690251377388243461 := by
  unfold tailWord_2156948
  simp only [CollatzResearch.WordTrace]
  refine ⟨39335178294876624117743749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52446904393168832156991665 39335178294876624117743749)
  ·
    refine ⟨7375345930289367022076953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39335178294876624117743749 7375345930289367022076953)
    ·
      refine ⟨5531509447717025266557715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7375345930289367022076953 5531509447717025266557715)
      ·
        refine ⟨8297264171575537899836573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5531509447717025266557715 8297264171575537899836573)
        ·
          refine ⟨3111474064340826712438715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8297264171575537899836573 3111474064340826712438715)
          ·
            refine ⟨4667211096511240068658073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111474064340826712438715 4667211096511240068658073)
            ·
              refine ⟨3500408322383430051493555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4667211096511240068658073 3500408322383430051493555)
              ·
                refine ⟨5250612483575145077240333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3500408322383430051493555 5250612483575145077240333)
                ·
                  refine ⟨1968979681340679403965125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5250612483575145077240333 1968979681340679403965125)
                  ·
                    refine ⟨369183690251377388243461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1968979681340679403965125 369183690251377388243461)
                    ·
                      rfl

theorem cell23_2156948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2156948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2156948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2156948 prefixEnd_2156948 := by exact prefixLift 2156948
  have htrace : WordTrace (prefixWord ++ tailWord_2156948) baseStart_2156948 baseEnd_2156948 := by
    simpa [prefixWord, tailWord_2156948, baseEnd_2156948] using wordTrace_append hprefix tailTrace_2156948
  have hstable : (prefixWord ++ tailWord_2156948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2156948).length < 2 ^ (prefixWord ++ tailWord_2156948).sum := by decide
  have hdescent : baseEnd_2156948 < baseStart_2156948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2156948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157024 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 4]
def baseStart_2157024 : Nat := 118140960795 + 2157024 * 2 ^ 59
def prefixEnd_2157024 : Nat := 4983230072969 + 3 ^ 40 * 2157024 * 2
def baseEnd_2157024 : Nat := 1107590095283873867380033

theorem tailTrace_2157024 : CollatzResearch.WordTrace tailWord_2157024 prefixEnd_2157024 1107590095283873867380033 := by
  unfold tailWord_2157024
  simp only [CollatzResearch.WordTrace]
  refine ⟨39336564268738956607627063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52448752358318608810169417 39336564268738956607627063)
  ·
    refine ⟨59004846403108434911440595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39336564268738956607627063 59004846403108434911440595)
    ·
      refine ⟨88507269604662652367160893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59004846403108434911440595 88507269604662652367160893)
      ·
        refine ⟨33190226101748494637685335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88507269604662652367160893 33190226101748494637685335)
        ·
          refine ⟨49785339152622741956528003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33190226101748494637685335 49785339152622741956528003)
          ·
            refine ⟨74678008728934112934792005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49785339152622741956528003 74678008728934112934792005)
            ·
              refine ⟨14002126636675146175273501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74678008728934112934792005 14002126636675146175273501)
              ·
                refine ⟨5250797488753179815727563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14002126636675146175273501 5250797488753179815727563)
                ·
                  refine ⟨7876196233129769723591345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5250797488753179815727563 7876196233129769723591345)
                  ·
                    refine ⟨5907147174847327292693509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7876196233129769723591345 5907147174847327292693509)
                    ·
                      refine ⟨1107590095283873867380033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5907147174847327292693509 1107590095283873867380033)
                      ·
                        rfl

theorem cell23_2157024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_2157024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157024 prefixEnd_2157024 := by exact prefixLift 2157024
  have htrace : WordTrace (prefixWord ++ tailWord_2157024) baseStart_2157024 baseEnd_2157024 := by
    simpa [prefixWord, tailWord_2157024, baseEnd_2157024] using wordTrace_append hprefix tailTrace_2157024
  have hstable : (prefixWord ++ tailWord_2157024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157024).length < 2 ^ (prefixWord ++ tailWord_2157024).sum := by decide
  have hdescent : baseEnd_2157024 < baseStart_2157024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157031 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2157031 : Nat := 118140960795 + 2157031 * 2 ^ 59
def prefixEnd_2157031 : Nat := 4983230072969 + 3 ^ 40 * 2157031 * 2
def baseEnd_2157031 : Nat := 1107593689648455339992501

theorem tailTrace_2157031 : CollatzResearch.WordTrace tailWord_2157031 prefixEnd_2157031 1107593689648455339992501 := by
  unfold tailWord_2157031
  simp only [CollatzResearch.WordTrace]
  refine ⟨78673383848452553410758947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52448922565635035607172631 78673383848452553410758947)
  ·
    refine ⟨118010075772678830116138421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78673383848452553410758947 118010075772678830116138421)
    ·
      refine ⟨11063444603688640323387977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118010075772678830116138421 11063444603688640323387977)
      ·
        refine ⟨8297583452766480242540983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11063444603688640323387977 8297583452766480242540983)
        ·
          refine ⟨12446375179149720363811475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8297583452766480242540983 12446375179149720363811475)
          ·
            refine ⟨18669562768724580545717213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12446375179149720363811475 18669562768724580545717213)
            ·
              refine ⟨7001086038271717704643955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18669562768724580545717213 7001086038271717704643955)
              ·
                refine ⟨10501629057407576556965933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7001086038271717704643955 10501629057407576556965933)
                ·
                  refine ⟨3938110896527841208862225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10501629057407576556965933 3938110896527841208862225)
                  ·
                    refine ⟨2953583172395880906646669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3938110896527841208862225 2953583172395880906646669)
                    ·
                      refine ⟨1107593689648455339992501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2953583172395880906646669 1107593689648455339992501)
                      ·
                        rfl

theorem cell23_2157031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2157031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157031 prefixEnd_2157031 := by exact prefixLift 2157031
  have htrace : WordTrace (prefixWord ++ tailWord_2157031) baseStart_2157031 baseEnd_2157031 := by
    simpa [prefixWord, tailWord_2157031, baseEnd_2157031] using wordTrace_append hprefix tailTrace_2157031
  have hstable : (prefixWord ++ tailWord_2157031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157031).length < 2 ^ (prefixWord ++ tailWord_2157031).sum := by decide
  have hdescent : baseEnd_2157031 < baseStart_2157031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157034 : List Nat := [3, 1, 3, 1, 3, 1, 2, 9]
def baseStart_2157034 : Nat := 118140960795 + 2157034 * 2 ^ 59
def prefixEnd_2157034 : Nat := 4983230072969 + 3 ^ 40 * 2157034 * 2
def baseEnd_2157034 : Nat := 41022045558904401046481

theorem tailTrace_2157034 : CollatzResearch.WordTrace tailWord_2157034 prefixEnd_2157034 41022045558904401046481 := by
  unfold tailWord_2157034
  simp only [CollatzResearch.WordTrace]
  refine ⟨19668373316860421230779539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52448995511627789948745437 19668373316860421230779539)
  ·
    refine ⟨29502559975290631846169309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19668373316860421230779539 29502559975290631846169309)
    ·
      refine ⟨11063459990733986942313491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29502559975290631846169309 11063459990733986942313491)
      ·
        refine ⟨16595189986100980413470237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11063459990733986942313491 16595189986100980413470237)
        ·
          refine ⟨6223196244787867655051339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16595189986100980413470237 6223196244787867655051339)
          ·
            refine ⟨9334794367181801482577009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6223196244787867655051339 9334794367181801482577009)
            ·
              refine ⟨7001095775386351111932757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9334794367181801482577009 7001095775386351111932757)
              ·
                refine ⟨41022045558904401046481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7001095775386351111932757 41022045558904401046481)
                ·
                  rfl

theorem cell23_2157034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 9].length) (baseStart_2157034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157034 prefixEnd_2157034 := by exact prefixLift 2157034
  have htrace : WordTrace (prefixWord ++ tailWord_2157034) baseStart_2157034 baseEnd_2157034 := by
    simpa [prefixWord, tailWord_2157034, baseEnd_2157034] using wordTrace_append hprefix tailTrace_2157034
  have hstable : (prefixWord ++ tailWord_2157034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157034).length < 2 ^ (prefixWord ++ tailWord_2157034).sum := by decide
  have hdescent : baseEnd_2157034 < baseStart_2157034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157048 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 1, 2, 3]
def baseStart_2157048 : Nat := 118140960795 + 2157048 * 2 ^ 59
def prefixEnd_2157048 : Nat := 4983230072969 + 3 ^ 40 * 2157048 * 2
def baseEnd_2157048 : Nat := 1107602418819581773479923

theorem tailTrace_2157048 : CollatzResearch.WordTrace tailWord_2157048 prefixEnd_2157048 1107602418819581773479923 := by
  unfold tailWord_2157048
  simp only [CollatzResearch.WordTrace]
  refine ⟨39337001944695482657063899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52449335926260643542751865 39337001944695482657063899)
  ·
    refine ⟨59005502917043223985595849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39337001944695482657063899 59005502917043223985595849)
    ·
      refine ⟨44254127187782417989196887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59005502917043223985595849 44254127187782417989196887)
      ·
        refine ⟨66381190781673626983795331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44254127187782417989196887 66381190781673626983795331)
        ·
          refine ⟨99571786172510440475692997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66381190781673626983795331 99571786172510440475692997)
          ·
            refine ⟨18669709907345707589192437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99571786172510440475692997 18669709907345707589192437)
            ·
              refine ⟨1750285303813660086486791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18669709907345707589192437 1750285303813660086486791)
              ·
                refine ⟨2625427955720490129730187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750285303813660086486791 2625427955720490129730187)
                ·
                  refine ⟨3938141933580735194595281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2625427955720490129730187 3938141933580735194595281)
                  ·
                    refine ⟨2953606450185551395946461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3938141933580735194595281 2953606450185551395946461)
                    ·
                      refine ⟨1107602418819581773479923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2953606450185551395946461 1107602418819581773479923)
                      ·
                        rfl

theorem cell23_2157048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 1, 2, 3].length) (baseStart_2157048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157048 prefixEnd_2157048 := by exact prefixLift 2157048
  have htrace : WordTrace (prefixWord ++ tailWord_2157048) baseStart_2157048 baseEnd_2157048 := by
    simpa [prefixWord, tailWord_2157048, baseEnd_2157048] using wordTrace_append hprefix tailTrace_2157048
  have hstable : (prefixWord ++ tailWord_2157048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157048).length < 2 ^ (prefixWord ++ tailWord_2157048).sum := by decide
  have hdescent : baseEnd_2157048 < baseStart_2157048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157061 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 4, 1, 3]
def baseStart_2157061 : Nat := 118140960795 + 2157061 * 2 ^ 59
def prefixEnd_2157061 : Nat := 4983230072969 + 3 ^ 40 * 2157061 * 2
def baseEnd_2157061 : Nat := 1107609094068090222617363

theorem tailTrace_2157061 : CollatzResearch.WordTrace tailWord_2157061 prefixEnd_2157061 1107609094068090222617363 := by
  unfold tailWord_2157061
  simp only [CollatzResearch.WordTrace]
  refine ⟨78674478038343868534351037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52449652025562579022900691 78674478038343868534351037)
  ·
    refine ⟨29502929264378950700381639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78674478038343868534351037 29502929264378950700381639)
    ·
      refine ⟨44254393896568426050572459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29502929264378950700381639 44254393896568426050572459)
      ·
        refine ⟨66381590844852639075858689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44254393896568426050572459 66381590844852639075858689)
        ·
          refine ⟨49786193133639479306894017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66381590844852639075858689 49786193133639479306894017)
          ·
            refine ⟨37339644850229609480170513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49786193133639479306894017 37339644850229609480170513)
            ·
              refine ⟨28004733637672207110127885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37339644850229609480170513 28004733637672207110127885)
              ·
                refine ⟨10501775114127077666297957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28004733637672207110127885 10501775114127077666297957)
                ·
                  refine ⟨1969082833898827062430867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10501775114127077666297957 1969082833898827062430867)
                  ·
                    refine ⟨2953624250848240593646301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1969082833898827062430867 2953624250848240593646301)
                    ·
                      refine ⟨1107609094068090222617363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2953624250848240593646301 1107609094068090222617363)
                      ·
                        rfl

theorem cell23_2157061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_2157061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157061 prefixEnd_2157061 := by exact prefixLift 2157061
  have htrace : WordTrace (prefixWord ++ tailWord_2157061) baseStart_2157061 baseEnd_2157061 := by
    simpa [prefixWord, tailWord_2157061, baseEnd_2157061] using wordTrace_append hprefix tailTrace_2157061
  have hstable : (prefixWord ++ tailWord_2157061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157061).length < 2 ^ (prefixWord ++ tailWord_2157061).sum := by decide
  have hdescent : baseEnd_2157061 < baseStart_2157061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157071 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 3, 3, 2]
def baseStart_2157071 : Nat := 118140960795 + 2157071 * 2 ^ 59
def prefixEnd_2157071 : Nat := 4983230072969 + 3 ^ 40 * 2157071 * 2
def baseEnd_2157071 : Nat := 1107614228874635183492317

theorem tailTrace_2157071 : CollatzResearch.WordTrace tailWord_2157071 prefixEnd_2157071 1107614228874635183492317 := by
  unfold tailWord_2157071
  simp only [CollatzResearch.WordTrace]
  refine ⟨78674842768307640242215067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52449895178871760161476711 78674842768307640242215067)
  ·
    refine ⟨118012264152461460363322601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78674842768307640242215067 118012264152461460363322601)
    ·
      refine ⟨88509198114346095272491951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118012264152461460363322601 88509198114346095272491951)
      ·
        refine ⟨132763797171519142908737927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88509198114346095272491951 132763797171519142908737927)
        ·
          refine ⟨199145695757278714363106891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132763797171519142908737927 199145695757278714363106891)
          ·
            refine ⟨298718543635918071544660337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199145695757278714363106891 298718543635918071544660337)
            ·
              refine ⟨224038907726938553658495253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298718543635918071544660337 224038907726938553658495253)
              ·
                refine ⟨10501823799700244702741965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 224038907726938553658495253 10501823799700244702741965)
                ·
                  refine ⟨3938183924887591763528237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10501823799700244702741965 3938183924887591763528237)
                  ·
                    refine ⟨1476818971832846911323089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3938183924887591763528237 1476818971832846911323089)
                    ·
                      refine ⟨1107614228874635183492317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1476818971832846911323089 1107614228874635183492317)
                      ·
                        rfl

theorem cell23_2157071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 3, 2].length) (baseStart_2157071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157071 prefixEnd_2157071 := by exact prefixLift 2157071
  have htrace : WordTrace (prefixWord ++ tailWord_2157071) baseStart_2157071 baseEnd_2157071 := by
    simpa [prefixWord, tailWord_2157071, baseEnd_2157071] using wordTrace_append hprefix tailTrace_2157071
  have hstable : (prefixWord ++ tailWord_2157071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157071).length < 2 ^ (prefixWord ++ tailWord_2157071).sum := by decide
  have hdescent : baseEnd_2157071 < baseStart_2157071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157104 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 5]
def baseStart_2157104 : Nat := 118140960795 + 2157104 * 2 ^ 59
def prefixEnd_2157104 : Nat := 4983230072969 + 3 ^ 40 * 2157104 * 2
def baseEnd_2157104 : Nat := 1107631173736233554379665

theorem tailTrace_2157104 : CollatzResearch.WordTrace tailWord_2157104 prefixEnd_2157104 1107631173736233554379665 := by
  unfold tailWord_2157104
  simp only [CollatzResearch.WordTrace]
  refine ⟨39338023188594043439083183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52450697584792057918777577 39338023188594043439083183)
  ·
    refine ⟨59007034782891065158624775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39338023188594043439083183 59007034782891065158624775)
    ·
      refine ⟨88510552174336597737937163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59007034782891065158624775 88510552174336597737937163)
      ·
        refine ⟨132765828261504896606905745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88510552174336597737937163 132765828261504896606905745)
        ·
          refine ⟨99574371196128672455179309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132765828261504896606905745 99574371196128672455179309)
          ·
            refine ⟨37340389198548252170692241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99574371196128672455179309 37340389198548252170692241)
            ·
              refine ⟨28005291898911189128019181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37340389198548252170692241 28005291898911189128019181)
              ·
                refine ⟨10501984462091695923007193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28005291898911189128019181 10501984462091695923007193)
                ·
                  refine ⟨7876488346568771942255395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10501984462091695923007193 7876488346568771942255395)
                  ·
                    refine ⟨11814732519853157913383093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7876488346568771942255395 11814732519853157913383093)
                    ·
                      refine ⟨1107631173736233554379665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11814732519853157913383093 1107631173736233554379665)
                      ·
                        rfl

theorem cell23_2157104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_2157104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157104 prefixEnd_2157104 := by exact prefixLift 2157104
  have htrace : WordTrace (prefixWord ++ tailWord_2157104) baseStart_2157104 baseEnd_2157104 := by
    simpa [prefixWord, tailWord_2157104, baseEnd_2157104] using wordTrace_append hprefix tailTrace_2157104
  have hstable : (prefixWord ++ tailWord_2157104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157104).length < 2 ^ (prefixWord ++ tailWord_2157104).sum := by decide
  have hdescent : baseEnd_2157104 < baseStart_2157104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157105 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 1, 3, 2]
def baseStart_2157105 : Nat := 118140960795 + 2157105 * 2 ^ 59
def prefixEnd_2157105 : Nat := 4983230072969 + 3 ^ 40 * 2157105 * 2
def baseEnd_2157105 : Nat := 1107631687216888050467161

theorem tailTrace_2157105 : CollatzResearch.WordTrace tailWord_2157105 prefixEnd_2157105 1107631687216888050467161 := by
  unfold tailWord_2157105
  simp only [CollatzResearch.WordTrace]
  refine ⟨78676082850184464048952769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52450721900122976032635179 78676082850184464048952769)
  ·
    refine ⟨59007062137638348036714577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78676082850184464048952769 59007062137638348036714577)
    ·
      refine ⟨44255296603228761027535933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59007062137638348036714577 44255296603228761027535933)
      ·
        refine ⟨16595736226210785385325975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44255296603228761027535933 16595736226210785385325975)
        ·
          refine ⟨24893604339316178077988963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16595736226210785385325975 24893604339316178077988963)
          ·
            refine ⟨37340406508974267116983445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24893604339316178077988963 37340406508974267116983445)
            ·
              refine ⟨1750331555108168771108599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37340406508974267116983445 1750331555108168771108599)
              ·
                refine ⟨2625497332662253156662899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750331555108168771108599 2625497332662253156662899)
                ·
                  refine ⟨3938245998993379734994349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2625497332662253156662899 3938245998993379734994349)
                  ·
                    refine ⟨1476842249622517400622881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3938245998993379734994349 1476842249622517400622881)
                    ·
                      refine ⟨1107631687216888050467161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1476842249622517400622881 1107631687216888050467161)
                      ·
                        rfl

theorem cell23_2157105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_2157105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157105 prefixEnd_2157105 := by exact prefixLift 2157105
  have htrace : WordTrace (prefixWord ++ tailWord_2157105) baseStart_2157105 baseEnd_2157105 := by
    simpa [prefixWord, tailWord_2157105, baseEnd_2157105] using wordTrace_append hprefix tailTrace_2157105
  have hstable : (prefixWord ++ tailWord_2157105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157105).length < 2 ^ (prefixWord ++ tailWord_2157105).sum := by decide
  have hdescent : baseEnd_2157105 < baseStart_2157105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157161 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 1, 7, 2]
def baseStart_2157161 : Nat := 118140960795 + 2157161 * 2 ^ 59
def prefixEnd_2157161 : Nat := 4983230072969 + 3 ^ 40 * 2157161 * 2
def baseEnd_2157161 : Nat := 1107660442133539831366903

theorem tailTrace_2157161 : CollatzResearch.WordTrace tailWord_2157161 prefixEnd_2157161 1107660442133539831366903 := by
  unfold tailWord_2157161
  simp only [CollatzResearch.WordTrace]
  refine ⟨78678125337981585612991337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52452083558654390408660891 78678125337981585612991337)
  ·
    refine ⟨59008594003486189209743503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78678125337981585612991337 59008594003486189209743503)
    ·
      refine ⟨88512891005229283814615255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59008594003486189209743503 88512891005229283814615255)
      ·
        refine ⟨132769336507843925721922883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88512891005229283814615255 132769336507843925721922883)
        ·
          refine ⟨199154004761765888582884325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132769336507843925721922883 199154004761765888582884325)
          ·
            refine ⟨37341375892831104109290811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199154004761765888582884325 37341375892831104109290811)
            ·
              refine ⟨56012063839246656163936217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37341375892831104109290811 56012063839246656163936217)
              ·
                refine ⟨42009047879434992122952163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56012063839246656163936217 42009047879434992122952163)
                ·
                  refine ⟨63013571819152488184428245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42009047879434992122952163 63013571819152488184428245)
                  ·
                    refine ⟨1476880589511386441822537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 63013571819152488184428245 1476880589511386441822537)
                    ·
                      refine ⟨1107660442133539831366903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1476880589511386441822537 1107660442133539831366903)
                      ·
                        rfl

theorem cell23_2157161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 7, 2].length) (baseStart_2157161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157161 prefixEnd_2157161 := by exact prefixLift 2157161
  have htrace : WordTrace (prefixWord ++ tailWord_2157161) baseStart_2157161 baseEnd_2157161 := by
    simpa [prefixWord, tailWord_2157161, baseEnd_2157161] using wordTrace_append hprefix tailTrace_2157161
  have hstable : (prefixWord ++ tailWord_2157161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157161).length < 2 ^ (prefixWord ++ tailWord_2157161).sum := by decide
  have hdescent : baseEnd_2157161 < baseStart_2157161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157191 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 4]
def baseStart_2157191 : Nat := 118140960795 + 2157191 * 2 ^ 59
def prefixEnd_2157191 : Nat := 4983230072969 + 3 ^ 40 * 2157191 * 2
def baseEnd_2157191 : Nat := 1107675846553174713991765

theorem tailTrace_2157191 : CollatzResearch.WordTrace tailWord_2157191 prefixEnd_2157191 1107675846553174713991765 := by
  unfold tailWord_2157191
  simp only [CollatzResearch.WordTrace]
  refine ⟨78679219527872900736583427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52452813018581933824388951 78679219527872900736583427)
  ·
    refine ⟨118018829291809351104875141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78679219527872900736583427 118018829291809351104875141)
    ·
      refine ⟨22128530492214253332164089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118018829291809351104875141 22128530492214253332164089)
      ·
        refine ⟨16596397869160689999123067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22128530492214253332164089 16596397869160689999123067)
        ·
          refine ⟨24894596803741034998684601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16596397869160689999123067 24894596803741034998684601)
          ·
            refine ⟨18670947602805776249013451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24894596803741034998684601 18670947602805776249013451)
            ·
              refine ⟨28006421404208664373520177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18670947602805776249013451 28006421404208664373520177)
              ·
                refine ⟨21004816053156498280140133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28006421404208664373520177 21004816053156498280140133)
                ·
                  refine ⟨3938403009966843427526275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21004816053156498280140133 3938403009966843427526275)
                  ·
                    refine ⟨5907604514950265141289413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3938403009966843427526275 5907604514950265141289413)
                    ·
                      refine ⟨1107675846553174713991765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5907604514950265141289413 1107675846553174713991765)
                      ·
                        rfl

theorem cell23_2157191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_2157191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157191 prefixEnd_2157191 := by exact prefixLift 2157191
  have htrace : WordTrace (prefixWord ++ tailWord_2157191) baseStart_2157191 baseEnd_2157191 := by
    simpa [prefixWord, tailWord_2157191, baseEnd_2157191] using wordTrace_append hprefix tailTrace_2157191
  have hstable : (prefixWord ++ tailWord_2157191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157191).length < 2 ^ (prefixWord ++ tailWord_2157191).sum := by decide
  have hdescent : baseEnd_2157191 < baseStart_2157191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157208 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 2, 1, 4]
def baseStart_2157208 : Nat := 118140960795 + 2157208 * 2 ^ 59
def prefixEnd_2157208 : Nat := 4983230072969 + 3 ^ 40 * 2157208 * 2
def baseEnd_2157208 : Nat := 1107684575724301147479187

theorem tailTrace_2157208 : CollatzResearch.WordTrace tailWord_2157208 prefixEnd_2157208 1107684575724301147479187 := by
  unfold tailWord_2157208
  simp only [CollatzResearch.WordTrace]
  refine ⟨39339919784405656319976139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52453226379207541759968185 39339919784405656319976139)
  ·
    refine ⟨59009879676608484479964209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39339919784405656319976139 59009879676608484479964209)
    ·
      refine ⟨44257409757456363359973157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59009879676608484479964209 44257409757456363359973157)
      ·
        refine ⟨8298264329523068129994967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44257409757456363359973157 8298264329523068129994967)
        ·
          refine ⟨12447396494284602194992451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8298264329523068129994967 12447396494284602194992451)
          ·
            refine ⟨18671094741426903292488677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12447396494284602194992451 18671094741426903292488677)
            ·
              refine ⟨3500830264017544367341627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18671094741426903292488677 3500830264017544367341627)
              ·
                refine ⟨5251245396026316551012441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3500830264017544367341627 5251245396026316551012441)
                ·
                  refine ⟨3938434047019737413259331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5251245396026316551012441 3938434047019737413259331)
                  ·
                    refine ⟨5907651070529606119888997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3938434047019737413259331 5907651070529606119888997)
                    ·
                      refine ⟨1107684575724301147479187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5907651070529606119888997 1107684575724301147479187)
                      ·
                        rfl

theorem cell23_2157208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_2157208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157208 prefixEnd_2157208 := by exact prefixLift 2157208
  have htrace : WordTrace (prefixWord ++ tailWord_2157208) baseStart_2157208 baseEnd_2157208 := by
    simpa [prefixWord, tailWord_2157208, baseEnd_2157208] using wordTrace_append hprefix tailTrace_2157208
  have hstable : (prefixWord ++ tailWord_2157208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157208).length < 2 ^ (prefixWord ++ tailWord_2157208).sum := by decide
  have hdescent : baseEnd_2157208 < baseStart_2157208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157226 : List Nat := [3, 1, 5, 2, 2, 1, 2, 2, 5]
def baseStart_2157226 : Nat := 118140960795 + 2157226 * 2 ^ 59
def prefixEnd_2157226 : Nat := 4983230072969 + 3 ^ 40 * 2157226 * 2
def baseEnd_2157226 : Nat := 123077090930675786339345

theorem tailTrace_2157226 : CollatzResearch.WordTrace tailWord_2157226 prefixEnd_2157226 123077090930675786339345 := by
  unfold tailWord_2157226
  simp only [CollatzResearch.WordTrace]
  refine ⟨19670124020686525428526883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52453664055164067809405021 19670124020686525428526883)
  ·
    refine ⟨29505186031029788142790325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19670124020686525428526883 29505186031029788142790325)
    ·
      refine ⟨2766111190409042638386593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29505186031029788142790325 2766111190409042638386593)
      ·
        refine ⟨2074583392806781978789945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2766111190409042638386593 2074583392806781978789945)
        ·
          refine ⟨1555937544605086484092459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2074583392806781978789945 1555937544605086484092459)
          ·
            refine ⟨2333906316907629726138689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1555937544605086484092459 2333906316907629726138689)
            ·
              refine ⟨1750429737680722294604017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2333906316907629726138689 1750429737680722294604017)
              ·
                refine ⟨1312822303260541720953013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1750429737680722294604017 1312822303260541720953013)
                ·
                  refine ⟨123077090930675786339345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1312822303260541720953013 123077090930675786339345)
                  ·
                    rfl

theorem cell23_2157226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_2157226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157226 prefixEnd_2157226 := by exact prefixLift 2157226
  have htrace : WordTrace (prefixWord ++ tailWord_2157226) baseStart_2157226 baseEnd_2157226 := by
    simpa [prefixWord, tailWord_2157226, baseEnd_2157226] using wordTrace_append hprefix tailTrace_2157226
  have hstable : (prefixWord ++ tailWord_2157226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157226).length < 2 ^ (prefixWord ++ tailWord_2157226).sum := by decide
  have hdescent : baseEnd_2157226 < baseStart_2157226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157231 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 6]
def baseStart_2157231 : Nat := 118140960795 + 2157231 * 2 ^ 59
def prefixEnd_2157231 : Nat := 4983230072969 + 3 ^ 40 * 2157231 * 2
def baseEnd_2157231 : Nat := 123077376197706061943509

theorem tailTrace_2157231 : CollatzResearch.WordTrace tailWord_2157231 prefixEnd_2157231 123077376197706061943509 := by
  unfold tailWord_2157231
  simp only [CollatzResearch.WordTrace]
  refine ⟨78680678447727987568039547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52453785631818658378693031 78680678447727987568039547)
  ·
    refine ⟨118021017671591981352059321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78680678447727987568039547 118021017671591981352059321)
    ·
      refine ⟨88515763253693986014044491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118021017671591981352059321 88515763253693986014044491)
      ·
        refine ⟨132773644880540979021066737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88515763253693986014044491 132773644880540979021066737)
        ·
          refine ⟨99580233660405734265800053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132773644880540979021066737 99580233660405734265800053)
          ·
            refine ⟨9335646905663037587418755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99580233660405734265800053 9335646905663037587418755)
            ·
              refine ⟨14003470358494556381128133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9335646905663037587418755 14003470358494556381128133)
              ·
                refine ⟨2625650692217729321461525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14003470358494556381128133 2625650692217729321461525)
                ·
                  refine ⟨123077376197706061943509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2625650692217729321461525 123077376197706061943509)
                  ·
                    rfl

theorem cell23_2157231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 6].length) (baseStart_2157231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157231 prefixEnd_2157231 := by exact prefixLift 2157231
  have htrace : WordTrace (prefixWord ++ tailWord_2157231) baseStart_2157231 baseEnd_2157231 := by
    simpa [prefixWord, tailWord_2157231, baseEnd_2157231] using wordTrace_append hprefix tailTrace_2157231
  have hstable : (prefixWord ++ tailWord_2157231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157231).length < 2 ^ (prefixWord ++ tailWord_2157231).sum := by decide
  have hdescent : baseEnd_2157231 < baseStart_2157231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157235 : List Nat := [1, 1, 1, 2, 3, 5, 1, 4, 1, 4]
def baseStart_2157235 : Nat := 118140960795 + 2157235 * 2 ^ 59
def prefixEnd_2157235 : Nat := 4983230072969 + 3 ^ 40 * 2157235 * 2
def baseEnd_2157235 : Nat := 369232813233990847280521

theorem tailTrace_2157235 : CollatzResearch.WordTrace tailWord_2157235 prefixEnd_2157235 369232813233990847280521 := by
  unfold tailWord_2157235
  simp only [CollatzResearch.WordTrace]
  refine ⟨78680824339713496251185159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52453882893142330834123439 78680824339713496251185159)
  ·
    refine ⟨118021236509570244376777739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78680824339713496251185159 118021236509570244376777739)
    ·
      refine ⟨177031854764355366565166609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118021236509570244376777739 177031854764355366565166609)
      ·
        refine ⟨132773891073266524923874957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177031854764355366565166609 132773891073266524923874957)
        ·
          refine ⟨49790209152474946846453109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132773891073266524923874957 49790209152474946846453109)
          ·
            refine ⟨4667832108044526266854979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49790209152474946846453109 4667832108044526266854979)
            ·
              refine ⟨7001748162066789400282469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4667832108044526266854979 7001748162066789400282469)
              ·
                refine ⟨1312827780387523012552963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7001748162066789400282469 1312827780387523012552963)
                ·
                  refine ⟨1969241670581284518829445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1312827780387523012552963 1969241670581284518829445)
                  ·
                    refine ⟨369232813233990847280521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1969241670581284518829445 369232813233990847280521)
                    ·
                      rfl

theorem cell23_2157235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 4, 1, 4].length) (baseStart_2157235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157235 prefixEnd_2157235 := by exact prefixLift 2157235
  have htrace : WordTrace (prefixWord ++ tailWord_2157235) baseStart_2157235 baseEnd_2157235 := by
    simpa [prefixWord, tailWord_2157235, baseEnd_2157235] using wordTrace_append hprefix tailTrace_2157235
  have hstable : (prefixWord ++ tailWord_2157235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157235).length < 2 ^ (prefixWord ++ tailWord_2157235).sum := by decide
  have hdescent : baseEnd_2157235 < baseStart_2157235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157241 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 2, 5, 3]
def baseStart_2157241 : Nat := 118140960795 + 2157241 * 2 ^ 59
def prefixEnd_2157241 : Nat := 4983230072969 + 3 ^ 40 * 2157241 * 2
def baseEnd_2157241 : Nat := 1107701520585899518366535

theorem tailTrace_2157241 : CollatzResearch.WordTrace tailWord_2157241 prefixEnd_2157241 1107701520585899518366535 := by
  unfold tailWord_2157241
  simp only [CollatzResearch.WordTrace]
  refine ⟨78681043177691759275903577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52454028785127839517269051 78681043177691759275903577)
  ·
    refine ⟨59010782383268819456927683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78681043177691759275903577 59010782383268819456927683)
    ·
      refine ⟨88516173574903229185391525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59010782383268819456927683 88516173574903229185391525)
      ·
        refine ⟨16596782545294355472260911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88516173574903229185391525 16596782545294355472260911)
        ·
          refine ⟨24895173817941533208391367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16596782545294355472260911 24895173817941533208391367)
          ·
            refine ⟨37342760726912299812587051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24895173817941533208391367 37342760726912299812587051)
            ·
              refine ⟨56014141090368449718880577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37342760726912299812587051 56014141090368449718880577)
              ·
                refine ⟨42010605817776337289160433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56014141090368449718880577 42010605817776337289160433)
                ·
                  refine ⟨31507954363332252966870325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42010605817776337289160433 31507954363332252966870325)
                  ·
                    refine ⟨2953870721562398715644093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31507954363332252966870325 2953870721562398715644093)
                    ·
                      refine ⟨1107701520585899518366535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2953870721562398715644093 1107701520585899518366535)
                      ·
                        rfl

theorem cell23_2157241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_2157241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157241 prefixEnd_2157241 := by exact prefixLift 2157241
  have htrace : WordTrace (prefixWord ++ tailWord_2157241) baseStart_2157241 baseEnd_2157241 := by
    simpa [prefixWord, tailWord_2157241, baseEnd_2157241] using wordTrace_append hprefix tailTrace_2157241
  have hstable : (prefixWord ++ tailWord_2157241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157241).length < 2 ^ (prefixWord ++ tailWord_2157241).sum := by decide
  have hdescent : baseEnd_2157241 < baseStart_2157241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157269 : List Nat := [1, 3, 2, 5, 1, 1, 2, 3, 1, 4]
def baseStart_2157269 : Nat := 118140960795 + 2157269 * 2 ^ 59
def prefixEnd_2157269 : Nat := 4983230072969 + 3 ^ 40 * 2157269 * 2
def baseEnd_2157269 : Nat := 369238632681408469605469

theorem tailTrace_2157269 : CollatzResearch.WordTrace tailWord_2157269 prefixEnd_2157269 369238632681408469605469 := by
  unfold tailWord_2157269
  simp only [CollatzResearch.WordTrace]
  refine ⟨78682064421590320057922861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52454709614393546705281907 78682064421590320057922861)
  ·
    refine ⟨29505774158096370021721073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78682064421590320057922861 29505774158096370021721073)
    ·
      refine ⟨22129330618572277516290805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29505774158096370021721073 22129330618572277516290805)
      ·
        refine ⟨2074624745491151017152263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22129330618572277516290805 2074624745491151017152263)
        ·
          refine ⟨3111937118236726525728395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2074624745491151017152263 3111937118236726525728395)
          ·
            refine ⟨4667905677355089788592593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111937118236726525728395 4667905677355089788592593)
            ·
              refine ⟨3500929258016317341444445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4667905677355089788592593 3500929258016317341444445)
              ·
                refine ⟨1312848471756119003041667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3500929258016317341444445 1312848471756119003041667)
                ·
                  refine ⟨1969272707634178504562501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1312848471756119003041667 1969272707634178504562501)
                  ·
                    refine ⟨369238632681408469605469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1969272707634178504562501 369238632681408469605469)
                    ·
                      rfl

theorem cell23_2157269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_2157269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157269 prefixEnd_2157269 := by exact prefixLift 2157269
  have htrace : WordTrace (prefixWord ++ tailWord_2157269) baseStart_2157269 baseEnd_2157269 := by
    simpa [prefixWord, tailWord_2157269, baseEnd_2157269] using wordTrace_append hprefix tailTrace_2157269
  have hstable : (prefixWord ++ tailWord_2157269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157269).length < 2 ^ (prefixWord ++ tailWord_2157269).sum := by decide
  have hdescent : baseEnd_2157269 < baseStart_2157269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157308 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 1, 6]
def baseStart_2157308 : Nat := 118140960795 + 2157308 * 2 ^ 59
def prefixEnd_2157308 : Nat := 4983230072969 + 3 ^ 40 * 2157308 * 2
def baseEnd_2157308 : Nat := 369245307929916918742909

theorem tailTrace_2157308 : CollatzResearch.WordTrace tailWord_2157308 prefixEnd_2157308 369245307929916918742909 := by
  unfold tailWord_2157308
  simp only [CollatzResearch.WordTrace]
  refine ⟨39341743434224514859296289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52455657912299353145728385 39341743434224514859296289)
  ·
    refine ⟨29506307575668386144472217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39341743434224514859296289 29506307575668386144472217)
    ·
      refine ⟨22129730681751289608354163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29506307575668386144472217 22129730681751289608354163)
      ·
        refine ⟨33194596022626934412531245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22129730681751289608354163 33194596022626934412531245)
        ·
          refine ⟨12447973508485100404699217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33194596022626934412531245 12447973508485100404699217)
          ·
            refine ⟨9335980131363825303524413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12447973508485100404699217 9335980131363825303524413)
            ·
              refine ⟨3500992549261434488821655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9335980131363825303524413 3500992549261434488821655)
              ·
                refine ⟨5251488823892151733232483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3500992549261434488821655 5251488823892151733232483)
                ·
                  refine ⟨7877233235838227599848725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5251488823892151733232483 7877233235838227599848725)
                  ·
                    refine ⟨369245307929916918742909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7877233235838227599848725 369245307929916918742909)
                    ·
                      rfl

theorem cell23_2157308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_2157308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157308 prefixEnd_2157308 := by exact prefixLift 2157308
  have htrace : WordTrace (prefixWord ++ tailWord_2157308) baseStart_2157308 baseEnd_2157308 := by
    simpa [prefixWord, tailWord_2157308, baseEnd_2157308] using wordTrace_append hprefix tailTrace_2157308
  have hstable : (prefixWord ++ tailWord_2157308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157308).length < 2 ^ (prefixWord ++ tailWord_2157308).sum := by decide
  have hdescent : baseEnd_2157308 < baseStart_2157308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157335 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 5]
def baseStart_2157335 : Nat := 118140960795 + 2157335 * 2 ^ 59
def prefixEnd_2157335 : Nat := 4983230072969 + 3 ^ 40 * 2157335 * 2
def baseEnd_2157335 : Nat := 1107749787767422150591103

theorem tailTrace_2157335 : CollatzResearch.WordTrace tailWord_2157335 prefixEnd_2157335 1107749787767422150591103 := by
  unfold tailWord_2157335
  simp only [CollatzResearch.WordTrace]
  refine ⟨78684471639351213329825459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52456314426234142219883639 78684471639351213329825459)
  ·
    refine ⟨118026707459026819994738189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78684471639351213329825459 118026707459026819994738189)
    ·
      refine ⟨44260015297135057498026821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118026707459026819994738189 44260015297135057498026821)
      ·
        refine ⟨8298752868212823280880029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44260015297135057498026821 8298752868212823280880029)
        ·
          refine ⟨3112032325579808730330011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8298752868212823280880029 3112032325579808730330011)
          ·
            refine ⟨4668048488369713095495017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3112032325579808730330011 4668048488369713095495017)
            ·
              refine ⟨3501036366277284821621263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4668048488369713095495017 3501036366277284821621263)
              ·
                refine ⟨5251554549415927232431895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3501036366277284821621263 5251554549415927232431895)
                ·
                  refine ⟨7877331824123890848647843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5251554549415927232431895 7877331824123890848647843)
                  ·
                    refine ⟨11815997736185836272971765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7877331824123890848647843 11815997736185836272971765)
                    ·
                      refine ⟨1107749787767422150591103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11815997736185836272971765 1107749787767422150591103)
                      ·
                        rfl

theorem cell23_2157335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_2157335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157335 prefixEnd_2157335 := by exact prefixLift 2157335
  have htrace : WordTrace (prefixWord ++ tailWord_2157335) baseStart_2157335 baseEnd_2157335 := by
    simpa [prefixWord, tailWord_2157335, baseEnd_2157335] using wordTrace_append hprefix tailTrace_2157335
  have hstable : (prefixWord ++ tailWord_2157335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157335).length < 2 ^ (prefixWord ++ tailWord_2157335).sum := by decide
  have hdescent : baseEnd_2157335 < baseStart_2157335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157366 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_2157366 : Nat := 118140960795 + 2157366 * 2 ^ 59
def prefixEnd_2157366 : Nat := 4983230072969 + 3 ^ 40 * 2157366 * 2
def baseEnd_2157366 : Nat := 1107765705667711529303461

theorem tailTrace_2157366 : CollatzResearch.WordTrace tailWord_2157366 prefixEnd_2157366 1107765705667711529303461 := by
  unfold tailWord_2157366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4917850143889931601512747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52457068201492603749469301 4917850143889931601512747)
  ·
    refine ⟨7376775215834897402269121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4917850143889931601512747 7376775215834897402269121)
    ·
      refine ⟨5532581411876173051701841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7376775215834897402269121 5532581411876173051701841)
      ·
        refine ⟨4149436058907129788776381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5532581411876173051701841 4149436058907129788776381)
        ·
          refine ⟨1556038522090173670791143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4149436058907129788776381 1556038522090173670791143)
          ·
            refine ⟨2334057783135260506186715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1556038522090173670791143 2334057783135260506186715)
            ·
              refine ⟨3501086674702890759280073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2334057783135260506186715 3501086674702890759280073)
              ·
                refine ⟨2625815006027168069460055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3501086674702890759280073 2625815006027168069460055)
                ·
                  refine ⟨3938722509040752104190083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2625815006027168069460055 3938722509040752104190083)
                  ·
                    refine ⟨5908083763561128156285125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3938722509040752104190083 5908083763561128156285125)
                    ·
                      refine ⟨1107765705667711529303461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5908083763561128156285125 1107765705667711529303461)
                      ·
                        rfl

theorem cell23_2157366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_2157366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157366 prefixEnd_2157366 := by exact prefixLift 2157366
  have htrace : WordTrace (prefixWord ++ tailWord_2157366) baseStart_2157366 baseEnd_2157366 := by
    simpa [prefixWord, tailWord_2157366, baseEnd_2157366] using wordTrace_append hprefix tailTrace_2157366
  have hstable : (prefixWord ++ tailWord_2157366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157366).length < 2 ^ (prefixWord ++ tailWord_2157366).sum := by decide
  have hdescent : baseEnd_2157366 < baseStart_2157366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157381 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_2157381 : Nat := 118140960795 + 2157381 * 2 ^ 59
def prefixEnd_2157381 : Nat := 4983230072969 + 3 ^ 40 * 2157381 * 2
def baseEnd_2157381 : Nat := 369257802625842990205297

theorem tailTrace_2157381 : CollatzResearch.WordTrace tailWord_2157381 prefixEnd_2157381 369257802625842990205297 := by
  unfold tailWord_2157381
  simp only [CollatzResearch.WordTrace]
  refine ⟨78686149397184563185999997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52457432931456375457333331 78686149397184563185999997)
  ·
    refine ⟨29507306023944211194749999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78686149397184563185999997 29507306023944211194749999)
    ·
      refine ⟨44260959035916316792124999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29507306023944211194749999 44260959035916316792124999)
      ·
        refine ⟨66391438553874475188187499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44260959035916316792124999 66391438553874475188187499)
        ·
          refine ⟨99587157830811712782281249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66391438553874475188187499 99587157830811712782281249)
          ·
            refine ⟨74690368373108784586710937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99587157830811712782281249 74690368373108784586710937)
            ·
              refine ⟨56017776279831588440033203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74690368373108784586710937 56017776279831588440033203)
              ·
                refine ⟨84026664419747382660049805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56017776279831588440033203 84026664419747382660049805)
                ·
                  refine ⟨31509999157405268497518677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84026664419747382660049805 31509999157405268497518677)
                  ·
                    refine ⟨369257802625842990205297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 31509999157405268497518677 369257802625842990205297)
                    ·
                      rfl

theorem cell23_2157381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_2157381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157381 prefixEnd_2157381 := by exact prefixLift 2157381
  have htrace : WordTrace (prefixWord ++ tailWord_2157381) baseStart_2157381 baseEnd_2157381 := by
    simpa [prefixWord, tailWord_2157381, baseEnd_2157381] using wordTrace_append hprefix tailTrace_2157381
  have hstable : (prefixWord ++ tailWord_2157381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157381).length < 2 ^ (prefixWord ++ tailWord_2157381).sum := by decide
  have hdescent : baseEnd_2157381 < baseStart_2157381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157408 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 3]
def baseStart_2157408 : Nat := 118140960795 + 2157408 * 2 ^ 59
def prefixEnd_2157408 : Nat := 4983230072969 + 3 ^ 40 * 2157408 * 2
def baseEnd_2157408 : Nat := 1107787271855200364978267

theorem tailTrace_2157408 : CollatzResearch.WordTrace tailWord_2157408 prefixEnd_2157408 1107787271855200364978267 := by
  unfold tailWord_2157408
  simp only [CollatzResearch.WordTrace]
  refine ⟨39343567084043373398616439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52458089445391164531488585 39343567084043373398616439)
  ·
    refine ⟨59015350626065060097924659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39343567084043373398616439 59015350626065060097924659)
    ·
      refine ⟨88523025939097590146886989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59015350626065060097924659 88523025939097590146886989)
      ·
        refine ⟨33196134727161596305082621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88523025939097590146886989 33196134727161596305082621)
        ·
          refine ⟨12448550522685598614405983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33196134727161596305082621 12448550522685598614405983)
          ·
            refine ⟨18672825784028397921608975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12448550522685598614405983 18672825784028397921608975)
            ·
              refine ⟨28009238676042596882413463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18672825784028397921608975 28009238676042596882413463)
              ·
                refine ⟨42013858014063895323620195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28009238676042596882413463 42013858014063895323620195)
                ·
                  refine ⟨63020787021095842985430293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42013858014063895323620195 63020787021095842985430293)
                  ·
                    refine ⟨2954099391613867639942045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63020787021095842985430293 2954099391613867639942045)
                    ·
                      refine ⟨1107787271855200364978267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2954099391613867639942045 1107787271855200364978267)
                      ·
                        rfl

theorem cell23_2157408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_2157408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157408 prefixEnd_2157408 := by exact prefixLift 2157408
  have htrace : WordTrace (prefixWord ++ tailWord_2157408) baseStart_2157408 baseEnd_2157408 := by
    simpa [prefixWord, tailWord_2157408, baseEnd_2157408] using wordTrace_append hprefix tailTrace_2157408
  have hstable : (prefixWord ++ tailWord_2157408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157408).length < 2 ^ (prefixWord ++ tailWord_2157408).sum := by decide
  have hdescent : baseEnd_2157408 < baseStart_2157408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157445 : List Nat := [1, 3, 1, 1, 3, 3, 1, 5, 5]
def baseStart_2157445 : Nat := 118140960795 + 2157445 * 2 ^ 59
def prefixEnd_2157445 : Nat := 4983230072969 + 3 ^ 40 * 2157445 * 2
def baseEnd_2157445 : Nat := 123089585626601857801733

theorem tailTrace_2157445 : CollatzResearch.WordTrace tailWord_2157445 prefixEnd_2157445 123089585626601857801733 := by
  unfold tailWord_2157445
  simp only [CollatzResearch.WordTrace]
  refine ⟨78688483668952702116329789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52458989112635134744219859 78688483668952702116329789)
  ·
    refine ⟨29508181375857263293623671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78688483668952702116329789 29508181375857263293623671)
    ·
      refine ⟨44262272063785894940435507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29508181375857263293623671 44262272063785894940435507)
      ·
        refine ⟨66393408095678842410653261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44262272063785894940435507 66393408095678842410653261)
        ·
          refine ⟨24897528035879565903994973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66393408095678842410653261 24897528035879565903994973)
          ·
            refine ⟨9336573013454837213998115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24897528035879565903994973 9336573013454837213998115)
            ·
              refine ⟨14004859520182255820997173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9336573013454837213998115 14004859520182255820997173)
              ·
                refine ⟨1312955580017086483218485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14004859520182255820997173 1312955580017086483218485)
                ·
                  refine ⟨123089585626601857801733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1312955580017086483218485 123089585626601857801733)
                  ·
                    rfl

theorem cell23_2157445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_2157445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157445 prefixEnd_2157445 := by exact prefixLift 2157445
  have htrace : WordTrace (prefixWord ++ tailWord_2157445) baseStart_2157445 baseEnd_2157445 := by
    simpa [prefixWord, tailWord_2157445, baseEnd_2157445] using wordTrace_append hprefix tailTrace_2157445
  have hstable : (prefixWord ++ tailWord_2157445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157445).length < 2 ^ (prefixWord ++ tailWord_2157445).sum := by decide
  have hdescent : baseEnd_2157445 < baseStart_2157445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157492 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2157492 : Nat := 118140960795 + 2157492 * 2 ^ 59
def prefixEnd_2157492 : Nat := 4983230072969 + 3 ^ 40 * 2157492 * 2
def baseEnd_2157492 : Nat := 369276801410059345442627

theorem tailTrace_2157492 : CollatzResearch.WordTrace tailWord_2157492 prefixEnd_2157492 369276801410059345442627 := by
  unfold tailWord_2157492
  simp only [CollatzResearch.WordTrace]
  refine ⟨39345098949891214571645365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52460131933188286095527153 39345098949891214571645365)
  ·
    refine ⟨3688603026552301366091753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39345098949891214571645365 3688603026552301366091753)
    ·
      refine ⟨2766452269914226024568815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3688603026552301366091753 2766452269914226024568815)
      ·
        refine ⟨4149678404871339036853223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766452269914226024568815 4149678404871339036853223)
        ·
          refine ⟨6224517607307008555279835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4149678404871339036853223 6224517607307008555279835)
          ·
            refine ⟨9336776410960512832919753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6224517607307008555279835 9336776410960512832919753)
            ·
              refine ⟨7002582308220384624689815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9336776410960512832919753 7002582308220384624689815)
              ·
                refine ⟨10503873462330576937034723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7002582308220384624689815 10503873462330576937034723)
                ·
                  refine ⟨15755810193495865405552085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10503873462330576937034723 15755810193495865405552085)
                  ·
                    refine ⟨369276801410059345442627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15755810193495865405552085 369276801410059345442627)
                    ·
                      rfl

theorem cell23_2157492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2157492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157492 prefixEnd_2157492 := by exact prefixLift 2157492
  have htrace : WordTrace (prefixWord ++ tailWord_2157492) baseStart_2157492 baseEnd_2157492 := by
    simpa [prefixWord, tailWord_2157492, baseEnd_2157492] using wordTrace_append hprefix tailTrace_2157492
  have hstable : (prefixWord ++ tailWord_2157492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157492).length < 2 ^ (prefixWord ++ tailWord_2157492).sum := by decide
  have hdescent : baseEnd_2157492 < baseStart_2157492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157495 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 1, 6, 2]
def baseStart_2157495 : Nat := 118140960795 + 2157495 * 2 ^ 59
def prefixEnd_2157495 : Nat := 4983230072969 + 3 ^ 40 * 2157495 * 2
def baseEnd_2157495 : Nat := 1107831944672141524590367

theorem tailTrace_2157495 : CollatzResearch.WordTrace tailWord_2157495 prefixEnd_2157495 1107831944672141524590367 := by
  unfold tailWord_2157495
  simp only [CollatzResearch.WordTrace]
  refine ⟨78690307318771560655649939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52460204879181040437099959 78690307318771560655649939)
  ·
    refine ⟨118035460978157340983474909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78690307318771560655649939 118035460978157340983474909)
    ·
      refine ⟨44263297866809002868803091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118035460978157340983474909 44263297866809002868803091)
      ·
        refine ⟨66394946800213504303204637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44263297866809002868803091 66394946800213504303204637)
        ·
          refine ⟨24898105050080064113701739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66394946800213504303204637 24898105050080064113701739)
          ·
            refine ⟨37347157575120096170552609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24898105050080064113701739 37347157575120096170552609)
            ·
              refine ⟨28010368181340072127914457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37347157575120096170552609 28010368181340072127914457)
              ·
                refine ⟨21007776136005054095935843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28010368181340072127914457 21007776136005054095935843)
                ·
                  refine ⟨31511664204007581143903765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21007776136005054095935843 31511664204007581143903765)
                  ·
                    refine ⟨1477109259562855366120489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31511664204007581143903765 1477109259562855366120489)
                    ·
                      refine ⟨1107831944672141524590367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1477109259562855366120489 1107831944672141524590367)
                      ·
                        rfl

theorem cell23_2157495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 6, 2].length) (baseStart_2157495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157495 prefixEnd_2157495 := by exact prefixLift 2157495
  have htrace : WordTrace (prefixWord ++ tailWord_2157495) baseStart_2157495 baseEnd_2157495 := by
    simpa [prefixWord, tailWord_2157495, baseEnd_2157495] using wordTrace_append hprefix tailTrace_2157495
  have hstable : (prefixWord ++ tailWord_2157495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157495).length < 2 ^ (prefixWord ++ tailWord_2157495).sum := by decide
  have hdescent : baseEnd_2157495 < baseStart_2157495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157512 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_2157512 : Nat := 118140960795 + 2157512 * 2 ^ 59
def prefixEnd_2157512 : Nat := 4983230072969 + 3 ^ 40 * 2157512 * 2
def baseEnd_2157512 : Nat := 1107840673843267958077789

theorem tailTrace_2157512 : CollatzResearch.WordTrace tailWord_2157512 prefixEnd_2157512 1107840673843267958077789 := by
  unfold tailWord_2157512
  simp only [CollatzResearch.WordTrace]
  refine ⟨39345463679854986279509395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52460618239806648372679193 39345463679854986279509395)
  ·
    refine ⟨59018195519782479419264093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39345463679854986279509395 59018195519782479419264093)
    ·
      refine ⟨22131823319918429782224035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59018195519782479419264093 22131823319918429782224035)
      ·
        refine ⟨33197734979877644673336053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22131823319918429782224035 33197734979877644673336053)
        ·
          refine ⟨3112287654363529188125255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33197734979877644673336053 3112287654363529188125255)
          ·
            refine ⟨4668431481545293782187883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3112287654363529188125255 4668431481545293782187883)
            ·
              refine ⟨7002647222317940673281825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4668431481545293782187883 7002647222317940673281825)
              ·
                refine ⟨5251985416738455504961369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7002647222317940673281825 5251985416738455504961369)
                ·
                  refine ⟨3938989062553841628721027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5251985416738455504961369 3938989062553841628721027)
                  ·
                    refine ⟨5908483593830762443081541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3938989062553841628721027 5908483593830762443081541)
                    ·
                      refine ⟨1107840673843267958077789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5908483593830762443081541 1107840673843267958077789)
                      ·
                        rfl

theorem cell23_2157512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_2157512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157512 prefixEnd_2157512 := by exact prefixLift 2157512
  have htrace : WordTrace (prefixWord ++ tailWord_2157512) baseStart_2157512 baseEnd_2157512 := by
    simpa [prefixWord, tailWord_2157512, baseEnd_2157512] using wordTrace_append hprefix tailTrace_2157512
  have hstable : (prefixWord ++ tailWord_2157512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157512).length < 2 ^ (prefixWord ++ tailWord_2157512).sum := by decide
  have hdescent : baseEnd_2157512 < baseStart_2157512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157515 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 3]
def baseStart_2157515 : Nat := 118140960795 + 2157515 * 2 ^ 59
def prefixEnd_2157515 : Nat := 4983230072969 + 3 ^ 40 * 2157515 * 2
def baseEnd_2157515 : Nat := 1107842214285231446340275

theorem tailTrace_2157515 : CollatzResearch.WordTrace tailWord_2157515 prefixEnd_2157515 1107842214285231446340275 := by
  unfold tailWord_2157515
  simp only [CollatzResearch.WordTrace]
  refine ⟨78691036778699104071377999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52460691185799402714251999 78691036778699104071377999)
  ·
    refine ⟨118036555168048656107066999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78691036778699104071377999 118036555168048656107066999)
    ·
      refine ⟨177054832752072984160600499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118036555168048656107066999 177054832752072984160600499)
      ·
        refine ⟨265582249128109476240900749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177054832752072984160600499 265582249128109476240900749)
        ·
          refine ⟨99593343423041053590337781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265582249128109476240900749 99593343423041053590337781)
          ·
            refine ⟨9336875945910098774094167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99593343423041053590337781 9336875945910098774094167)
            ·
              refine ⟨14005313918865148161141251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9336875945910098774094167 14005313918865148161141251)
              ·
                refine ⟨21007970878297722241711877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14005313918865148161141251 21007970878297722241711877)
                ·
                  refine ⟨3938994539680822920320977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21007970878297722241711877 3938994539680822920320977)
                  ·
                    refine ⟨2954245904760617190240733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3938994539680822920320977 2954245904760617190240733)
                    ·
                      refine ⟨1107842214285231446340275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2954245904760617190240733 1107842214285231446340275)
                      ·
                        rfl

theorem cell23_2157515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 3].length) (baseStart_2157515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157515 prefixEnd_2157515 := by exact prefixLift 2157515
  have htrace : WordTrace (prefixWord ++ tailWord_2157515) baseStart_2157515 baseEnd_2157515 := by
    simpa [prefixWord, tailWord_2157515, baseEnd_2157515] using wordTrace_append hprefix tailTrace_2157515
  have hstable : (prefixWord ++ tailWord_2157515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157515).length < 2 ^ (prefixWord ++ tailWord_2157515).sum := by decide
  have hdescent : baseEnd_2157515 < baseStart_2157515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157602 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_2157602 : Nat := 118140960795 + 2157602 * 2 ^ 59
def prefixEnd_2157602 : Nat := 4983230072969 + 3 ^ 40 * 2157602 * 2
def baseEnd_2157602 : Nat := 1107886887102172605952375

theorem tailTrace_2157602 : CollatzResearch.WordTrace tailWord_2157602 prefixEnd_2157602 1107886887102172605952375 := by
  unfold tailWord_2157602
  simp only [CollatzResearch.WordTrace]
  refine ⟨19673552482345979482448765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52462806619589278619863373 19673552482345979482448765)
  ·
    refine ⟨7377582180879742305918287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19673552482345979482448765 7377582180879742305918287)
    ·
      refine ⟨11066373271319613458877431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7377582180879742305918287 11066373271319613458877431)
      ·
        refine ⟨16599559906979420188316147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11066373271319613458877431 16599559906979420188316147)
        ·
          refine ⟨24899339860469130282474221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16599559906979420188316147 24899339860469130282474221)
          ·
            refine ⟨9337252447675923855927833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24899339860469130282474221 9337252447675923855927833)
            ·
              refine ⟨7002939335756942891945875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9337252447675923855927833 7002939335756942891945875)
              ·
                refine ⟨10504409003635414337918813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7002939335756942891945875 10504409003635414337918813)
                ·
                  refine ⟨3939153376363280376719555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10504409003635414337918813 3939153376363280376719555)
                  ·
                    refine ⟨5908730064544920565079333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3939153376363280376719555 5908730064544920565079333)
                    ·
                      refine ⟨1107886887102172605952375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5908730064544920565079333 1107886887102172605952375)
                      ·
                        rfl

theorem cell23_2157602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_2157602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157602 prefixEnd_2157602 := by exact prefixLift 2157602
  have htrace : WordTrace (prefixWord ++ tailWord_2157602) baseStart_2157602 baseEnd_2157602 := by
    simpa [prefixWord, tailWord_2157602, baseEnd_2157602] using wordTrace_append hprefix tailTrace_2157602
  have hstable : (prefixWord ++ tailWord_2157602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157602).length < 2 ^ (prefixWord ++ tailWord_2157602).sum := by decide
  have hdescent : baseEnd_2157602 < baseStart_2157602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157625 : List Nat := [1, 2, 1, 5, 2, 2, 10]
def baseStart_2157625 : Nat := 118140960795 + 2157625 * 2 ^ 59
def prefixEnd_2157625 : Nat := 4983230072969 + 3 ^ 40 * 2157625 * 2
def baseEnd_2157625 : Nat := 13677761693299086616849

theorem tailTrace_2157625 : CollatzResearch.WordTrace tailWord_2157625 prefixEnd_2157625 13677761693299086616849 := by
  unfold tailWord_2157625
  simp only [CollatzResearch.WordTrace]
  refine ⟨78695048808300592857882329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52463365872200395238588219 78695048808300592857882329)
  ·
    refine ⟨59021286606225444643411747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78695048808300592857882329 59021286606225444643411747)
    ·
      refine ⟨88531929909338166965117621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59021286606225444643411747 88531929909338166965117621)
      ·
        refine ⟨8299868429000453152979777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88531929909338166965117621 8299868429000453152979777)
        ·
          refine ⟨6224901321750339864734833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8299868429000453152979777 6224901321750339864734833)
          ·
            refine ⟨4668675991312754898551125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6224901321750339864734833 4668675991312754898551125)
            ·
              refine ⟨13677761693299086616849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4668675991312754898551125 13677761693299086616849)
              ·
                rfl

theorem cell23_2157625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 10].length) (baseStart_2157625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157625 prefixEnd_2157625 := by exact prefixLift 2157625
  have htrace : WordTrace (prefixWord ++ tailWord_2157625) baseStart_2157625 baseEnd_2157625 := by
    simpa [prefixWord, tailWord_2157625, baseEnd_2157625] using wordTrace_append hprefix tailTrace_2157625
  have hstable : (prefixWord ++ tailWord_2157625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157625).length < 2 ^ (prefixWord ++ tailWord_2157625).sum := by decide
  have hdescent : baseEnd_2157625 < baseStart_2157625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157629 : List Nat := [1, 4, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_2157629 : Nat := 118140960795 + 2157629 * 2 ^ 59
def prefixEnd_2157629 : Nat := 4983230072969 + 3 ^ 40 * 2157629 * 2
def baseEnd_2157629 : Nat := 369300250359948000104917

theorem tailTrace_2157629 : CollatzResearch.WordTrace tailWord_2157629 prefixEnd_2157629 369300250359948000104917 := by
  unfold tailWord_2157629
  simp only [CollatzResearch.WordTrace]
  refine ⟨78695194700286101541027941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52463463133524067694018627 78695194700286101541027941)
  ·
    refine ⟨14755349006303644038942739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78695194700286101541027941 14755349006303644038942739)
    ·
      refine ⟨22133023509455466058414109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14755349006303644038942739 22133023509455466058414109)
      ·
        refine ⟨8299883816045799771905291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22133023509455466058414109 8299883816045799771905291)
        ·
          refine ⟨12449825724068699657857937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8299883816045799771905291 12449825724068699657857937)
          ·
            refine ⟨9337369293051524743393453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12449825724068699657857937 9337369293051524743393453)
            ·
              refine ⟨3501513484894321778772545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9337369293051524743393453 3501513484894321778772545)
              ·
                refine ⟨2626135113670741334079409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3501513484894321778772545 2626135113670741334079409)
                ·
                  refine ⟨1969601335253056000559557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2626135113670741334079409 1969601335253056000559557)
                  ·
                    refine ⟨369300250359948000104917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1969601335253056000559557 369300250359948000104917)
                    ·
                      rfl

theorem cell23_2157629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_2157629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157629 prefixEnd_2157629 := by exact prefixLift 2157629
  have htrace : WordTrace (prefixWord ++ tailWord_2157629) baseStart_2157629 baseEnd_2157629 := by
    simpa [prefixWord, tailWord_2157629, baseEnd_2157629] using wordTrace_append hprefix tailTrace_2157629
  have hstable : (prefixWord ++ tailWord_2157629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157629).length < 2 ^ (prefixWord ++ tailWord_2157629).sum := by decide
  have hdescent : baseEnd_2157629 < baseStart_2157629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157665 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_2157665 : Nat := 118140960795 + 2157665 * 2 ^ 59
def prefixEnd_2157665 : Nat := 4983230072969 + 3 ^ 40 * 2157665 * 2
def baseEnd_2157665 : Nat := 1107919236383405859464585

theorem tailTrace_2157665 : CollatzResearch.WordTrace tailWord_2157665 prefixEnd_2157665 1107919236383405859464585 := by
  unfold tailWord_2157665
  simp only [CollatzResearch.WordTrace]
  refine ⟨78696507728155679689338449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52464338485437119792892299 78696507728155679689338449)
  ·
    refine ⟨59022380796116759767003837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78696507728155679689338449 59022380796116759767003837)
    ·
      refine ⟨22133392798543784912626439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59022380796116759767003837 22133392798543784912626439)
      ·
        refine ⟨33200089197815677368939659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22133392798543784912626439 33200089197815677368939659)
        ·
          refine ⟨49800133796723516053409489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33200089197815677368939659 49800133796723516053409489)
          ·
            refine ⟨37350100347542637040057117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49800133796723516053409489 37350100347542637040057117)
            ·
              refine ⟨14006287630328488890021419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37350100347542637040057117 14006287630328488890021419)
              ·
                refine ⟨21009431445492733335032129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14006287630328488890021419 21009431445492733335032129)
                ·
                  refine ⟨15757073584119550001274097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21009431445492733335032129 15757073584119550001274097)
                  ·
                    refine ⟨11817805188089662500955573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15757073584119550001274097 11817805188089662500955573)
                    ·
                      refine ⟨1107919236383405859464585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11817805188089662500955573 1107919236383405859464585)
                      ·
                        rfl

theorem cell23_2157665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_2157665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157665 prefixEnd_2157665 := by exact prefixLift 2157665
  have htrace : WordTrace (prefixWord ++ tailWord_2157665) baseStart_2157665 baseEnd_2157665 := by
    simpa [prefixWord, tailWord_2157665, baseEnd_2157665] using wordTrace_append hprefix tailTrace_2157665
  have hstable : (prefixWord ++ tailWord_2157665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157665).length < 2 ^ (prefixWord ++ tailWord_2157665).sum := by decide
  have hdescent : baseEnd_2157665 < baseStart_2157665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157679 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 1, 3, 2]
def baseStart_2157679 : Nat := 118140960795 + 2157679 * 2 ^ 59
def prefixEnd_2157679 : Nat := 4983230072969 + 3 ^ 40 * 2157679 * 2
def baseEnd_2157679 : Nat := 1107926425112568804689521

theorem tailTrace_2157679 : CollatzResearch.WordTrace tailWord_2157679 prefixEnd_2157679 1107926425112568804689521 := by
  unfold tailWord_2157679
  simp only [CollatzResearch.WordTrace]
  refine ⟨78697018350104960080348091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52464678900069973386898727 78697018350104960080348091)
  ·
    refine ⟨118045527525157440120522137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78697018350104960080348091 118045527525157440120522137)
    ·
      refine ⟨88534145643868080090391603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118045527525157440120522137 88534145643868080090391603)
      ·
        refine ⟨132801218465802120135587405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88534145643868080090391603 132801218465802120135587405)
        ·
          refine ⟨49800456924675795050845277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132801218465802120135587405 49800456924675795050845277)
          ·
            refine ⟨18675171346753423144066979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49800456924675795050845277 18675171346753423144066979)
            ·
              refine ⟨28012757020130134716100469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18675171346753423144066979 28012757020130134716100469)
              ·
                refine ⟨2626195970637200129634419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28012757020130134716100469 2626195970637200129634419)
                ·
                  refine ⟨3939293955955800194451629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626195970637200129634419 3939293955955800194451629)
                  ·
                    refine ⟨1477235233483425072919361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3939293955955800194451629 1477235233483425072919361)
                    ·
                      refine ⟨1107926425112568804689521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1477235233483425072919361 1107926425112568804689521)
                      ·
                        rfl

theorem cell23_2157679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 3, 2].length) (baseStart_2157679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157679 prefixEnd_2157679 := by exact prefixLift 2157679
  have htrace : WordTrace (prefixWord ++ tailWord_2157679) baseStart_2157679 baseEnd_2157679 := by
    simpa [prefixWord, tailWord_2157679, baseEnd_2157679] using wordTrace_append hprefix tailTrace_2157679
  have hstable : (prefixWord ++ tailWord_2157679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157679).length < 2 ^ (prefixWord ++ tailWord_2157679).sum := by decide
  have hdescent : baseEnd_2157679 < baseStart_2157679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157686 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2157686 : Nat := 118140960795 + 2157686 * 2 ^ 59
def prefixEnd_2157686 : Nat := 4983230072969 + 3 ^ 40 * 2157686 * 2
def baseEnd_2157686 : Nat := 1107930019477150277301989

theorem tailTrace_2157686 : CollatzResearch.WordTrace tailWord_2157686 prefixEnd_2157686 1107930019477150277301989 := by
  unfold tailWord_2157686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4918579603817475017240807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52464849107386400183901941 4918579603817475017240807)
  ·
    refine ⟨7377869405726212525861211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4918579603817475017240807 7377869405726212525861211)
    ·
      refine ⟨11066804108589318788791817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7377869405726212525861211 11066804108589318788791817)
      ·
        refine ⟨8300103081441989091593863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11066804108589318788791817 8300103081441989091593863)
        ·
          refine ⟨12450154622162983637390795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8300103081441989091593863 12450154622162983637390795)
          ·
            refine ⟨18675231933244475456086193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12450154622162983637390795 18675231933244475456086193)
            ·
              refine ⟨14006423949933356592064645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18675231933244475456086193 14006423949933356592064645)
              ·
                refine ⟨2626204490612504361012121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14006423949933356592064645 2626204490612504361012121)
                ·
                  refine ⟨1969653367959378270759091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2626204490612504361012121 1969653367959378270759091)
                  ·
                    refine ⟨2954480051939067406138637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1969653367959378270759091 2954480051939067406138637)
                    ·
                      refine ⟨1107930019477150277301989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2954480051939067406138637 1107930019477150277301989)
                      ·
                        rfl

theorem cell23_2157686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2157686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157686 prefixEnd_2157686 := by exact prefixLift 2157686
  have htrace : WordTrace (prefixWord ++ tailWord_2157686) baseStart_2157686 baseEnd_2157686 := by
    simpa [prefixWord, tailWord_2157686, baseEnd_2157686] using wordTrace_append hprefix tailTrace_2157686
  have hstable : (prefixWord ++ tailWord_2157686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157686).length < 2 ^ (prefixWord ++ tailWord_2157686).sum := by decide
  have hdescent : baseEnd_2157686 < baseStart_2157686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157715 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 7]
def baseStart_2157715 : Nat := 118140960795 + 2157715 * 2 ^ 59
def prefixEnd_2157715 : Nat := 4983230072969 + 3 ^ 40 * 2157715 * 2
def baseEnd_2157715 : Nat := 123104990046236740426595

theorem tailTrace_2157715 : CollatzResearch.WordTrace tailWord_2157715 prefixEnd_2157715 123104990046236740426595 := by
  unfold tailWord_2157715
  simp only [CollatzResearch.WordTrace]
  refine ⟨78698331377974538228658599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52465554251983025485772399 78698331377974538228658599)
  ·
    refine ⟨118047497066961807342987899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78698331377974538228658599 118047497066961807342987899)
    ·
      refine ⟨177071245600442711014481849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118047497066961807342987899 177071245600442711014481849)
      ·
        refine ⟨132803434200332033260861387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177071245600442711014481849 132803434200332033260861387)
        ·
          refine ⟨199205151300498049891292081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132803434200332033260861387 199205151300498049891292081)
          ·
            refine ⟨149403863475373537418469061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199205151300498049891292081 149403863475373537418469061)
            ·
              refine ⟨28013224401632538265962949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149403863475373537418469061 28013224401632538265962949)
              ·
                refine ⟨5252479575306100924868053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28013224401632538265962949 5252479575306100924868053)
                ·
                  refine ⟨123104990046236740426595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5252479575306100924868053 123104990046236740426595)
                  ·
                    rfl

theorem cell23_2157715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 7].length) (baseStart_2157715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157715 prefixEnd_2157715 := by exact prefixLift 2157715
  have htrace : WordTrace (prefixWord ++ tailWord_2157715) baseStart_2157715 baseEnd_2157715 := by
    simpa [prefixWord, tailWord_2157715, baseEnd_2157715] using wordTrace_append hprefix tailTrace_2157715
  have hstable : (prefixWord ++ tailWord_2157715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157715).length < 2 ^ (prefixWord ++ tailWord_2157715).sum := by decide
  have hdescent : baseEnd_2157715 < baseStart_2157715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157726 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_2157726 : Nat := 118140960795 + 2157726 * 2 ^ 59
def prefixEnd_2157726 : Nat := 4983230072969 + 3 ^ 40 * 2157726 * 2
def baseEnd_2157726 : Nat := 1107950558703330120801805

theorem tailTrace_2157726 : CollatzResearch.WordTrace tailWord_2157726 prefixEnd_2157726 1107950558703330120801805 := by
  unfold tailWord_2157726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9837341572616835888413629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52465821720623124738206021 9837341572616835888413629)
  ·
    refine ⟨3689003089731313458155111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9837341572616835888413629 3689003089731313458155111)
    ·
      refine ⟨5533504634596970187232667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3689003089731313458155111 5533504634596970187232667)
      ·
        refine ⟨8300256951895455280849001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5533504634596970187232667 8300256951895455280849001)
        ·
          refine ⟨6225192713921591460636751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8300256951895455280849001 6225192713921591460636751)
          ·
            refine ⟨9337789070882387190955127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6225192713921591460636751 9337789070882387190955127)
            ·
              refine ⟨14006683606323580786432691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9337789070882387190955127 14006683606323580786432691)
              ·
                refine ⟨21010025409485371179649037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14006683606323580786432691 21010025409485371179649037)
                ·
                  refine ⟨7878759528557014192368389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21010025409485371179649037 7878759528557014192368389)
                  ·
                    refine ⟨1477267411604440161069073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7878759528557014192368389 1477267411604440161069073)
                    ·
                      refine ⟨1107950558703330120801805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1477267411604440161069073 1107950558703330120801805)
                      ·
                        rfl

theorem cell23_2157726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_2157726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157726 prefixEnd_2157726 := by exact prefixLift 2157726
  have htrace : WordTrace (prefixWord ++ tailWord_2157726) baseStart_2157726 baseEnd_2157726 := by
    simpa [prefixWord, tailWord_2157726, baseEnd_2157726] using wordTrace_append hprefix tailTrace_2157726
  have hstable : (prefixWord ++ tailWord_2157726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157726).length < 2 ^ (prefixWord ++ tailWord_2157726).sum := by decide
  have hdescent : baseEnd_2157726 < baseStart_2157726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157730 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_2157730 : Nat := 118140960795 + 2157730 * 2 ^ 59
def prefixEnd_2157730 : Nat := 4983230072969 + 3 ^ 40 * 2157730 * 2
def baseEnd_2157730 : Nat := 1107952612625948105151787

theorem tailTrace_2157730 : CollatzResearch.WordTrace tailWord_2157730 prefixEnd_2157730 1107952612625948105151787 := by
  unfold tailWord_2157730
  simp only [CollatzResearch.WordTrace]
  refine ⟨19674719618230048947613661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52465918981946797193636429 19674719618230048947613661)
  ·
    refine ⟨7378019856836268355355123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19674719618230048947613661 7378019856836268355355123)
    ·
      refine ⟨11067029785254402533032685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7378019856836268355355123 11067029785254402533032685)
      ·
        refine ⟨4150136169470400949887257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11067029785254402533032685 4150136169470400949887257)
        ·
          refine ⟨3112602127102800712415443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4150136169470400949887257 3112602127102800712415443)
          ·
            refine ⟨4668903190654201068623165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3112602127102800712415443 4668903190654201068623165)
            ·
              refine ⟨1750838696495325400733687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4668903190654201068623165 1750838696495325400733687)
              ·
                refine ⟨2626258044742988101100531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1750838696495325400733687 2626258044742988101100531)
                ·
                  refine ⟨3939387067114482151650797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626258044742988101100531 3939387067114482151650797)
                  ·
                    refine ⟨1477270150167930806869049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3939387067114482151650797 1477270150167930806869049)
                    ·
                      refine ⟨1107952612625948105151787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1477270150167930806869049 1107952612625948105151787)
                      ·
                        rfl

theorem cell23_2157730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_2157730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157730 prefixEnd_2157730 := by exact prefixLift 2157730
  have htrace : WordTrace (prefixWord ++ tailWord_2157730) baseStart_2157730 baseEnd_2157730 := by
    simpa [prefixWord, tailWord_2157730, baseEnd_2157730] using wordTrace_append hprefix tailTrace_2157730
  have hstable : (prefixWord ++ tailWord_2157730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157730).length < 2 ^ (prefixWord ++ tailWord_2157730).sum := by decide
  have hdescent : baseEnd_2157730 < baseStart_2157730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157755 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 7]
def baseStart_2157755 : Nat := 118140960795 + 2157755 * 2 ^ 59
def prefixEnd_2157755 : Nat := 4983230072969 + 3 ^ 40 * 2157755 * 2
def baseEnd_2157755 : Nat := 1107965449642310507339171

theorem tailTrace_2157755 : CollatzResearch.WordTrace tailWord_2157755 prefixEnd_2157755 1107965449642310507339171 := by
  unfold tailWord_2157755
  simp only [CollatzResearch.WordTrace]
  refine ⟨78699790297829625060114719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52466526865219750040076479 78699790297829625060114719)
  ·
    refine ⟨118049685446744437590172079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78699790297829625060114719 118049685446744437590172079)
    ·
      refine ⟨177074528170116656385258119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118049685446744437590172079 177074528170116656385258119)
      ·
        refine ⟨265611792255174984577887179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177074528170116656385258119 265611792255174984577887179)
        ·
          refine ⟨398417688382762476866830769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265611792255174984577887179 398417688382762476866830769)
          ·
            refine ⟨298813266287071857650123077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398417688382762476866830769 298813266287071857650123077)
            ·
              refine ⟨56027487428825973309398077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 298813266287071857650123077 56027487428825973309398077)
              ·
                refine ⟨21010307785809739991024279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56027487428825973309398077 21010307785809739991024279)
                ·
                  refine ⟨31515461678714609986536419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21010307785809739991024279 31515461678714609986536419)
                  ·
                    refine ⟨47273192518071914979804629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31515461678714609986536419 47273192518071914979804629)
                    ·
                      refine ⟨1107965449642310507339171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 47273192518071914979804629 1107965449642310507339171)
                      ·
                        rfl

theorem cell23_2157755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 7].length) (baseStart_2157755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157755 prefixEnd_2157755 := by exact prefixLift 2157755
  have htrace : WordTrace (prefixWord ++ tailWord_2157755) baseStart_2157755 baseEnd_2157755 := by
    simpa [prefixWord, tailWord_2157755, baseEnd_2157755] using wordTrace_append hprefix tailTrace_2157755
  have hstable : (prefixWord ++ tailWord_2157755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157755).length < 2 ^ (prefixWord ++ tailWord_2157755).sum := by decide
  have hdescent : baseEnd_2157755 < baseStart_2157755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157775 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 1, 10]
def baseStart_2157775 : Nat := 118140960795 + 2157775 * 2 ^ 59
def prefixEnd_2157775 : Nat := 4983230072969 + 3 ^ 40 * 2157775 * 2
def baseEnd_2157775 : Nat := 369325239751800143029693

theorem tailTrace_2157775 : CollatzResearch.WordTrace tailWord_2157775 prefixEnd_2157775 369325239751800143029693 := by
  unfold tailWord_2157775
  simp only [CollatzResearch.WordTrace]
  refine ⟨78700519757757168475842779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52467013171838112317228519 78700519757757168475842779)
  ·
    refine ⟨118050779636635752713764169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78700519757757168475842779 118050779636635752713764169)
    ·
      refine ⟨88538084727476814535323127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118050779636635752713764169 88538084727476814535323127)
      ·
        refine ⟨132807127091215221802984691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88538084727476814535323127 132807127091215221802984691)
        ·
          refine ⟨199210690636822832704477037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132807127091215221802984691 199210690636822832704477037)
          ·
            refine ⟨74704008988808562264178889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199210690636822832704477037 74704008988808562264178889)
            ·
              refine ⟨56028006741606421698134167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74704008988808562264178889 56028006741606421698134167)
              ·
                refine ⟨84042010112409632547201251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56028006741606421698134167 84042010112409632547201251)
                ·
                  refine ⟨126063015168614448820801877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84042010112409632547201251 126063015168614448820801877)
                  ·
                    refine ⟨369325239751800143029693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 126063015168614448820801877 369325239751800143029693)
                    ·
                      rfl

theorem cell23_2157775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 10].length) (baseStart_2157775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157775 prefixEnd_2157775 := by exact prefixLift 2157775
  have htrace : WordTrace (prefixWord ++ tailWord_2157775) baseStart_2157775 baseEnd_2157775 := by
    simpa [prefixWord, tailWord_2157775, baseEnd_2157775] using wordTrace_append hprefix tailTrace_2157775
  have hstable : (prefixWord ++ tailWord_2157775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157775).length < 2 ^ (prefixWord ++ tailWord_2157775).sum := by decide
  have hdescent : baseEnd_2157775 < baseStart_2157775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157956 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_2157956 : Nat := 118140960795 + 2157956 * 2 ^ 59
def prefixEnd_2157956 : Nat := 4983230072969 + 3 ^ 40 * 2157956 * 2
def baseEnd_2157956 : Nat := 1108068659253864220925747

theorem tailTrace_2157956 : CollatzResearch.WordTrace tailWord_2157956 prefixEnd_2157956 1108068659253864220925747 := by
  unfold tailWord_2157956
  simp only [CollatzResearch.WordTrace]
  refine ⟨39353560685050718194090861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52471414246734290925454481 39353560685050718194090861)
  ·
    refine ⟨14757585256894019322784073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39353560685050718194090861 14757585256894019322784073)
    ·
      refine ⟨11068188942670514492088055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14757585256894019322784073 11068188942670514492088055)
      ·
        refine ⟨16602283414005771738132083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11068188942670514492088055 16602283414005771738132083)
        ·
          refine ⟨24903425121008657607198125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16602283414005771738132083 24903425121008657607198125)
          ·
            refine ⟨9338784420378246602699297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24903425121008657607198125 9338784420378246602699297)
            ·
              refine ⟨7004088315283684952024473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9338784420378246602699297 7004088315283684952024473)
              ·
                refine ⟨5253066236462763714018355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7004088315283684952024473 5253066236462763714018355)
                ·
                  refine ⟨7879599354694145571027533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5253066236462763714018355 7879599354694145571027533)
                  ·
                    refine ⟨2954849758010304589135325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7879599354694145571027533 2954849758010304589135325)
                    ·
                      refine ⟨1108068659253864220925747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2954849758010304589135325 1108068659253864220925747)
                      ·
                        rfl

theorem cell23_2157956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_2157956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157956 prefixEnd_2157956 := by exact prefixLift 2157956
  have htrace : WordTrace (prefixWord ++ tailWord_2157956) baseStart_2157956 baseEnd_2157956 := by
    simpa [prefixWord, tailWord_2157956, baseEnd_2157956] using wordTrace_append hprefix tailTrace_2157956
  have hstable : (prefixWord ++ tailWord_2157956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157956).length < 2 ^ (prefixWord ++ tailWord_2157956).sum := by decide
  have hdescent : baseEnd_2157956 < baseStart_2157956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157960 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 1, 2, 3]
def baseStart_2157960 : Nat := 118140960795 + 2157960 * 2 ^ 59
def prefixEnd_2157960 : Nat := 4983230072969 + 3 ^ 40 * 2157960 * 2
def baseEnd_2157960 : Nat := 1108070713176482205275729

theorem tailTrace_2157960 : CollatzResearch.WordTrace tailWord_2157960 prefixEnd_2157960 1108070713176482205275729 := by
  unfold tailWord_2157960
  simp only [CollatzResearch.WordTrace]
  refine ⟨39353633631043472535663667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52471511508057963380884889 39353633631043472535663667)
  ·
    refine ⟨59030450446565208803495501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39353633631043472535663667 59030450446565208803495501)
    ·
      refine ⟨22136418917461953301310813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59030450446565208803495501 22136418917461953301310813)
      ·
        refine ⟨8301157094048232487991555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22136418917461953301310813 8301157094048232487991555)
        ·
          refine ⟨12451735641072348731987333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8301157094048232487991555 12451735641072348731987333)
          ·
            refine ⟨2334700432701065387247625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12451735641072348731987333 2334700432701065387247625)
            ·
              refine ⟨1751025324525799040435719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2334700432701065387247625 1751025324525799040435719)
              ·
                refine ⟨2626537986788698560653579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1751025324525799040435719 2626537986788698560653579)
                ·
                  refine ⟨3939806980183047840980369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626537986788698560653579 3939806980183047840980369)
                  ·
                    refine ⟨2954855235137285880735277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3939806980183047840980369 2954855235137285880735277)
                    ·
                      refine ⟨1108070713176482205275729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2954855235137285880735277 1108070713176482205275729)
                      ·
                        rfl

theorem cell23_2157960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_2157960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157960 prefixEnd_2157960 := by exact prefixLift 2157960
  have htrace : WordTrace (prefixWord ++ tailWord_2157960) baseStart_2157960 baseEnd_2157960 := by
    simpa [prefixWord, tailWord_2157960, baseEnd_2157960] using wordTrace_append hprefix tailTrace_2157960
  have hstable : (prefixWord ++ tailWord_2157960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157960).length < 2 ^ (prefixWord ++ tailWord_2157960).sum := by decide
  have hdescent : baseEnd_2157960 < baseStart_2157960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157973 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 2, 1, 3]
def baseStart_2157973 : Nat := 118140960795 + 2157973 * 2 ^ 59
def prefixEnd_2157973 : Nat := 4983230072969 + 3 ^ 40 * 2157973 * 2
def baseEnd_2157973 : Nat := 1108077388424990654413169

theorem tailTrace_2157973 : CollatzResearch.WordTrace tailWord_2157973 prefixEnd_2157973 1108077388424990654413169 := by
  unfold tailWord_2157973
  simp only [CollatzResearch.WordTrace]
  refine ⟨78707741411039848291550573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52471827607359898861033715 78707741411039848291550573)
  ·
    refine ⟨29515403029139943109331465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78707741411039848291550573 29515403029139943109331465)
    ·
      refine ⟨22136552271854957331998599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29515403029139943109331465 22136552271854957331998599)
      ·
        refine ⟨33204828407782435997997899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22136552271854957331998599 33204828407782435997997899)
        ·
          refine ⟨49807242611673653996996849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33204828407782435997997899 49807242611673653996996849)
          ·
            refine ⟨37355431958755240497747637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49807242611673653996996849 37355431958755240497747637)
            ·
              refine ⟨3502071746133303796663841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37355431958755240497747637 3502071746133303796663841)
              ·
                refine ⟨2626553809599977847497881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3502071746133303796663841 2626553809599977847497881)
                ·
                  refine ⟨1969915357199983385623411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2626553809599977847497881 1969915357199983385623411)
                  ·
                    refine ⟨2954873035799975078435117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1969915357199983385623411 2954873035799975078435117)
                    ·
                      refine ⟨1108077388424990654413169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2954873035799975078435117 1108077388424990654413169)
                      ·
                        rfl

theorem cell23_2157973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_2157973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157973 prefixEnd_2157973 := by exact prefixLift 2157973
  have htrace : WordTrace (prefixWord ++ tailWord_2157973) baseStart_2157973 baseEnd_2157973 := by
    simpa [prefixWord, tailWord_2157973, baseEnd_2157973] using wordTrace_append hprefix tailTrace_2157973
  have hstable : (prefixWord ++ tailWord_2157973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157973).length < 2 ^ (prefixWord ++ tailWord_2157973).sum := by decide
  have hdescent : baseEnd_2157973 < baseStart_2157973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2157999 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 3]
def baseStart_2157999 : Nat := 118140960795 + 2157999 * 2 ^ 59
def prefixEnd_2157999 : Nat := 4983230072969 + 3 ^ 40 * 2157999 * 2
def baseEnd_2157999 : Nat := 1108090738922007552688049

theorem tailTrace_2157999 : CollatzResearch.WordTrace tailWord_2157999 prefixEnd_2157999 1108090738922007552688049 := by
  unfold tailWord_2157999
  simp only [CollatzResearch.WordTrace]
  refine ⟨78708689708945654731997051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52472459805963769821331367 78708689708945654731997051)
  ·
    refine ⟨118063034563418482097995577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78708689708945654731997051 118063034563418482097995577)
    ·
      refine ⟨88547275922563861573496683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118063034563418482097995577 88547275922563861573496683)
      ·
        refine ⟨132820913883845792360245025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88547275922563861573496683 132820913883845792360245025)
        ·
          refine ⟨99615685412884344270183769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132820913883845792360245025 99615685412884344270183769)
          ·
            refine ⟨74711764059663258202637827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99615685412884344270183769 74711764059663258202637827)
            ·
              refine ⟨112067646089494887303956741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74711764059663258202637827 112067646089494887303956741)
              ·
                refine ⟨21012683641780291369491889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112067646089494887303956741 21012683641780291369491889)
                ·
                  refine ⟨15759512731335218527118917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21012683641780291369491889 15759512731335218527118917)
                  ·
                    refine ⟨2954908637125353473834797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15759512731335218527118917 2954908637125353473834797)
                    ·
                      refine ⟨1108090738922007552688049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2954908637125353473834797 1108090738922007552688049)
                      ·
                        rfl

theorem cell23_2157999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 4, 3].length) (baseStart_2157999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2157999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2157999 prefixEnd_2157999 := by exact prefixLift 2157999
  have htrace : WordTrace (prefixWord ++ tailWord_2157999) baseStart_2157999 baseEnd_2157999 := by
    simpa [prefixWord, tailWord_2157999, baseEnd_2157999] using wordTrace_append hprefix tailTrace_2157999
  have hstable : (prefixWord ++ tailWord_2157999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2157999).length < 2 ^ (prefixWord ++ tailWord_2157999).sum := by decide
  have hdescent : baseEnd_2157999 < baseStart_2157999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2157999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158013 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 6, 2, 2]
def baseStart_2158013 : Nat := 118140960795 + 2158013 * 2 ^ 59
def prefixEnd_2158013 : Nat := 4983230072969 + 3 ^ 40 * 2158013 * 2
def baseEnd_2158013 : Nat := 1108097927651170497912985

theorem tailTrace_2158013 : CollatzResearch.WordTrace tailWord_2158013 prefixEnd_2158013 1108097927651170497912985 := by
  unfold tailWord_2158013
  simp only [CollatzResearch.WordTrace]
  refine ⟨78709200330894935123006693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52472800220596623415337795 78709200330894935123006693)
  ·
    refine ⟨14757975062042800335563755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78709200330894935123006693 14757975062042800335563755)
    ·
      refine ⟨22136962593064200503345633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14757975062042800335563755 22136962593064200503345633)
      ·
        refine ⟨16602721944798150377509225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22136962593064200503345633 16602721944798150377509225)
        ·
          refine ⟨12452041458598612783131919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16602721944798150377509225 12452041458598612783131919)
          ·
            refine ⟨18678062187897919174697879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12452041458598612783131919 18678062187897919174697879)
            ·
              refine ⟨28017093281846878762046819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18678062187897919174697879 28017093281846878762046819)
              ·
                refine ⟨42025639922770318143070229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28017093281846878762046819 42025639922770318143070229)
                ·
                  refine ⟨1969951871379858662956417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42025639922770318143070229 1969951871379858662956417)
                  ·
                    refine ⟨1477463903534893997217313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1969951871379858662956417 1477463903534893997217313)
                    ·
                      refine ⟨1108097927651170497912985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1477463903534893997217313 1108097927651170497912985)
                      ·
                        rfl

theorem cell23_2158013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_2158013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158013 prefixEnd_2158013 := by exact prefixLift 2158013
  have htrace : WordTrace (prefixWord ++ tailWord_2158013) baseStart_2158013 baseEnd_2158013 := by
    simpa [prefixWord, tailWord_2158013, baseEnd_2158013] using wordTrace_append hprefix tailTrace_2158013
  have hstable : (prefixWord ++ tailWord_2158013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158013).length < 2 ^ (prefixWord ++ tailWord_2158013).sum := by decide
  have hdescent : baseEnd_2158013 < baseStart_2158013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158089 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 5]
def baseStart_2158089 : Nat := 118140960795 + 2158089 * 2 ^ 59
def prefixEnd_2158089 : Nat := 4983230072969 + 3 ^ 40 * 2158089 * 2
def baseEnd_2158089 : Nat := 1108136952180912200562635

theorem tailTrace_2158089 : CollatzResearch.WordTrace tailWord_2158089 prefixEnd_2158089 1108136952180912200562635 := by
  unfold tailWord_2158089
  simp only [CollatzResearch.WordTrace]
  refine ⟨78711972278619600102773321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52474648185746400068515547 78711972278619600102773321)
  ·
    refine ⟨59033979208964700077079991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78711972278619600102773321 59033979208964700077079991)
    ·
      refine ⟨88550968813447050115619987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59033979208964700077079991 88550968813447050115619987)
      ·
        refine ⟨132826453220170575173429981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88550968813447050115619987 132826453220170575173429981)
        ·
          refine ⟨49809919957563965690036243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132826453220170575173429981 49809919957563965690036243)
          ·
            refine ⟨74714879936345948535054365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49809919957563965690036243 74714879936345948535054365)
            ·
              refine ⟨28018079976129730700645387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74714879936345948535054365 28018079976129730700645387)
              ·
                refine ⟨42027119964194596050968081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28018079976129730700645387 42027119964194596050968081)
                ·
                  refine ⟨31520339973145947038226061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42027119964194596050968081 31520339973145947038226061)
                  ·
                    refine ⟨11820127489929730139334773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31520339973145947038226061 11820127489929730139334773)
                    ·
                      refine ⟨1108136952180912200562635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11820127489929730139334773 1108136952180912200562635)
                      ·
                        rfl

theorem cell23_2158089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_2158089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158089 prefixEnd_2158089 := by exact prefixLift 2158089
  have htrace : WordTrace (prefixWord ++ tailWord_2158089) baseStart_2158089 baseEnd_2158089 := by
    simpa [prefixWord, tailWord_2158089, baseEnd_2158089] using wordTrace_append hprefix tailTrace_2158089
  have hstable : (prefixWord ++ tailWord_2158089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158089).length < 2 ^ (prefixWord ++ tailWord_2158089).sum := by decide
  have hdescent : baseEnd_2158089 < baseStart_2158089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158106 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3]
def baseStart_2158106 : Nat := 118140960795 + 2158106 * 2 ^ 59
def prefixEnd_2158106 : Nat := 4983230072969 + 3 ^ 40 * 2158106 * 2
def baseEnd_2158106 : Nat := 1108145681352038634050057

theorem tailTrace_2158106 : CollatzResearch.WordTrace tailWord_2158106 prefixEnd_2158106 1108145681352038634050057 := by
  unfold tailWord_2158106
  simp only [CollatzResearch.WordTrace]
  refine ⟨19678148079889503001535543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52475061546372008004094781 19678148079889503001535543)
  ·
    refine ⟨29517222119834254502303315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19678148079889503001535543 29517222119834254502303315)
    ·
      refine ⟨44275833179751381753454973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29517222119834254502303315 44275833179751381753454973)
      ·
        refine ⟨16603437442406768157545615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44275833179751381753454973 16603437442406768157545615)
        ·
          refine ⟨24905156163610152236318423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16603437442406768157545615 24905156163610152236318423)
          ·
            refine ⟨37357734245415228354477635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24905156163610152236318423 37357734245415228354477635)
            ·
              refine ⟨56036601368122842531716453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37357734245415228354477635 56036601368122842531716453)
              ·
                refine ⟨10506862756523032974696835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56036601368122842531716453 10506862756523032974696835)
                ·
                  refine ⟨15760294134784549462045253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10506862756523032974696835 15760294134784549462045253)
                  ·
                    refine ⟨2955055150272103024133485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15760294134784549462045253 2955055150272103024133485)
                    ·
                      refine ⟨1108145681352038634050057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2955055150272103024133485 1108145681352038634050057)
                      ·
                        rfl

theorem cell23_2158106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_2158106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158106 prefixEnd_2158106 := by exact prefixLift 2158106
  have htrace : WordTrace (prefixWord ++ tailWord_2158106) baseStart_2158106 baseEnd_2158106 := by
    simpa [prefixWord, tailWord_2158106, baseEnd_2158106] using wordTrace_append hprefix tailTrace_2158106
  have hstable : (prefixWord ++ tailWord_2158106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158106).length < 2 ^ (prefixWord ++ tailWord_2158106).sum := by decide
  have hdescent : baseEnd_2158106 < baseStart_2158106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158113 : List Nat := [1, 2, 3, 2, 2, 3, 1, 2, 3, 4]
def baseStart_2158113 : Nat := 118140960795 + 2158113 * 2 ^ 59
def prefixEnd_2158113 : Nat := 4983230072969 + 3 ^ 40 * 2158113 * 2
def baseEnd_2158113 : Nat := 369383091905540035554175

theorem tailTrace_2158113 : CollatzResearch.WordTrace tailWord_2158113 prefixEnd_2158113 369383091905540035554175 := by
  unfold tailWord_2158113
  simp only [CollatzResearch.WordTrace]
  refine ⟨78712847630532652201646993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52475231753688434801097995 78712847630532652201646993)
  ·
    refine ⟨59034635722899489151235245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78712847630532652201646993 59034635722899489151235245)
    ·
      refine ⟨22137988396087308431713217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59034635722899489151235245 22137988396087308431713217)
      ·
        refine ⟨16603491297065481323784913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22137988396087308431713217 16603491297065481323784913)
        ·
          refine ⟨12452618472799110992838685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16603491297065481323784913 12452618472799110992838685)
          ·
            refine ⟨4669731927299666622314507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12452618472799110992838685 4669731927299666622314507)
            ·
              refine ⟨7004597890949499933471761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4669731927299666622314507 7004597890949499933471761)
              ·
                refine ⟨5253448418212124950103821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7004597890949499933471761 5253448418212124950103821)
                ·
                  refine ⟨1970043156829546856288933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5253448418212124950103821 1970043156829546856288933)
                  ·
                    refine ⟨369383091905540035554175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1970043156829546856288933 369383091905540035554175)
                    ·
                      rfl

theorem cell23_2158113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_2158113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158113 prefixEnd_2158113 := by exact prefixLift 2158113
  have htrace : WordTrace (prefixWord ++ tailWord_2158113) baseStart_2158113 baseEnd_2158113 := by
    simpa [prefixWord, tailWord_2158113, baseEnd_2158113] using wordTrace_append hprefix tailTrace_2158113
  have hstable : (prefixWord ++ tailWord_2158113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158113).length < 2 ^ (prefixWord ++ tailWord_2158113).sum := by decide
  have hdescent : baseEnd_2158113 < baseStart_2158113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158143 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 6]
def baseStart_2158143 : Nat := 118140960795 + 2158143 * 2 ^ 59
def prefixEnd_2158143 : Nat := 4983230072969 + 3 ^ 40 * 2158143 * 2
def baseEnd_2158143 : Nat := 123129408904028332143043

theorem tailTrace_2158143 : CollatzResearch.WordTrace tailWord_2158143 prefixEnd_2158143 123129408904028332143043 := by
  unfold tailWord_2158143
  simp only [CollatzResearch.WordTrace]
  refine ⟨78713941820423967325239083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52475961213615978216826055 78713941820423967325239083)
  ·
    refine ⟨118070912730635950987858625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78713941820423967325239083 118070912730635950987858625)
    ·
      refine ⟨88553184547976963240893969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118070912730635950987858625 88553184547976963240893969)
      ·
        refine ⟨66414888410982722430670477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88553184547976963240893969 66414888410982722430670477)
        ·
          refine ⟨24905583154118520911501429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66414888410982722430670477 24905583154118520911501429)
          ·
            refine ⟨2334898420698611335453259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24905583154118520911501429 2334898420698611335453259)
            ·
              refine ⟨3502347631047917003179889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2334898420698611335453259 3502347631047917003179889)
              ·
                refine ⟨2626760723285937752384917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3502347631047917003179889 2626760723285937752384917)
                ·
                  refine ⟨123129408904028332143043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2626760723285937752384917 123129408904028332143043)
                  ·
                    rfl

theorem cell23_2158143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 6].length) (baseStart_2158143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158143 prefixEnd_2158143 := by exact prefixLift 2158143
  have htrace : WordTrace (prefixWord ++ tailWord_2158143) baseStart_2158143 baseEnd_2158143 := by
    simpa [prefixWord, tailWord_2158143, baseEnd_2158143] using wordTrace_append hprefix tailTrace_2158143
  have hstable : (prefixWord ++ tailWord_2158143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158143).length < 2 ^ (prefixWord ++ tailWord_2158143).sum := by decide
  have hdescent : baseEnd_2158143 < baseStart_2158143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158197 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_2158197 : Nat := 118140960795 + 2158197 * 2 ^ 59
def prefixEnd_2158197 : Nat := 4983230072969 + 3 ^ 40 * 2158197 * 2
def baseEnd_2158197 : Nat := 1108192408091597778012139

theorem tailTrace_2158197 : CollatzResearch.WordTrace tailWord_2158197 prefixEnd_2158197 1108192408091597778012139 := by
  unfold tailWord_2158197
  simp only [CollatzResearch.WordTrace]
  refine ⟨78715911362228334547704845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52477274241485556365136563 78715911362228334547704845)
  ·
    refine ⟨29518466760835625455389317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78715911362228334547704845 29518466760835625455389317)
    ·
      refine ⟨5534712517656679772885497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29518466760835625455389317 5534712517656679772885497)
      ·
        refine ⟨4151034388242509829664123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5534712517656679772885497 4151034388242509829664123)
        ·
          refine ⟨6226551582363764744496185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4151034388242509829664123 6226551582363764744496185)
          ·
            refine ⟨4669913686772823558372139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6226551582363764744496185 4669913686772823558372139)
            ·
              refine ⟨7004870530159235337558209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4669913686772823558372139 7004870530159235337558209)
              ·
                refine ⟨5253652897619426503168657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7004870530159235337558209 5253652897619426503168657)
                ·
                  refine ⟨3940239673214569877376493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5253652897619426503168657 3940239673214569877376493)
                  ·
                    refine ⟨1477589877455463704016185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3940239673214569877376493 1477589877455463704016185)
                    ·
                      refine ⟨1108192408091597778012139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1477589877455463704016185 1108192408091597778012139)
                      ·
                        rfl

theorem cell23_2158197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_2158197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158197 prefixEnd_2158197 := by exact prefixLift 2158197
  have htrace : WordTrace (prefixWord ++ tailWord_2158197) baseStart_2158197 baseEnd_2158197 := by
    simpa [prefixWord, tailWord_2158197, baseEnd_2158197] using wordTrace_append hprefix tailTrace_2158197
  have hstable : (prefixWord ++ tailWord_2158197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158197).length < 2 ^ (prefixWord ++ tailWord_2158197).sum := by decide
  have hdescent : baseEnd_2158197 < baseStart_2158197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158203 : List Nat := [1, 1, 1, 1, 1, 4, 4, 4, 2, 4]
def baseStart_2158203 : Nat := 118140960795 + 2158203 * 2 ^ 59
def prefixEnd_2158203 : Nat := 4983230072969 + 3 ^ 40 * 2158203 * 2
def baseEnd_2158203 : Nat := 369398496325174918179037

theorem tailTrace_2158203 : CollatzResearch.WordTrace tailWord_2158203 prefixEnd_2158203 369398496325174918179037 := by
  unfold tailWord_2158203
  simp only [CollatzResearch.WordTrace]
  refine ⟨78716130200206597572423263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52477420133471065048282175 78716130200206597572423263)
  ·
    refine ⟨118074195300309896358634895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78716130200206597572423263 118074195300309896358634895)
    ·
      refine ⟨177111292950464844537952343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118074195300309896358634895 177111292950464844537952343)
      ·
        refine ⟨265666939425697266806928515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177111292950464844537952343 265666939425697266806928515)
        ·
          refine ⟨398500409138545900210392773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265666939425697266806928515 398500409138545900210392773)
          ·
            refine ⟨74718826713477356289448645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 398500409138545900210392773 74718826713477356289448645)
            ·
              refine ⟨14009780008777004304271621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74718826713477356289448645 14009780008777004304271621)
              ·
                refine ⟨2626833751645688307050929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14009780008777004304271621 2626833751645688307050929)
                ·
                  refine ⟨1970125313734266230288197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2626833751645688307050929 1970125313734266230288197)
                  ·
                    refine ⟨369398496325174918179037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1970125313734266230288197 369398496325174918179037)
                    ·
                      rfl

theorem cell23_2158203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 2, 4].length) (baseStart_2158203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158203 prefixEnd_2158203 := by exact prefixLift 2158203
  have htrace : WordTrace (prefixWord ++ tailWord_2158203) baseStart_2158203 baseEnd_2158203 := by
    simpa [prefixWord, tailWord_2158203, baseEnd_2158203] using wordTrace_append hprefix tailTrace_2158203
  have hstable : (prefixWord ++ tailWord_2158203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158203).length < 2 ^ (prefixWord ++ tailWord_2158203).sum := by decide
  have hdescent : baseEnd_2158203 < baseStart_2158203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158213 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 3, 2, 3]
def baseStart_2158213 : Nat := 118140960795 + 2158213 * 2 ^ 59
def prefixEnd_2158213 : Nat := 4983230072969 + 3 ^ 40 * 2158213 * 2
def baseEnd_2158213 : Nat := 1108200623782069715412065

theorem tailTrace_2158213 : CollatzResearch.WordTrace tailWord_2158213 prefixEnd_2158213 1108200623782069715412065 := by
  unfold tailWord_2158213
  simp only [CollatzResearch.WordTrace]
  refine ⟨78716494930170369280287293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52477663286780246186858195 78716494930170369280287293)
  ·
    refine ⟨29518685598813888480107735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78716494930170369280287293 29518685598813888480107735)
    ·
      refine ⟨44278028398220832720161603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29518685598813888480107735 44278028398220832720161603)
      ·
        refine ⟨66417042597331249080242405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44278028398220832720161603 66417042597331249080242405)
        ·
          refine ⟨12453195486999609202545451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66417042597331249080242405 12453195486999609202545451)
          ·
            refine ⟨18679793230499413803818177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12453195486999609202545451 18679793230499413803818177)
            ·
              refine ⟨14009844922874560352863633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18679793230499413803818177 14009844922874560352863633)
              ·
                refine ⟨10507383692155920264647725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14009844922874560352863633 10507383692155920264647725)
                ·
                  refine ⟨3940268884558470099242897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10507383692155920264647725 3940268884558470099242897)
                  ·
                    refine ⟨2955201663418852574432173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3940268884558470099242897 2955201663418852574432173)
                    ·
                      refine ⟨1108200623782069715412065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2955201663418852574432173 1108200623782069715412065)
                      ·
                        rfl

theorem cell23_2158213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_2158213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158213 prefixEnd_2158213 := by exact prefixLift 2158213
  have htrace : WordTrace (prefixWord ++ tailWord_2158213) baseStart_2158213 baseEnd_2158213 := by
    simpa [prefixWord, tailWord_2158213, baseEnd_2158213] using wordTrace_append hprefix tailTrace_2158213
  have hstable : (prefixWord ++ tailWord_2158213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158213).length < 2 ^ (prefixWord ++ tailWord_2158213).sum := by decide
  have hdescent : baseEnd_2158213 < baseStart_2158213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158243 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 3]
def baseStart_2158243 : Nat := 118140960795 + 2158243 * 2 ^ 59
def prefixEnd_2158243 : Nat := 4983230072969 + 3 ^ 40 * 2158243 * 2
def baseEnd_2158243 : Nat := 1108216028201704598036927

theorem tailTrace_2158243 : CollatzResearch.WordTrace tailWord_2158243 prefixEnd_2158243 1108216028201704598036927 := by
  unfold tailWord_2158243
  simp only [CollatzResearch.WordTrace]
  refine ⟨78717589120061684403879383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52478392746707789602586255 78717589120061684403879383)
  ·
    refine ⟨118076383680092526605819075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78717589120061684403879383 118076383680092526605819075)
    ·
      refine ⟨177114575520138789908728613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118076383680092526605819075 177114575520138789908728613)
      ·
        refine ⟨33208982910026023107886615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177114575520138789908728613 33208982910026023107886615)
        ·
          refine ⟨49813474365039034661829923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33208982910026023107886615 49813474365039034661829923)
          ·
            refine ⟨74720211547558551992744885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49813474365039034661829923 74720211547558551992744885)
            ·
              refine ⟨7005019832583614249319833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74720211547558551992744885 7005019832583614249319833)
              ·
                refine ⟨5253764874437710686989875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7005019832583614249319833 5253764874437710686989875)
                ·
                  refine ⟨7880647311656566030484813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5253764874437710686989875 7880647311656566030484813)
                  ·
                    refine ⟨2955242741871212261431805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7880647311656566030484813 2955242741871212261431805)
                    ·
                      refine ⟨1108216028201704598036927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2955242741871212261431805 1108216028201704598036927)
                      ·
                        rfl

theorem cell23_2158243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_2158243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158243 prefixEnd_2158243 := by exact prefixLift 2158243
  have htrace : WordTrace (prefixWord ++ tailWord_2158243) baseStart_2158243 baseEnd_2158243 := by
    simpa [prefixWord, tailWord_2158243, baseEnd_2158243] using wordTrace_append hprefix tailTrace_2158243
  have hstable : (prefixWord ++ tailWord_2158243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158243).length < 2 ^ (prefixWord ++ tailWord_2158243).sum := by decide
  have hdescent : baseEnd_2158243 < baseStart_2158243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158254 : List Nat := [4, 1, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_2158254 : Nat := 118140960795 + 2158254 * 2 ^ 59
def prefixEnd_2158254 : Nat := 4983230072969 + 3 ^ 40 * 2158254 * 2
def baseEnd_2158254 : Nat := 369407225496301351666459

theorem tailTrace_2158254 : CollatzResearch.WordTrace tailWord_2158254 prefixEnd_2158254 369407225496301351666459 := by
  unfold tailWord_2158254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9839748790377729160316227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52478660215347888855019877 9839748790377729160316227)
  ·
    refine ⟨14759623185566593740474341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9839748790377729160316227 14759623185566593740474341)
    ·
      refine ⟨2767429347293736326338939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14759623185566593740474341 2767429347293736326338939)
      ·
        refine ⟨4151144020940604489508409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2767429347293736326338939 4151144020940604489508409)
        ·
          refine ⟨3113358015705453367131307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4151144020940604489508409 3113358015705453367131307)
          ·
            refine ⟨4670037023558180050696961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3113358015705453367131307 4670037023558180050696961)
            ·
              refine ⟨3502527767668635038022721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4670037023558180050696961 3502527767668635038022721)
              ·
                refine ⟨2626895825751476278517041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3502527767668635038022721 2626895825751476278517041)
                ·
                  refine ⟨1970171869313607208887781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2626895825751476278517041 1970171869313607208887781)
                  ·
                    refine ⟨369407225496301351666459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1970171869313607208887781 369407225496301351666459)
                    ·
                      rfl

theorem cell23_2158254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_2158254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158254 prefixEnd_2158254 := by exact prefixLift 2158254
  have htrace : WordTrace (prefixWord ++ tailWord_2158254) baseStart_2158254 baseEnd_2158254 := by
    simpa [prefixWord, tailWord_2158254, baseEnd_2158254] using wordTrace_append hprefix tailTrace_2158254
  have hstable : (prefixWord ++ tailWord_2158254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158254).length < 2 ^ (prefixWord ++ tailWord_2158254).sum := by decide
  have hdescent : baseEnd_2158254 < baseStart_2158254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158256 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_2158256 : Nat := 118140960795 + 2158256 * 2 ^ 59
def prefixEnd_2158256 : Nat := 4983230072969 + 3 ^ 40 * 2158256 * 2
def baseEnd_2158256 : Nat := 1108222703450213047174367

theorem tailTrace_2158256 : CollatzResearch.WordTrace tailWord_2158256 prefixEnd_2158256 1108222703450213047174367 := by
  unfold tailWord_2158256
  simp only [CollatzResearch.WordTrace]
  refine ⟨39359031634507293812051311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52478708846009725082735081 39359031634507293812051311)
  ·
    refine ⟨59038547451760940718076967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39359031634507293812051311 59038547451760940718076967)
    ·
      refine ⟨88557821177641411077115451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59038547451760940718076967 88557821177641411077115451)
      ·
        refine ⟨132836731766462116615673177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88557821177641411077115451 132836731766462116615673177)
        ·
          refine ⟨99627548824846587461754883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132836731766462116615673177 99627548824846587461754883)
          ·
            refine ⟨149441323237269881192632325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99627548824846587461754883 149441323237269881192632325)
            ·
              refine ⟨28020248106988102723618561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149441323237269881192632325 28020248106988102723618561)
              ·
                refine ⟨21015186080241077042713921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28020248106988102723618561 21015186080241077042713921)
                ·
                  refine ⟨15761389560180807782035441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21015186080241077042713921 15761389560180807782035441)
                  ·
                    refine ⟨11821042170135605836526581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15761389560180807782035441 11821042170135605836526581)
                    ·
                      refine ⟨1108222703450213047174367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11821042170135605836526581 1108222703450213047174367)
                      ·
                        rfl

theorem cell23_2158256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_2158256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158256 prefixEnd_2158256 := by exact prefixLift 2158256
  have htrace : WordTrace (prefixWord ++ tailWord_2158256) baseStart_2158256 baseEnd_2158256 := by
    simpa [prefixWord, tailWord_2158256, baseEnd_2158256] using wordTrace_append hprefix tailTrace_2158256
  have hstable : (prefixWord ++ tailWord_2158256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158256).length < 2 ^ (prefixWord ++ tailWord_2158256).sum := by decide
  have hdescent : baseEnd_2158256 < baseStart_2158256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158261 : List Nat := [1, 3, 3, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_2158261 : Nat := 118140960795 + 2158261 * 2 ^ 59
def prefixEnd_2158261 : Nat := 4983230072969 + 3 ^ 40 * 2158261 * 2
def baseEnd_2158261 : Nat := 1108225270853485527611845

theorem tailTrace_2158261 : CollatzResearch.WordTrace tailWord_2158261 prefixEnd_2158261 1108225270853485527611845 := by
  unfold tailWord_2158261
  simp only [CollatzResearch.WordTrace]
  refine ⟨78718245633996473478034637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52478830422664315652023091 78718245633996473478034637)
  ·
    refine ⟨29519342112748677554262989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78718245633996473478034637 29519342112748677554262989)
    ·
      refine ⟨11069753292280754082848621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29519342112748677554262989 11069753292280754082848621)
      ·
        refine ⟨4151157484605282781068233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11069753292280754082848621 4151157484605282781068233)
        ·
          refine ⟨3113368113453962085801175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4151157484605282781068233 3113368113453962085801175)
          ·
            refine ⟨4670052170180943128701763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3113368113453962085801175 4670052170180943128701763)
            ·
              refine ⟨7005078255271414693052645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4670052170180943128701763 7005078255271414693052645)
              ·
                refine ⟨1313452172863390254947371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7005078255271414693052645 1313452172863390254947371)
                ·
                  refine ⟨1970178259295085382421057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1313452172863390254947371 1970178259295085382421057)
                  ·
                    refine ⟨1477633694471314036815793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1970178259295085382421057 1477633694471314036815793)
                    ·
                      refine ⟨1108225270853485527611845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1477633694471314036815793 1108225270853485527611845)
                      ·
                        rfl

theorem cell23_2158261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_2158261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158261 prefixEnd_2158261 := by exact prefixLift 2158261
  have htrace : WordTrace (prefixWord ++ tailWord_2158261) baseStart_2158261 baseEnd_2158261 := by
    simpa [prefixWord, tailWord_2158261, baseEnd_2158261] using wordTrace_append hprefix tailTrace_2158261
  have hstable : (prefixWord ++ tailWord_2158261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158261).length < 2 ^ (prefixWord ++ tailWord_2158261).sum := by decide
  have hdescent : baseEnd_2158261 < baseStart_2158261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158311 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2158311 : Nat := 118140960795 + 2158311 * 2 ^ 59
def prefixEnd_2158311 : Nat := 4983230072969 + 3 ^ 40 * 2158311 * 2
def baseEnd_2158311 : Nat := 1108250944886210331986615

theorem tailTrace_2158311 : CollatzResearch.WordTrace tailWord_2158311 prefixEnd_2158311 1108250944886210331986615 := by
  unfold tailWord_2158311
  simp only [CollatzResearch.WordTrace]
  refine ⟨78720069283815332017354787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52480046189210221344903191 78720069283815332017354787)
  ·
    refine ⟨118080103925722998026032181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78720069283815332017354787 118080103925722998026032181)
    ·
      refine ⟨11070009743036531064940517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118080103925722998026032181 11070009743036531064940517)
      ·
        refine ⟨2075626826819349574676347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11070009743036531064940517 2075626826819349574676347)
        ·
          refine ⟨3113440240229024362014521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2075626826819349574676347 3113440240229024362014521)
          ·
            refine ⟨2335080180171768271510891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3113440240229024362014521 2335080180171768271510891)
            ·
              refine ⟨3502620270257652407266337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335080180171768271510891 3502620270257652407266337)
              ·
                refine ⟨2626965202693239305449753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3502620270257652407266337 2626965202693239305449753)
                ·
                  refine ⟨1970223902019929479087315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2626965202693239305449753 1970223902019929479087315)
                  ·
                    refine ⟨2955335853029894218630973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1970223902019929479087315 2955335853029894218630973)
                    ·
                      refine ⟨1108250944886210331986615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2955335853029894218630973 1108250944886210331986615)
                      ·
                        rfl

theorem cell23_2158311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2158311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158311 prefixEnd_2158311 := by exact prefixLift 2158311
  have htrace : WordTrace (prefixWord ++ tailWord_2158311) baseStart_2158311 baseEnd_2158311 := by
    simpa [prefixWord, tailWord_2158311, baseEnd_2158311] using wordTrace_append hprefix tailTrace_2158311
  have hstable : (prefixWord ++ tailWord_2158311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158311).length < 2 ^ (prefixWord ++ tailWord_2158311).sum := by decide
  have hdescent : baseEnd_2158311 < baseStart_2158311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158333 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 1, 5, 3]
def baseStart_2158333 : Nat := 118140960795 + 2158333 * 2 ^ 59
def prefixEnd_2158333 : Nat := 4983230072969 + 3 ^ 40 * 2158333 * 2
def baseEnd_2158333 : Nat := 1108262241460609245911513

theorem tailTrace_2158333 : CollatzResearch.WordTrace tailWord_2158333 prefixEnd_2158333 1108262241460609245911513 := by
  unfold tailWord_2158333
  simp only [CollatzResearch.WordTrace]
  refine ⟨78720871689735629774655653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52480581126490419849770435 78720871689735629774655653)
  ·
    refine ⟨14760163441825430582747935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78720871689735629774655653 14760163441825430582747935)
    ·
      refine ⟨22140245162738145874121903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14760163441825430582747935 22140245162738145874121903)
      ·
        refine ⟨33210367744107218811182855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22140245162738145874121903 33210367744107218811182855)
        ·
          refine ⟨49815551616160828216774283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33210367744107218811182855 49815551616160828216774283)
          ·
            refine ⟨74723327424241242325161425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49815551616160828216774283 74723327424241242325161425)
            ·
              refine ⟨56042495568180931743871069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74723327424241242325161425 56042495568180931743871069)
              ·
                refine ⟨21015935838067849403951651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56042495568180931743871069 21015935838067849403951651)
                ·
                  refine ⟨31523903757101774105927477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21015935838067849403951651 31523903757101774105927477)
                  ·
                    refine ⟨2955365977228291322430701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31523903757101774105927477 2955365977228291322430701)
                    ·
                      refine ⟨1108262241460609245911513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2955365977228291322430701 1108262241460609245911513)
                      ·
                        rfl

theorem cell23_2158333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_2158333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158333 prefixEnd_2158333 := by exact prefixLift 2158333
  have htrace : WordTrace (prefixWord ++ tailWord_2158333) baseStart_2158333 baseEnd_2158333 := by
    simpa [prefixWord, tailWord_2158333, baseEnd_2158333] using wordTrace_append hprefix tailTrace_2158333
  have hstable : (prefixWord ++ tailWord_2158333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158333).length < 2 ^ (prefixWord ++ tailWord_2158333).sum := by decide
  have hdescent : baseEnd_2158333 < baseStart_2158333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158353 : List Nat := [1, 2, 2, 1, 1, 3, 1, 5, 2, 5]
def baseStart_2158353 : Nat := 118140960795 + 2158353 * 2 ^ 59
def prefixEnd_2158353 : Nat := 4983230072969 + 3 ^ 40 * 2158353 * 2
def baseEnd_2158353 : Nat := 369424170357899722553807

theorem tailTrace_2158353 : CollatzResearch.WordTrace tailWord_2158353 prefixEnd_2158353 369424170357899722553807 := by
  unfold tailWord_2158353
  simp only [CollatzResearch.WordTrace]
  refine ⟨78721601149663173190383713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52481067433108782126922475 78721601149663173190383713)
  ·
    refine ⟨59041200862247379892787785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78721601149663173190383713 59041200862247379892787785)
    ·
      refine ⟨44280900646685534919590839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59041200862247379892787785 44280900646685534919590839)
      ·
        refine ⟨66421350970028302379386259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44280900646685534919590839 66421350970028302379386259)
        ·
          refine ⟨99632026455042453569079389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66421350970028302379386259 99632026455042453569079389)
          ·
            refine ⟨37362009920640920088404771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99632026455042453569079389 37362009920640920088404771)
            ·
              refine ⟨56043014880961380132607157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37362009920640920088404771 56043014880961380132607157)
              ·
                refine ⟨5254032645090129387431921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56043014880961380132607157 5254032645090129387431921)
                ·
                  refine ⟨3940524483817597040573941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5254032645090129387431921 3940524483817597040573941)
                  ·
                    refine ⟨369424170357899722553807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3940524483817597040573941 369424170357899722553807)
                    ·
                      rfl

theorem cell23_2158353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_2158353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158353 prefixEnd_2158353 := by exact prefixLift 2158353
  have htrace : WordTrace (prefixWord ++ tailWord_2158353) baseStart_2158353 baseEnd_2158353 := by
    simpa [prefixWord, tailWord_2158353, baseEnd_2158353] using wordTrace_append hprefix tailTrace_2158353
  have hstable : (prefixWord ++ tailWord_2158353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158353).length < 2 ^ (prefixWord ++ tailWord_2158353).sum := by decide
  have hdescent : baseEnd_2158353 < baseStart_2158353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158357 : List Nat := [1, 3, 2, 1, 2, 5, 1, 3, 5]
def baseStart_2158357 : Nat := 118140960795 + 2158357 * 2 ^ 59
def prefixEnd_2158357 : Nat := 4983230072969 + 3 ^ 40 * 2158357 * 2
def baseEnd_2158357 : Nat := 123141618332924128001267

theorem tailTrace_2158357 : CollatzResearch.WordTrace tailWord_2158357 prefixEnd_2158357 123141618332924128001267 := by
  unfold tailWord_2158357
  simp only [CollatzResearch.WordTrace]
  refine ⟨78721747041648681873529325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52481164694432454582352883 78721747041648681873529325)
  ·
    refine ⟨29520655140618255702573497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78721747041648681873529325 29520655140618255702573497)
    ·
      refine ⟨22140491355463691776930123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29520655140618255702573497 22140491355463691776930123)
      ·
        refine ⟨33210737033195537665395185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22140491355463691776930123 33210737033195537665395185)
        ·
          refine ⟨24908052774896653249046389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33210737033195537665395185 24908052774896653249046389)
          ·
            refine ⟨2335129947646561242098099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24908052774896653249046389 2335129947646561242098099)
            ·
              refine ⟨3502694921469841863147149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2335129947646561242098099 3502694921469841863147149)
              ·
                refine ⟨1313510595551190698680181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3502694921469841863147149 1313510595551190698680181)
                ·
                  refine ⟨123141618332924128001267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1313510595551190698680181 123141618332924128001267)
                  ·
                    rfl

theorem cell23_2158357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_2158357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158357 prefixEnd_2158357 := by exact prefixLift 2158357
  have htrace : WordTrace (prefixWord ++ tailWord_2158357) baseStart_2158357 baseEnd_2158357 := by
    simpa [prefixWord, tailWord_2158357, baseEnd_2158357] using wordTrace_append hprefix tailTrace_2158357
  have hstable : (prefixWord ++ tailWord_2158357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158357).length < 2 ^ (prefixWord ++ tailWord_2158357).sum := by decide
  have hdescent : baseEnd_2158357 < baseStart_2158357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158370 : List Nat := [3, 3, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_2158370 : Nat := 118140960795 + 2158370 * 2 ^ 59
def prefixEnd_2158370 : Nat := 4983230072969 + 3 ^ 40 * 2158370 * 2
def baseEnd_2158370 : Nat := 369427080081608533716281

theorem tailTrace_2158370 : CollatzResearch.WordTrace tailWord_2158370 prefixEnd_2158370 369427080081608533716281 := by
  unfold tailWord_2158370
  simp only [CollatzResearch.WordTrace]
  refine ⟨19680555297650396273438141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52481480793734390062501709 19680555297650396273438141)
  ·
    refine ⟨7380208236618898602539303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19680555297650396273438141 7380208236618898602539303)
    ·
      refine ⟨11070312354928347903808955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7380208236618898602539303 11070312354928347903808955)
      ·
        refine ⟨16605468532392521855713433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11070312354928347903808955 16605468532392521855713433)
        ·
          refine ⟨12454101399294391391785075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16605468532392521855713433 12454101399294391391785075)
          ·
            refine ⟨18681152098941587087677613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12454101399294391391785075 18681152098941587087677613)
            ·
              refine ⟨7005432037103095157879105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18681152098941587087677613 7005432037103095157879105)
              ·
                refine ⟨5254074027827321368409329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7005432037103095157879105 5254074027827321368409329)
                ·
                  refine ⟨3940555520870491026306997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5254074027827321368409329 3940555520870491026306997)
                  ·
                    refine ⟨369427080081608533716281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3940555520870491026306997 369427080081608533716281)
                    ·
                      rfl

theorem cell23_2158370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_2158370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158370 prefixEnd_2158370 := by exact prefixLift 2158370
  have htrace : WordTrace (prefixWord ++ tailWord_2158370) baseStart_2158370 baseEnd_2158370 := by
    simpa [prefixWord, tailWord_2158370, baseEnd_2158370] using wordTrace_append hprefix tailTrace_2158370
  have hstable : (prefixWord ++ tailWord_2158370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158370).length < 2 ^ (prefixWord ++ tailWord_2158370).sum := by decide
  have hdescent : baseEnd_2158370 < baseStart_2158370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158433 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_2158433 : Nat := 118140960795 + 2158433 * 2 ^ 59
def prefixEnd_2158433 : Nat := 4983230072969 + 3 ^ 40 * 2158433 * 2
def baseEnd_2158433 : Nat := 1108313589526058854661053

theorem tailTrace_2158433 : CollatzResearch.WordTrace tailWord_2158433 prefixEnd_2158433 1108313589526058854661053 := by
  unfold tailWord_2158433
  simp only [CollatzResearch.WordTrace]
  refine ⟨78724518989373346853295953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52483012659582231235530635 78724518989373346853295953)
  ·
    refine ⟨59043389242030010139971965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78724518989373346853295953 59043389242030010139971965)
    ·
      refine ⟨22141270965761253802489487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59043389242030010139971965 22141270965761253802489487)
      ·
        refine ⟨33211906448641880703734231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22141270965761253802489487 33211906448641880703734231)
        ·
          refine ⟨49817859672962821055601347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33211906448641880703734231 49817859672962821055601347)
          ·
            refine ⟨74726789509444231583402021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49817859672962821055601347 74726789509444231583402021)
            ·
              refine ⟨14011273033020793421887879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74726789509444231583402021 14011273033020793421887879)
              ·
                refine ⟨21016909549531190132831819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14011273033020793421887879 21016909549531190132831819)
                ·
                  refine ⟨31525364324296785199247729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21016909549531190132831819 31525364324296785199247729)
                  ·
                    refine ⟨23644023243222588899435797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31525364324296785199247729 23644023243222588899435797)
                    ·
                      refine ⟨1108313589526058854661053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 23644023243222588899435797 1108313589526058854661053)
                      ·
                        rfl

theorem cell23_2158433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_2158433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158433 prefixEnd_2158433 := by exact prefixLift 2158433
  have htrace : WordTrace (prefixWord ++ tailWord_2158433) baseStart_2158433 baseEnd_2158433 := by
    simpa [prefixWord, tailWord_2158433, baseEnd_2158433] using wordTrace_append hprefix tailTrace_2158433
  have hstable : (prefixWord ++ tailWord_2158433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158433).length < 2 ^ (prefixWord ++ tailWord_2158433).sum := by decide
  have hdescent : baseEnd_2158433 < baseStart_2158433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158457 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 3, 1, 3]
def baseStart_2158457 : Nat := 118140960795 + 2158457 * 2 ^ 59
def prefixEnd_2158457 : Nat := 4983230072969 + 3 ^ 40 * 2158457 * 2
def baseEnd_2158457 : Nat := 1108325913061766760760943

theorem tailTrace_2158457 : CollatzResearch.WordTrace tailWord_2158457 prefixEnd_2158457 1108325913061766760760943 := by
  unfold tailWord_2158457
  simp only [CollatzResearch.WordTrace]
  refine ⟨78725394341286398952169625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52483596227524265968113083 78725394341286398952169625)
  ·
    refine ⟨59044045755964799214127219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78725394341286398952169625 59044045755964799214127219)
    ·
      refine ⟨88566068633947198821190829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59044045755964799214127219 88566068633947198821190829)
      ·
        refine ⟨33212275737730199557946561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88566068633947198821190829 33212275737730199557946561)
        ·
          refine ⟨24909206803297649668459921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33212275737730199557946561 24909206803297649668459921)
          ·
            refine ⟨18681905102473237251344941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24909206803297649668459921 18681905102473237251344941)
            ·
              refine ⟨7005714413427463969254353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18681905102473237251344941 7005714413427463969254353)
              ·
                refine ⟨5254285810070597976940765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7005714413427463969254353 5254285810070597976940765)
                ·
                  refine ⟨1970357178776474241352787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5254285810070597976940765 1970357178776474241352787)
                  ·
                    refine ⟨2955535768164711362029181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1970357178776474241352787 2955535768164711362029181)
                    ·
                      refine ⟨1108325913061766760760943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2955535768164711362029181 1108325913061766760760943)
                      ·
                        rfl

theorem cell23_2158457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_2158457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158457 prefixEnd_2158457 := by exact prefixLift 2158457
  have htrace : WordTrace (prefixWord ++ tailWord_2158457) baseStart_2158457 baseEnd_2158457 := by
    simpa [prefixWord, tailWord_2158457, baseEnd_2158457] using wordTrace_append hprefix tailTrace_2158457
  have hstable : (prefixWord ++ tailWord_2158457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158457).length < 2 ^ (prefixWord ++ tailWord_2158457).sum := by decide
  have hdescent : baseEnd_2158457 < baseStart_2158457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158467 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 1, 5, 2]
def baseStart_2158467 : Nat := 118140960795 + 2158467 * 2 ^ 59
def prefixEnd_2158467 : Nat := 4983230072969 + 3 ^ 40 * 2158467 * 2
def baseEnd_2158467 : Nat := 1108331047868311721635897

theorem tailTrace_2158467 : CollatzResearch.WordTrace tailWord_2158467 prefixEnd_2158467 1108331047868311721635897 := by
  unfold tailWord_2158467
  simp only [CollatzResearch.WordTrace]
  refine ⟨78725759071250170660033655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52483839380833447106689103 78725759071250170660033655)
  ·
    refine ⟨118088638606875255990050483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78725759071250170660033655 118088638606875255990050483)
    ·
      refine ⟨177132957910312883985075725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118088638606875255990050483 177132957910312883985075725)
      ·
        refine ⟨66424859216367331494403397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177132957910312883985075725 66424859216367331494403397)
        ·
          refine ⟨12454661103068874655200637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66424859216367331494403397 12454661103068874655200637)
          ·
            refine ⟨4670497913650827995700239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12454661103068874655200637 4670497913650827995700239)
            ·
              refine ⟨7005746870476241993550359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4670497913650827995700239 7005746870476241993550359)
              ·
                refine ⟨10508620305714362990325539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7005746870476241993550359 10508620305714362990325539)
                ·
                  refine ⟨15762930458571544485488309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10508620305714362990325539 15762930458571544485488309)
                  ·
                    refine ⟨1477774730491082295514529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15762930458571544485488309 1477774730491082295514529)
                    ·
                      refine ⟨1108331047868311721635897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1477774730491082295514529 1108331047868311721635897)
                      ·
                        rfl

theorem cell23_2158467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 5, 2].length) (baseStart_2158467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158467 prefixEnd_2158467 := by exact prefixLift 2158467
  have htrace : WordTrace (prefixWord ++ tailWord_2158467) baseStart_2158467 baseEnd_2158467 := by
    simpa [prefixWord, tailWord_2158467, baseEnd_2158467] using wordTrace_append hprefix tailTrace_2158467
  have hstable : (prefixWord ++ tailWord_2158467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158467).length < 2 ^ (prefixWord ++ tailWord_2158467).sum := by decide
  have hdescent : baseEnd_2158467 < baseStart_2158467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158500 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_2158500 : Nat := 118140960795 + 2158500 * 2 ^ 59
def prefixEnd_2158500 : Nat := 4983230072969 + 3 ^ 40 * 2158500 * 2
def baseEnd_2158500 : Nat := 1108347992729910092523245

theorem tailTrace_2158500 : CollatzResearch.WordTrace tailWord_2158500 prefixEnd_2158500 1108347992729910092523245 := by
  unfold tailWord_2158500
  simp only [CollatzResearch.WordTrace]
  refine ⟨39363481340065308647992477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52484641786753744863989969 39363481340065308647992477)
  ·
    refine ⟨14761305502524490742997179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39363481340065308647992477 14761305502524490742997179)
    ·
      refine ⟨22141958253786736114495769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14761305502524490742997179 22141958253786736114495769)
      ·
        refine ⟨16606468690340052085871827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22141958253786736114495769 16606468690340052085871827)
        ·
          refine ⟨24909703035510078128807741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16606468690340052085871827 24909703035510078128807741)
          ·
            refine ⟨9341138638316279298302903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24909703035510078128807741 9341138638316279298302903)
            ·
              refine ⟨14011707957474418947454355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9341138638316279298302903 14011707957474418947454355)
              ·
                refine ⟨21017561936211628421181533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14011707957474418947454355 21017561936211628421181533)
                ·
                  refine ⟨7881585726079360657943075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21017561936211628421181533 7881585726079360657943075)
                  ·
                    refine ⟨11822378589119040986914613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7881585726079360657943075 11822378589119040986914613)
                    ·
                      refine ⟨1108347992729910092523245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11822378589119040986914613 1108347992729910092523245)
                      ·
                        rfl

theorem cell23_2158500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_2158500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158500 prefixEnd_2158500 := by exact prefixLift 2158500
  have htrace : WordTrace (prefixWord ++ tailWord_2158500) baseStart_2158500 baseEnd_2158500 := by
    simpa [prefixWord, tailWord_2158500, baseEnd_2158500] using wordTrace_append hprefix tailTrace_2158500
  have hstable : (prefixWord ++ tailWord_2158500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158500).length < 2 ^ (prefixWord ++ tailWord_2158500).sum := by decide
  have hdescent : baseEnd_2158500 < baseStart_2158500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158564 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_2158564 : Nat := 118140960795 + 2158564 * 2 ^ 59
def prefixEnd_2158564 : Nat := 4983230072969 + 3 ^ 40 * 2158564 * 2
def baseEnd_2158564 : Nat := 1108380855491797842122951

theorem tailTrace_2158564 : CollatzResearch.WordTrace tailWord_2158564 prefixEnd_2158564 1108380855491797842122951 := by
  unfold tailWord_2158564
  simp only [CollatzResearch.WordTrace]
  refine ⟨39364648475949378113157373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52486197967932504150876497 39364648475949378113157373)
  ·
    refine ⟨14761743178481016792434015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39364648475949378113157373 14761743178481016792434015)
    ·
      refine ⟨22142614767721525188651023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14761743178481016792434015 22142614767721525188651023)
      ·
        refine ⟨33213922151582287782976535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22142614767721525188651023 33213922151582287782976535)
        ·
          refine ⟨49820883227373431674464803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33213922151582287782976535 49820883227373431674464803)
          ·
            refine ⟨74731324841060147511697205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49820883227373431674464803 74731324841060147511697205)
            ·
              refine ⟨7006061703849388829221613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74731324841060147511697205 7006061703849388829221613)
              ·
                refine ⟨2627273138943520810958105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7006061703849388829221613 2627273138943520810958105)
                ·
                  refine ⟨1970454854207640608218579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2627273138943520810958105 1970454854207640608218579)
                  ·
                    refine ⟨2955682281311460912327869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1970454854207640608218579 2955682281311460912327869)
                    ·
                      refine ⟨1108380855491797842122951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2955682281311460912327869 1108380855491797842122951)
                      ·
                        rfl

theorem cell23_2158564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_2158564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158564 prefixEnd_2158564 := by exact prefixLift 2158564
  have htrace : WordTrace (prefixWord ++ tailWord_2158564) baseStart_2158564 baseEnd_2158564 := by
    simpa [prefixWord, tailWord_2158564, baseEnd_2158564] using wordTrace_append hprefix tailTrace_2158564
  have hstable : (prefixWord ++ tailWord_2158564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158564).length < 2 ^ (prefixWord ++ tailWord_2158564).sum := by decide
  have hdescent : baseEnd_2158564 < baseStart_2158564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158587 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 3, 4, 2]
def baseStart_2158587 : Nat := 118140960795 + 2158587 * 2 ^ 59
def prefixEnd_2158587 : Nat := 4983230072969 + 3 ^ 40 * 2158587 * 2
def baseEnd_2158587 : Nat := 1108392665546851252135345

theorem tailTrace_2158587 : CollatzResearch.WordTrace tailWord_2158587 prefixEnd_2158587 1108392665546851252135345 := by
  unfold tailWord_2158587
  simp only [CollatzResearch.WordTrace]
  refine ⟨78730135830815431154402015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52486757220543620769601343 78730135830815431154402015)
  ·
    refine ⟨118095203746223146731603023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78730135830815431154402015 118095203746223146731603023)
    ·
      refine ⟨177142805619334720097404535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118095203746223146731603023 177142805619334720097404535)
      ·
        refine ⟨265714208429002080146106803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177142805619334720097404535 265714208429002080146106803)
        ·
          refine ⟨398571312643503120219160205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265714208429002080146106803 398571312643503120219160205)
          ·
            refine ⟨149464242241313670082185077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 398571312643503120219160205 149464242241313670082185077)
            ·
              refine ⟨14012272710123156570204851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149464242241313670082185077 14012272710123156570204851)
              ·
                refine ⟨21018409065184734855307277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14012272710123156570204851 21018409065184734855307277)
                ·
                  refine ⟨7881903399444275570740229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21018409065184734855307277 7881903399444275570740229)
                  ·
                    refine ⟨1477856887395801669513793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7881903399444275570740229 1477856887395801669513793)
                    ·
                      refine ⟨1108392665546851252135345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1477856887395801669513793 1108392665546851252135345)
                      ·
                        rfl

theorem cell23_2158587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 4, 2].length) (baseStart_2158587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158587 prefixEnd_2158587 := by exact prefixLift 2158587
  have htrace : WordTrace (prefixWord ++ tailWord_2158587) baseStart_2158587 baseEnd_2158587 := by
    simpa [prefixWord, tailWord_2158587, baseEnd_2158587] using wordTrace_append hprefix tailTrace_2158587
  have hstable : (prefixWord ++ tailWord_2158587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158587).length < 2 ^ (prefixWord ++ tailWord_2158587).sum := by decide
  have hdescent : baseEnd_2158587 < baseStart_2158587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158621 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_2158621 : Nat := 118140960795 + 2158621 * 2 ^ 59
def prefixEnd_2158621 : Nat := 4983230072969 + 3 ^ 40 * 2158621 * 2
def baseEnd_2158621 : Nat := 1108410123889104119110189

theorem tailTrace_2158621 : CollatzResearch.WordTrace tailWord_2158621 prefixEnd_2158621 1108410123889104119110189 := by
  unfold tailWord_2158621
  simp only [CollatzResearch.WordTrace]
  refine ⟨78731375912692254961139717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52487583941794836640759811 78731375912692254961139717)
  ·
    refine ⟨14762132983629797805213697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78731375912692254961139717 14762132983629797805213697)
    ·
      refine ⟨11071599737722348353910273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14762132983629797805213697 11071599737722348353910273)
      ·
        refine ⟨8303699803291761265432705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11071599737722348353910273 8303699803291761265432705)
        ·
          refine ⟨6227774852468820949074529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8303699803291761265432705 6227774852468820949074529)
          ·
            refine ⟨4670831139351615711805897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6227774852468820949074529 4670831139351615711805897)
            ·
              refine ⟨3503123354513711783854423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4670831139351615711805897 3503123354513711783854423)
              ·
                refine ⟨5254685031770567675781635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503123354513711783854423 5254685031770567675781635)
                ·
                  refine ⟨7882027547655851513672453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5254685031770567675781635 7882027547655851513672453)
                  ·
                    refine ⟨1477880165185472158813585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7882027547655851513672453 1477880165185472158813585)
                    ·
                      refine ⟨1108410123889104119110189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1477880165185472158813585 1108410123889104119110189)
                      ·
                        rfl

theorem cell23_2158621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_2158621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158621 prefixEnd_2158621 := by exact prefixLift 2158621
  have htrace : WordTrace (prefixWord ++ tailWord_2158621) baseStart_2158621 baseEnd_2158621 := by
    simpa [prefixWord, tailWord_2158621, baseEnd_2158621] using wordTrace_append hprefix tailTrace_2158621
  have hstable : (prefixWord ++ tailWord_2158621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158621).length < 2 ^ (prefixWord ++ tailWord_2158621).sum := by decide
  have hdescent : baseEnd_2158621 < baseStart_2158621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158677 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_2158677 : Nat := 118140960795 + 2158677 * 2 ^ 59
def prefixEnd_2158677 : Nat := 4983230072969 + 3 ^ 40 * 2158677 * 2
def baseEnd_2158677 : Nat := 1108438878805755900009931

theorem tailTrace_2158677 : CollatzResearch.WordTrace tailWord_2158677 prefixEnd_2158677 1108438878805755900009931 := by
  unfold tailWord_2158677
  simp only [CollatzResearch.WordTrace]
  refine ⟨78733418400489376525178285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52488945600326251016785523 78733418400489376525178285)
  ·
    refine ⟨29525031900183516196941857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78733418400489376525178285 29525031900183516196941857)
    ·
      refine ⟨22143773925137637147706393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29525031900183516196941857 22143773925137637147706393)
      ·
        refine ⟨16607830443853227860779795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22143773925137637147706393 16607830443853227860779795)
        ·
          refine ⟨24911745665779841791169693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16607830443853227860779795 24911745665779841791169693)
          ·
            refine ⟨9341904624667440671688635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24911745665779841791169693 9341904624667440671688635)
            ·
              refine ⟨14012856937001161007532953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9341904624667440671688635 14012856937001161007532953)
              ·
                refine ⟨10509642702750870755649715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14012856937001161007532953 10509642702750870755649715)
                ·
                  refine ⟨15764464054126306133474573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10509642702750870755649715 15764464054126306133474573)
                  ·
                    refine ⟨5911674020297364800052965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15764464054126306133474573 5911674020297364800052965)
                    ·
                      refine ⟨1108438878805755900009931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5911674020297364800052965 1108438878805755900009931)
                      ·
                        rfl

theorem cell23_2158677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_2158677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158677 prefixEnd_2158677 := by exact prefixLift 2158677
  have htrace : WordTrace (prefixWord ++ tailWord_2158677) baseStart_2158677 baseEnd_2158677 := by
    simpa [prefixWord, tailWord_2158677, baseEnd_2158677] using wordTrace_append hprefix tailTrace_2158677
  have hstable : (prefixWord ++ tailWord_2158677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158677).length < 2 ^ (prefixWord ++ tailWord_2158677).sum := by decide
  have hdescent : baseEnd_2158677 < baseStart_2158677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2158687 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 5, 4]
def baseStart_2158687 : Nat := 118140960795 + 2158687 * 2 ^ 59
def prefixEnd_2158687 : Nat := 4983230072969 + 3 ^ 40 * 2158687 * 2
def baseEnd_2158687 : Nat := 369481337870766953628295

theorem tailTrace_2158687 : CollatzResearch.WordTrace tailWord_2158687 prefixEnd_2158687 369481337870766953628295 := by
  unfold tailWord_2158687
  simp only [CollatzResearch.WordTrace]
  refine ⟨78733783130453148233042315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52489188753635432155361543 78733783130453148233042315)
  ·
    refine ⟨118100674695679722349563473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78733783130453148233042315 118100674695679722349563473)
    ·
      refine ⟨88575506021759791762172605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118100674695679722349563473 88575506021759791762172605)
      ·
        refine ⟨33215814758159921910814727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88575506021759791762172605 33215814758159921910814727)
        ·
          refine ⟨49823722137239882866222091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33215814758159921910814727 49823722137239882866222091)
          ·
            refine ⟨74735583205859824299333137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49823722137239882866222091 74735583205859824299333137)
            ·
              refine ⟨56051687404394868224499853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74735583205859824299333137 56051687404394868224499853)
              ·
                refine ⟨21019382776648075584187445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56051687404394868224499853 21019382776648075584187445)
                ·
                  refine ⟨1970567135310757086017573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21019382776648075584187445 1970567135310757086017573)
                  ·
                    refine ⟨369481337870766953628295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1970567135310757086017573 369481337870766953628295)
                    ·
                      rfl

theorem cell23_2158687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5, 4].length) (baseStart_2158687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2158687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2158687 prefixEnd_2158687 := by exact prefixLift 2158687
  have htrace : WordTrace (prefixWord ++ tailWord_2158687) baseStart_2158687 baseEnd_2158687 := by
    simpa [prefixWord, tailWord_2158687, baseEnd_2158687] using wordTrace_append hprefix tailTrace_2158687
  have hstable : (prefixWord ++ tailWord_2158687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2158687).length < 2 ^ (prefixWord ++ tailWord_2158687).sum := by decide
  have hdescent : baseEnd_2158687 < baseStart_2158687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2158687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
