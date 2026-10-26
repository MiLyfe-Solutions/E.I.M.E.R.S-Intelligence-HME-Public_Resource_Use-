import V185TrunkScan23Chunk1220

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7235397 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 1, 3, 2]
def baseStart_7235397 : Nat := 118140960795 + 7235397 * 2 ^ 59
def prefixEnd_7235397 : Nat := 4983230072969 + 3 ^ 40 * 7235397 * 2
def baseEnd_7235397 : Nat := 3715236387099133209662521

theorem tailTrace_7235397 : CollatzResearch.WordTrace tailWord_7235397 prefixEnd_7235397 3715236387099133209662521 := by
  unfold tailWord_7235397
  simp only [CollatzResearch.WordTrace]
  refine ⟨263896608568399851273016445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175931072378933234182010963 263896608568399851273016445)
  ·
    refine ⟨98961228213149944227381167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263896608568399851273016445 98961228213149944227381167)
    ·
      refine ⟨148441842319724916341071751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98961228213149944227381167 148441842319724916341071751)
      ·
        refine ⟨222662763479587374511607627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148441842319724916341071751 222662763479587374511607627)
        ·
          refine ⟨333994145219381061767411441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222662763479587374511607627 333994145219381061767411441)
          ·
            refine ⟨250495608914535796325558581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333994145219381061767411441 250495608914535796325558581)
            ·
              refine ⟨23483963335737730905521117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250495608914535796325558581 23483963335737730905521117)
              ·
                refine ⟨8806486250901649089570419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23483963335737730905521117 8806486250901649089570419)
                ·
                  refine ⟨13209729376352473634355629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8806486250901649089570419 13209729376352473634355629)
                  ·
                    refine ⟨4953648516132177612883361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13209729376352473634355629 4953648516132177612883361)
                    ·
                      refine ⟨3715236387099133209662521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4953648516132177612883361 3715236387099133209662521)
                      ·
                        rfl

theorem cell23_7235397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 3, 2].length) (baseStart_7235397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235397 prefixEnd_7235397 := by exact prefixLift 7235397
  have htrace : WordTrace (prefixWord ++ tailWord_7235397) baseStart_7235397 baseEnd_7235397 := by
    simpa [prefixWord, tailWord_7235397, baseEnd_7235397] using wordTrace_append hprefix tailTrace_7235397
  have hstable : (prefixWord ++ tailWord_7235397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235397).length < 2 ^ (prefixWord ++ tailWord_7235397).sum := by decide
  have hdescent : baseEnd_7235397 < baseStart_7235397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235460 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_7235460 : Nat := 118140960795 + 7235460 * 2 ^ 59
def prefixEnd_7235460 : Nat := 4983230072969 + 3 ^ 40 * 7235460 * 2
def baseEnd_7235460 : Nat := 3715268736380366463174731

theorem tailTrace_7235460 : CollatzResearch.WordTrace tailWord_7235460 prefixEnd_7235460 3715268736380366463174731 := by
  unfold tailWord_7235460
  simp only [CollatzResearch.WordTrace]
  refine ⟨131949453183585806516279917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175932604244781075355039889 131949453183585806516279917)
  ·
    refine ⟨49481044943844677443604969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131949453183585806516279917 49481044943844677443604969)
    ·
      refine ⟨37110783707883508082703727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49481044943844677443604969 37110783707883508082703727)
      ·
        refine ⟨55666175561825262124055591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37110783707883508082703727 55666175561825262124055591)
        ·
          refine ⟨83499263342737893186083387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55666175561825262124055591 83499263342737893186083387)
          ·
            refine ⟨125248895014106839779125081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83499263342737893186083387 125248895014106839779125081)
            ·
              refine ⟨93936671260580129834343811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125248895014106839779125081 93936671260580129834343811)
              ·
                refine ⟨140905006890870194751515717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93936671260580129834343811 140905006890870194751515717)
                ·
                  refine ⟨26419688792038161515909197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140905006890870194751515717 26419688792038161515909197)
                  ·
                    refine ⟨9907383297014310568465949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26419688792038161515909197 9907383297014310568465949)
                    ·
                      refine ⟨3715268736380366463174731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9907383297014310568465949 3715268736380366463174731)
                      ·
                        rfl

theorem cell23_7235460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_7235460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235460 prefixEnd_7235460 := by exact prefixLift 7235460
  have htrace : WordTrace (prefixWord ++ tailWord_7235460) baseStart_7235460 baseEnd_7235460 := by
    simpa [prefixWord, tailWord_7235460, baseEnd_7235460] using wordTrace_append hprefix tailTrace_7235460
  have hstable : (prefixWord ++ tailWord_7235460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235460).length < 2 ^ (prefixWord ++ tailWord_7235460).sum := by decide
  have hdescent : baseEnd_7235460 < baseStart_7235460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235473 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_7235473 : Nat := 118140960795 + 7235473 * 2 ^ 59
def prefixEnd_7235473 : Nat := 4983230072969 + 3 ^ 40 * 7235473 * 2
def baseEnd_7235473 : Nat := 3715275411628874912312171

theorem tailTrace_7235473 : CollatzResearch.WordTrace tailWord_7235473 prefixEnd_7235473 3715275411628874912312171 := by
  unfold tailWord_7235473
  simp only [CollatzResearch.WordTrace]
  refine ⟨263899380516124516252783073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175932920344083010835188715 263899380516124516252783073)
  ·
    refine ⟨197924535387093387189587305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263899380516124516252783073 197924535387093387189587305)
    ·
      refine ⟨148443401540320040392190479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197924535387093387189587305 148443401540320040392190479)
      ·
        refine ⟨222665102310480060588285719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148443401540320040392190479 222665102310480060588285719)
        ·
          refine ⟨333997653465720090882428579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222665102310480060588285719 333997653465720090882428579)
          ·
            refine ⟨500996480198580136323642869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333997653465720090882428579 500996480198580136323642869)
            ·
              refine ⟨46968420018616887780341519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 500996480198580136323642869 46968420018616887780341519)
              ·
                refine ⟨70452630027925331670512279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46968420018616887780341519 70452630027925331670512279)
                ·
                  refine ⟨105678945041887997505768419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70452630027925331670512279 105678945041887997505768419)
                  ·
                    refine ⟨158518417562831996258652629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105678945041887997505768419 158518417562831996258652629)
                    ·
                      refine ⟨3715275411628874912312171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158518417562831996258652629 3715275411628874912312171)
                      ·
                        rfl

theorem cell23_7235473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_7235473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235473 prefixEnd_7235473 := by exact prefixLift 7235473
  have htrace : WordTrace (prefixWord ++ tailWord_7235473) baseStart_7235473 baseEnd_7235473 := by
    simpa [prefixWord, tailWord_7235473, baseEnd_7235473] using wordTrace_append hprefix tailTrace_7235473
  have hstable : (prefixWord ++ tailWord_7235473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235473).length < 2 ^ (prefixWord ++ tailWord_7235473).sum := by decide
  have hdescent : baseEnd_7235473 < baseStart_7235473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235493 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_7235493 : Nat := 118140960795 + 7235493 * 2 ^ 59
def prefixEnd_7235493 : Nat := 4983230072969 + 3 ^ 40 * 7235493 * 2
def baseEnd_7235493 : Nat := 1238428560413988278020693

theorem tailTrace_7235493 : CollatzResearch.WordTrace tailWord_7235493 prefixEnd_7235493 1238428560413988278020693 := by
  unfold tailWord_7235493
  simp only [CollatzResearch.WordTrace]
  refine ⟨263900109976052059668511133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175933406650701373112340755 263900109976052059668511133)
  ·
    refine ⟨98962541241019522375691675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263900109976052059668511133 98962541241019522375691675)
    ·
      refine ⟨148443811861529283563537513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98962541241019522375691675 148443811861529283563537513)
      ·
        refine ⟨111332858896146962672653135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148443811861529283563537513 111332858896146962672653135)
        ·
          refine ⟨166999288344220444008979703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111332858896146962672653135 166999288344220444008979703)
          ·
            refine ⟨250498932516330666013469555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166999288344220444008979703 250498932516330666013469555)
            ·
              refine ⟨375748398774495999020204333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250498932516330666013469555 375748398774495999020204333)
              ·
                refine ⟨140905649540435999632576625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375748398774495999020204333 140905649540435999632576625)
                ·
                  refine ⟨105679237155326999724432469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140905649540435999632576625 105679237155326999724432469)
                  ·
                    refine ⟨1238428560413988278020693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105679237155326999724432469 1238428560413988278020693)
                    ·
                      rfl

theorem cell23_7235493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_7235493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235493 prefixEnd_7235493 := by exact prefixLift 7235493
  have htrace : WordTrace (prefixWord ++ tailWord_7235493) baseStart_7235493 baseEnd_7235493 := by
    simpa [prefixWord, tailWord_7235493, baseEnd_7235493] using wordTrace_append hprefix tailTrace_7235493
  have hstable : (prefixWord ++ tailWord_7235493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235493).length < 2 ^ (prefixWord ++ tailWord_7235493).sum := by decide
  have hdescent : baseEnd_7235493 < baseStart_7235493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235517 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_7235517 : Nat := 118140960795 + 7235517 * 2 ^ 59
def prefixEnd_7235517 : Nat := 4983230072969 + 3 ^ 40 * 7235517 * 2
def baseEnd_7235517 : Nat := 3715298004777672740161969

theorem tailTrace_7235517 : CollatzResearch.WordTrace tailWord_7235517 prefixEnd_7235517 3715298004777672740161969 := by
  unfold tailWord_7235517
  simp only [CollatzResearch.WordTrace]
  refine ⟨263900985327965111767384805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175933990218643407844923203 263900985327965111767384805)
  ·
    refine ⟨49481434748993458456384651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 263900985327965111767384805 49481434748993458456384651)
    ·
      refine ⟨74222152123490187684576977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49481434748993458456384651 74222152123490187684576977)
      ·
        refine ⟨55666614092617640763432733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74222152123490187684576977 55666614092617640763432733)
        ·
          refine ⟨20874980284731615286287275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55666614092617640763432733 20874980284731615286287275)
          ·
            refine ⟨31312470427097422929430913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20874980284731615286287275 31312470427097422929430913)
            ·
              refine ⟨23484352820323067197073185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31312470427097422929430913 23484352820323067197073185)
              ·
                refine ⟨17613264615242300397804889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23484352820323067197073185 17613264615242300397804889)
                ·
                  refine ⟨13209948461431725298353667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17613264615242300397804889 13209948461431725298353667)
                  ·
                    refine ⟨19814922692147587947530501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13209948461431725298353667 19814922692147587947530501)
                    ·
                      refine ⟨3715298004777672740161969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19814922692147587947530501 3715298004777672740161969)
                      ·
                        rfl

theorem cell23_7235517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_7235517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235517 prefixEnd_7235517 := by exact prefixLift 7235517
  have htrace : WordTrace (prefixWord ++ tailWord_7235517) baseStart_7235517 baseEnd_7235517 := by
    simpa [prefixWord, tailWord_7235517, baseEnd_7235517] using wordTrace_append hprefix tailTrace_7235517
  have hstable : (prefixWord ++ tailWord_7235517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235517).length < 2 ^ (prefixWord ++ tailWord_7235517).sum := by decide
  have hdescent : baseEnd_7235517 < baseStart_7235517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235548 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 2, 5]
def baseStart_7235548 : Nat := 118140960795 + 7235548 * 2 ^ 59
def prefixEnd_7235548 : Nat := 4983230072969 + 3 ^ 40 * 7235548 * 2
def baseEnd_7235548 : Nat := 1238437974225987372958109

theorem tailTrace_7235548 : CollatzResearch.WordTrace tailWord_7235548 prefixEnd_7235548 1238437974225987372958109 := by
  unfold tailWord_7235548
  simp only [CollatzResearch.WordTrace]
  refine ⟨131951057995426402030881649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175934743993901869374508865 131951057995426402030881649)
  ·
    refine ⟨98963293496569801523161237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131951057995426402030881649 98963293496569801523161237)
    ·
      refine ⟨4638904382651709446398183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98963293496569801523161237 4638904382651709446398183)
      ·
        refine ⟨6958356573977564169597275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4638904382651709446398183 6958356573977564169597275)
        ·
          refine ⟨10437534860966346254395913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6958356573977564169597275 10437534860966346254395913)
          ·
            refine ⟨7828151145724759690796935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10437534860966346254395913 7828151145724759690796935)
            ·
              refine ⟨11742226718587139536195403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7828151145724759690796935 11742226718587139536195403)
              ·
                refine ⟨17613340077880709304293105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11742226718587139536195403 17613340077880709304293105)
                ·
                  refine ⟨13210005058410531978219829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17613340077880709304293105 13210005058410531978219829)
                  ·
                    refine ⟨1238437974225987372958109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13210005058410531978219829 1238437974225987372958109)
                    ·
                      rfl

theorem cell23_7235548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_7235548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235548 prefixEnd_7235548 := by exact prefixLift 7235548
  have htrace : WordTrace (prefixWord ++ tailWord_7235548) baseStart_7235548 baseEnd_7235548 := by
    simpa [prefixWord, tailWord_7235548, baseEnd_7235548] using wordTrace_append hprefix tailTrace_7235548
  have hstable : (prefixWord ++ tailWord_7235548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235548).length < 2 ^ (prefixWord ++ tailWord_7235548).sum := by decide
  have hdescent : baseEnd_7235548 < baseStart_7235548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235567 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 5, 1, 3]
def baseStart_7235567 : Nat := 118140960795 + 7235567 * 2 ^ 59
def prefixEnd_7235567 : Nat := 4983230072969 + 3 ^ 40 * 7235567 * 2
def baseEnd_7235567 : Nat := 3715323678810397544536739

theorem tailTrace_7235567 : CollatzResearch.WordTrace tailWord_7235567 prefixEnd_7235567 3715323678810397544536739 := by
  unfold tailWord_7235567
  simp only [CollatzResearch.WordTrace]
  refine ⟨263902808977783970306704955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175935205985189313537803303 263902808977783970306704955)
  ·
    refine ⟨395854213466675955460057433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263902808977783970306704955 395854213466675955460057433)
    ·
      refine ⟨296890660100006966595043075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395854213466675955460057433 296890660100006966595043075)
      ·
        refine ⟨445335990150010449892564613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296890660100006966595043075 445335990150010449892564613)
        ·
          refine ⟨83500498153126959354855865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445335990150010449892564613 83500498153126959354855865)
          ·
            refine ⟨62625373614845219516141899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83500498153126959354855865 62625373614845219516141899)
            ·
              refine ⟨93938060422267829274212849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62625373614845219516141899 93938060422267829274212849)
              ·
                refine ⟨70453545316700871955659637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93938060422267829274212849 70453545316700871955659637)
                ·
                  refine ⟨6605019873440706745843091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70453545316700871955659637 6605019873440706745843091)
                  ·
                    refine ⟨9907529810161060118764637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6605019873440706745843091 9907529810161060118764637)
                    ·
                      refine ⟨3715323678810397544536739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9907529810161060118764637 3715323678810397544536739)
                      ·
                        rfl

theorem cell23_7235567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 1, 3].length) (baseStart_7235567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235567 prefixEnd_7235567 := by exact prefixLift 7235567
  have htrace : WordTrace (prefixWord ++ tailWord_7235567) baseStart_7235567 baseEnd_7235567 := by
    simpa [prefixWord, tailWord_7235567, baseEnd_7235567] using wordTrace_append hprefix tailTrace_7235567
  have hstable : (prefixWord ++ tailWord_7235567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235567).length < 2 ^ (prefixWord ++ tailWord_7235567).sum := by decide
  have hdescent : baseEnd_7235567 < baseStart_7235567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235654 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_7235654 : Nat := 118140960795 + 7235654 * 2 ^ 59
def prefixEnd_7235654 : Nat := 4983230072969 + 3 ^ 40 * 7235654 * 2
def baseEnd_7235654 : Nat := 3715368351627338704148839

theorem tailTrace_7235654 : CollatzResearch.WordTrace tailWord_7235654 prefixEnd_7235654 3715368351627338704148839 := by
  unfold tailWord_7235654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8247061941514649505160063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 175937321418979189443414677 8247061941514649505160063)
  ·
    refine ⟨12370592912271974257740095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8247061941514649505160063 12370592912271974257740095)
    ·
      refine ⟨18555889368407961386610143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12370592912271974257740095 18555889368407961386610143)
      ·
        refine ⟨27833834052611942079915215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18555889368407961386610143 27833834052611942079915215)
        ·
          refine ⟨41750751078917913119872823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27833834052611942079915215 41750751078917913119872823)
          ·
            refine ⟨62626126618376869679809235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41750751078917913119872823 62626126618376869679809235)
            ·
              refine ⟨93939189927565304519713853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62626126618376869679809235 93939189927565304519713853)
              ·
                refine ⟨35227196222836989194892695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93939189927565304519713853 35227196222836989194892695)
                ·
                  refine ⟨52840794334255483792339043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35227196222836989194892695 52840794334255483792339043)
                  ·
                    refine ⟨79261191501383225688508565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52840794334255483792339043 79261191501383225688508565)
                    ·
                      refine ⟨3715368351627338704148839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79261191501383225688508565 3715368351627338704148839)
                      ·
                        rfl

theorem cell23_7235654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_7235654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235654 prefixEnd_7235654 := by exact prefixLift 7235654
  have htrace : WordTrace (prefixWord ++ tailWord_7235654) baseStart_7235654 baseEnd_7235654 := by
    simpa [prefixWord, tailWord_7235654, baseEnd_7235654] using wordTrace_append hprefix tailTrace_7235654
  have hstable : (prefixWord ++ tailWord_7235654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235654).length < 2 ^ (prefixWord ++ tailWord_7235654).sum := by decide
  have hdescent : baseEnd_7235654 < baseStart_7235654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235657 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 1, 3, 3]
def baseStart_7235657 : Nat := 118140960795 + 7235657 * 2 ^ 59
def prefixEnd_7235657 : Nat := 4983230072969 + 3 ^ 40 * 7235657 * 2
def baseEnd_7235657 : Nat := 3715369892069302192411325

theorem tailTrace_7235657 : CollatzResearch.WordTrace tailWord_7235657 prefixEnd_7235657 3715369892069302192411325 := by
  unfold tailWord_7235657
  simp only [CollatzResearch.WordTrace]
  refine ⟨263906091547457915677481225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175937394364971943784987483 263906091547457915677481225)
  ·
    refine ⟨197929568660593436758110919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263906091547457915677481225 197929568660593436758110919)
    ·
      refine ⟨296894352990890155137166379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197929568660593436758110919 296894352990890155137166379)
      ·
        refine ⟨445341529486335232705749569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296894352990890155137166379 445341529486335232705749569)
        ·
          refine ⟨334006147114751424529312177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445341529486335232705749569 334006147114751424529312177)
          ·
            refine ⟨250504610336063568396984133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334006147114751424529312177 250504610336063568396984133)
            ·
              refine ⟨46969614438011919074434525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250504610336063568396984133 46969614438011919074434525)
              ·
                refine ⟨17613605414254469652912947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46969614438011919074434525 17613605414254469652912947)
                ·
                  refine ⟨26420408121381704479369421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17613605414254469652912947 26420408121381704479369421)
                  ·
                    refine ⟨9907653045518139179763533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26420408121381704479369421 9907653045518139179763533)
                    ·
                      refine ⟨3715369892069302192411325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9907653045518139179763533 3715369892069302192411325)
                      ·
                        rfl

theorem cell23_7235657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 3, 3].length) (baseStart_7235657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235657 prefixEnd_7235657 := by exact prefixLift 7235657
  have htrace : WordTrace (prefixWord ++ tailWord_7235657) baseStart_7235657 baseEnd_7235657 := by
    simpa [prefixWord, tailWord_7235657, baseEnd_7235657] using wordTrace_append hprefix tailTrace_7235657
  have hstable : (prefixWord ++ tailWord_7235657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235657).length < 2 ^ (prefixWord ++ tailWord_7235657).sum := by decide
  have hdescent : baseEnd_7235657 < baseStart_7235657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235735 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 1, 3, 2]
def baseStart_7235735 : Nat := 118140960795 + 7235735 * 2 ^ 59
def prefixEnd_7235735 : Nat := 4983230072969 + 3 ^ 40 * 7235735 * 2
def baseEnd_7235735 : Nat := 3715409943560352887235967

theorem tailTrace_7235735 : CollatzResearch.WordTrace tailWord_7235735 prefixEnd_7235735 3715409943560352887235967 := by
  unfold tailWord_7235735
  simp only [CollatzResearch.WordTrace]
  refine ⟨263908936441175334998820659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175939290960783556665880439 263908936441175334998820659)
  ·
    refine ⟨395863404661763002498230989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263908936441175334998820659 395863404661763002498230989)
    ·
      refine ⟨148448776748161125936836621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395863404661763002498230989 148448776748161125936836621)
      ·
        refine ⟨55668291280560422226313733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148448776748161125936836621 55668291280560422226313733)
        ·
          refine ⟨10437804615105079167433825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55668291280560422226313733 10437804615105079167433825)
          ·
            refine ⟨7828353461328809375575369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10437804615105079167433825 7828353461328809375575369)
            ·
              refine ⟨5871265095996607031681527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7828353461328809375575369 5871265095996607031681527)
              ·
                refine ⟨8806897643994910547522291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871265095996607031681527 8806897643994910547522291)
                ·
                  refine ⟨13210346465992365821283437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8806897643994910547522291 13210346465992365821283437)
                  ·
                    refine ⟨4953879924747137182981289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13210346465992365821283437 4953879924747137182981289)
                    ·
                      refine ⟨3715409943560352887235967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4953879924747137182981289 3715409943560352887235967)
                      ·
                        rfl

theorem cell23_7235735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_7235735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235735 prefixEnd_7235735 := by exact prefixLift 7235735
  have htrace : WordTrace (prefixWord ++ tailWord_7235735) baseStart_7235735 baseEnd_7235735 := by
    simpa [prefixWord, tailWord_7235735, baseEnd_7235735] using wordTrace_append hprefix tailTrace_7235735
  have hstable : (prefixWord ++ tailWord_7235735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235735).length < 2 ^ (prefixWord ++ tailWord_7235735).sum := by decide
  have hdescent : baseEnd_7235735 < baseStart_7235735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235742 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 2, 1, 3]
def baseStart_7235742 : Nat := 118140960795 + 7235742 * 2 ^ 59
def prefixEnd_7235742 : Nat := 4983230072969 + 3 ^ 40 * 7235742 * 2
def baseEnd_7235742 : Nat := 3715413537924934359848435

theorem tailTrace_7235742 : CollatzResearch.WordTrace tailWord_7235742 prefixEnd_7235742 3715413537924934359848435 := by
  unfold tailWord_7235742
  simp only [CollatzResearch.WordTrace]
  refine ⟨32988648969018746899290685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175939461168099983462883653 32988648969018746899290685)
  ·
    refine ⟨12370743363382030087234007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32988648969018746899290685 12370743363382030087234007)
    ·
      refine ⟨18556115045073045130851011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12370743363382030087234007 18556115045073045130851011)
      ·
        refine ⟨27834172567609567696276517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18556115045073045130851011 27834172567609567696276517)
        ·
          refine ⟨5218907356426793943051847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27834172567609567696276517 5218907356426793943051847)
          ·
            refine ⟨7828361034640190914577771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5218907356426793943051847 7828361034640190914577771)
            ·
              refine ⟨11742541551960286371866657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7828361034640190914577771 11742541551960286371866657)
              ·
                refine ⟨8806906163970214778899993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11742541551960286371866657 8806906163970214778899993)
                ·
                  refine ⟨6605179622977661084174995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8806906163970214778899993 6605179622977661084174995)
                  ·
                    refine ⟨9907769434466491626262493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6605179622977661084174995 9907769434466491626262493)
                    ·
                      refine ⟨3715413537924934359848435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9907769434466491626262493 3715413537924934359848435)
                      ·
                        rfl

theorem cell23_7235742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_7235742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235742 prefixEnd_7235742 := by exact prefixLift 7235742
  have htrace : WordTrace (prefixWord ++ tailWord_7235742) baseStart_7235742 baseEnd_7235742 := by
    simpa [prefixWord, tailWord_7235742, baseEnd_7235742] using wordTrace_append hprefix tailTrace_7235742
  have hstable : (prefixWord ++ tailWord_7235742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235742).length < 2 ^ (prefixWord ++ tailWord_7235742).sum := by decide
  have hdescent : baseEnd_7235742 < baseStart_7235742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235748 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 4, 2, 2]
def baseStart_7235748 : Nat := 118140960795 + 7235748 * 2 ^ 59
def prefixEnd_7235748 : Nat := 4983230072969 + 3 ^ 40 * 7235748 * 2
def baseEnd_7235748 : Nat := 3715416618808861336373407

theorem tailTrace_7235748 : CollatzResearch.WordTrace tailWord_7235748 prefixEnd_7235748 3715416618808861336373407 := by
  unfold tailWord_7235748
  simp only [CollatzResearch.WordTrace]
  refine ⟨131954705295064119109521949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175939607060085492146029265 131954705295064119109521949)
  ·
    refine ⟨49483014485649044666070731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131954705295064119109521949 49483014485649044666070731)
    ·
      refine ⟨74224521728473566999106097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49483014485649044666070731 74224521728473566999106097)
      ·
        refine ⟨55668391296355175249329573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74224521728473566999106097 55668391296355175249329573)
        ·
          refine ⟨10437823368066595359249295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55668391296355175249329573 10437823368066595359249295)
          ·
            refine ⟨15656735052099893038873943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10437823368066595359249295 15656735052099893038873943)
            ·
              refine ⟨23485102578149839558310915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15656735052099893038873943 23485102578149839558310915)
              ·
                refine ⟨35227653867224759337466373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23485102578149839558310915 35227653867224759337466373)
                ·
                  refine ⟨6605185100104642375774945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35227653867224759337466373 6605185100104642375774945)
                  ·
                    refine ⟨4953888825078481781831209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6605185100104642375774945 4953888825078481781831209)
                    ·
                      refine ⟨3715416618808861336373407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4953888825078481781831209 3715416618808861336373407)
                      ·
                        rfl

theorem cell23_7235748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_7235748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235748 prefixEnd_7235748 := by exact prefixLift 7235748
  have htrace : WordTrace (prefixWord ++ tailWord_7235748) baseStart_7235748 baseEnd_7235748 := by
    simpa [prefixWord, tailWord_7235748, baseEnd_7235748] using wordTrace_append hprefix tailTrace_7235748
  have hstable : (prefixWord ++ tailWord_7235748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235748).length < 2 ^ (prefixWord ++ tailWord_7235748).sum := by decide
  have hdescent : baseEnd_7235748 < baseStart_7235748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235765 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_7235765 : Nat := 118140960795 + 7235765 * 2 ^ 59
def prefixEnd_7235765 : Nat := 4983230072969 + 3 ^ 40 * 7235765 * 2
def baseEnd_7235765 : Nat := 3715425347979987769860829

theorem tailTrace_7235765 : CollatzResearch.WordTrace tailWord_7235765 prefixEnd_7235765 3715425347979987769860829 := by
  unfold tailWord_7235765
  simp only [CollatzResearch.WordTrace]
  refine ⟨263910030631066650122412749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175940020420711100081608499 263910030631066650122412749)
  ·
    refine ⟨98966261486649993795904781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263910030631066650122412749 98966261486649993795904781)
    ·
      refine ⟨37112348057493747673464293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98966261486649993795904781 37112348057493747673464293)
      ·
        refine ⟨6958565260780077688774555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37112348057493747673464293 6958565260780077688774555)
        ·
          refine ⟨10437847891170116533161833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6958565260780077688774555 10437847891170116533161833)
          ·
            refine ⟨7828385918377587399871375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10437847891170116533161833 7828385918377587399871375)
            ·
              refine ⟨11742578877566381099807063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7828385918377587399871375 11742578877566381099807063)
              ·
                refine ⟨17613868316349571649710595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11742578877566381099807063 17613868316349571649710595)
                ·
                  refine ⟨26420802474524357474565893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17613868316349571649710595 26420802474524357474565893)
                  ·
                    refine ⟨4953900463973317026481105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26420802474524357474565893 4953900463973317026481105)
                    ·
                      refine ⟨3715425347979987769860829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4953900463973317026481105 3715425347979987769860829)
                      ·
                        rfl

theorem cell23_7235765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_7235765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235765 prefixEnd_7235765 := by exact prefixLift 7235765
  have htrace : WordTrace (prefixWord ++ tailWord_7235765) baseStart_7235765 baseEnd_7235765 := by
    simpa [prefixWord, tailWord_7235765, baseEnd_7235765] using wordTrace_append hprefix tailTrace_7235765
  have hstable : (prefixWord ++ tailWord_7235765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235765).length < 2 ^ (prefixWord ++ tailWord_7235765).sum := by decide
  have hdescent : baseEnd_7235765 < baseStart_7235765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235767 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 1, 7]
def baseStart_7235767 : Nat := 118140960795 + 7235767 * 2 ^ 59
def prefixEnd_7235767 : Nat := 4983230072969 + 3 ^ 40 * 7235767 * 2
def baseEnd_7235767 : Nat := 1238475458313765587345273

theorem tailTrace_7235767 : CollatzResearch.WordTrace tailWord_7235767 prefixEnd_7235767 1238475458313765587345273 := by
  unfold tailWord_7235767
  simp only [CollatzResearch.WordTrace]
  refine ⟨263910103577059404463985555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175940069051372936309323703 263910103577059404463985555)
  ·
    refine ⟨395865155365589106695978333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263910103577059404463985555 395865155365589106695978333)
    ·
      refine ⟨148449433262095915010991875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395865155365589106695978333 148449433262095915010991875)
      ·
        refine ⟨222674149893143872516487813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148449433262095915010991875 222674149893143872516487813)
        ·
          refine ⟨41751403104964476096841465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222674149893143872516487813 41751403104964476096841465)
          ·
            refine ⟨31313552328723357072631099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41751403104964476096841465 31313552328723357072631099)
            ·
              refine ⟨46970328493085035608946649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31313552328723357072631099 46970328493085035608946649)
              ·
                refine ⟨35227746369813776706709987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46970328493085035608946649 35227746369813776706709987)
                ·
                  refine ⟨52841619554720665060064981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35227746369813776706709987 52841619554720665060064981)
                  ·
                    refine ⟨1238475458313765587345273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52841619554720665060064981 1238475458313765587345273)
                    ·
                      rfl

theorem cell23_7235767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_7235767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235767 prefixEnd_7235767 := by exact prefixLift 7235767
  have htrace : WordTrace (prefixWord ++ tailWord_7235767) baseStart_7235767 baseEnd_7235767 := by
    simpa [prefixWord, tailWord_7235767, baseEnd_7235767] using wordTrace_append hprefix tailTrace_7235767
  have hstable : (prefixWord ++ tailWord_7235767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235767).length < 2 ^ (prefixWord ++ tailWord_7235767).sum := by decide
  have hdescent : baseEnd_7235767 < baseStart_7235767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235787 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 4]
def baseStart_7235787 : Nat := 118140960795 + 7235787 * 2 ^ 59
def prefixEnd_7235787 : Nat := 4983230072969 + 3 ^ 40 * 7235787 * 2
def baseEnd_7235787 : Nat := 3715436644554386683785727

theorem tailTrace_7235787 : CollatzResearch.WordTrace tailWord_7235787 prefixEnd_7235787 3715436644554386683785727 := by
  unfold tailWord_7235787
  simp only [CollatzResearch.WordTrace]
  refine ⟨263910833036986947879713615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175940555357991298586475743 263910833036986947879713615)
  ·
    refine ⟨395866249555480421819570423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263910833036986947879713615 395866249555480421819570423)
    ·
      refine ⟨593799374333220632729355635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395866249555480421819570423 593799374333220632729355635)
      ·
        refine ⟨890699061499830949094033453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593799374333220632729355635 890699061499830949094033453)
        ·
          refine ⟨334012148062436605910262545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 890699061499830949094033453 334012148062436605910262545)
          ·
            refine ⟨250509111046827454432696909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334012148062436605910262545 250509111046827454432696909)
            ·
              refine ⟨93940916642560295412261341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250509111046827454432696909 93940916642560295412261341)
              ·
                refine ⟨35227843740960110779598003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93940916642560295412261341 35227843740960110779598003)
                ·
                  refine ⟨52841765611440166169397005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35227843740960110779598003 52841765611440166169397005)
                  ·
                    refine ⟨19815662104290062313523877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52841765611440166169397005 19815662104290062313523877)
                    ·
                      refine ⟨3715436644554386683785727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19815662104290062313523877 3715436644554386683785727)
                      ·
                        rfl

theorem cell23_7235787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 3, 4].length) (baseStart_7235787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235787 prefixEnd_7235787 := by exact prefixLift 7235787
  have htrace : WordTrace (prefixWord ++ tailWord_7235787) baseStart_7235787 baseEnd_7235787 := by
    simpa [prefixWord, tailWord_7235787, baseEnd_7235787] using wordTrace_append hprefix tailTrace_7235787
  have hstable : (prefixWord ++ tailWord_7235787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235787).length < 2 ^ (prefixWord ++ tailWord_7235787).sum := by decide
  have hdescent : baseEnd_7235787 < baseStart_7235787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235811 : List Nat := [1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7235811 : Nat := 118140960795 + 7235811 * 2 ^ 59
def prefixEnd_7235811 : Nat := 4983230072969 + 3 ^ 40 * 7235811 * 2
def baseEnd_7235811 : Nat := 3715448968090094589885617

theorem tailTrace_7235811 : CollatzResearch.WordTrace tailWord_7235811 prefixEnd_7235811 3715448968090094589885617 := by
  unfold tailWord_7235811
  simp only [CollatzResearch.WordTrace]
  refine ⟨263911708388899999978587287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175941138925933333319058191 263911708388899999978587287)
  ·
    refine ⟨395867562583349999967880931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263911708388899999978587287 395867562583349999967880931)
    ·
      refine ⟨593801343875024999951821397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395867562583349999967880931 593801343875024999951821397)
      ·
        refine ⟨6958609498535449218185407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 593801343875024999951821397 6958609498535449218185407)
        ·
          refine ⟨10437914247803173827278111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6958609498535449218185407 10437914247803173827278111)
          ·
            refine ⟨15656871371704760740917167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10437914247803173827278111 15656871371704760740917167)
            ·
              refine ⟨23485307057557141111375751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15656871371704760740917167 23485307057557141111375751)
              ·
                refine ⟨35227960586335711667063627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23485307057557141111375751 35227960586335711667063627)
                ·
                  refine ⟨52841940879503567500595441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35227960586335711667063627 52841940879503567500595441)
                  ·
                    refine ⟨39631455659627675625446581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52841940879503567500595441 39631455659627675625446581)
                    ·
                      refine ⟨3715448968090094589885617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39631455659627675625446581 3715448968090094589885617)
                      ·
                        rfl

theorem cell23_7235811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7235811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235811 prefixEnd_7235811 := by exact prefixLift 7235811
  have htrace : WordTrace (prefixWord ++ tailWord_7235811) baseStart_7235811 baseEnd_7235811 := by
    simpa [prefixWord, tailWord_7235811, baseEnd_7235811] using wordTrace_append hprefix tailTrace_7235811
  have hstable : (prefixWord ++ tailWord_7235811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235811).length < 2 ^ (prefixWord ++ tailWord_7235811).sum := by decide
  have hdescent : baseEnd_7235811 < baseStart_7235811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235841 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_7235841 : Nat := 118140960795 + 7235841 * 2 ^ 59
def prefixEnd_7235841 : Nat := 4983230072969 + 3 ^ 40 * 7235841 * 2
def baseEnd_7235841 : Nat := 3715464372509729472510479

theorem tailTrace_7235841 : CollatzResearch.WordTrace tailWord_7235841 prefixEnd_7235841 3715464372509729472510479 := by
  unfold tailWord_7235841
  simp only [CollatzResearch.WordTrace]
  refine ⟨263912802578791315102179377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175941868385860876734786251 263912802578791315102179377)
  ·
    refine ⟨197934601934093486326634533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263912802578791315102179377 197934601934093486326634533)
    ·
      refine ⟨37112737862642528686243975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197934601934093486326634533 37112737862642528686243975)
      ·
        refine ⟨55669106793963793029365963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37112737862642528686243975 55669106793963793029365963)
        ·
          refine ⟨83503660190945689544048945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55669106793963793029365963 83503660190945689544048945)
          ·
            refine ⟨62627745143209267158036709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83503660190945689544048945 62627745143209267158036709)
            ·
              refine ⟨11742702214351737592131883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62627745143209267158036709 11742702214351737592131883)
              ·
                refine ⟨17614053321527606388197825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11742702214351737592131883 17614053321527606388197825)
                ·
                  refine ⟨13210539991145704791148369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17614053321527606388197825 13210539991145704791148369)
                  ·
                    refine ⟨9907904993359278593361277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13210539991145704791148369 9907904993359278593361277)
                    ·
                      refine ⟨3715464372509729472510479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9907904993359278593361277 3715464372509729472510479)
                      ·
                        rfl

theorem cell23_7235841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_7235841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235841 prefixEnd_7235841 := by exact prefixLift 7235841
  have htrace : WordTrace (prefixWord ++ tailWord_7235841) baseStart_7235841 baseEnd_7235841 := by
    simpa [prefixWord, tailWord_7235841, baseEnd_7235841] using wordTrace_append hprefix tailTrace_7235841
  have hstable : (prefixWord ++ tailWord_7235841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235841).length < 2 ^ (prefixWord ++ tailWord_7235841).sum := by decide
  have hdescent : baseEnd_7235841 < baseStart_7235841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235898 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2]
def baseStart_7235898 : Nat := 118140960795 + 7235898 * 2 ^ 59
def prefixEnd_7235898 : Nat := 4983230072969 + 3 ^ 40 * 7235898 * 2
def baseEnd_7235898 : Nat := 3715493640907035749497717

theorem tailTrace_7235898 : CollatzResearch.WordTrace tailWord_7235898 prefixEnd_7235898 3715493640907035749497717 := by
  unfold tailWord_7235898
  simp only [CollatzResearch.WordTrace]
  refine ⟨65978720384896203459251087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175943254359723209224669565 65978720384896203459251087)
  ·
    refine ⟨98968080577344305188876631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65978720384896203459251087 98968080577344305188876631)
    ·
      refine ⟨148452120866016457783314947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98968080577344305188876631 148452120866016457783314947)
      ·
        refine ⟨222678181299024686674972421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148452120866016457783314947 222678181299024686674972421)
        ·
          refine ⟨41752158993567128751557329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222678181299024686674972421 41752158993567128751557329)
          ·
            refine ⟨31314119245175346563667997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41752158993567128751557329 31314119245175346563667997)
            ·
              refine ⟨11742794716940754961375499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31314119245175346563667997 11742794716940754961375499)
              ·
                refine ⟨17614192075411132442063249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11742794716940754961375499 17614192075411132442063249)
                ·
                  refine ⟨13210644056558349331547437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17614192075411132442063249 13210644056558349331547437)
                  ·
                    refine ⟨4953991521209380999330289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13210644056558349331547437 4953991521209380999330289)
                    ·
                      refine ⟨3715493640907035749497717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4953991521209380999330289 3715493640907035749497717)
                      ·
                        rfl

theorem cell23_7235898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 3, 2].length) (baseStart_7235898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235898 prefixEnd_7235898 := by exact prefixLift 7235898
  have htrace : WordTrace (prefixWord ++ tailWord_7235898) baseStart_7235898 baseEnd_7235898 := by
    simpa [prefixWord, tailWord_7235898, baseEnd_7235898] using wordTrace_append hprefix tailTrace_7235898
  have hstable : (prefixWord ++ tailWord_7235898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235898).length < 2 ^ (prefixWord ++ tailWord_7235898).sum := by decide
  have hdescent : baseEnd_7235898 < baseStart_7235898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235911 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_7235911 : Nat := 118140960795 + 7235911 * 2 ^ 59
def prefixEnd_7235911 : Nat := 4983230072969 + 3 ^ 40 * 7235911 * 2
def baseEnd_7235911 : Nat := 3715500316155544198635157

theorem tailTrace_7235911 : CollatzResearch.WordTrace tailWord_7235911 prefixEnd_7235911 3715500316155544198635157 := by
  unfold tailWord_7235911
  simp only [CollatzResearch.WordTrace]
  refine ⟨263915355688537717057227587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175943570459025144704818391 263915355688537717057227587)
  ·
    refine ⟨395873033532806575585841381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263915355688537717057227587 395873033532806575585841381)
    ·
      refine ⟨74226193787401232922345259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 395873033532806575585841381 74226193787401232922345259)
      ·
        refine ⟨111339290681101849383517889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74226193787401232922345259 111339290681101849383517889)
        ·
          refine ⟨83504468010826387037638417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111339290681101849383517889 83504468010826387037638417)
          ·
            refine ⟨62628351008119790278228813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83504468010826387037638417 62628351008119790278228813)
            ·
              refine ⟨23485631628044921354335805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62628351008119790278228813 23485631628044921354335805)
              ·
                refine ⟨8807111860516845507875927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23485631628044921354335805 8807111860516845507875927)
                ·
                  refine ⟨13210667790775268261813891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8807111860516845507875927 13210667790775268261813891)
                  ·
                    refine ⟨19816001686162902392720837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13210667790775268261813891 19816001686162902392720837)
                    ·
                      refine ⟨3715500316155544198635157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19816001686162902392720837 3715500316155544198635157)
                      ·
                        rfl

theorem cell23_7235911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_7235911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235911 prefixEnd_7235911 := by exact prefixLift 7235911
  have htrace : WordTrace (prefixWord ++ tailWord_7235911) baseStart_7235911 baseEnd_7235911 := by
    simpa [prefixWord, tailWord_7235911, baseEnd_7235911] using wordTrace_append hprefix tailTrace_7235911
  have hstable : (prefixWord ++ tailWord_7235911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235911).length < 2 ^ (prefixWord ++ tailWord_7235911).sum := by decide
  have hdescent : baseEnd_7235911 < baseStart_7235911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235921 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 4, 4]
def baseStart_7235921 : Nat := 118140960795 + 7235921 * 2 ^ 59
def prefixEnd_7235921 : Nat := 4983230072969 + 3 ^ 40 * 7235921 * 2
def baseEnd_7235921 : Nat := 1238501816987363053170037

theorem tailTrace_7235921 : CollatzResearch.WordTrace tailWord_7235921 prefixEnd_7235921 1238501816987363053170037 := by
  unfold tailWord_7235921
  simp only [CollatzResearch.WordTrace]
  refine ⟨263915720418501488765091617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175943813612334325843394411 263915720418501488765091617)
  ·
    refine ⟨197936790313876116573818713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263915720418501488765091617 197936790313876116573818713)
    ·
      refine ⟨148452592735407087430364035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197936790313876116573818713 148452592735407087430364035)
      ·
        refine ⟨222678889103110631145546053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148452592735407087430364035 222678889103110631145546053)
        ·
          refine ⟨41752291706833243339789885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222678889103110631145546053 41752291706833243339789885)
          ·
            refine ⟨15657109390062466252421207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41752291706833243339789885 15657109390062466252421207)
            ·
              refine ⟨23485664085093699378631811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15657109390062466252421207 23485664085093699378631811)
              ·
                refine ⟨35228496127640549067947717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23485664085093699378631811 35228496127640549067947717)
                ·
                  refine ⟨6605343023932602950240197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35228496127640549067947717 6605343023932602950240197)
                  ·
                    refine ⟨1238501816987363053170037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6605343023932602950240197 1238501816987363053170037)
                    ·
                      rfl

theorem cell23_7235921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_7235921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235921 prefixEnd_7235921 := by exact prefixLift 7235921
  have htrace : WordTrace (prefixWord ++ tailWord_7235921) baseStart_7235921 baseEnd_7235921 := by
    simpa [prefixWord, tailWord_7235921, baseEnd_7235921] using wordTrace_append hprefix tailTrace_7235921
  have hstable : (prefixWord ++ tailWord_7235921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235921).length < 2 ^ (prefixWord ++ tailWord_7235921).sum := by decide
  have hdescent : baseEnd_7235921 < baseStart_7235921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235938 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_7235938 : Nat := 118140960795 + 7235938 * 2 ^ 59
def prefixEnd_7235938 : Nat := 4983230072969 + 3 ^ 40 * 7235938 * 2
def baseEnd_7235938 : Nat := 1238504726711071864332511

theorem tailTrace_7235938 : CollatzResearch.WordTrace tailWord_7235938 prefixEnd_7235938 1238504726711071864332511 := by
  unfold tailWord_7235938
  simp only [CollatzResearch.WordTrace]
  refine ⟨65979085114859975167115117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175944226972959933778973645 65979085114859975167115117)
  ·
    refine ⟨24742156918072490687668169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65979085114859975167115117 24742156918072490687668169)
    ·
      refine ⟨18556617688554368015751127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24742156918072490687668169 18556617688554368015751127)
      ·
        refine ⟨27834926532831552023626691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18556617688554368015751127 27834926532831552023626691)
        ·
          refine ⟨41752389799247328035440037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27834926532831552023626691 41752389799247328035440037)
          ·
            refine ⟨7828573087358874006645007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41752389799247328035440037 7828573087358874006645007)
            ·
              refine ⟨11742859631038311009967511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7828573087358874006645007 11742859631038311009967511)
              ·
                refine ⟨17614289446557466514951267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11742859631038311009967511 17614289446557466514951267)
                ·
                  refine ⟨26421434169836199772426901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17614289446557466514951267 26421434169836199772426901)
                  ·
                    refine ⟨1238504726711071864332511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26421434169836199772426901 1238504726711071864332511)
                    ·
                      rfl

theorem cell23_7235938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_7235938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235938 prefixEnd_7235938 := by exact prefixLift 7235938
  have htrace : WordTrace (prefixWord ++ tailWord_7235938) baseStart_7235938 baseEnd_7235938 := by
    simpa [prefixWord, tailWord_7235938, baseEnd_7235938] using wordTrace_append hprefix tailTrace_7235938
  have hstable : (prefixWord ++ tailWord_7235938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235938).length < 2 ^ (prefixWord ++ tailWord_7235938).sum := by decide
  have hdescent : baseEnd_7235938 < baseStart_7235938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7235941 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 4]
def baseStart_7235941 : Nat := 118140960795 + 7235941 * 2 ^ 59
def prefixEnd_7235941 : Nat := 4983230072969 + 3 ^ 40 * 7235941 * 2
def baseEnd_7235941 : Nat := 3715515720575179081260019

theorem tailTrace_7235941 : CollatzResearch.WordTrace tailWord_7235941 prefixEnd_7235941 3715515720575179081260019 := by
  unfold tailWord_7235941
  simp only [CollatzResearch.WordTrace]
  refine ⟨263916449878429032180819677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175944299918952688120546451 263916449878429032180819677)
  ·
    refine ⟨98968668704410887067807379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263916449878429032180819677 98968668704410887067807379)
    ·
      refine ⟨148453003056616330601711069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98968668704410887067807379 148453003056616330601711069)
      ·
        refine ⟨55669876146231123975641651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148453003056616330601711069 55669876146231123975641651)
        ·
          refine ⟨83504814219346685963462477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55669876146231123975641651 83504814219346685963462477)
          ·
            refine ⟨31314305332255007236298429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83504814219346685963462477 31314305332255007236298429)
            ·
              refine ⟨11742864499595627713611911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31314305332255007236298429 11742864499595627713611911)
              ·
                refine ⟨17614296749393441570417867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11742864499595627713611911 17614296749393441570417867)
                ·
                  refine ⟨26421445124090162355626801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17614296749393441570417867 26421445124090162355626801)
                  ·
                    refine ⟨19816083843067621766720101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26421445124090162355626801 19816083843067621766720101)
                    ·
                      refine ⟨3715515720575179081260019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19816083843067621766720101 3715515720575179081260019)
                      ·
                        rfl

theorem cell23_7235941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_7235941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7235941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7235941 prefixEnd_7235941 := by exact prefixLift 7235941
  have htrace : WordTrace (prefixWord ++ tailWord_7235941) baseStart_7235941 baseEnd_7235941 := by
    simpa [prefixWord, tailWord_7235941, baseEnd_7235941] using wordTrace_append hprefix tailTrace_7235941
  have hstable : (prefixWord ++ tailWord_7235941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7235941).length < 2 ^ (prefixWord ++ tailWord_7235941).sum := by decide
  have hdescent : baseEnd_7235941 < baseStart_7235941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7235941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236018 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2]
def baseStart_7236018 : Nat := 118140960795 + 7236018 * 2 ^ 59
def prefixEnd_7236018 : Nat := 4983230072969 + 3 ^ 40 * 7236018 * 2
def baseEnd_7236018 : Nat := 3715555258585575279997165

theorem tailTrace_7236018 : CollatzResearch.WordTrace tailWord_7236018 prefixEnd_7236018 3715555258585575279997165 := by
  unfold tailWord_7236018
  simp only [CollatzResearch.WordTrace]
  refine ⟨65979814574787518582843177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175946172199433382887581805 65979814574787518582843177)
  ·
    refine ⟨49484860931090638937132383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65979814574787518582843177 49484860931090638937132383)
    ·
      refine ⟨74227291396635958405698575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49484860931090638937132383 74227291396635958405698575)
      ·
        refine ⟨111340937094953937608547863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74227291396635958405698575 111340937094953937608547863)
        ·
          refine ⟨167011405642430906412821795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111340937094953937608547863 167011405642430906412821795)
          ·
            refine ⟨250517108463646359619232693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167011405642430906412821795 250517108463646359619232693)
            ·
              refine ⟨23485978918466846214303065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250517108463646359619232693 23485978918466846214303065)
              ·
                refine ⟨17614484188850134660727299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23485978918466846214303065 17614484188850134660727299)
                ·
                  refine ⟨26421726283275201991090949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17614484188850134660727299 26421726283275201991090949)
                  ·
                    refine ⟨4954073678114100373329553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26421726283275201991090949 4954073678114100373329553)
                    ·
                      refine ⟨3715555258585575279997165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954073678114100373329553 3715555258585575279997165)
                      ·
                        rfl

theorem cell23_7236018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_7236018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236018 prefixEnd_7236018 := by exact prefixLift 7236018
  have htrace : WordTrace (prefixWord ++ tailWord_7236018) baseStart_7236018 baseEnd_7236018 := by
    simpa [prefixWord, tailWord_7236018, baseEnd_7236018] using wordTrace_append hprefix tailTrace_7236018
  have hstable : (prefixWord ++ tailWord_7236018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236018).length < 2 ^ (prefixWord ++ tailWord_7236018).sum := by decide
  have hdescent : baseEnd_7236018 < baseStart_7236018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236052 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_7236052 : Nat := 118140960795 + 7236052 * 2 ^ 59
def prefixEnd_7236052 : Nat := 4983230072969 + 3 ^ 40 * 7236052 * 2
def baseEnd_7236052 : Nat := 3715572716927828146972009

theorem tailTrace_7236052 : CollatzResearch.WordTrace tailWord_7236052 prefixEnd_7236052 3715572716927828146972009 := by
  unfold tailWord_7236052
  simp only [CollatzResearch.WordTrace]
  refine ⟨131960249190513449069055205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175946998920684598758740273 131960249190513449069055205)
  ·
    refine ⟨24742546723221271700447851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131960249190513449069055205 24742546723221271700447851)
    ·
      refine ⟨37113820084831907550671777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24742546723221271700447851 37113820084831907550671777)
      ·
        refine ⟨27835365063623930663003833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37113820084831907550671777 27835365063623930663003833)
        ·
          refine ⟨20876523797717947997252875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27835365063623930663003833 20876523797717947997252875)
          ·
            refine ⟨31314785696576921995879313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20876523797717947997252875 31314785696576921995879313)
            ·
              refine ⟨23486089272432691496909485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31314785696576921995879313 23486089272432691496909485)
              ·
                refine ⟨8807283477162259311341057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23486089272432691496909485 8807283477162259311341057)
                ·
                  refine ⟨6605462607871694483505793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8807283477162259311341057 6605462607871694483505793)
                  ·
                    refine ⟨4954096955903770862629345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6605462607871694483505793 4954096955903770862629345)
                    ·
                      refine ⟨3715572716927828146972009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954096955903770862629345 3715572716927828146972009)
                      ·
                        rfl

theorem cell23_7236052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_7236052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236052 prefixEnd_7236052 := by exact prefixLift 7236052
  have htrace : WordTrace (prefixWord ++ tailWord_7236052) baseStart_7236052 baseEnd_7236052 := by
    simpa [prefixWord, tailWord_7236052, baseEnd_7236052] using wordTrace_append hprefix tailTrace_7236052
  have hstable : (prefixWord ++ tailWord_7236052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236052).length < 2 ^ (prefixWord ++ tailWord_7236052).sum := by decide
  have hdescent : baseEnd_7236052 < baseStart_7236052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236071 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 1, 7]
def baseStart_7236071 : Nat := 118140960795 + 7236071 * 2 ^ 59
def prefixEnd_7236071 : Nat := 4983230072969 + 3 ^ 40 * 7236071 * 2
def baseEnd_7236071 : Nat := 1238527491020087857544807

theorem tailTrace_7236071 : CollatzResearch.WordTrace tailWord_7236071 prefixEnd_7236071 1238527491020087857544807 := by
  unfold tailWord_7236071
  simp only [CollatzResearch.WordTrace]
  refine ⟨263921191367958064383052067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175947460911972042922034711 263921191367958064383052067)
  ·
    refine ⟨395881787051937096574578101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263921191367958064383052067 395881787051937096574578101)
    ·
      refine ⟨37113917536119102803866697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 395881787051937096574578101 37113917536119102803866697)
      ·
        refine ⟨27835438152089327102900023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37113917536119102803866697 27835438152089327102900023)
        ·
          refine ⟨41753157228133990654350035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27835438152089327102900023 41753157228133990654350035)
          ·
            refine ⟨62629735842200985981525053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41753157228133990654350035 62629735842200985981525053)
            ·
              refine ⟨23486150940825369743071895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62629735842200985981525053 23486150940825369743071895)
              ·
                refine ⟨35229226411238054614607843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23486150940825369743071895 35229226411238054614607843)
                ·
                  refine ⟨52843839616857081921911765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35229226411238054614607843 52843839616857081921911765)
                  ·
                    refine ⟨1238527491020087857544807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52843839616857081921911765 1238527491020087857544807)
                    ·
                      rfl

theorem cell23_7236071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_7236071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236071 prefixEnd_7236071 := by exact prefixLift 7236071
  have htrace : WordTrace (prefixWord ++ tailWord_7236071) baseStart_7236071 baseEnd_7236071 := by
    simpa [prefixWord, tailWord_7236071, baseEnd_7236071] using wordTrace_append hprefix tailTrace_7236071
  have hstable : (prefixWord ++ tailWord_7236071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236071).length < 2 ^ (prefixWord ++ tailWord_7236071).sum := by decide
  have hdescent : baseEnd_7236071 < baseStart_7236071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236111 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 3]
def baseStart_7236111 : Nat := 118140960795 + 7236111 * 2 ^ 59
def prefixEnd_7236111 : Nat := 4983230072969 + 3 ^ 40 * 7236111 * 2
def baseEnd_7236111 : Nat := 3715603012286443416134237

theorem tailTrace_7236111 : CollatzResearch.WordTrace tailWord_7236111 prefixEnd_7236111 3715603012286443416134237 := by
  unfold tailWord_7236111
  simp only [CollatzResearch.WordTrace]
  refine ⟨263922650287813151214508187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175948433525208767476338791 263922650287813151214508187)
  ·
    refine ⟨395883975431719726821762281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263922650287813151214508187 395883975431719726821762281)
    ·
      refine ⟨296912981573789795116321711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395883975431719726821762281 296912981573789795116321711)
      ·
        refine ⟨445369472360684692674482567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296912981573789795116321711 445369472360684692674482567)
        ·
          refine ⟨668054208541027039011723851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445369472360684692674482567 668054208541027039011723851)
          ·
            refine ⟨1002081312811540558517585777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668054208541027039011723851 1002081312811540558517585777)
            ·
              refine ⟨751560984608655418888189333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002081312811540558517585777 751560984608655418888189333)
              ·
                refine ⟨35229421153530722760383875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 751560984608655418888189333 35229421153530722760383875)
                ·
                  refine ⟨52844131730296084140575813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35229421153530722760383875 52844131730296084140575813)
                  ·
                    refine ⟨9908274699430515776357965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52844131730296084140575813 9908274699430515776357965)
                    ·
                      refine ⟨3715603012286443416134237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9908274699430515776357965 3715603012286443416134237)
                      ·
                        rfl

theorem cell23_7236111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 3].length) (baseStart_7236111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236111 prefixEnd_7236111 := by exact prefixLift 7236111
  have htrace : WordTrace (prefixWord ++ tailWord_7236111) baseStart_7236111 baseEnd_7236111 := by
    simpa [prefixWord, tailWord_7236111, baseEnd_7236111] using wordTrace_append hprefix tailTrace_7236111
  have hstable : (prefixWord ++ tailWord_7236111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236111).length < 2 ^ (prefixWord ++ tailWord_7236111).sum := by decide
  have hdescent : baseEnd_7236111 < baseStart_7236111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236131 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 8]
def baseStart_7236131 : Nat := 118140960795 + 7236131 * 2 ^ 59
def prefixEnd_7236131 : Nat := 4983230072969 + 3 ^ 40 * 7236131 * 2
def baseEnd_7236131 : Nat := 412845920211059259764905

theorem tailTrace_7236131 : CollatzResearch.WordTrace tailWord_7236131 prefixEnd_7236131 412845920211059259764905 := by
  unfold tailWord_7236131
  simp only [CollatzResearch.WordTrace]
  refine ⟨263923379747740694630236247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175948919831827129753490831 263923379747740694630236247)
  ·
    refine ⟨395885069621611041945354371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263923379747740694630236247 395885069621611041945354371)
    ·
      refine ⟨593827604432416562918031557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395885069621611041945354371 593827604432416562918031557)
      ·
        refine ⟨111342675831078105547130917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 593827604432416562918031557 111342675831078105547130917)
        ·
          refine ⟨20876751718327144790087047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111342675831078105547130917 20876751718327144790087047)
          ·
            refine ⟨31315127577490717185130571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20876751718327144790087047 31315127577490717185130571)
            ·
              refine ⟨46972691366236075777695857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31315127577490717185130571 46972691366236075777695857)
              ·
                refine ⟨35229518524677056833271893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46972691366236075777695857 35229518524677056833271893)
                ·
                  refine ⟨412845920211059259764905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35229518524677056833271893 412845920211059259764905)
                  ·
                    rfl

theorem cell23_7236131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 8].length) (baseStart_7236131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236131 prefixEnd_7236131 := by exact prefixLift 7236131
  have htrace : WordTrace (prefixWord ++ tailWord_7236131) baseStart_7236131 baseEnd_7236131 := by
    simpa [prefixWord, tailWord_7236131, baseEnd_7236131] using wordTrace_append hprefix tailTrace_7236131
  have hstable : (prefixWord ++ tailWord_7236131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236131).length < 2 ^ (prefixWord ++ tailWord_7236131).sum := by decide
  have hdescent : baseEnd_7236131 < baseStart_7236131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236152 : List Nat := [2, 1, 2, 1, 4, 1, 5, 2, 1, 4]
def baseStart_7236152 : Nat := 118140960795 + 7236152 * 2 ^ 59
def prefixEnd_7236152 : Nat := 4983230072969 + 3 ^ 40 * 7236152 * 2
def baseEnd_7236152 : Nat := 1238541354997759251907183

theorem tailTrace_7236152 : CollatzResearch.WordTrace tailWord_7236152 prefixEnd_7236152 1238541354997759251907183 := by
  unfold tailWord_7236152
  simp only [CollatzResearch.WordTrace]
  refine ⟨131962072840332307608375355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175949430453776410144500473 131962072840332307608375355)
  ·
    refine ⟨197943109260498461412563033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131962072840332307608375355 197943109260498461412563033)
    ·
      refine ⟨148457331945373846059422275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197943109260498461412563033 148457331945373846059422275)
      ·
        refine ⟨222685997918060769089133413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148457331945373846059422275 222685997918060769089133413)
        ·
          refine ⟨41753624609636394204212515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222685997918060769089133413 41753624609636394204212515)
          ·
            refine ⟨62630436914454591306318773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41753624609636394204212515 62630436914454591306318773)
            ·
              refine ⟨5871603460730117934967385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62630436914454591306318773 5871603460730117934967385)
              ·
                refine ⟨4403702595547588451225539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5871603460730117934967385 4403702595547588451225539)
                ·
                  refine ⟨6605553893321382676838309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403702595547588451225539 6605553893321382676838309)
                  ·
                    refine ⟨1238541354997759251907183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6605553893321382676838309 1238541354997759251907183)
                    ·
                      rfl

theorem cell23_7236152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_7236152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236152 prefixEnd_7236152 := by exact prefixLift 7236152
  have htrace : WordTrace (prefixWord ++ tailWord_7236152) baseStart_7236152 baseEnd_7236152 := by
    simpa [prefixWord, tailWord_7236152, baseEnd_7236152] using wordTrace_append hprefix tailTrace_7236152
  have hstable : (prefixWord ++ tailWord_7236152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236152).length < 2 ^ (prefixWord ++ tailWord_7236152).sum := by decide
  have hdescent : baseEnd_7236152 < baseStart_7236152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236165 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 6]
def baseStart_7236165 : Nat := 118140960795 + 7236165 * 2 ^ 59
def prefixEnd_7236165 : Nat := 4983230072969 + 3 ^ 40 * 7236165 * 2
def baseEnd_7236165 : Nat := 412847860026865133873221

theorem tailTrace_7236165 : CollatzResearch.WordTrace tailWord_7236165 prefixEnd_7236165 412847860026865133873221 := by
  unfold tailWord_7236165
  simp only [CollatzResearch.WordTrace]
  refine ⟨263924619829617518436973949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175949746553078345624649299 263924619829617518436973949)
  ·
    refine ⟨98971732436106569413865231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263924619829617518436973949 98971732436106569413865231)
    ·
      refine ⟨148457598654159854120797847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98971732436106569413865231 148457598654159854120797847)
      ·
        refine ⟨222686397981239781181196771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148457598654159854120797847 222686397981239781181196771)
        ·
          refine ⟨334029596971859671771795157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222686397981239781181196771 334029596971859671771795157)
          ·
            refine ⟨7828818679027961057151449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 334029596971859671771795157 7828818679027961057151449)
            ·
              refine ⟨5871614009270970792863587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7828818679027961057151449 5871614009270970792863587)
              ·
                refine ⟨8807421013906456189295381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871614009270970792863587 8807421013906456189295381)
                ·
                  refine ⟨412847860026865133873221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8807421013906456189295381 412847860026865133873221)
                  ·
                    rfl

theorem cell23_7236165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_7236165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236165 prefixEnd_7236165 := by exact prefixLift 7236165
  have htrace : WordTrace (prefixWord ++ tailWord_7236165) baseStart_7236165 baseEnd_7236165 := by
    simpa [prefixWord, tailWord_7236165, baseEnd_7236165] using wordTrace_append hprefix tailTrace_7236165
  have hstable : (prefixWord ++ tailWord_7236165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236165).length < 2 ^ (prefixWord ++ tailWord_7236165).sum := by decide
  have hdescent : baseEnd_7236165 < baseStart_7236165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236168 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 3, 5, 2]
def baseStart_7236168 : Nat := 118140960795 + 7236168 * 2 ^ 59
def prefixEnd_7236168 : Nat := 4983230072969 + 3 ^ 40 * 7236168 * 2
def baseEnd_7236168 : Nat := 3715632280683749693121475

theorem tailTrace_7236168 : CollatzResearch.WordTrace tailWord_7236168 prefixEnd_7236168 3715632280683749693121475 := by
  unfold tailWord_7236168
  simp only [CollatzResearch.WordTrace]
  refine ⟨131962364624303324974666579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175949819499071099966222105 131962364624303324974666579)
  ·
    refine ⟨197943546936454987461999869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131962364624303324974666579 197943546936454987461999869)
    ·
      refine ⟨74228830101170620298249951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197943546936454987461999869 74228830101170620298249951)
      ·
        refine ⟨111343245151755930447374927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74228830101170620298249951 111343245151755930447374927)
        ·
          refine ⟨167014867727633895671062391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111343245151755930447374927 167014867727633895671062391)
          ·
            refine ⟨250522301591450843506593587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167014867727633895671062391 250522301591450843506593587)
            ·
              refine ⟨375783452387176265259890381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250522301591450843506593587 375783452387176265259890381)
              ·
                refine ⟨140918794645191099472458893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375783452387176265259890381 140918794645191099472458893)
                ·
                  refine ⟨52844547991946662302172085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140918794645191099472458893 52844547991946662302172085)
                  ·
                    refine ⟨4954176374244999590828633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52844547991946662302172085 4954176374244999590828633)
                    ·
                      refine ⟨3715632280683749693121475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954176374244999590828633 3715632280683749693121475)
                      ·
                        rfl

theorem cell23_7236168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_7236168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236168 prefixEnd_7236168 := by exact prefixLift 7236168
  have htrace : WordTrace (prefixWord ++ tailWord_7236168) baseStart_7236168 baseEnd_7236168 := by
    simpa [prefixWord, tailWord_7236168, baseEnd_7236168] using wordTrace_append hprefix tailTrace_7236168
  have hstable : (prefixWord ++ tailWord_7236168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236168).length < 2 ^ (prefixWord ++ tailWord_7236168).sum := by decide
  have hdescent : baseEnd_7236168 < baseStart_7236168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236178 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_7236178 : Nat := 118140960795 + 7236178 * 2 ^ 59
def prefixEnd_7236178 : Nat := 4983230072969 + 3 ^ 40 * 7236178 * 2
def baseEnd_7236178 : Nat := 1238545805163431551332143

theorem tailTrace_7236178 : CollatzResearch.WordTrace tailWord_7236178 prefixEnd_7236178 1238545805163431551332143 := by
  unfold tailWord_7236178
  simp only [CollatzResearch.WordTrace]
  refine ⟨65981273494642605414299297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175950062652380281104798125 65981273494642605414299297)
  ·
    refine ⟨49485955120981954060724473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65981273494642605414299297 49485955120981954060724473)
    ·
      refine ⟨37114466340736465545543355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49485955120981954060724473 37114466340736465545543355)
      ·
        refine ⟨55671699511104698318315033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37114466340736465545543355 55671699511104698318315033)
        ·
          refine ⟨41753774633328523738736275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55671699511104698318315033 41753774633328523738736275)
          ·
            refine ⟨62630661949992785608104413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41753774633328523738736275 62630661949992785608104413)
            ·
              refine ⟨23486498231247294603039155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62630661949992785608104413 23486498231247294603039155)
              ·
                refine ⟨35229747346870941904558733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23486498231247294603039155 35229747346870941904558733)
                ·
                  refine ⟨13211155255076603214209525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35229747346870941904558733 13211155255076603214209525)
                  ·
                    refine ⟨1238545805163431551332143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13211155255076603214209525 1238545805163431551332143)
                    ·
                      rfl

theorem cell23_7236178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_7236178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236178 prefixEnd_7236178 := by exact prefixLift 7236178
  have htrace : WordTrace (prefixWord ++ tailWord_7236178) baseStart_7236178 baseEnd_7236178 := by
    simpa [prefixWord, tailWord_7236178, baseEnd_7236178] using wordTrace_append hprefix tailTrace_7236178
  have hstable : (prefixWord ++ tailWord_7236178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236178).length < 2 ^ (prefixWord ++ tailWord_7236178).sum := by decide
  have hdescent : baseEnd_7236178 < baseStart_7236178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236195 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 1, 5]
def baseStart_7236195 : Nat := 118140960795 + 7236195 * 2 ^ 59
def prefixEnd_7236195 : Nat := 4983230072969 + 3 ^ 40 * 7236195 * 2
def baseEnd_7236195 : Nat := 1238548714887140362494617

theorem tailTrace_7236195 : CollatzResearch.WordTrace tailWord_7236195 prefixEnd_7236195 1238548714887140362494617 := by
  unfold tailWord_7236195
  simp only [CollatzResearch.WordTrace]
  refine ⟨263925714019508833560566039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175950476013005889040377359 263925714019508833560566039)
  ·
    refine ⟨395888571029263250340849059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263925714019508833560566039 395888571029263250340849059)
    ·
      refine ⟨593832856543894875511273589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395888571029263250340849059 593832856543894875511273589)
      ·
        refine ⟨55671830300990144579181899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 593832856543894875511273589 55671830300990144579181899)
        ·
          refine ⟨83507745451485216868772849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55671830300990144579181899 83507745451485216868772849)
          ·
            refine ⟨62630809088613912651579637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83507745451485216868772849 62630809088613912651579637)
            ·
              refine ⟨5871638352057554311085591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62630809088613912651579637 5871638352057554311085591)
              ·
                refine ⟨8807457528086331466628387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871638352057554311085591 8807457528086331466628387)
                ·
                  refine ⟨13211186292129497199942581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8807457528086331466628387 13211186292129497199942581)
                  ·
                    refine ⟨1238548714887140362494617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13211186292129497199942581 1238548714887140362494617)
                    ·
                      rfl

theorem cell23_7236195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 5].length) (baseStart_7236195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236195 prefixEnd_7236195 := by exact prefixLift 7236195
  have htrace : WordTrace (prefixWord ++ tailWord_7236195) baseStart_7236195 baseEnd_7236195 := by
    simpa [prefixWord, tailWord_7236195, baseEnd_7236195] using wordTrace_append hprefix tailTrace_7236195
  have hstable : (prefixWord ++ tailWord_7236195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236195).length < 2 ^ (prefixWord ++ tailWord_7236195).sum := by decide
  have hdescent : baseEnd_7236195 < baseStart_7236195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236211 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 6]
def baseStart_7236211 : Nat := 118140960795 + 7236211 * 2 ^ 59
def prefixEnd_7236211 : Nat := 4983230072969 + 3 ^ 40 * 7236211 * 2
def baseEnd_7236211 : Nat := 3715654360351893024883777

theorem tailTrace_7236211 : CollatzResearch.WordTrace tailWord_7236211 prefixEnd_7236211 3715654360351893024883777 := by
  unfold tailWord_7236211
  simp only [CollatzResearch.WordTrace]
  refine ⟨263926297587450868293148487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175950865058300578862098991 263926297587450868293148487)
  ·
    refine ⟨395889446381176302439722731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263926297587450868293148487 395889446381176302439722731)
    ·
      refine ⟨593834169571764453659584097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395889446381176302439722731 593834169571764453659584097)
      ·
        refine ⟨445375627178823340244688073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593834169571764453659584097 445375627178823340244688073)
        ·
          refine ⟨334031720384117505183516055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445375627178823340244688073 334031720384117505183516055)
          ·
            refine ⟨501047580576176257775274083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334031720384117505183516055 501047580576176257775274083)
            ·
              refine ⟨751571370864264386662911125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501047580576176257775274083 751571370864264386662911125)
              ·
                refine ⟨35229908009262393124823959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 751571370864264386662911125 35229908009262393124823959)
                ·
                  refine ⟨52844862013893589687235939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35229908009262393124823959 52844862013893589687235939)
                  ·
                    refine ⟨79267293020840384530853909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52844862013893589687235939 79267293020840384530853909)
                    ·
                      refine ⟨3715654360351893024883777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79267293020840384530853909 3715654360351893024883777)
                      ·
                        rfl

theorem cell23_7236211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_7236211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236211 prefixEnd_7236211 := by exact prefixLift 7236211
  have htrace : WordTrace (prefixWord ++ tailWord_7236211) baseStart_7236211 baseEnd_7236211 := by
    simpa [prefixWord, tailWord_7236211, baseEnd_7236211] using wordTrace_append hprefix tailTrace_7236211
  have hstable : (prefixWord ++ tailWord_7236211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236211).length < 2 ^ (prefixWord ++ tailWord_7236211).sum := by decide
  have hdescent : baseEnd_7236211 < baseStart_7236211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236225 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 2, 4]
def baseStart_7236225 : Nat := 118140960795 + 7236225 * 2 ^ 59
def prefixEnd_7236225 : Nat := 4983230072969 + 3 ^ 40 * 7236225 * 2
def baseEnd_7236225 : Nat := 1238553849693685323369571

theorem tailTrace_7236225 : CollatzResearch.WordTrace tailWord_7236225 prefixEnd_7236225 1238553849693685323369571 := by
  unfold tailWord_7236225
  simp only [CollatzResearch.WordTrace]
  refine ⟨263926808209400148684158129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175951205472933432456105419 263926808209400148684158129)
  ·
    refine ⟨197945106157050111513118597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263926808209400148684158129 197945106157050111513118597)
    ·
      refine ⟨37114707404446895908709737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197945106157050111513118597 37114707404446895908709737)
      ·
        refine ⟨27836030553335171931532303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37114707404446895908709737 27836030553335171931532303)
        ·
          refine ⟨41754045830002757897298455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27836030553335171931532303 41754045830002757897298455)
          ·
            refine ⟨62631068745004136845947683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41754045830002757897298455 62631068745004136845947683)
            ·
              refine ⟨93946603117506205268921525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62631068745004136845947683 93946603117506205268921525)
              ·
                refine ⟨8807494042266206743961393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93946603117506205268921525 8807494042266206743961393)
                ·
                  refine ⟨6605620531699655057971045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8807494042266206743961393 6605620531699655057971045)
                  ·
                    refine ⟨1238553849693685323369571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6605620531699655057971045 1238553849693685323369571)
                    ·
                      rfl

theorem cell23_7236225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_7236225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236225 prefixEnd_7236225 := by exact prefixLift 7236225
  have htrace : WordTrace (prefixWord ++ tailWord_7236225) baseStart_7236225 baseEnd_7236225 := by
    simpa [prefixWord, tailWord_7236225, baseEnd_7236225] using wordTrace_append hprefix tailTrace_7236225
  have hstable : (prefixWord ++ tailWord_7236225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236225).length < 2 ^ (prefixWord ++ tailWord_7236225).sum := by decide
  have hdescent : baseEnd_7236225 < baseStart_7236225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236241 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_7236241 : Nat := 118140960795 + 7236241 * 2 ^ 59
def prefixEnd_7236241 : Nat := 4983230072969 + 3 ^ 40 * 7236241 * 2
def baseEnd_7236241 : Nat := 3715669764771527907508639

theorem tailTrace_7236241 : CollatzResearch.WordTrace tailWord_7236241 prefixEnd_7236241 3715669764771527907508639 := by
  unfold tailWord_7236241
  simp only [CollatzResearch.WordTrace]
  refine ⟨263927391777342183416740577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175951594518228122277827051 263927391777342183416740577)
  ·
    refine ⟨197945543833006637562555433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263927391777342183416740577 197945543833006637562555433)
    ·
      refine ⟨148459157874754978171916575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197945543833006637562555433 148459157874754978171916575)
      ·
        refine ⟨222688736812132467257874863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148459157874754978171916575 222688736812132467257874863)
        ·
          refine ⟨334033105218198700886812295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222688736812132467257874863 334033105218198700886812295)
          ·
            refine ⟨501049657827298051330218443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334033105218198700886812295 501049657827298051330218443)
            ·
              refine ⟨751574486740947076995327665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501049657827298051330218443 751574486740947076995327665)
              ·
                refine ⟨563680865055710307746495749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751574486740947076995327665 563680865055710307746495749)
                ·
                  refine ⟨105690162197945682702467953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 563680865055710307746495749 105690162197945682702467953)
                  ·
                    refine ⟨79267621648459262026850965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105690162197945682702467953 79267621648459262026850965)
                    ·
                      refine ⟨3715669764771527907508639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79267621648459262026850965 3715669764771527907508639)
                      ·
                        rfl

theorem cell23_7236241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_7236241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236241 prefixEnd_7236241 := by exact prefixLift 7236241
  have htrace : WordTrace (prefixWord ++ tailWord_7236241) baseStart_7236241 baseEnd_7236241 := by
    simpa [prefixWord, tailWord_7236241, baseEnd_7236241] using wordTrace_append hprefix tailTrace_7236241
  have hstable : (prefixWord ++ tailWord_7236241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236241).length < 2 ^ (prefixWord ++ tailWord_7236241).sum := by decide
  have hdescent : baseEnd_7236241 < baseStart_7236241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236249 : List Nat := [1, 2, 1, 2, 1, 2, 6, 3, 1, 2, 2]
def baseStart_7236249 : Nat := 118140960795 + 7236249 * 2 ^ 59
def prefixEnd_7236249 : Nat := 4983230072969 + 3 ^ 40 * 7236249 * 2
def baseEnd_7236249 : Nat := 3715673872616763876208603

theorem tailTrace_7236249 : CollatzResearch.WordTrace tailWord_7236249 prefixEnd_7236249 3715673872616763876208603 := by
  unfold tailWord_7236249
  simp only [CollatzResearch.WordTrace]
  refine ⟨263927683561313200783031801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175951789040875467188687867 263927683561313200783031801)
  ·
    refine ⟨197945762670984900587273851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263927683561313200783031801 197945762670984900587273851)
    ·
      refine ⟨296918644006477350880910777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197945762670984900587273851 296918644006477350880910777)
      ·
        refine ⟨222688983004858013160683083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296918644006477350880910777 222688983004858013160683083)
        ·
          refine ⟨334033474507287019741024625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222688983004858013160683083 334033474507287019741024625)
          ·
            refine ⟨250525105880465264805768469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334033474507287019741024625 250525105880465264805768469)
            ·
              refine ⟨11743364338146809287770397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 250525105880465264805768469 11743364338146809287770397)
              ·
                refine ⟨4403761626805053482913899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11743364338146809287770397 4403761626805053482913899)
                ·
                  refine ⟨6605642440207580224370849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403761626805053482913899 6605642440207580224370849)
                  ·
                    refine ⟨4954231830155685168278137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6605642440207580224370849 4954231830155685168278137)
                    ·
                      refine ⟨3715673872616763876208603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954231830155685168278137 3715673872616763876208603)
                      ·
                        rfl

theorem cell23_7236249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 1, 2, 2].length) (baseStart_7236249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236249 prefixEnd_7236249 := by exact prefixLift 7236249
  have htrace : WordTrace (prefixWord ++ tailWord_7236249) baseStart_7236249 baseEnd_7236249 := by
    simpa [prefixWord, tailWord_7236249, baseEnd_7236249] using wordTrace_append hprefix tailTrace_7236249
  have hstable : (prefixWord ++ tailWord_7236249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236249).length < 2 ^ (prefixWord ++ tailWord_7236249).sum := by decide
  have hdescent : baseEnd_7236249 < baseStart_7236249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236252 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_7236252 : Nat := 118140960795 + 7236252 * 2 ^ 59
def prefixEnd_7236252 : Nat := 4983230072969 + 3 ^ 40 * 7236252 * 2
def baseEnd_7236252 : Nat := 3715675413058727364471089

theorem tailTrace_7236252 : CollatzResearch.WordTrace tailWord_7236252 prefixEnd_7236252 3715675413058727364471089 := by
  unfold tailWord_7236252
  simp only [CollatzResearch.WordTrace]
  refine ⟨131963896490151166147695505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175951861986868221530260673 131963896490151166147695505)
  ·
    refine ⟨98972922367613374610771629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131963896490151166147695505 98972922367613374610771629)
    ·
      refine ⟨37114845887855015479039361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98972922367613374610771629 37114845887855015479039361)
      ·
        refine ⟨27836134415891261609279521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37114845887855015479039361 27836134415891261609279521)
        ·
          refine ⟨20877100811918446206959641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27836134415891261609279521 20877100811918446206959641)
          ·
            refine ⟨15657825608938834655219731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20877100811918446206959641 15657825608938834655219731)
            ·
              refine ⟨23486738413408251982829597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15657825608938834655219731 23486738413408251982829597)
              ·
                refine ⟨8807526905028094493561099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23486738413408251982829597 8807526905028094493561099)
                ·
                  refine ⟨13211290357542141740341649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8807526905028094493561099 13211290357542141740341649)
                  ·
                    refine ⟨9908467768156606305256237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13211290357542141740341649 9908467768156606305256237)
                    ·
                      refine ⟨3715675413058727364471089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9908467768156606305256237 3715675413058727364471089)
                      ·
                        rfl

theorem cell23_7236252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_7236252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236252 prefixEnd_7236252 := by exact prefixLift 7236252
  have htrace : WordTrace (prefixWord ++ tailWord_7236252) baseStart_7236252 baseEnd_7236252 := by
    simpa [prefixWord, tailWord_7236252, baseEnd_7236252] using wordTrace_append hprefix tailTrace_7236252
  have hstable : (prefixWord ++ tailWord_7236252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236252).length < 2 ^ (prefixWord ++ tailWord_7236252).sum := by decide
  have hdescent : baseEnd_7236252 < baseStart_7236252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236289 : List Nat := [1, 2, 6, 2, 1, 2, 2, 7]
def baseStart_7236289 : Nat := 118140960795 + 7236289 * 2 ^ 59
def prefixEnd_7236289 : Nat := 4983230072969 + 3 ^ 40 * 7236289 * 2
def baseEnd_7236289 : Nat := 137618311549738656285497

theorem tailTrace_7236289 : CollatzResearch.WordTrace tailWord_7236289 prefixEnd_7236289 137618311549738656285497 := by
  unfold tailWord_7236289
  simp only [CollatzResearch.WordTrace]
  refine ⟨263929142481168287614487921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175952761654112191742991947 263929142481168287614487921)
  ·
    refine ⟨197946856860876215710865941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263929142481168287614487921 197946856860876215710865941)
    ·
      refine ⟨9278758915353572611446841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 197946856860876215710865941 9278758915353572611446841)
      ·
        refine ⟨6959069186515179458585131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9278758915353572611446841 6959069186515179458585131)
        ·
          refine ⟨10438603779772769187877697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6959069186515179458585131 10438603779772769187877697)
          ·
            refine ⟨7828952834829576890908273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10438603779772769187877697 7828952834829576890908273)
            ·
              refine ⟨5871714626122182668181205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7828952834829576890908273 5871714626122182668181205)
              ·
                refine ⟨137618311549738656285497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5871714626122182668181205 137618311549738656285497)
                ·
                  rfl

theorem cell23_7236289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 7].length) (baseStart_7236289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236289 prefixEnd_7236289 := by exact prefixLift 7236289
  have htrace : WordTrace (prefixWord ++ tailWord_7236289) baseStart_7236289 baseEnd_7236289 := by
    simpa [prefixWord, tailWord_7236289, baseEnd_7236289] using wordTrace_append hprefix tailTrace_7236289
  have hstable : (prefixWord ++ tailWord_7236289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236289).length < 2 ^ (prefixWord ++ tailWord_7236289).sum := by decide
  have hdescent : baseEnd_7236289 < baseStart_7236289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236305 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 3, 4, 2]
def baseStart_7236305 : Nat := 118140960795 + 7236305 * 2 ^ 59
def prefixEnd_7236305 : Nat := 4983230072969 + 3 ^ 40 * 7236305 * 2
def baseEnd_7236305 : Nat := 3715702627533415657108345

theorem tailTrace_7236305 : CollatzResearch.WordTrace tailWord_7236305 prefixEnd_7236305 3715702627533415657108345 := by
  unfold tailWord_7236305
  simp only [CollatzResearch.WordTrace]
  refine ⟨263929726049110322347070369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175953150699406881564713579 263929726049110322347070369)
  ·
    refine ⟨197947294536832741760302777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263929726049110322347070369 197947294536832741760302777)
    ·
      refine ⟨148460470902624556320227083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197947294536832741760302777 148460470902624556320227083)
      ·
        refine ⟨222690706353936834480340625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148460470902624556320227083 222690706353936834480340625)
        ·
          refine ⟨167018029765452625860255469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222690706353936834480340625 167018029765452625860255469)
          ·
            refine ⟨62631761162044734697595801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167018029765452625860255469 62631761162044734697595801)
            ·
              refine ⟨46973820871533551023196851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62631761162044734697595801 46973820871533551023196851)
              ·
                refine ⟨70460731307300326534795277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46973820871533551023196851 70460731307300326534795277)
                ·
                  refine ⟨26422774240237622450548229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70460731307300326534795277 26422774240237622450548229)
                  ·
                    refine ⟨4954270170044554209477793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26422774240237622450548229 4954270170044554209477793)
                    ·
                      refine ⟨3715702627533415657108345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954270170044554209477793 3715702627533415657108345)
                      ·
                        rfl

theorem cell23_7236305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 4, 2].length) (baseStart_7236305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236305 prefixEnd_7236305 := by exact prefixLift 7236305
  have htrace : WordTrace (prefixWord ++ tailWord_7236305) baseStart_7236305 baseEnd_7236305 := by
    simpa [prefixWord, tailWord_7236305, baseEnd_7236305] using wordTrace_append hprefix tailTrace_7236305
  have hstable : (prefixWord ++ tailWord_7236305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236305).length < 2 ^ (prefixWord ++ tailWord_7236305).sum := by decide
  have hdescent : baseEnd_7236305 < baseStart_7236305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236395 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 1, 6, 2]
def baseStart_7236395 : Nat := 118140960795 + 7236395 * 2 ^ 59
def prefixEnd_7236395 : Nat := 4983230072969 + 3 ^ 40 * 7236395 * 2
def baseEnd_7236395 : Nat := 3715748840792320304982931

theorem tailTrace_7236395 : CollatzResearch.WordTrace tailWord_7236395 prefixEnd_7236395 3715748840792320304982931 := by
  unfold tailWord_7236395
  simp only [CollatzResearch.WordTrace]
  refine ⟨263933008618784267717846639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175955339079189511811897759 263933008618784267717846639)
  ·
    refine ⟨395899512928176401576769959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263933008618784267717846639 395899512928176401576769959)
    ·
      refine ⟨593849269392264602365154939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395899512928176401576769959 593849269392264602365154939)
      ·
        refine ⟨890773904088396903547732409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593849269392264602365154939 890773904088396903547732409)
        ·
          refine ⟨668080428066297677660799307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890773904088396903547732409 668080428066297677660799307)
          ·
            refine ⟨1002120642099446516491198961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668080428066297677660799307 1002120642099446516491198961)
            ·
              refine ⟨751590481574584887368399221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002120642099446516491198961 751590481574584887368399221)
              ·
                refine ⟨70461607647617333190787427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 751590481574584887368399221 70461607647617333190787427)
                ·
                  refine ⟨105692411471425999786181141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70461607647617333190787427 105692411471425999786181141)
                  ·
                    refine ⟨4954331787723093739977241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 105692411471425999786181141 4954331787723093739977241)
                    ·
                      refine ⟨3715748840792320304982931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954331787723093739977241 3715748840792320304982931)
                      ·
                        rfl

theorem cell23_7236395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 6, 2].length) (baseStart_7236395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236395 prefixEnd_7236395 := by exact prefixLift 7236395
  have htrace : WordTrace (prefixWord ++ tailWord_7236395) baseStart_7236395 baseEnd_7236395 := by
    simpa [prefixWord, tailWord_7236395, baseEnd_7236395] using wordTrace_append hprefix tailTrace_7236395
  have hstable : (prefixWord ++ tailWord_7236395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236395).length < 2 ^ (prefixWord ++ tailWord_7236395).sum := by decide
  have hdescent : baseEnd_7236395 < baseStart_7236395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236439 : List Nat := [1, 1, 3, 2, 4, 1, 2, 4, 1, 4]
def baseStart_7236439 : Nat := 118140960795 + 7236439 * 2 ^ 59
def prefixEnd_7236439 : Nat := 4983230072969 + 3 ^ 40 * 7236439 * 2
def baseEnd_7236439 : Nat := 1238590477980372710944243

theorem tailTrace_7236439 : CollatzResearch.WordTrace tailWord_7236439 prefixEnd_7236439 1238590477980372710944243 := by
  unfold tailWord_7236439
  simp only [CollatzResearch.WordTrace]
  refine ⟨263934613430624863232448371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175956408953749908821632247 263934613430624863232448371)
  ·
    refine ⟨395901920145937294848672557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263934613430624863232448371 395901920145937294848672557)
    ·
      refine ⟨148463220054726485568252209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395901920145937294848672557 148463220054726485568252209)
      ·
        refine ⟨111347415041044864176189157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148463220054726485568252209 111347415041044864176189157)
        ·
          refine ⟨20877640320195912033035467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111347415041044864176189157 20877640320195912033035467)
          ·
            refine ⟨31316460480293868049553201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20877640320195912033035467 31316460480293868049553201)
            ·
              refine ⟨23487345360220401037164901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31316460480293868049553201 23487345360220401037164901)
              ·
                refine ⟨4403877255041325194468419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23487345360220401037164901 4403877255041325194468419)
                ·
                  refine ⟨6605815882561987791702629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4403877255041325194468419 6605815882561987791702629)
                  ·
                    refine ⟨1238590477980372710944243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6605815882561987791702629 1238590477980372710944243)
                    ·
                      rfl

theorem cell23_7236439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_7236439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236439 prefixEnd_7236439 := by exact prefixLift 7236439
  have htrace : WordTrace (prefixWord ++ tailWord_7236439) baseStart_7236439 baseEnd_7236439 := by
    simpa [prefixWord, tailWord_7236439, baseEnd_7236439] using wordTrace_append hprefix tailTrace_7236439
  have hstable : (prefixWord ++ tailWord_7236439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236439).length < 2 ^ (prefixWord ++ tailWord_7236439).sum := by decide
  have hdescent : baseEnd_7236439 < baseStart_7236439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236489 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 2, 3, 2]
def baseStart_7236489 : Nat := 118140960795 + 7236489 * 2 ^ 59
def prefixEnd_7236489 : Nat := 4983230072969 + 3 ^ 40 * 7236489 * 2
def baseEnd_7236489 : Nat := 3715797107973842937207499

theorem tailTrace_7236489 : CollatzResearch.WordTrace tailWord_7236489 prefixEnd_7236489 3715797107973842937207499 := by
  unfold tailWord_7236489
  simp only [CollatzResearch.WordTrace]
  refine ⟨263936437080443721771768521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175957624720295814514512347 263936437080443721771768521)
  ·
    refine ⟨197952327810332791328826391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263936437080443721771768521 197952327810332791328826391)
    ·
      refine ⟨296928491715499186993239587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197952327810332791328826391 296928491715499186993239587)
      ·
        refine ⟨445392737573248780489859381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296928491715499186993239587 445392737573248780489859381)
        ·
          refine ⟨41755569147492073170924317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 445392737573248780489859381 41755569147492073170924317)
          ·
            refine ⟨15658338430309527439096619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41755569147492073170924317 15658338430309527439096619)
            ·
              refine ⟨23487507645464291158644929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15658338430309527439096619 23487507645464291158644929)
              ·
                refine ⟨17615630734098218368983697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23487507645464291158644929 17615630734098218368983697)
                ·
                  refine ⟨13211723050573663776737773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17615630734098218368983697 13211723050573663776737773)
                  ·
                    refine ⟨4954396143965123916276665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13211723050573663776737773 4954396143965123916276665)
                    ·
                      refine ⟨3715797107973842937207499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954396143965123916276665 3715797107973842937207499)
                      ·
                        rfl

theorem cell23_7236489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 3, 2].length) (baseStart_7236489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236489 prefixEnd_7236489 := by exact prefixLift 7236489
  have htrace : WordTrace (prefixWord ++ tailWord_7236489) baseStart_7236489 baseEnd_7236489 := by
    simpa [prefixWord, tailWord_7236489, baseEnd_7236489] using wordTrace_append hprefix tailTrace_7236489
  have hstable : (prefixWord ++ tailWord_7236489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236489).length < 2 ^ (prefixWord ++ tailWord_7236489).sum := by decide
  have hdescent : baseEnd_7236489 < baseStart_7236489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236505 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 2, 6, 3]
def baseStart_7236505 : Nat := 118140960795 + 7236505 * 2 ^ 59
def prefixEnd_7236505 : Nat := 4983230072969 + 3 ^ 40 * 7236505 * 2
def baseEnd_7236505 : Nat := 3715805323664314874607425

theorem tailTrace_7236505 : CollatzResearch.WordTrace tailWord_7236505 prefixEnd_7236505 3715805323664314874607425 := by
  unfold tailWord_7236505
  simp only [CollatzResearch.WordTrace]
  refine ⟨263937020648385756504350969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175958013765590504336233979 263937020648385756504350969)
  ·
    refine ⟨197952765486289317378263227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263937020648385756504350969 197952765486289317378263227)
    ·
      refine ⟨296929148229433976067394841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197952765486289317378263227 296929148229433976067394841)
      ·
        refine ⟨222696861172075482050546131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296929148229433976067394841 222696861172075482050546131)
        ·
          refine ⟨334045291758113223075819197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222696861172075482050546131 334045291758113223075819197)
          ·
            refine ⟨125266984409292458653432199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334045291758113223075819197 125266984409292458653432199)
            ·
              refine ⟨187900476613938687980148299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125266984409292458653432199 187900476613938687980148299)
              ·
                refine ⟨281850714920908031970222449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187900476613938687980148299 281850714920908031970222449)
                ·
                  refine ⟨211388036190681023977666837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281850714920908031970222449 211388036190681023977666837)
                  ·
                    refine ⟨9908814196438172998953133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 211388036190681023977666837 9908814196438172998953133)
                    ·
                      refine ⟨3715805323664314874607425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9908814196438172998953133 3715805323664314874607425)
                      ·
                        rfl

theorem cell23_7236505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_7236505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236505 prefixEnd_7236505 := by exact prefixLift 7236505
  have htrace : WordTrace (prefixWord ++ tailWord_7236505) baseStart_7236505 baseEnd_7236505 := by
    simpa [prefixWord, tailWord_7236505, baseEnd_7236505] using wordTrace_append hprefix tailTrace_7236505
  have hstable : (prefixWord ++ tailWord_7236505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236505).length < 2 ^ (prefixWord ++ tailWord_7236505).sum := by decide
  have hdescent : baseEnd_7236505 < baseStart_7236505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236515 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 6]
def baseStart_7236515 : Nat := 118140960795 + 7236515 * 2 ^ 59
def prefixEnd_7236515 : Nat := 4983230072969 + 3 ^ 40 * 7236515 * 2
def baseEnd_7236515 : Nat := 3715810458470859835482379

theorem tailTrace_7236515 : CollatzResearch.WordTrace tailWord_7236515 prefixEnd_7236515 3715810458470859835482379 := by
  unfold tailWord_7236515
  simp only [CollatzResearch.WordTrace]
  refine ⟨263937385378349528212214999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175958256918899685474809999 263937385378349528212214999)
  ·
    refine ⟨395906078067524292318322499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263937385378349528212214999 395906078067524292318322499)
    ·
      refine ⟨593859117101286438477483749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395906078067524292318322499 593859117101286438477483749)
      ·
        refine ⟨111348584456491207214528203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 593859117101286438477483749 111348584456491207214528203)
        ·
          refine ⟨167022876684736810821792305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111348584456491207214528203 167022876684736810821792305)
          ·
            refine ⟨125267157513552608116344229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167022876684736810821792305 125267157513552608116344229)
            ·
              refine ⟨23487592033791114021814543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125267157513552608116344229 23487592033791114021814543)
              ·
                refine ⟨35231388050686671032721815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23487592033791114021814543 35231388050686671032721815)
                ·
                  refine ⟨52847082076030006549082723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35231388050686671032721815 52847082076030006549082723)
                  ·
                    refine ⟨79270623114045009823624085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52847082076030006549082723 79270623114045009823624085)
                    ·
                      refine ⟨3715810458470859835482379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79270623114045009823624085 3715810458470859835482379)
                      ·
                        rfl

theorem cell23_7236515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_7236515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236515 prefixEnd_7236515 := by exact prefixLift 7236515
  have htrace : WordTrace (prefixWord ++ tailWord_7236515) baseStart_7236515 baseEnd_7236515 := by
    simpa [prefixWord, tailWord_7236515, baseEnd_7236515] using wordTrace_append hprefix tailTrace_7236515
  have hstable : (prefixWord ++ tailWord_7236515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236515).length < 2 ^ (prefixWord ++ tailWord_7236515).sum := by decide
  have hdescent : baseEnd_7236515 < baseStart_7236515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236519 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_7236519 : Nat := 118140960795 + 7236519 * 2 ^ 59
def prefixEnd_7236519 : Nat := 4983230072969 + 3 ^ 40 * 7236519 * 2
def baseEnd_7236519 : Nat := 3715812512393477819832361

theorem tailTrace_7236519 : CollatzResearch.WordTrace tailWord_7236519 prefixEnd_7236519 3715812512393477819832361 := by
  unfold tailWord_7236519
  simp only [CollatzResearch.WordTrace]
  refine ⟨263937531270335036895360611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175958354180223357930240407 263937531270335036895360611)
  ·
    refine ⟨395906296905502555343040917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263937531270335036895360611 395906296905502555343040917)
    ·
      refine ⟨18558107667445432281705043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 395906296905502555343040917 18558107667445432281705043)
      ·
        refine ⟨27837161501168148422557565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18558107667445432281705043 27837161501168148422557565)
        ·
          refine ⟨10438935562938055658459087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27837161501168148422557565 10438935562938055658459087)
          ·
            refine ⟨15658403344407083487688631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10438935562938055658459087 15658403344407083487688631)
            ·
              refine ⟨23487605016610625231532947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15658403344407083487688631 23487605016610625231532947)
              ·
                refine ⟨35231407524915937847299421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23487605016610625231532947 35231407524915937847299421)
                ·
                  refine ⟨13211777821843476692737283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35231407524915937847299421 13211777821843476692737283)
                  ·
                    refine ⟨19817666732765215039105925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13211777821843476692737283 19817666732765215039105925)
                    ·
                      refine ⟨3715812512393477819832361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19817666732765215039105925 3715812512393477819832361)
                      ·
                        rfl

theorem cell23_7236519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_7236519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236519 prefixEnd_7236519 := by exact prefixLift 7236519
  have htrace : WordTrace (prefixWord ++ tailWord_7236519) baseStart_7236519 baseEnd_7236519 := by
    simpa [prefixWord, tailWord_7236519, baseEnd_7236519] using wordTrace_append hprefix tailTrace_7236519
  have hstable : (prefixWord ++ tailWord_7236519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236519).length < 2 ^ (prefixWord ++ tailWord_7236519).sum := by decide
  have hdescent : baseEnd_7236519 < baseStart_7236519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236555 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 2, 7]
def baseStart_7236555 : Nat := 118140960795 + 7236555 * 2 ^ 59
def prefixEnd_7236555 : Nat := 4983230072969 + 3 ^ 40 * 7236555 * 2
def baseEnd_7236555 : Nat := 1238610332565679892994065

theorem tailTrace_7236555 : CollatzResearch.WordTrace tailWord_7236555 prefixEnd_7236555 1238610332565679892994065 := by
  unfold tailWord_7236555
  simp only [CollatzResearch.WordTrace]
  refine ⟨263938844298204615043671119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175959229532136410029114079 263938844298204615043671119)
  ·
    refine ⟨395908266447306922565506679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263938844298204615043671119 395908266447306922565506679)
    ·
      refine ⟨593862399670960383848260019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395908266447306922565506679 593862399670960383848260019)
      ·
        refine ⟨890793599506440575772390029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593862399670960383848260019 890793599506440575772390029)
        ·
          refine ⟨334047599814915215914646261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 890793599506440575772390029 334047599814915215914646261)
          ·
            refine ⟨31316962482648301491998087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 334047599814915215914646261 31316962482648301491998087)
            ·
              refine ⟨46975443723972452237997131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31316962482648301491998087 46975443723972452237997131)
              ·
                refine ⟨70463165585958678356995697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46975443723972452237997131 70463165585958678356995697)
                ·
                  refine ⟨52847374189469008767746773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70463165585958678356995697 52847374189469008767746773)
                  ·
                    refine ⟨1238610332565679892994065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52847374189469008767746773 1238610332565679892994065)
                    ·
                      rfl

theorem cell23_7236555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 7].length) (baseStart_7236555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236555 prefixEnd_7236555 := by exact prefixLift 7236555
  have htrace : WordTrace (prefixWord ++ tailWord_7236555) baseStart_7236555 baseEnd_7236555 := by
    simpa [prefixWord, tailWord_7236555, baseEnd_7236555] using wordTrace_append hprefix tailTrace_7236555
  have hstable : (prefixWord ++ tailWord_7236555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236555).length < 2 ^ (prefixWord ++ tailWord_7236555).sum := by decide
  have hdescent : baseEnd_7236555 < baseStart_7236555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236566 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_7236566 : Nat := 118140960795 + 7236566 * 2 ^ 59
def prefixEnd_7236566 : Nat := 4983230072969 + 3 ^ 40 * 7236566 * 2
def baseEnd_7236566 : Nat := 3715836645984239135944645

theorem tailTrace_7236566 : CollatzResearch.WordTrace tailWord_7236566 prefixEnd_7236566 3715836645984239135944645 := by
  unfold tailWord_7236566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16496202843822797745145097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175959497000776509281547701 16496202843822797745145097)
  ·
    refine ⟨12372152132867098308858823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16496202843822797745145097 12372152132867098308858823)
    ·
      refine ⟨18558228199300647463288235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12372152132867098308858823 18558228199300647463288235)
      ·
        refine ⟨27837342298950971194932353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18558228199300647463288235 27837342298950971194932353)
        ·
          refine ⟨20878006724213228396199265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27837342298950971194932353 20878006724213228396199265)
          ·
            refine ⟨15658505043159921297149449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20878006724213228396199265 15658505043159921297149449)
            ·
              refine ⟨11743878782369940972862087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15658505043159921297149449 11743878782369940972862087)
              ·
                refine ⟨17615818173554911459293131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11743878782369940972862087 17615818173554911459293131)
                ·
                  refine ⟨26423727260332367188939697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17615818173554911459293131 26423727260332367188939697)
                  ·
                    refine ⟨19817795445249275391704773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26423727260332367188939697 19817795445249275391704773)
                    ·
                      refine ⟨3715836645984239135944645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19817795445249275391704773 3715836645984239135944645)
                      ·
                        rfl

theorem cell23_7236566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_7236566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236566 prefixEnd_7236566 := by exact prefixLift 7236566
  have htrace : WordTrace (prefixWord ++ tailWord_7236566) baseStart_7236566 baseEnd_7236566 := by
    simpa [prefixWord, tailWord_7236566, baseEnd_7236566] using wordTrace_append hprefix tailTrace_7236566
  have hstable : (prefixWord ++ tailWord_7236566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236566).length < 2 ^ (prefixWord ++ tailWord_7236566).sum := by decide
  have hdescent : baseEnd_7236566 < baseStart_7236566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236569 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 1, 3, 3]
def baseStart_7236569 : Nat := 118140960795 + 7236569 * 2 ^ 59
def prefixEnd_7236569 : Nat := 4983230072969 + 3 ^ 40 * 7236569 * 2
def baseEnd_7236569 : Nat := 3715838186426202624207131

theorem tailTrace_7236569 : CollatzResearch.WordTrace tailWord_7236569 prefixEnd_7236569 3715838186426202624207131 := by
  unfold tailWord_7236569
  simp only [CollatzResearch.WordTrace]
  refine ⟨263939354920153895434680761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175959569946769263623120507 263939354920153895434680761)
  ·
    refine ⟨197954516190115421576010571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263939354920153895434680761 197954516190115421576010571)
    ·
      refine ⟨296931774285173132364015857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197954516190115421576010571 296931774285173132364015857)
      ·
        refine ⟨222698830713879849273011893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296931774285173132364015857 222698830713879849273011893)
        ·
          refine ⟨20878015379426235869344865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222698830713879849273011893 20878015379426235869344865)
          ·
            refine ⟨15658511534569676902008649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20878015379426235869344865 15658511534569676902008649)
            ·
              refine ⟨11743883650927257676506487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15658511534569676902008649 11743883650927257676506487)
              ·
                refine ⟨17615825476390886514759731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11743883650927257676506487 17615825476390886514759731)
                ·
                  refine ⟨26423738214586329772139597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17615825476390886514759731 26423738214586329772139597)
                  ·
                    refine ⟨9908901830469873664552349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26423738214586329772139597 9908901830469873664552349)
                    ·
                      refine ⟨3715838186426202624207131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9908901830469873664552349 3715838186426202624207131)
                      ·
                        rfl

theorem cell23_7236569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_7236569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236569 prefixEnd_7236569 := by exact prefixLift 7236569
  have htrace : WordTrace (prefixWord ++ tailWord_7236569) baseStart_7236569 baseEnd_7236569 := by
    simpa [prefixWord, tailWord_7236569, baseEnd_7236569] using wordTrace_append hprefix tailTrace_7236569
  have hstable : (prefixWord ++ tailWord_7236569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236569).length < 2 ^ (prefixWord ++ tailWord_7236569).sum := by decide
  have hdescent : baseEnd_7236569 < baseStart_7236569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236579 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 3, 3, 2]
def baseStart_7236579 : Nat := 118140960795 + 7236579 * 2 ^ 59
def prefixEnd_7236579 : Nat := 4983230072969 + 3 ^ 40 * 7236579 * 2
def baseEnd_7236579 : Nat := 3715843321232747585082085

theorem tailTrace_7236579 : CollatzResearch.WordTrace tailWord_7236579 prefixEnd_7236579 3715843321232747585082085 := by
  unfold tailWord_7236579
  simp only [CollatzResearch.WordTrace]
  refine ⟨263939719650117667142544791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175959813100078444761696527 263939719650117667142544791)
  ·
    refine ⟨395909579475176500713817187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263939719650117667142544791 395909579475176500713817187)
    ·
      refine ⟨593864369212764751070725781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395909579475176500713817187 593864369212764751070725781)
      ·
        refine ⟨27837392306848347706440271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 593864369212764751070725781 27837392306848347706440271)
        ·
          refine ⟨41756088460272521559660407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27837392306848347706440271 41756088460272521559660407)
          ·
            refine ⟨62634132690408782339490611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41756088460272521559660407 62634132690408782339490611)
            ·
              refine ⟨93951199035613173509235917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62634132690408782339490611 93951199035613173509235917)
              ·
                refine ⟨35231699638354940065963469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93951199035613173509235917 35231699638354940065963469)
                ·
                  refine ⟨13211887364383102524736301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35231699638354940065963469 13211887364383102524736301)
                  ·
                    refine ⟨4954457761643663446776113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13211887364383102524736301 4954457761643663446776113)
                    ·
                      refine ⟨3715843321232747585082085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954457761643663446776113 3715843321232747585082085)
                      ·
                        rfl

theorem cell23_7236579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_7236579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236579 prefixEnd_7236579 := by exact prefixLift 7236579
  have htrace : WordTrace (prefixWord ++ tailWord_7236579) baseStart_7236579 baseEnd_7236579 := by
    simpa [prefixWord, tailWord_7236579, baseEnd_7236579] using wordTrace_append hprefix tailTrace_7236579
  have hstable : (prefixWord ++ tailWord_7236579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236579).length < 2 ^ (prefixWord ++ tailWord_7236579).sum := by decide
  have hdescent : baseEnd_7236579 < baseStart_7236579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236590 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_7236590 : Nat := 118140960795 + 7236590 * 2 ^ 59
def prefixEnd_7236590 : Nat := 4983230072969 + 3 ^ 40 * 7236590 * 2
def baseEnd_7236590 : Nat := 3715848969519947042044535

theorem tailTrace_7236590 : CollatzResearch.WordTrace tailWord_7236590 prefixEnd_7236590 3715848969519947042044535 := by
  unfold tailWord_7236590
  simp only [CollatzResearch.WordTrace]
  refine ⟨32992515106634727002649403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175960080568718544014130149 32992515106634727002649403)
  ·
    refine ⟨49488772659952090503974105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32992515106634727002649403 49488772659952090503974105)
    ·
      refine ⟨37116579494964067877980579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49488772659952090503974105 37116579494964067877980579)
      ·
        refine ⟨55674869242446101816970869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37116579494964067877980579 55674869242446101816970869)
        ·
          refine ⟨5219518991479322045341019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55674869242446101816970869 5219518991479322045341019)
          ·
            refine ⟨7829278487218983068011529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5219518991479322045341019 7829278487218983068011529)
            ·
              refine ⟨5871958865414237301008647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7829278487218983068011529 5871958865414237301008647)
              ·
                refine ⟨8807938298121355951512971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5871958865414237301008647 8807938298121355951512971)
                ·
                  refine ⟨13211907447182033927269457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8807938298121355951512971 13211907447182033927269457)
                  ·
                    refine ⟨9908930585386525445452093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13211907447182033927269457 9908930585386525445452093)
                    ·
                      refine ⟨3715848969519947042044535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9908930585386525445452093 3715848969519947042044535)
                      ·
                        rfl

theorem cell23_7236590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_7236590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236590 prefixEnd_7236590 := by exact prefixLift 7236590
  have htrace : WordTrace (prefixWord ++ tailWord_7236590) baseStart_7236590 baseEnd_7236590 := by
    simpa [prefixWord, tailWord_7236590, baseEnd_7236590] using wordTrace_append hprefix tailTrace_7236590
  have hstable : (prefixWord ++ tailWord_7236590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236590).length < 2 ^ (prefixWord ++ tailWord_7236590).sum := by decide
  have hdescent : baseEnd_7236590 < baseStart_7236590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236625 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_7236625 : Nat := 118140960795 + 7236625 * 2 ^ 59
def prefixEnd_7236625 : Nat := 4983230072969 + 3 ^ 40 * 7236625 * 2
def baseEnd_7236625 : Nat := 3715866941342854405106873

theorem tailTrace_7236625 : CollatzResearch.WordTrace tailWord_7236625 prefixEnd_7236625 3715866941342854405106873 := by
  unfold tailWord_7236625
  simp only [CollatzResearch.WordTrace]
  refine ⟨263941397407951016998719329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175960931605300677999146219 263941397407951016998719329)
  ·
    refine ⟨197956048055963262749039497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263941397407951016998719329 197956048055963262749039497)
    ·
      refine ⟨148467036041972447061779623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197956048055963262749039497 148467036041972447061779623)
      ·
        refine ⟨222700554062958670592669435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148467036041972447061779623 222700554062958670592669435)
        ·
          refine ⟨334050831094438005889004153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222700554062958670592669435 334050831094438005889004153)
          ·
            refine ⟨250538123320828504416753115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334050831094438005889004153 250538123320828504416753115)
            ·
              refine ⟨375807184981242756625129673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250538123320828504416753115 375807184981242756625129673)
              ·
                refine ⟨281855388735932067468847255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375807184981242756625129673 281855388735932067468847255)
                ·
                  refine ⟨422783083103898101203270883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281855388735932067468847255 422783083103898101203270883)
                  ·
                    refine ⟨634174624655847151804906325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 422783083103898101203270883 634174624655847151804906325)
                    ·
                      refine ⟨3715866941342854405106873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 634174624655847151804906325 3715866941342854405106873)
                      ·
                        rfl

theorem cell23_7236625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_7236625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236625 prefixEnd_7236625 := by exact prefixLift 7236625
  have htrace : WordTrace (prefixWord ++ tailWord_7236625) baseStart_7236625 baseEnd_7236625 := by
    simpa [prefixWord, tailWord_7236625, baseEnd_7236625] using wordTrace_append hprefix tailTrace_7236625
  have hstable : (prefixWord ++ tailWord_7236625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236625).length < 2 ^ (prefixWord ++ tailWord_7236625).sum := by decide
  have hdescent : baseEnd_7236625 < baseStart_7236625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236632 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 7]
def baseStart_7236632 : Nat := 118140960795 + 7236632 * 2 ^ 59
def prefixEnd_7236632 : Nat := 4983230072969 + 3 ^ 40 * 7236632 * 2
def baseEnd_7236632 : Nat := 412874503967492875302149

theorem tailTrace_7236632 : CollatzResearch.WordTrace tailWord_7236632 prefixEnd_7236632 412874503967492875302149 := by
  unfold tailWord_7236632
  simp only [CollatzResearch.WordTrace]
  refine ⟨131970826359462828597112075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175961101812617104796149433 131970826359462828597112075)
  ·
    refine ⟨197956239539194242895668113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131970826359462828597112075 197956239539194242895668113)
    ·
      refine ⟨148467179654395682171751085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197956239539194242895668113 148467179654395682171751085)
      ·
        refine ⟨55675192370398380814406657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148467179654395682171751085 55675192370398380814406657)
        ·
          refine ⟨41756394277798785610804993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55675192370398380814406657 41756394277798785610804993)
          ·
            refine ⟨31317295708349089208103745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41756394277798785610804993 31317295708349089208103745)
            ·
              refine ⟨23487971781261816906077809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31317295708349089208103745 23487971781261816906077809)
              ·
                refine ⟨17615978835946362679558357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23487971781261816906077809 17615978835946362679558357)
                ·
                  refine ⟨412874503967492875302149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17615978835946362679558357 412874503967492875302149)
                  ·
                    rfl

theorem cell23_7236632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 7].length) (baseStart_7236632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236632 prefixEnd_7236632 := by exact prefixLift 7236632
  have htrace : WordTrace (prefixWord ++ tailWord_7236632) baseStart_7236632 baseEnd_7236632 := by
    simpa [prefixWord, tailWord_7236632, baseEnd_7236632] using wordTrace_append hprefix tailTrace_7236632
  have hstable : (prefixWord ++ tailWord_7236632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236632).length < 2 ^ (prefixWord ++ tailWord_7236632).sum := by decide
  have hdescent : baseEnd_7236632 < baseStart_7236632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236635 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 6]
def baseStart_7236635 : Nat := 118140960795 + 7236635 * 2 ^ 59
def prefixEnd_7236635 : Nat := 4983230072969 + 3 ^ 40 * 7236635 * 2
def baseEnd_7236635 : Nat := 3715872076149399365981827

theorem tailTrace_7236635 : CollatzResearch.WordTrace tailWord_7236635 prefixEnd_7236635 3715872076149399365981827 := by
  unfold tailWord_7236635
  simp only [CollatzResearch.WordTrace]
  refine ⟨263941762137914788706583359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175961174758609859137722239 263941762137914788706583359)
  ·
    refine ⟨395912643206872183059875039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263941762137914788706583359 395912643206872183059875039)
    ·
      refine ⟨593868964810308274589812559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395912643206872183059875039 593868964810308274589812559)
      ·
        refine ⟨890803447215462411884718839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593868964810308274589812559 890803447215462411884718839)
        ·
          refine ⟨1336205170823193617827078259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890803447215462411884718839 1336205170823193617827078259)
          ·
            refine ⟨2004307756234790426740617389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336205170823193617827078259 2004307756234790426740617389)
            ·
              refine ⟨751615408588046410027731521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2004307756234790426740617389 751615408588046410027731521)
              ·
                refine ⟨563711556441034807520798641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751615408588046410027731521 563711556441034807520798641)
                ·
                  refine ⟨422783667330776105640598981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563711556441034807520798641 422783667330776105640598981)
                  ·
                    refine ⟨79271937624520519807612309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422783667330776105640598981 79271937624520519807612309)
                    ·
                      refine ⟨3715872076149399365981827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79271937624520519807612309 3715872076149399365981827)
                      ·
                        rfl

theorem cell23_7236635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_7236635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236635 prefixEnd_7236635 := by exact prefixLift 7236635
  have htrace : WordTrace (prefixWord ++ tailWord_7236635) baseStart_7236635 baseEnd_7236635 := by
    simpa [prefixWord, tailWord_7236635, baseEnd_7236635] using wordTrace_append hprefix tailTrace_7236635
  have hstable : (prefixWord ++ tailWord_7236635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236635).length < 2 ^ (prefixWord ++ tailWord_7236635).sum := by decide
  have hdescent : baseEnd_7236635 < baseStart_7236635 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236672 : List Nat := [2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 5]
def baseStart_7236672 : Nat := 118140960795 + 7236672 * 2 ^ 59
def prefixEnd_7236672 : Nat := 4983230072969 + 3 ^ 40 * 7236672 * 2
def baseEnd_7236672 : Nat := 3715891074933615721219157

theorem tailTrace_7236672 : CollatzResearch.WordTrace tailWord_7236672 prefixEnd_7236672 3715891074933615721219157 := by
  unfold tailWord_7236672
  simp only [CollatzResearch.WordTrace]
  refine ⟨131971555819390372012840135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175962074425853829350453513 131971555819390372012840135)
  ·
    refine ⟨197957333729085558019260203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131971555819390372012840135 197957333729085558019260203)
    ·
      refine ⟨296936000593628337028890305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197957333729085558019260203 296936000593628337028890305)
      ·
        refine ⟨222702000445221252771667729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296936000593628337028890305 222702000445221252771667729)
        ·
          refine ⟨167026500333915939578750797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222702000445221252771667729 167026500333915939578750797)
          ·
            refine ⟨62634937625218477342031549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167026500333915939578750797 62634937625218477342031549)
            ·
              refine ⟨23488101609456929003261831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62634937625218477342031549 23488101609456929003261831)
              ·
                refine ⟨35232152414185393504892747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23488101609456929003261831 35232152414185393504892747)
                ·
                  refine ⟨52848228621278090257339121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35232152414185393504892747 52848228621278090257339121)
                  ·
                    refine ⟨39636171465958567693004341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52848228621278090257339121 39636171465958567693004341)
                    ·
                      refine ⟨3715891074933615721219157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39636171465958567693004341 3715891074933615721219157)
                      ·
                        rfl

theorem cell23_7236672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_7236672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236672 prefixEnd_7236672 := by exact prefixLift 7236672
  have htrace : WordTrace (prefixWord ++ tailWord_7236672) baseStart_7236672 baseEnd_7236672 := by
    simpa [prefixWord, tailWord_7236672, baseEnd_7236672] using wordTrace_append hprefix tailTrace_7236672
  have hstable : (prefixWord ++ tailWord_7236672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236672).length < 2 ^ (prefixWord ++ tailWord_7236672).sum := by decide
  have hdescent : baseEnd_7236672 < baseStart_7236672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236682 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_7236682 : Nat := 118140960795 + 7236682 * 2 ^ 59
def prefixEnd_7236682 : Nat := 4983230072969 + 3 ^ 40 * 7236682 * 2
def baseEnd_7236682 : Nat := 3715896209740160682094111

theorem tailTrace_7236682 : CollatzResearch.WordTrace tailWord_7236682 prefixEnd_7236682 3715896209740160682094111 := by
  unfold tailWord_7236682
  simp only [CollatzResearch.WordTrace]
  refine ⟨65985869092186128933386075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175962317579163010489029533 65985869092186128933386075)
  ·
    refine ⟨98978803638279193400079113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65985869092186128933386075 98978803638279193400079113)
    ·
      refine ⟨74234102728709395050059335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98978803638279193400079113 74234102728709395050059335)
      ·
        refine ⟨111351154093064092575089003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74234102728709395050059335 111351154093064092575089003)
        ·
          refine ⟨167026731139596138862633505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111351154093064092575089003 167026731139596138862633505)
          ·
            refine ⟨125270048354697104146975129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167026731139596138862633505 125270048354697104146975129)
            ·
              refine ⟨93952536266022828110231347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125270048354697104146975129 93952536266022828110231347)
              ·
                refine ⟨140928804399034242165347021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93952536266022828110231347 140928804399034242165347021)
                ·
                  refine ⟨52848301649637840812005133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140928804399034242165347021 52848301649637840812005133)
                  ·
                    refine ⟨19818113118614190304501925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52848301649637840812005133 19818113118614190304501925)
                    ·
                      refine ⟨3715896209740160682094111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19818113118614190304501925 3715896209740160682094111)
                      ·
                        rfl

theorem cell23_7236682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_7236682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236682 prefixEnd_7236682 := by exact prefixLift 7236682
  have htrace : WordTrace (prefixWord ++ tailWord_7236682) baseStart_7236682 baseEnd_7236682 := by
    simpa [prefixWord, tailWord_7236682, baseEnd_7236682] using wordTrace_append hprefix tailTrace_7236682
  have hstable : (prefixWord ++ tailWord_7236682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236682).length < 2 ^ (prefixWord ++ tailWord_7236682).sum := by decide
  have hdescent : baseEnd_7236682 < baseStart_7236682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236692 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_7236692 : Nat := 118140960795 + 7236692 * 2 ^ 59
def prefixEnd_7236692 : Nat := 4983230072969 + 3 ^ 40 * 7236692 * 2
def baseEnd_7236692 : Nat := 1238633781515568547656355

theorem tailTrace_7236692 : CollatzResearch.WordTrace tailWord_7236692 prefixEnd_7236692 1238633781515568547656355 := by
  unfold tailWord_7236692
  simp only [CollatzResearch.WordTrace]
  refine ⟨131971920549354143720704165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175962560732472191627605553 131971920549354143720704165)
  ·
    refine ⟨24744735103003901947632031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131971920549354143720704165 24744735103003901947632031)
    ·
      refine ⟨37117102654505852921448047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24744735103003901947632031 37117102654505852921448047)
      ·
        refine ⟨55675653981758779382172071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37117102654505852921448047 55675653981758779382172071)
        ·
          refine ⟨83513480972638169073258107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55675653981758779382172071 83513480972638169073258107)
          ·
            refine ⟨125270221458957253609887161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83513480972638169073258107 125270221458957253609887161)
            ·
              refine ⟨93952666094217940207415371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125270221458957253609887161 93952666094217940207415371)
              ·
                refine ⟨140928999141326910311123057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93952666094217940207415371 140928999141326910311123057)
                ·
                  refine ⟨105696749355995182733342293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140928999141326910311123057 105696749355995182733342293)
                  ·
                    refine ⟨1238633781515568547656355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105696749355995182733342293 1238633781515568547656355)
                    ·
                      rfl

theorem cell23_7236692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_7236692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236692 prefixEnd_7236692 := by exact prefixLift 7236692
  have htrace : WordTrace (prefixWord ++ tailWord_7236692) baseStart_7236692 baseEnd_7236692 := by
    simpa [prefixWord, tailWord_7236692, baseEnd_7236692] using wordTrace_append hprefix tailTrace_7236692
  have hstable : (prefixWord ++ tailWord_7236692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236692).length < 2 ^ (prefixWord ++ tailWord_7236692).sum := by decide
  have hdescent : baseEnd_7236692 < baseStart_7236692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236719 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 3]
def baseStart_7236719 : Nat := 118140960795 + 7236719 * 2 ^ 59
def prefixEnd_7236719 : Nat := 4983230072969 + 3 ^ 40 * 7236719 * 2
def baseEnd_7236719 : Nat := 3715915208524377037331441

theorem tailTrace_7236719 : CollatzResearch.WordTrace tailWord_7236719 prefixEnd_7236719 3715915208524377037331441 := by
  unfold tailWord_7236719
  simp only [CollatzResearch.WordTrace]
  refine ⟨263944825869610471052641211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175963217246406980701760807 263944825869610471052641211)
  ·
    refine ⟨395917238804415706578961817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263944825869610471052641211 395917238804415706578961817)
    ·
      refine ⟨296937929103311779934221363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395917238804415706578961817 296937929103311779934221363)
      ·
        refine ⟨445406893654967669901332045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296937929103311779934221363 445406893654967669901332045)
        ·
          refine ⟨167027585120612876212999517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445406893654967669901332045 167027585120612876212999517)
          ·
            refine ⟨62635344420229828579874819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167027585120612876212999517 62635344420229828579874819)
            ·
              refine ⟨93953016630344742869812229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62635344420229828579874819 93953016630344742869812229)
              ·
                refine ⟨17616190618189639288089793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93953016630344742869812229 17616190618189639288089793)
                ·
                  refine ⟨13212142963642229466067345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17616190618189639288089793 13212142963642229466067345)
                  ·
                    refine ⟨9909107222731672099550509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13212142963642229466067345 9909107222731672099550509)
                    ·
                      refine ⟨3715915208524377037331441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9909107222731672099550509 3715915208524377037331441)
                      ·
                        rfl

theorem cell23_7236719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 3].length) (baseStart_7236719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236719 prefixEnd_7236719 := by exact prefixLift 7236719
  have htrace : WordTrace (prefixWord ++ tailWord_7236719) baseStart_7236719 baseEnd_7236719 := by
    simpa [prefixWord, tailWord_7236719, baseEnd_7236719] using wordTrace_append hprefix tailTrace_7236719
  have hstable : (prefixWord ++ tailWord_7236719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236719).length < 2 ^ (prefixWord ++ tailWord_7236719).sum := by decide
  have hdescent : baseEnd_7236719 < baseStart_7236719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236726 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_7236726 : Nat := 118140960795 + 7236726 * 2 ^ 59
def prefixEnd_7236726 : Nat := 4983230072969 + 3 ^ 40 * 7236726 * 2
def baseEnd_7236726 : Nat := 1238639600962986169981303

theorem tailTrace_7236726 : CollatzResearch.WordTrace tailWord_7236726 prefixEnd_7236726 1238639600962986169981303 := by
  unfold tailWord_7236726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16496567573786569453009127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 175963387453723407498764021 16496567573786569453009127)
  ·
    refine ⟨24744851360679854179513691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16496567573786569453009127 24744851360679854179513691)
    ·
      refine ⟨37117277041019781269270537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24744851360679854179513691 37117277041019781269270537)
      ·
        refine ⟨27837957780764835951952903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37117277041019781269270537 27837957780764835951952903)
        ·
          refine ⟨41756936671147253927929355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27837957780764835951952903 41756936671147253927929355)
          ·
            refine ⟨62635405006720880891894033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41756936671147253927929355 62635405006720880891894033)
            ·
              refine ⟨46976553755040660668920525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62635405006720880891894033 46976553755040660668920525)
              ·
                refine ⟨17616207658140247750845197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46976553755040660668920525 17616207658140247750845197)
                ·
                  refine ⟨6606077871802592906566949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17616207658140247750845197 6606077871802592906566949)
                  ·
                    refine ⟨1238639600962986169981303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6606077871802592906566949 1238639600962986169981303)
                    ·
                      rfl

theorem cell23_7236726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_7236726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236726 prefixEnd_7236726 := by exact prefixLift 7236726
  have htrace : WordTrace (prefixWord ++ tailWord_7236726) baseStart_7236726 baseEnd_7236726 := by
    simpa [prefixWord, tailWord_7236726, baseEnd_7236726] using wordTrace_append hprefix tailTrace_7236726
  have hstable : (prefixWord ++ tailWord_7236726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236726).length < 2 ^ (prefixWord ++ tailWord_7236726).sum := by decide
  have hdescent : baseEnd_7236726 < baseStart_7236726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236783 : List Nat := [1, 1, 2, 1, 2, 3, 4, 4, 1, 1, 3]
def baseStart_7236783 : Nat := 118140960795 + 7236783 * 2 ^ 59
def prefixEnd_7236783 : Nat := 4983230072969 + 3 ^ 40 * 7236783 * 2
def baseEnd_7236783 : Nat := 3715948071286264786931147

theorem tailTrace_7236783 : CollatzResearch.WordTrace tailWord_7236783 prefixEnd_7236783 3715948071286264786931147 := by
  unfold tailWord_7236783
  simp only [CollatzResearch.WordTrace]
  refine ⟨263947160141378609982971003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175964773427585739988647335 263947160141378609982971003)
  ·
    refine ⟨395920740212067914974456505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263947160141378609982971003 395920740212067914974456505)
    ·
      refine ⟨296940555159050936230842379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395920740212067914974456505 296940555159050936230842379)
      ·
        refine ⟨445410832738576404346263569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296940555159050936230842379 445410832738576404346263569)
        ·
          refine ⟨334058124553932303259697677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445410832738576404346263569 334058124553932303259697677)
          ·
            refine ⟨125271796707724613722386629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334058124553932303259697677 125271796707724613722386629)
            ·
              refine ⟨23488461882698365072947493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125271796707724613722386629 23488461882698365072947493)
              ·
                refine ⟨4404086603005943451177655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23488461882698365072947493 4404086603005943451177655)
                ·
                  refine ⟨6606129904508915176766483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404086603005943451177655 6606129904508915176766483)
                  ·
                    refine ⟨9909194856763372765149725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6606129904508915176766483 9909194856763372765149725)
                    ·
                      refine ⟨3715948071286264786931147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9909194856763372765149725 3715948071286264786931147)
                      ·
                        rfl

theorem cell23_7236783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 1, 1, 3].length) (baseStart_7236783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236783 prefixEnd_7236783 := by exact prefixLift 7236783
  have htrace : WordTrace (prefixWord ++ tailWord_7236783) baseStart_7236783 baseEnd_7236783 := by
    simpa [prefixWord, tailWord_7236783, baseEnd_7236783] using wordTrace_append hprefix tailTrace_7236783
  have hstable : (prefixWord ++ tailWord_7236783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236783).length < 2 ^ (prefixWord ++ tailWord_7236783).sum := by decide
  have hdescent : baseEnd_7236783 < baseStart_7236783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236799 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 1, 6]
def baseStart_7236799 : Nat := 118140960795 + 7236799 * 2 ^ 59
def prefixEnd_7236799 : Nat := 4983230072969 + 3 ^ 40 * 7236799 * 2
def baseEnd_7236799 : Nat := 1238652095658912241443691

theorem tailTrace_7236799 : CollatzResearch.WordTrace tailWord_7236799 prefixEnd_7236799 1238652095658912241443691 := by
  unfold tailWord_7236799
  simp only [CollatzResearch.WordTrace]
  refine ⟨263947743709320644715553451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175965162472880429810368967 263947743709320644715553451)
  ·
    refine ⟨395921615563980967073330177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263947743709320644715553451 395921615563980967073330177)
    ·
      refine ⟨296941211672985725304997633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395921615563980967073330177 296941211672985725304997633)
      ·
        refine ⟨222705908754739293978748225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296941211672985725304997633 222705908754739293978748225)
        ·
          refine ⟨167029431566054470484061169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222705908754739293978748225 167029431566054470484061169)
          ·
            refine ⟨125272073674540852863045877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167029431566054470484061169 125272073674540852863045877)
            ·
              refine ⟨11744256906988204955910551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125272073674540852863045877 11744256906988204955910551)
              ·
                refine ⟨17616385360482307433865827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11744256906988204955910551 17616385360482307433865827)
                ·
                  refine ⟨26424578040723461150798741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17616385360482307433865827 26424578040723461150798741)
                  ·
                    refine ⟨1238652095658912241443691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26424578040723461150798741 1238652095658912241443691)
                    ·
                      rfl

theorem cell23_7236799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 6].length) (baseStart_7236799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236799 prefixEnd_7236799 := by exact prefixLift 7236799
  have htrace : WordTrace (prefixWord ++ tailWord_7236799) baseStart_7236799 baseEnd_7236799 := by
    simpa [prefixWord, tailWord_7236799, baseEnd_7236799] using wordTrace_append hprefix tailTrace_7236799
  have hstable : (prefixWord ++ tailWord_7236799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236799).length < 2 ^ (prefixWord ++ tailWord_7236799).sum := by decide
  have hdescent : baseEnd_7236799 < baseStart_7236799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236809 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 7, 2, 3]
def baseStart_7236809 : Nat := 118140960795 + 7236809 * 2 ^ 59
def prefixEnd_7236809 : Nat := 4983230072969 + 3 ^ 40 * 7236809 * 2
def baseEnd_7236809 : Nat := 3715961421783281685206027

theorem tailTrace_7236809 : CollatzResearch.WordTrace tailWord_7236809 prefixEnd_7236809 3715961421783281685206027 := by
  unfold tailWord_7236809
  simp only [CollatzResearch.WordTrace]
  refine ⟨263948108439284416423417481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175965405626189610948944987 263948108439284416423417481)
  ·
    refine ⟨197961081329463312317563111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263948108439284416423417481 197961081329463312317563111)
    ·
      refine ⟨296941621994194968476344667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197961081329463312317563111 296941621994194968476344667)
      ·
        refine ⟨445412432991292452714517001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296941621994194968476344667 445412432991292452714517001)
        ·
          refine ⟨334059324743469339535887751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445412432991292452714517001 334059324743469339535887751)
          ·
            refine ⟨501088987115204009303831627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334059324743469339535887751 501088987115204009303831627)
            ·
              refine ⟨751633480672806013955747441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501088987115204009303831627 751633480672806013955747441)
              ·
                refine ⟨563725110504604510466810581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751633480672806013955747441 563725110504604510466810581)
                ·
                  refine ⟨13212307277451668214065873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 563725110504604510466810581 13212307277451668214065873)
                  ·
                    refine ⟨9909230458088751160549405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13212307277451668214065873 9909230458088751160549405)
                    ·
                      refine ⟨3715961421783281685206027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9909230458088751160549405 3715961421783281685206027)
                      ·
                        rfl

theorem cell23_7236809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 2, 3].length) (baseStart_7236809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236809 prefixEnd_7236809 := by exact prefixLift 7236809
  have htrace : WordTrace (prefixWord ++ tailWord_7236809) baseStart_7236809 baseEnd_7236809 := by
    simpa [prefixWord, tailWord_7236809, baseEnd_7236809] using wordTrace_append hprefix tailTrace_7236809
  have hstable : (prefixWord ++ tailWord_7236809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236809).length < 2 ^ (prefixWord ++ tailWord_7236809).sum := by decide
  have hdescent : baseEnd_7236809 < baseStart_7236809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236860 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_7236860 : Nat := 118140960795 + 7236860 * 2 ^ 59
def prefixEnd_7236860 : Nat := 4983230072969 + 3 ^ 40 * 7236860 * 2
def baseEnd_7236860 : Nat := 3715987609296660985668293

theorem tailTrace_7236860 : CollatzResearch.WordTrace tailWord_7236860 prefixEnd_7236860 3715987609296660985668293 := by
  unfold tailWord_7236860
  simp only [CollatzResearch.WordTrace]
  refine ⟨131974984281049826066762017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175966645708066434755682689 131974984281049826066762017)
  ·
    refine ⟨98981238210787369550071513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131974984281049826066762017 98981238210787369550071513)
    ·
      refine ⟨74235928658090527162553635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98981238210787369550071513 74235928658090527162553635)
      ·
        refine ⟨111353892987135790743830453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74235928658090527162553635 111353892987135790743830453)
        ·
          refine ⟨10439427467543980382234105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111353892987135790743830453 10439427467543980382234105)
          ·
            refine ⟨7829570600657985286675579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10439427467543980382234105 7829570600657985286675579)
            ·
              refine ⟨11744355900986977930013369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7829570600657985286675579 11744355900986977930013369)
              ·
                refine ⟨8808266925740233447510027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11744355900986977930013369 8808266925740233447510027)
                ·
                  refine ⟨13212400388610350171265041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8808266925740233447510027 13212400388610350171265041)
                  ·
                    refine ⟨9909300291457762628448781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13212400388610350171265041 9909300291457762628448781)
                    ·
                      refine ⟨3715987609296660985668293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9909300291457762628448781 3715987609296660985668293)
                      ·
                        rfl

theorem cell23_7236860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_7236860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236860 prefixEnd_7236860 := by exact prefixLift 7236860
  have htrace : WordTrace (prefixWord ++ tailWord_7236860) baseStart_7236860 baseEnd_7236860 := by
    simpa [prefixWord, tailWord_7236860, baseEnd_7236860] using wordTrace_append hprefix tailTrace_7236860
  have hstable : (prefixWord ++ tailWord_7236860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236860).length < 2 ^ (prefixWord ++ tailWord_7236860).sum := by decide
  have hdescent : baseEnd_7236860 < baseStart_7236860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236890 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3]
def baseStart_7236890 : Nat := 118140960795 + 7236890 * 2 ^ 59
def prefixEnd_7236890 : Nat := 4983230072969 + 3 ^ 40 * 7236890 * 2
def baseEnd_7236890 : Nat := 3716003013716295868293155

theorem tailTrace_7236890 : CollatzResearch.WordTrace tailWord_7236890 prefixEnd_7236890 3716003013716295868293155 := by
  unfold tailWord_7236890
  simp only [CollatzResearch.WordTrace]
  refine ⟨65987765687997741814279031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175967375167993978171410749 65987765687997741814279031)
  ·
    refine ⟨98981648531996612721418547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65987765687997741814279031 98981648531996612721418547)
    ·
      refine ⟨148472472797994919082127821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98981648531996612721418547 148472472797994919082127821)
      ·
        refine ⟨55677177299248094655797933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148472472797994919082127821 55677177299248094655797933)
        ·
          refine ⟨20878941487218035495924225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55677177299248094655797933 20878941487218035495924225)
          ·
            refine ⟨15659206115413526621943169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20878941487218035495924225 15659206115413526621943169)
            ·
              refine ⟨11744404586560144966457377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15659206115413526621943169 11744404586560144966457377)
              ·
                refine ⟨8808303439920108724843033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11744404586560144966457377 8808303439920108724843033)
                ·
                  refine ⟨6606227579940081543632275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8808303439920108724843033 6606227579940081543632275)
                  ·
                    refine ⟨9909341369910122315448413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6606227579940081543632275 9909341369910122315448413)
                    ·
                      refine ⟨3716003013716295868293155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9909341369910122315448413 3716003013716295868293155)
                      ·
                        rfl

theorem cell23_7236890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_7236890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236890 prefixEnd_7236890 := by exact prefixLift 7236890
  have htrace : WordTrace (prefixWord ++ tailWord_7236890) baseStart_7236890 baseEnd_7236890 := by
    simpa [prefixWord, tailWord_7236890, baseEnd_7236890] using wordTrace_append hprefix tailTrace_7236890
  have hstable : (prefixWord ++ tailWord_7236890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236890).length < 2 ^ (prefixWord ++ tailWord_7236890).sum := by decide
  have hdescent : baseEnd_7236890 < baseStart_7236890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236906 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_7236906 : Nat := 118140960795 + 7236906 * 2 ^ 59
def prefixEnd_7236906 : Nat := 4983230072969 + 3 ^ 40 * 7236906 * 2
def baseEnd_7236906 : Nat := 1238670409802255935231027

theorem tailTrace_7236906 : CollatzResearch.WordTrace tailWord_7236906 prefixEnd_7236906 1238670409802255935231027 := by
  unfold tailWord_7236906
  simp only [CollatzResearch.WordTrace]
  refine ⟨65987911579983250497424643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175967764213288667993132381 65987911579983250497424643)
  ·
    refine ⟨98981867369974875746136965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65987911579983250497424643 98981867369974875746136965)
    ·
      refine ⟨18559100131870289202400681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98981867369974875746136965 18559100131870289202400681)
      ·
        refine ⟨13919325098902716901800511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18559100131870289202400681 13919325098902716901800511)
        ·
          refine ⟨20878987648354075352700767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13919325098902716901800511 20878987648354075352700767)
          ·
            refine ⟨31318481472531113029051151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20878987648354075352700767 31318481472531113029051151)
            ·
              refine ⟨46977722208796669543576727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31318481472531113029051151 46977722208796669543576727)
              ·
                refine ⟨70466583313195004315365091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46977722208796669543576727 70466583313195004315365091)
                ·
                  refine ⟨105699874969792506473047637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70466583313195004315365091 105699874969792506473047637)
                  ·
                    refine ⟨1238670409802255935231027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105699874969792506473047637 1238670409802255935231027)
                    ·
                      rfl

theorem cell23_7236906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_7236906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236906 prefixEnd_7236906 := by exact prefixLift 7236906
  have htrace : WordTrace (prefixWord ++ tailWord_7236906) baseStart_7236906 baseEnd_7236906 := by
    simpa [prefixWord, tailWord_7236906, baseEnd_7236906] using wordTrace_append hprefix tailTrace_7236906
  have hstable : (prefixWord ++ tailWord_7236906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236906).length < 2 ^ (prefixWord ++ tailWord_7236906).sum := by decide
  have hdescent : baseEnd_7236906 < baseStart_7236906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236913 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 1, 4, 2]
def baseStart_7236913 : Nat := 118140960795 + 7236913 * 2 ^ 59
def prefixEnd_7236913 : Nat := 4983230072969 + 3 ^ 40 * 7236913 * 2
def baseEnd_7236913 : Nat := 3716014823771349278305549

theorem tailTrace_7236913 : CollatzResearch.WordTrace tailWord_7236913 prefixEnd_7236913 3716014823771349278305549 := by
  unfold tailWord_7236913
  simp only [CollatzResearch.WordTrace]
  refine ⟨263951901630907642185203393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175967934420605094790135595 263951901630907642185203393)
  ·
    refine ⟨197963926223180731638902545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263951901630907642185203393 197963926223180731638902545)
    ·
      refine ⟨148472944667385548729176909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197963926223180731638902545 148472944667385548729176909)
      ·
        refine ⟨55677354250269580773441341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148472944667385548729176909 55677354250269580773441341)
        ·
          refine ⟨20879007843851092790040503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55677354250269580773441341 20879007843851092790040503)
          ·
            refine ⟨31318511765776639185060755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20879007843851092790040503 31318511765776639185060755)
            ·
              refine ⟨46977767648664958777591133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31318511765776639185060755 46977767648664958777591133)
              ·
                refine ⟨17616662868249359541596675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46977767648664958777591133 17616662868249359541596675)
                ·
                  refine ⟨26424994302374039312395013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17616662868249359541596675 26424994302374039312395013)
                  ·
                    refine ⟨4954686431695132371074065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26424994302374039312395013 4954686431695132371074065)
                    ·
                      refine ⟨3716014823771349278305549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954686431695132371074065 3716014823771349278305549)
                      ·
                        rfl

theorem cell23_7236913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_7236913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236913 prefixEnd_7236913 := by exact prefixLift 7236913
  have htrace : WordTrace (prefixWord ++ tailWord_7236913) baseStart_7236913 baseEnd_7236913 := by
    simpa [prefixWord, tailWord_7236913, baseEnd_7236913] using wordTrace_append hprefix tailTrace_7236913
  have hstable : (prefixWord ++ tailWord_7236913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236913).length < 2 ^ (prefixWord ++ tailWord_7236913).sum := by decide
  have hdescent : baseEnd_7236913 < baseStart_7236913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236926 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 1, 4, 4]
def baseStart_7236926 : Nat := 118140960795 + 7236926 * 2 ^ 59
def prefixEnd_7236926 : Nat := 4983230072969 + 3 ^ 40 * 7236926 * 2
def baseEnd_7236926 : Nat := 3716021499019857727442989

theorem tailTrace_7236926 : CollatzResearch.WordTrace tailWord_7236926 prefixEnd_7236926 3716021499019857727442989 := by
  unfold tailWord_7236926
  simp only [CollatzResearch.WordTrace]
  refine ⟨32994046972482568175678329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175968250519907030270284421 32994046972482568175678329)
  ·
    refine ⟨24745535229361926131758747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32994046972482568175678329 24745535229361926131758747)
    ·
      refine ⟨37118302844042889197638121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24745535229361926131758747 37118302844042889197638121)
      ·
        refine ⟨27838727133032166898228591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37118302844042889197638121 27838727133032166898228591)
        ·
          refine ⟨41758090699548250347342887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27838727133032166898228591 41758090699548250347342887)
          ·
            refine ⟨62637136049322375521014331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41758090699548250347342887 62637136049322375521014331)
            ·
              refine ⟨93955704073983563281521497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62637136049322375521014331 93955704073983563281521497)
              ·
                refine ⟨70466778055487672461141123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93955704073983563281521497 70466778055487672461141123)
                ·
                  refine ⟨105700167083231508691711685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70466778055487672461141123 105700167083231508691711685)
                  ·
                    refine ⟨19818781328105907879695941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105700167083231508691711685 19818781328105907879695941)
                    ·
                      refine ⟨3716021499019857727442989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19818781328105907879695941 3716021499019857727442989)
                      ·
                        rfl

theorem cell23_7236926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_7236926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236926 prefixEnd_7236926 := by exact prefixLift 7236926
  have htrace : WordTrace (prefixWord ++ tailWord_7236926) baseStart_7236926 baseEnd_7236926 := by
    simpa [prefixWord, tailWord_7236926, baseEnd_7236926] using wordTrace_append hprefix tailTrace_7236926
  have hstable : (prefixWord ++ tailWord_7236926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236926).length < 2 ^ (prefixWord ++ tailWord_7236926).sum := by decide
  have hdescent : baseEnd_7236926 < baseStart_7236926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236941 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_7236941 : Nat := 118140960795 + 7236941 * 2 ^ 59
def prefixEnd_7236941 : Nat := 4983230072969 + 3 ^ 40 * 7236941 * 2
def baseEnd_7236941 : Nat := 3716029201229675168755421

theorem tailTrace_7236941 : CollatzResearch.WordTrace tailWord_7236941 prefixEnd_7236941 3716029201229675168755421 := by
  unfold tailWord_7236941
  simp only [CollatzResearch.WordTrace]
  refine ⟨263952922874806202967222677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175968615249870801978148451 263952922874806202967222677)
  ·
    refine ⟨12372793259756540764088563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 263952922874806202967222677 12372793259756540764088563)
    ·
      refine ⟨18559189889634811146132845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12372793259756540764088563 18559189889634811146132845)
      ·
        refine ⟨6959696208613054179799817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18559189889634811146132845 6959696208613054179799817)
        ·
          refine ⟨5219772156459790634849863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6959696208613054179799817 5219772156459790634849863)
          ·
            refine ⟨7829658234689685952274795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5219772156459790634849863 7829658234689685952274795)
            ·
              refine ⟨11744487352034528928412193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7829658234689685952274795 11744487352034528928412193)
              ·
                refine ⟨8808365514025896696309145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11744487352034528928412193 8808365514025896696309145)
                ·
                  refine ⟨6606274135519422522231859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8808365514025896696309145 6606274135519422522231859)
                  ·
                    refine ⟨9909411203279133783347789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6606274135519422522231859 9909411203279133783347789)
                    ·
                      refine ⟨3716029201229675168755421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9909411203279133783347789 3716029201229675168755421)
                      ·
                        rfl

theorem cell23_7236941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_7236941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236941 prefixEnd_7236941 := by exact prefixLift 7236941
  have htrace : WordTrace (prefixWord ++ tailWord_7236941) baseStart_7236941 baseEnd_7236941 := by
    simpa [prefixWord, tailWord_7236941, baseEnd_7236941] using wordTrace_append hprefix tailTrace_7236941
  have hstable : (prefixWord ++ tailWord_7236941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236941).length < 2 ^ (prefixWord ++ tailWord_7236941).sum := by decide
  have hdescent : baseEnd_7236941 < baseStart_7236941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7236959 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_7236959 : Nat := 118140960795 + 7236959 * 2 ^ 59
def prefixEnd_7236959 : Nat := 4983230072969 + 3 ^ 40 * 7236959 * 2
def baseEnd_7236959 : Nat := 3716038443881456098330337

theorem tailTrace_7236959 : CollatzResearch.WordTrace tailWord_7236959 prefixEnd_7236959 3716038443881456098330337 := by
  unfold tailWord_7236959
  simp only [CollatzResearch.WordTrace]
  refine ⟨263953579388740992041377931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175969052925827328027585287 263953579388740992041377931)
  ·
    refine ⟨395930369083111488062066897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263953579388740992041377931 395930369083111488062066897)
    ·
      refine ⟨296947776812333616046550173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395930369083111488062066897 296947776812333616046550173)
      ·
        refine ⟨111355416304625106017456315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296947776812333616046550173 111355416304625106017456315)
        ·
          refine ⟨167033124456937659026184473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111355416304625106017456315 167033124456937659026184473)
          ·
            refine ⟨125274843342703244269638355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167033124456937659026184473 125274843342703244269638355)
            ·
              refine ⟨187912265014054866404457533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125274843342703244269638355 187912265014054866404457533)
              ·
                refine ⟨70467099380270574901671575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187912265014054866404457533 70467099380270574901671575)
                ·
                  refine ⟨105700649070405862352507363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70467099380270574901671575 105700649070405862352507363)
                  ·
                    refine ⟨158550973605608793528761045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105700649070405862352507363 158550973605608793528761045)
                    ·
                      refine ⟨3716038443881456098330337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158550973605608793528761045 3716038443881456098330337)
                      ·
                        rfl

theorem cell23_7236959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_7236959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7236959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7236959 prefixEnd_7236959 := by exact prefixLift 7236959
  have htrace : WordTrace (prefixWord ++ tailWord_7236959) baseStart_7236959 baseEnd_7236959 := by
    simpa [prefixWord, tailWord_7236959, baseEnd_7236959] using wordTrace_append hprefix tailTrace_7236959
  have hstable : (prefixWord ++ tailWord_7236959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7236959).length < 2 ^ (prefixWord ++ tailWord_7236959).sum := by decide
  have hdescent : baseEnd_7236959 < baseStart_7236959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7236959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237010 : List Nat := [3, 2, 3, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_7237010 : Nat := 118140960795 + 7237010 * 2 ^ 59
def prefixEnd_7237010 : Nat := 4983230072969 + 3 ^ 40 * 7237010 * 2
def baseEnd_7237010 : Nat := 3716064631394835398792603

theorem tailTrace_7237010 : CollatzResearch.WordTrace tailWord_7237010 prefixEnd_7237010 3716064631394835398792603 := by
  unfold tailWord_7237010
  simp only [CollatzResearch.WordTrace]
  refine ⟨65988859877889056937871121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175970293007704151834322989 65988859877889056937871121)
  ·
    refine ⟨49491644908416792703403341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65988859877889056937871121 49491644908416792703403341)
    ·
      refine ⟨18559366840656297263776253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49491644908416792703403341 18559366840656297263776253)
      ·
        refine ⟨6959762565246111473916095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18559366840656297263776253 6959762565246111473916095)
        ·
          refine ⟨10439643847869167210874143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6959762565246111473916095 10439643847869167210874143)
          ·
            refine ⟨15659465771803750816311215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10439643847869167210874143 15659465771803750816311215)
            ·
              refine ⟨23489198657705626224466823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15659465771803750816311215 23489198657705626224466823)
              ·
                refine ⟨35233797986558439336700235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23489198657705626224466823 35233797986558439336700235)
                ·
                  refine ⟨52850696979837659005050353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35233797986558439336700235 52850696979837659005050353)
                  ·
                    refine ⟨39638022734878244253787765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52850696979837659005050353 39638022734878244253787765)
                    ·
                      refine ⟨3716064631394835398792603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39638022734878244253787765 3716064631394835398792603)
                      ·
                        rfl

theorem cell23_7237010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_7237010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237010 prefixEnd_7237010 := by exact prefixLift 7237010
  have htrace : WordTrace (prefixWord ++ tailWord_7237010) baseStart_7237010 baseEnd_7237010 := by
    simpa [prefixWord, tailWord_7237010, baseEnd_7237010] using wordTrace_append hprefix tailTrace_7237010
  have hstable : (prefixWord ++ tailWord_7237010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237010).length < 2 ^ (prefixWord ++ tailWord_7237010).sum := by decide
  have hdescent : baseEnd_7237010 < baseStart_7237010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237013 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 3, 4]
def baseStart_7237013 : Nat := 118140960795 + 7237013 * 2 ^ 59
def prefixEnd_7237013 : Nat := 4983230072969 + 3 ^ 40 * 7237013 * 2
def baseEnd_7237013 : Nat := 1238688723945599629018363

theorem tailTrace_7237013 : CollatzResearch.WordTrace tailWord_7237013 prefixEnd_7237013 1238688723945599629018363 := by
  unfold tailWord_7237013
  simp only [CollatzResearch.WordTrace]
  refine ⟨263955548930545359263843693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175970365953696906175895795 263955548930545359263843693)
  ·
    refine ⟨98983330848954509723941385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263955548930545359263843693 98983330848954509723941385)
    ·
      refine ⟨74237498136715882292956039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98983330848954509723941385 74237498136715882292956039)
      ·
        refine ⟨111356247205073823439434059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74237498136715882292956039 111356247205073823439434059)
        ·
          refine ⟨167034370807610735159151089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111356247205073823439434059 167034370807610735159151089)
          ·
            refine ⟨125275778105708051369363317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167034370807610735159151089 125275778105708051369363317)
            ·
              refine ⟨11744604197410129815877811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125275778105708051369363317 11744604197410129815877811)
              ·
                refine ⟨17616906296115194723816717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11744604197410129815877811 17616906296115194723816717)
                ·
                  refine ⟨6606339861043198021431269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17616906296115194723816717 6606339861043198021431269)
                  ·
                    refine ⟨1238688723945599629018363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6606339861043198021431269 1238688723945599629018363)
                    ·
                      rfl

theorem cell23_7237013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_7237013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237013 prefixEnd_7237013 := by exact prefixLift 7237013
  have htrace : WordTrace (prefixWord ++ tailWord_7237013) baseStart_7237013 baseEnd_7237013 := by
    simpa [prefixWord, tailWord_7237013, baseEnd_7237013] using wordTrace_append hprefix tailTrace_7237013
  have hstable : (prefixWord ++ tailWord_7237013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237013).length < 2 ^ (prefixWord ++ tailWord_7237013).sum := by decide
  have hdescent : baseEnd_7237013 < baseStart_7237013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237019 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 9]
def baseStart_7237019 : Nat := 118140960795 + 7237019 * 2 ^ 59
def prefixEnd_7237019 : Nat := 4983230072969 + 3 ^ 40 * 7237019 * 2
def baseEnd_7237019 : Nat := 3716069252720725863580061

theorem tailTrace_7237019 : CollatzResearch.WordTrace tailWord_7237019 prefixEnd_7237019 3716069252720725863580061 := by
  unfold tailWord_7237019
  simp only [CollatzResearch.WordTrace]
  refine ⟨263955767768523622288562111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175970511845682414859041407 263955767768523622288562111)
  ·
    refine ⟨395933651652785433432843167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263955767768523622288562111 395933651652785433432843167)
    ·
      refine ⟨593900477479178150149264751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395933651652785433432843167 593900477479178150149264751)
      ·
        refine ⟨890850716218767225223897127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593900477479178150149264751 890850716218767225223897127)
        ·
          refine ⟨1336276074328150837835845691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890850716218767225223897127 1336276074328150837835845691)
          ·
            refine ⟨2004414111492226256753768537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336276074328150837835845691 2004414111492226256753768537)
            ·
              refine ⟨1503310583619169692565326403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2004414111492226256753768537 1503310583619169692565326403)
              ·
                refine ⟨2254965875428754538847989605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503310583619169692565326403 2254965875428754538847989605)
                ·
                  refine ⟨422806101642891476033998051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2254965875428754538847989605 422806101642891476033998051)
                  ·
                    refine ⟨634209152464337214050997077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 422806101642891476033998051 634209152464337214050997077)
                    ·
                      refine ⟨3716069252720725863580061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 634209152464337214050997077 3716069252720725863580061)
                      ·
                        rfl

theorem cell23_7237019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_7237019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237019 prefixEnd_7237019 := by exact prefixLift 7237019
  have htrace : WordTrace (prefixWord ++ tailWord_7237019) baseStart_7237019 baseEnd_7237019 := by
    simpa [prefixWord, tailWord_7237019, baseEnd_7237019] using wordTrace_append hprefix tailTrace_7237019
  have hstable : (prefixWord ++ tailWord_7237019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237019).length < 2 ^ (prefixWord ++ tailWord_7237019).sum := by decide
  have hdescent : baseEnd_7237019 < baseStart_7237019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237036 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 3]
def baseStart_7237036 : Nat := 118140960795 + 7237036 * 2 ^ 59
def prefixEnd_7237036 : Nat := 4983230072969 + 3 ^ 40 * 7237036 * 2
def baseEnd_7237036 : Nat := 3716077981891852297067483

theorem tailTrace_7237036 : CollatzResearch.WordTrace tailWord_7237036 prefixEnd_7237036 3716077981891852297067483 := by
  unfold tailWord_7237036
  simp only [CollatzResearch.WordTrace]
  refine ⟨131978193904731017095965481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175970925206308022794620641 131978193904731017095965481)
  ·
    refine ⟨98983645428548262821974111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131978193904731017095965481 98983645428548262821974111)
    ·
      refine ⟨148475468142822394232961167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98983645428548262821974111 148475468142822394232961167)
      ·
        refine ⟨222713202214233591349441751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148475468142822394232961167 222713202214233591349441751)
        ·
          refine ⟨334069803321350387024162627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222713202214233591349441751 334069803321350387024162627)
          ·
            refine ⟨501104704982025580536243941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334069803321350387024162627 501104704982025580536243941)
            ·
              refine ⟨93957132184129796350545739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 501104704982025580536243941 93957132184129796350545739)
              ·
                refine ⟨140935698276194694525818609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93957132184129796350545739 140935698276194694525818609)
                ·
                  refine ⟨105701773707146020894363957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140935698276194694525818609 105701773707146020894363957)
                  ·
                    refine ⟨9909541285044939458846621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105701773707146020894363957 9909541285044939458846621)
                    ·
                      refine ⟨3716077981891852297067483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9909541285044939458846621 3716077981891852297067483)
                      ·
                        rfl

theorem cell23_7237036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_7237036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237036 prefixEnd_7237036 := by exact prefixLift 7237036
  have htrace : WordTrace (prefixWord ++ tailWord_7237036) baseStart_7237036 baseEnd_7237036 := by
    simpa [prefixWord, tailWord_7237036, baseEnd_7237036] using wordTrace_append hprefix tailTrace_7237036
  have hstable : (prefixWord ++ tailWord_7237036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237036).length < 2 ^ (prefixWord ++ tailWord_7237036).sum := by decide
  have hdescent : baseEnd_7237036 < baseStart_7237036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237060 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 6]
def baseStart_7237060 : Nat := 118140960795 + 7237060 * 2 ^ 59
def prefixEnd_7237060 : Nat := 4983230072969 + 3 ^ 40 * 7237060 * 2
def baseEnd_7237060 : Nat := 412898922825284467018597

theorem tailTrace_7237060 : CollatzResearch.WordTrace tailWord_7237060 prefixEnd_7237060 412898922825284467018597 := by
  unfold tailWord_7237060
  simp only [CollatzResearch.WordTrace]
  refine ⟨131978631580687543145402317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175971508774250057527203089 131978631580687543145402317)
  ·
    refine ⟨49491986842757828679525869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131978631580687543145402317 49491986842757828679525869)
    ·
      refine ⟨18559495066034185754822201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49491986842757828679525869 18559495066034185754822201)
      ·
        refine ⟨13919621299525639316116651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18559495066034185754822201 13919621299525639316116651)
        ·
          refine ⟨20879431949288458974174977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13919621299525639316116651 20879431949288458974174977)
          ·
            refine ⟨15659573961966344230631233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20879431949288458974174977 15659573961966344230631233)
            ·
              refine ⟨11744680471474758172973425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15659573961966344230631233 11744680471474758172973425)
              ·
                refine ⟨8808510353606068629730069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11744680471474758172973425 8808510353606068629730069)
                ·
                  refine ⟨412898922825284467018597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8808510353606068629730069 412898922825284467018597)
                  ·
                    rfl

theorem cell23_7237060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_7237060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237060 prefixEnd_7237060 := by exact prefixLift 7237060
  have htrace : WordTrace (prefixWord ++ tailWord_7237060) baseStart_7237060 baseEnd_7237060 := by
    simpa [prefixWord, tailWord_7237060, baseEnd_7237060] using wordTrace_append hprefix tailTrace_7237060
  have hstable : (prefixWord ++ tailWord_7237060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237060).length < 2 ^ (prefixWord ++ tailWord_7237060).sum := by decide
  have hdescent : baseEnd_7237060 < baseStart_7237060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237127 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 3, 2, 2]
def baseStart_7237127 : Nat := 118140960795 + 7237127 * 2 ^ 59
def prefixEnd_7237127 : Nat := 4983230072969 + 3 ^ 40 * 7237127 * 2
def baseEnd_7237127 : Nat := 3716124708631411441029565

theorem tailTrace_7237127 : CollatzResearch.WordTrace tailWord_7237127 prefixEnd_7237127 3716124708631411441029565 := by
  unfold tailWord_7237127
  simp only [CollatzResearch.WordTrace]
  refine ⟨263959706852132356733493635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175973137901421571155662423 263959706852132356733493635)
  ·
    refine ⟨395939560278198535100240453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263959706852132356733493635 395939560278198535100240453)
    ·
      refine ⟨74238667552162225331295085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 395939560278198535100240453 74238667552162225331295085)
      ·
        refine ⟨27839500332060834499235657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74238667552162225331295085 27839500332060834499235657)
        ·
          refine ⟨20879625249045625874426743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27839500332060834499235657 20879625249045625874426743)
          ·
            refine ⟨31319437873568438811640115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20879625249045625874426743 31319437873568438811640115)
            ·
              refine ⟨46979156810352658217460173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31319437873568438811640115 46979156810352658217460173)
              ·
                refine ⟨17617183803882246831547565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46979156810352658217460173 17617183803882246831547565)
                ·
                  refine ⟨6606443926455842561830337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17617183803882246831547565 6606443926455842561830337)
                  ·
                    refine ⟨4954832944841881921372753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6606443926455842561830337 4954832944841881921372753)
                    ·
                      refine ⟨3716124708631411441029565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954832944841881921372753 3716124708631411441029565)
                      ·
                        rfl

theorem cell23_7237127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_7237127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237127 prefixEnd_7237127 := by exact prefixLift 7237127
  have htrace : WordTrace (prefixWord ++ tailWord_7237127) baseStart_7237127 baseEnd_7237127 := by
    simpa [prefixWord, tailWord_7237127, baseEnd_7237127] using wordTrace_append hprefix tailTrace_7237127
  have hstable : (prefixWord ++ tailWord_7237127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237127).length < 2 ^ (prefixWord ++ tailWord_7237127).sum := by decide
  have hdescent : baseEnd_7237127 < baseStart_7237127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237170 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2]
def baseStart_7237170 : Nat := 118140960795 + 7237170 * 2 ^ 59
def prefixEnd_7237170 : Nat := 4983230072969 + 3 ^ 40 * 7237170 * 2
def baseEnd_7237170 : Nat := 3716146788299554772791867

theorem tailTrace_7237170 : CollatzResearch.WordTrace tailWord_7237170 prefixEnd_7237170 3716146788299554772791867 := by
  unfold tailWord_7237170
  simp only [CollatzResearch.WordTrace]
  refine ⟨65990318797744143769327241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175974183460651050051539309 65990318797744143769327241)
  ·
    refine ⟨49492739098308107826995431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65990318797744143769327241 49492739098308107826995431)
    ·
      refine ⟨74239108647462161740493147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49492739098308107826995431 74239108647462161740493147)
      ·
        refine ⟨111358662971193242610739721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74239108647462161740493147 111358662971193242610739721)
        ·
          refine ⟨83518997228394931958054791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111358662971193242610739721 83518997228394931958054791)
          ·
            refine ⟨125278495842592397937082187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83518997228394931958054791 125278495842592397937082187)
            ·
              refine ⟨187917743763888596905623281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125278495842592397937082187 187917743763888596905623281)
              ·
                refine ⟨140938307822916447679217461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187917743763888596905623281 140938307822916447679217461)
                ·
                  refine ⟨13212966358398416969926637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140938307822916447679217461 13212966358398416969926637)
                  ·
                    refine ⟨4954862384399406363722489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13212966358398416969926637 4954862384399406363722489)
                    ·
                      refine ⟨3716146788299554772791867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954862384399406363722489 3716146788299554772791867)
                      ·
                        rfl

theorem cell23_7237170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_7237170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237170 prefixEnd_7237170 := by exact prefixLift 7237170
  have htrace : WordTrace (prefixWord ++ tailWord_7237170) baseStart_7237170 baseEnd_7237170 := by
    simpa [prefixWord, tailWord_7237170, baseEnd_7237170] using wordTrace_append hprefix tailTrace_7237170
  have hstable : (prefixWord ++ tailWord_7237170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237170).length < 2 ^ (prefixWord ++ tailWord_7237170).sum := by decide
  have hdescent : baseEnd_7237170 < baseStart_7237170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237200 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 1, 4, 2]
def baseStart_7237200 : Nat := 118140960795 + 7237200 * 2 ^ 59
def prefixEnd_7237200 : Nat := 4983230072969 + 3 ^ 40 * 7237200 * 2
def baseEnd_7237200 : Nat := 3716162192719189655416729

theorem tailTrace_7237200 : CollatzResearch.WordTrace tailWord_7237200 prefixEnd_7237200 3716162192719189655416729 := by
  unfold tailWord_7237200
  simp only [CollatzResearch.WordTrace]
  refine ⟨131981184690433945100450527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175974912920578593467267369 131981184690433945100450527)
  ·
    refine ⟨197971777035650917650675791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131981184690433945100450527 197971777035650917650675791)
    ·
      refine ⟨296957665553476376476013687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197971777035650917650675791 296957665553476376476013687)
      ·
        refine ⟨445436498330214564714020531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296957665553476376476013687 445436498330214564714020531)
        ·
          refine ⟨668154747495321847071030797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445436498330214564714020531 668154747495321847071030797)
          ·
            refine ⟨250558030310745692651636549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 668154747495321847071030797 250558030310745692651636549)
            ·
              refine ⟨46979630683264817372181853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 250558030310745692651636549 46979630683264817372181853)
              ·
                refine ⟨17617361506224306514568195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46979630683264817372181853 17617361506224306514568195)
                ·
                  refine ⟨26426042259336459771852293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17617361506224306514568195 26426042259336459771852293)
                  ·
                    refine ⟨4954882923625586207222305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26426042259336459771852293 4954882923625586207222305)
                    ·
                      refine ⟨3716162192719189655416729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954882923625586207222305 3716162192719189655416729)
                      ·
                        rfl

theorem cell23_7237200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 4, 2].length) (baseStart_7237200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237200 prefixEnd_7237200 := by exact prefixLift 7237200
  have htrace : WordTrace (prefixWord ++ tailWord_7237200) baseStart_7237200 baseEnd_7237200 := by
    simpa [prefixWord, tailWord_7237200, baseEnd_7237200] using wordTrace_append hprefix tailTrace_7237200
  have hstable : (prefixWord ++ tailWord_7237200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237200).length < 2 ^ (prefixWord ++ tailWord_7237200).sum := by decide
  have hdescent : baseEnd_7237200 < baseStart_7237200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237233 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 3, 5, 3]
def baseStart_7237233 : Nat := 118140960795 + 7237233 * 2 ^ 59
def prefixEnd_7237233 : Nat := 4983230072969 + 3 ^ 40 * 7237233 * 2
def baseEnd_7237233 : Nat := 3716179137580788026304077

theorem tailTrace_7237233 : CollatzResearch.WordTrace tailWord_7237233 prefixEnd_7237233 3716179137580788026304077 := by
  unfold tailWord_7237233
  simp only [CollatzResearch.WordTrace]
  refine ⟨263963572989748336836852353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175975715326498891224568235 263963572989748336836852353)
  ·
    refine ⟨197972679742311252627639265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263963572989748336836852353 197972679742311252627639265)
    ·
      refine ⟨148479509806733439470729449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197972679742311252627639265 148479509806733439470729449)
      ·
        refine ⟨111359632355050079603047087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148479509806733439470729449 111359632355050079603047087)
        ·
          refine ⟨167039448532575119404570631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111359632355050079603047087 167039448532575119404570631)
          ·
            refine ⟨250559172798862679106855947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167039448532575119404570631 250559172798862679106855947)
            ·
              refine ⟨375838759198294018660283921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250559172798862679106855947 375838759198294018660283921)
              ·
                refine ⟨281879069398720513995212941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375838759198294018660283921 281879069398720513995212941)
                ·
                  refine ⟨105704651024520192748204853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281879069398720513995212941 105704651024520192748204853)
                  ·
                    refine ⟨9909811033548768070144205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105704651024520192748204853 9909811033548768070144205)
                    ·
                      refine ⟨3716179137580788026304077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9909811033548768070144205 3716179137580788026304077)
                      ·
                        rfl

theorem cell23_7237233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_7237233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237233 prefixEnd_7237233 := by exact prefixLift 7237233
  have htrace : WordTrace (prefixWord ++ tailWord_7237233) baseStart_7237233 baseEnd_7237233 := by
    simpa [prefixWord, tailWord_7237233, baseEnd_7237233] using wordTrace_append hprefix tailTrace_7237233
  have hstable : (prefixWord ++ tailWord_7237233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237233).length < 2 ^ (prefixWord ++ tailWord_7237233).sum := by decide
  have hdescent : baseEnd_7237233 < baseStart_7237233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237234 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 2, 2, 2]
def baseStart_7237234 : Nat := 118140960795 + 7237234 * 2 ^ 59
def prefixEnd_7237234 : Nat := 4983230072969 + 3 ^ 40 * 7237234 * 2
def baseEnd_7237234 : Nat := 3716179651061442522391573

theorem tailTrace_7237234 : CollatzResearch.WordTrace tailWord_7237234 prefixEnd_7237234 3716179651061442522391573 := by
  unfold tailWord_7237234
  simp only [CollatzResearch.WordTrace]
  refine ⟨65990902365686178501909689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175975739641829809338425837 65990902365686178501909689)
  ·
    refine ⟨49493176774264633876432267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65990902365686178501909689 49493176774264633876432267)
    ·
      refine ⟨74239765161396950814648401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49493176774264633876432267 74239765161396950814648401)
      ·
        refine ⟨55679823871047713110986301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74239765161396950814648401 55679823871047713110986301)
        ·
          refine ⟨20879933951642892416619863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55679823871047713110986301 20879933951642892416619863)
          ·
            refine ⟨31319900927464338624929795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20879933951642892416619863 31319900927464338624929795)
            ·
              refine ⟨46979851391196507937394693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31319900927464338624929795 46979851391196507937394693)
              ·
                refine ⟨8808722135849345238261505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46979851391196507937394693 8808722135849345238261505)
                ·
                  refine ⟨6606541601887008928696129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8808722135849345238261505 6606541601887008928696129)
                  ·
                    refine ⟨4954906201415256696522097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6606541601887008928696129 4954906201415256696522097)
                    ·
                      refine ⟨3716179651061442522391573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954906201415256696522097 3716179651061442522391573)
                      ·
                        rfl

theorem cell23_7237234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_7237234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237234 prefixEnd_7237234 := by exact prefixLift 7237234
  have htrace : WordTrace (prefixWord ++ tailWord_7237234) baseStart_7237234 baseEnd_7237234 := by
    simpa [prefixWord, tailWord_7237234, baseEnd_7237234] using wordTrace_append hprefix tailTrace_7237234
  have hstable : (prefixWord ++ tailWord_7237234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237234).length < 2 ^ (prefixWord ++ tailWord_7237234).sum := by decide
  have hdescent : baseEnd_7237234 < baseStart_7237234 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237253 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_7237253 : Nat := 118140960795 + 7237253 * 2 ^ 59
def prefixEnd_7237253 : Nat := 4983230072969 + 3 ^ 40 * 7237253 * 2
def baseEnd_7237253 : Nat := 1238729802397959316017995

theorem tailTrace_7237253 : CollatzResearch.WordTrace tailWord_7237253 prefixEnd_7237253 1238729802397959316017995 := by
  unfold tailWord_7237253
  simp only [CollatzResearch.WordTrace]
  refine ⟨263964302449675880252580413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175976201633117253501720275 263964302449675880252580413)
  ·
    refine ⟨98986613418628455094717655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263964302449675880252580413 98986613418628455094717655)
    ·
      refine ⟨148479920127942682642076483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98986613418628455094717655 148479920127942682642076483)
      ·
        refine ⟨222719880191914023963114725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148479920127942682642076483 222719880191914023963114725)
        ·
          refine ⟨41759977535983879493084011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222719880191914023963114725 41759977535983879493084011)
          ·
            refine ⟨62639966303975819239626017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41759977535983879493084011 62639966303975819239626017)
            ·
              refine ⟨46979974727981864429719513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62639966303975819239626017 46979974727981864429719513)
              ·
                refine ⟨35234981045986398322289635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46979974727981864429719513 35234981045986398322289635)
                ·
                  refine ⟨52852471568979597483434453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35234981045986398322289635 52852471568979597483434453)
                  ·
                    refine ⟨1238729802397959316017995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52852471568979597483434453 1238729802397959316017995)
                    ·
                      rfl

theorem cell23_7237253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_7237253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237253 prefixEnd_7237253 := by exact prefixLift 7237253
  have htrace : WordTrace (prefixWord ++ tailWord_7237253) baseStart_7237253 baseEnd_7237253 := by
    simpa [prefixWord, tailWord_7237253, baseEnd_7237253] using wordTrace_append hprefix tailTrace_7237253
  have hstable : (prefixWord ++ tailWord_7237253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237253).length < 2 ^ (prefixWord ++ tailWord_7237253).sum := by decide
  have hdescent : baseEnd_7237253 < baseStart_7237253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237260 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 2, 5, 2]
def baseStart_7237260 : Nat := 118140960795 + 7237260 * 2 ^ 59
def prefixEnd_7237260 : Nat := 4983230072969 + 3 ^ 40 * 7237260 * 2
def baseEnd_7237260 : Nat := 3716193001558459420666453

theorem tailTrace_7237260 : CollatzResearch.WordTrace tailWord_7237260 prefixEnd_7237260 3716193001558459420666453 := by
  unfold tailWord_7237260
  simp only [CollatzResearch.WordTrace]
  refine ⟨131982278880325260224042617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175976371840433680298723489 131982278880325260224042617)
  ·
    refine ⟨98986709160243945168031963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131982278880325260224042617 98986709160243945168031963)
    ·
      refine ⟨148480063740365917752047945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98986709160243945168031963 148480063740365917752047945)
      ·
        refine ⟨111360047805274438314035959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148480063740365917752047945 111360047805274438314035959)
        ·
          refine ⟨167040071707911657471053939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111360047805274438314035959 167040071707911657471053939)
          ·
            refine ⟨250560107561867486206580909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167040071707911657471053939 250560107561867486206580909)
            ·
              refine ⟨93960040335700307327467841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250560107561867486206580909 93960040335700307327467841)
              ·
                refine ⟨70470030251775230495600881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93960040335700307327467841 70470030251775230495600881)
                ·
                  refine ⟨52852522688831422871700661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70470030251775230495600881 52852522688831422871700661)
                  ·
                    refine ⟨4954924002077945894221937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52852522688831422871700661 4954924002077945894221937)
                    ·
                      refine ⟨3716193001558459420666453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4954924002077945894221937 3716193001558459420666453)
                      ·
                        rfl

theorem cell23_7237260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_7237260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237260 prefixEnd_7237260 := by exact prefixLift 7237260
  have htrace : WordTrace (prefixWord ++ tailWord_7237260) baseStart_7237260 baseEnd_7237260 := by
    simpa [prefixWord, tailWord_7237260, baseEnd_7237260] using wordTrace_append hprefix tailTrace_7237260
  have hstable : (prefixWord ++ tailWord_7237260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237260).length < 2 ^ (prefixWord ++ tailWord_7237260).sum := by decide
  have hdescent : baseEnd_7237260 < baseStart_7237260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237330 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 8]
def baseStart_7237330 : Nat := 118140960795 + 7237330 * 2 ^ 59
def prefixEnd_7237330 : Nat := 4983230072969 + 3 ^ 40 * 7237330 * 2
def baseEnd_7237330 : Nat := 412914327244919349643459

theorem tailTrace_7237330 : CollatzResearch.WordTrace tailWord_7237330 prefixEnd_7237330 412914327244919349643459 := by
  unfold tailWord_7237330
  simp only [CollatzResearch.WordTrace]
  refine ⟨65991777717599230600783361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175978073913597948268755629 65991777717599230600783361)
  ·
    refine ⟨49493833288199422950587521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65991777717599230600783361 49493833288199422950587521)
    ·
      refine ⟨37120374966149567212940641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49493833288199422950587521 37120374966149567212940641)
      ·
        refine ⟨27840281224612175409705481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37120374966149567212940641 27840281224612175409705481)
        ·
          refine ⟨20880210918459131557279111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27840281224612175409705481 20880210918459131557279111)
          ·
            refine ⟨31320316377688697335918667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20880210918459131557279111 31320316377688697335918667)
            ·
              refine ⟨46980474566533046003878001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31320316377688697335918667 46980474566533046003878001)
              ·
                refine ⟨35235355924899784502908501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46980474566533046003878001 35235355924899784502908501)
                ·
                  refine ⟨412914327244919349643459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35235355924899784502908501 412914327244919349643459)
                  ·
                    rfl

theorem cell23_7237330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_7237330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237330 prefixEnd_7237330 := by exact prefixLift 7237330
  have htrace : WordTrace (prefixWord ++ tailWord_7237330) baseStart_7237330 baseEnd_7237330 := by
    simpa [prefixWord, tailWord_7237330, baseEnd_7237330] using wordTrace_append hprefix tailTrace_7237330
  have hstable : (prefixWord ++ tailWord_7237330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237330).length < 2 ^ (prefixWord ++ tailWord_7237330).sum := by decide
  have hdescent : baseEnd_7237330 < baseStart_7237330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237351 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 3, 4]
def baseStart_7237351 : Nat := 118140960795 + 7237351 * 2 ^ 59
def prefixEnd_7237351 : Nat := 4983230072969 + 3 ^ 40 * 7237351 * 2
def baseEnd_7237351 : Nat := 1238746576099339521542845

theorem tailTrace_7237351 : CollatzResearch.WordTrace tailWord_7237351 prefixEnd_7237351 1238746576099339521542845 := by
  unfold tailWord_7237351
  simp only [CollatzResearch.WordTrace]
  refine ⟨263967876803320842989647907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175978584535547228659765271 263967876803320842989647907)
  ·
    refine ⟨395951815204981264484471861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263967876803320842989647907 395951815204981264484471861)
    ·
      refine ⟨37120482675466993545419237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 395951815204981264484471861 37120482675466993545419237)
      ·
        refine ⟨6960090501650061289766107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37120482675466993545419237 6960090501650061289766107)
        ·
          refine ⟨10440135752475091934649161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6960090501650061289766107 10440135752475091934649161)
          ·
            refine ⟨7830101814356318950986871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10440135752475091934649161 7830101814356318950986871)
            ·
              refine ⟨11745152721534478426480307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7830101814356318950986871 11745152721534478426480307)
              ·
                refine ⟨17617729082301717639720461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11745152721534478426480307 17617729082301717639720461)
                ·
                  refine ⟨6606648405863144114895173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17617729082301717639720461 6606648405863144114895173)
                  ·
                    refine ⟨1238746576099339521542845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6606648405863144114895173 1238746576099339521542845)
                    ·
                      rfl

theorem cell23_7237351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_7237351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237351 prefixEnd_7237351 := by exact prefixLift 7237351
  have htrace : WordTrace (prefixWord ++ tailWord_7237351) baseStart_7237351 baseEnd_7237351 := by
    simpa [prefixWord, tailWord_7237351, baseEnd_7237351] using wordTrace_append hprefix tailTrace_7237351
  have hstable : (prefixWord ++ tailWord_7237351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237351).length < 2 ^ (prefixWord ++ tailWord_7237351).sum := by decide
  have hdescent : baseEnd_7237351 < baseStart_7237351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237353 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_7237353 : Nat := 118140960795 + 7237353 * 2 ^ 59
def prefixEnd_7237353 : Nat := 4983230072969 + 3 ^ 40 * 7237353 * 2
def baseEnd_7237353 : Nat := 3716240755259327556803525

theorem tailTrace_7237353 : CollatzResearch.WordTrace tailWord_7237353 prefixEnd_7237353 3716240755259327556803525 := by
  unfold tailWord_7237353
  simp only [CollatzResearch.WordTrace]
  refine ⟨263967949749313597331220713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175978633166209064887480475 263967949749313597331220713)
  ·
    refine ⟨197975962311985197998415535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263967949749313597331220713 197975962311985197998415535)
    ·
      refine ⟨296963943467977796997623303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197975962311985197998415535 296963943467977796997623303)
      ·
        refine ⟨445445915201966695496434955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296963943467977796997623303 445445915201966695496434955)
        ·
          refine ⟨668168872802950043244652433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445445915201966695496434955 668168872802950043244652433)
          ·
            refine ⟨501126654602212532433489325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668168872802950043244652433 501126654602212532433489325)
            ·
              refine ⟨187922495475829699662558497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501126654602212532433489325 187922495475829699662558497)
              ·
                refine ⟨140941871606872274746918873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187922495475829699662558497 140941871606872274746918873)
                ·
                  refine ⟨105706403705154206060189155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140941871606872274746918873 105706403705154206060189155)
                  ·
                    refine ⟨158559605557731309090283733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 105706403705154206060189155 158559605557731309090283733)
                    ·
                      refine ⟨3716240755259327556803525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158559605557731309090283733 3716240755259327556803525)
                      ·
                        rfl

theorem cell23_7237353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_7237353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237353 prefixEnd_7237353 := by exact prefixLift 7237353
  have htrace : WordTrace (prefixWord ++ tailWord_7237353) baseStart_7237353 baseEnd_7237353 := by
    simpa [prefixWord, tailWord_7237353, baseEnd_7237353] using wordTrace_append hprefix tailTrace_7237353
  have hstable : (prefixWord ++ tailWord_7237353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237353).length < 2 ^ (prefixWord ++ tailWord_7237353).sum := by decide
  have hdescent : baseEnd_7237353 < baseStart_7237353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237377 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 1, 5]
def baseStart_7237377 : Nat := 118140960795 + 7237377 * 2 ^ 59
def prefixEnd_7237377 : Nat := 4983230072969 + 3 ^ 40 * 7237377 * 2
def baseEnd_7237377 : Nat := 1238751026265011820967805

theorem tailTrace_7237377 : CollatzResearch.WordTrace tailWord_7237377 prefixEnd_7237377 1238751026265011820967805 := by
  unfold tailWord_7237377
  simp only [CollatzResearch.WordTrace]
  refine ⟨263968825101226649430094385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175979216734151099620062923 263968825101226649430094385)
  ·
    refine ⟨197976618825919987072570789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263968825101226649430094385 197976618825919987072570789)
    ·
      refine ⟨37120616029859997576107023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197976618825919987072570789 37120616029859997576107023)
      ·
        refine ⟨55680924044789996364160535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37120616029859997576107023 55680924044789996364160535)
        ·
          refine ⟨83521386067184994546240803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55680924044789996364160535 83521386067184994546240803)
          ·
            refine ⟨125282079100777491819361205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83521386067184994546240803 125282079100777491819361205)
            ·
              refine ⟨11745194915697889858065113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125282079100777491819361205 11745194915697889858065113)
              ·
                refine ⟨8808896186773417393548835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11745194915697889858065113 8808896186773417393548835)
                ·
                  refine ⟨13213344280160126090323253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8808896186773417393548835 13213344280160126090323253)
                  ·
                    refine ⟨1238751026265011820967805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13213344280160126090323253 1238751026265011820967805)
                    ·
                      rfl

theorem cell23_7237377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_7237377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237377 prefixEnd_7237377 := by exact prefixLift 7237377
  have htrace : WordTrace (prefixWord ++ tailWord_7237377) baseStart_7237377 baseEnd_7237377 := by
    simpa [prefixWord, tailWord_7237377, baseEnd_7237377] using wordTrace_append hprefix tailTrace_7237377
  have hstable : (prefixWord ++ tailWord_7237377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237377).length < 2 ^ (prefixWord ++ tailWord_7237377).sum := by decide
  have hdescent : baseEnd_7237377 < baseStart_7237377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237384 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 2, 3, 2]
def baseStart_7237384 : Nat := 118140960795 + 7237384 * 2 ^ 59
def prefixEnd_7237384 : Nat := 4983230072969 + 3 ^ 40 * 7237384 * 2
def baseEnd_7237384 : Nat := 3716256673159616935515883

theorem tailTrace_7237384 : CollatzResearch.WordTrace tailWord_7237384 prefixEnd_7237384 3716256673159616935515883 := by
  unfold tailWord_7237384
  simp only [CollatzResearch.WordTrace]
  refine ⟨131984540206100644812799603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175979386941467526417066137 131984540206100644812799603)
  ·
    refine ⟨197976810309150967219199405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131984540206100644812799603 197976810309150967219199405)
    ·
      refine ⟨74241303865931612707199777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197976810309150967219199405 74241303865931612707199777)
      ·
        refine ⟨55680977899448709530399833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74241303865931612707199777 55680977899448709530399833)
        ·
          refine ⟨41760733424586532147799875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55680977899448709530399833 41760733424586532147799875)
          ·
            refine ⟨62641100136879798221699813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41760733424586532147799875 62641100136879798221699813)
            ·
              refine ⟨11745206275664962166568715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62641100136879798221699813 11745206275664962166568715)
              ·
                refine ⟨17617809413497443249853073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11745206275664962166568715 17617809413497443249853073)
                ·
                  refine ⟨13213357060123082437389805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17617809413497443249853073 13213357060123082437389805)
                  ·
                    refine ⟨4955008897546155914021177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13213357060123082437389805 4955008897546155914021177)
                    ·
                      refine ⟨3716256673159616935515883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955008897546155914021177 3716256673159616935515883)
                      ·
                        rfl

theorem cell23_7237384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_7237384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237384 prefixEnd_7237384 := by exact prefixLift 7237384
  have htrace : WordTrace (prefixWord ++ tailWord_7237384) baseStart_7237384 baseEnd_7237384 := by
    simpa [prefixWord, tailWord_7237384, baseEnd_7237384] using wordTrace_append hprefix tailTrace_7237384
  have hstable : (prefixWord ++ tailWord_7237384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237384).length < 2 ^ (prefixWord ++ tailWord_7237384).sum := by decide
  have hdescent : baseEnd_7237384 < baseStart_7237384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237390 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_7237390 : Nat := 118140960795 + 7237390 * 2 ^ 59
def prefixEnd_7237390 : Nat := 4983230072969 + 3 ^ 40 * 7237390 * 2
def baseEnd_7237390 : Nat := 1238753251347847970680285

theorem tailTrace_7237390 : CollatzResearch.WordTrace tailWord_7237390 prefixEnd_7237390 1238753251347847970680285 := by
  unfold tailWord_7237390
  simp only [CollatzResearch.WordTrace]
  refine ⟨32996162406272444081289703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 175979532833453035100211749 32996162406272444081289703)
  ·
    refine ⟨49494243609408666121934555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32996162406272444081289703 49494243609408666121934555)
    ·
      refine ⟨74241365414112999182901833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49494243609408666121934555 74241365414112999182901833)
      ·
        refine ⟨55681024060584749387176375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74241365414112999182901833 55681024060584749387176375)
        ·
          refine ⟨83521536090877124080764563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55681024060584749387176375 83521536090877124080764563)
          ·
            refine ⟨125282304136315686121146845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83521536090877124080764563 125282304136315686121146845)
            ·
              refine ⟨46980864051118382295430067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125282304136315686121146845 46980864051118382295430067)
              ·
                refine ⟨70471296076677573443145101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46980864051118382295430067 70471296076677573443145101)
                ·
                  refine ⟨26426736028754090041179413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70471296076677573443145101 26426736028754090041179413)
                  ·
                    refine ⟨1238753251347847970680285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26426736028754090041179413 1238753251347847970680285)
                    ·
                      rfl

theorem cell23_7237390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_7237390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237390 prefixEnd_7237390 := by exact prefixLift 7237390
  have htrace : WordTrace (prefixWord ++ tailWord_7237390) baseStart_7237390 baseEnd_7237390 := by
    simpa [prefixWord, tailWord_7237390, baseEnd_7237390] using wordTrace_append hprefix tailTrace_7237390
  have hstable : (prefixWord ++ tailWord_7237390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237390).length < 2 ^ (prefixWord ++ tailWord_7237390).sum := by decide
  have hdescent : baseEnd_7237390 < baseStart_7237390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237420 : List Nat := [2, 2, 1, 1, 1, 5, 3, 8]
def baseStart_7237420 : Nat := 118140960795 + 7237420 * 2 ^ 59
def prefixEnd_7237420 : Nat := 4983230072969 + 3 ^ 40 * 7237420 * 2
def baseEnd_7237420 : Nat := 137639820683821436839471

theorem tailTrace_7237420 : CollatzResearch.WordTrace tailWord_7237420 prefixEnd_7237420 137639820683821436839471 := by
  unfold tailWord_7237420
  simp only [CollatzResearch.WordTrace]
  refine ⟨131985196720035433886954857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175980262293380578515939809 131985196720035433886954857)
  ·
    refine ⟨98988897540026575415216143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131985196720035433886954857 98988897540026575415216143)
    ·
      refine ⟨148483346310039863122824215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98988897540026575415216143 148483346310039863122824215)
      ·
        refine ⟨222725019465059794684236323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148483346310039863122824215 222725019465059794684236323)
        ·
          refine ⟨334087529197589692026354485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222725019465059794684236323 334087529197589692026354485)
          ·
            refine ⟨31320705862274033627470733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 334087529197589692026354485 31320705862274033627470733)
            ·
              refine ⟨11745264698352762610301525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31320705862274033627470733 11745264698352762610301525)
              ·
                refine ⟨137639820683821436839471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11745264698352762610301525 137639820683821436839471)
                ·
                  rfl

theorem cell23_7237420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 8].length) (baseStart_7237420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237420 prefixEnd_7237420 := by exact prefixLift 7237420
  have htrace : WordTrace (prefixWord ++ tailWord_7237420) baseStart_7237420 baseEnd_7237420 := by
    simpa [prefixWord, tailWord_7237420, baseEnd_7237420] using wordTrace_append hprefix tailTrace_7237420
  have hstable : (prefixWord ++ tailWord_7237420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237420).length < 2 ^ (prefixWord ++ tailWord_7237420).sum := by decide
  have hdescent : baseEnd_7237420 < baseStart_7237420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237447 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_7237447 : Nat := 118140960795 + 7237447 * 2 ^ 59
def prefixEnd_7237447 : Nat := 4983230072969 + 3 ^ 40 * 7237447 * 2
def baseEnd_7237447 : Nat := 3716289022440850189028093

theorem tailTrace_7237447 : CollatzResearch.WordTrace tailWord_7237447 prefixEnd_7237447 3716289022440850189028093 := by
  unfold tailWord_7237447
  simp only [CollatzResearch.WordTrace]
  refine ⟨263971378210973051385142595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175980918807315367590095063 263971378210973051385142595)
  ·
    refine ⟨395957067316459577077713893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263971378210973051385142595 395957067316459577077713893)
    ·
      refine ⟨74241950121836170702071355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 395957067316459577077713893 74241950121836170702071355)
      ·
        refine ⟨111362925182754256053107033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74241950121836170702071355 111362925182754256053107033)
        ·
          refine ⟨83522193887065692039830275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111362925182754256053107033 83522193887065692039830275)
          ·
            refine ⟨125283290830598538059745413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83522193887065692039830275 125283290830598538059745413)
            ·
              refine ⟨23490617030737225886202265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125283290830598538059745413 23490617030737225886202265)
              ·
                refine ⟨17617962773052919414651699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23490617030737225886202265 17617962773052919414651699)
                ·
                  refine ⟨26426944159579379121977549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17617962773052919414651699 26426944159579379121977549)
                  ·
                    refine ⟨9910104059842267170741581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26426944159579379121977549 9910104059842267170741581)
                    ·
                      refine ⟨3716289022440850189028093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9910104059842267170741581 3716289022440850189028093)
                      ·
                        rfl

theorem cell23_7237447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_7237447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237447 prefixEnd_7237447 := by exact prefixLift 7237447
  have htrace : WordTrace (prefixWord ++ tailWord_7237447) baseStart_7237447 baseEnd_7237447 := by
    simpa [prefixWord, tailWord_7237447, baseEnd_7237447] using wordTrace_append hprefix tailTrace_7237447
  have hstable : (prefixWord ++ tailWord_7237447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237447).length < 2 ^ (prefixWord ++ tailWord_7237447).sum := by decide
  have hdescent : baseEnd_7237447 < baseStart_7237447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237448 : List Nat := [2, 1, 3, 1, 1, 5, 2, 3, 1, 2, 2]
def baseStart_7237448 : Nat := 118140960795 + 7237448 * 2 ^ 59
def prefixEnd_7237448 : Nat := 4983230072969 + 3 ^ 40 * 7237448 * 2
def baseEnd_7237448 : Nat := 3716289535921504685115589

theorem tailTrace_7237448 : CollatzResearch.WordTrace tailWord_7237448 prefixEnd_7237448 3716289535921504685115589 := by
  unfold tailWord_7237448
  simp only [CollatzResearch.WordTrace]
  refine ⟨131985707341984714277964499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175980943122646285703952665 131985707341984714277964499)
  ·
    refine ⟨197978561012977071416946749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131985707341984714277964499 197978561012977071416946749)
    ·
      refine ⟨74241960379866401781355031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197978561012977071416946749 74241960379866401781355031)
      ·
        refine ⟨111362940569799602672032547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74241960379866401781355031 111362940569799602672032547)
        ·
          refine ⟨167044410854699404008048821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111362940569799602672032547 167044410854699404008048821)
          ·
            refine ⟨15660413517628069125754577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167044410854699404008048821 15660413517628069125754577)
            ·
              refine ⟨11745310138221051844315933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15660413517628069125754577 11745310138221051844315933)
              ·
                refine ⟨4404491301832894441618475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11745310138221051844315933 4404491301832894441618475)
                ·
                  refine ⟨6606736952749341662427713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404491301832894441618475 6606736952749341662427713)
                  ·
                    refine ⟨4955052714562006246820785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6606736952749341662427713 4955052714562006246820785)
                    ·
                      refine ⟨3716289535921504685115589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955052714562006246820785 3716289535921504685115589)
                      ·
                        rfl

theorem cell23_7237448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_7237448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237448 prefixEnd_7237448 := by exact prefixLift 7237448
  have htrace : WordTrace (prefixWord ++ tailWord_7237448) baseStart_7237448 baseEnd_7237448 := by
    simpa [prefixWord, tailWord_7237448, baseEnd_7237448] using wordTrace_append hprefix tailTrace_7237448
  have hstable : (prefixWord ++ tailWord_7237448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237448).length < 2 ^ (prefixWord ++ tailWord_7237448).sum := by decide
  have hdescent : baseEnd_7237448 < baseStart_7237448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237504 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 6, 2, 2]
def baseStart_7237504 : Nat := 118140960795 + 7237504 * 2 ^ 59
def prefixEnd_7237504 : Nat := 4983230072969 + 3 ^ 40 * 7237504 * 2
def baseEnd_7237504 : Nat := 3716318290838156466015331

theorem tailTrace_7237504 : CollatzResearch.WordTrace tailWord_7237504 prefixEnd_7237504 3716318290838156466015331 := by
  unfold tailWord_7237504
  simp only [CollatzResearch.WordTrace]
  refine ⟨131986728585883275059983783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175982304781177700079978377 131986728585883275059983783)
  ·
    refine ⟨197980092878824912589975675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131986728585883275059983783 197980092878824912589975675)
    ·
      refine ⟨296970139318237368884963513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197980092878824912589975675 296970139318237368884963513)
      ·
        refine ⟨222727604488678026663722635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296970139318237368884963513 222727604488678026663722635)
        ·
          refine ⟨334091406733017039995583953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222727604488678026663722635 334091406733017039995583953)
          ·
            refine ⟨250568555049762779996687965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334091406733017039995583953 250568555049762779996687965)
            ·
              refine ⟨93963208143661042498757987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250568555049762779996687965 93963208143661042498757987)
              ·
                refine ⟨140944812215491563748136981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93963208143661042498757987 140944812215491563748136981)
                ·
                  refine ⟨6606788072601167050693921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 140944812215491563748136981 6606788072601167050693921)
                  ·
                    refine ⟨4955091054450875288020441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6606788072601167050693921 4955091054450875288020441)
                    ·
                      refine ⟨3716318290838156466015331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955091054450875288020441 3716318290838156466015331)
                      ·
                        rfl

theorem cell23_7237504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6, 2, 2].length) (baseStart_7237504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237504 prefixEnd_7237504 := by exact prefixLift 7237504
  have htrace : WordTrace (prefixWord ++ tailWord_7237504) baseStart_7237504 baseEnd_7237504 := by
    simpa [prefixWord, tailWord_7237504, baseEnd_7237504] using wordTrace_append hprefix tailTrace_7237504
  have hstable : (prefixWord ++ tailWord_7237504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237504).length < 2 ^ (prefixWord ++ tailWord_7237504).sum := by decide
  have hdescent : baseEnd_7237504 < baseStart_7237504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237507 : List Nat := [1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 5]
def baseStart_7237507 : Nat := 118140960795 + 7237507 * 2 ^ 59
def prefixEnd_7237507 : Nat := 4983230072969 + 3 ^ 40 * 7237507 * 2
def baseEnd_7237507 : Nat := 3716319831280119954277817

theorem tailTrace_7237507 : CollatzResearch.WordTrace tailWord_7237507 prefixEnd_7237507 3716319831280119954277817 := by
  unfold tailWord_7237507
  simp only [CollatzResearch.WordTrace]
  refine ⟨263973566590755681632326775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175982377727170454421551183 263973566590755681632326775)
  ·
    refine ⟨395960349886133522448490163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263973566590755681632326775 395960349886133522448490163)
    ·
      refine ⟨593940524829200283672735245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395960349886133522448490163 593940524829200283672735245)
      ·
        refine ⟨222727696810950106377275717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 593940524829200283672735245 222727696810950106377275717)
        ·
          refine ⟨41761443152053144945739197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222727696810950106377275717 41761443152053144945739197)
          ·
            refine ⟨15660541182019929354652199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41761443152053144945739197 15660541182019929354652199)
            ·
              refine ⟨23490811773029894031978299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15660541182019929354652199 23490811773029894031978299)
              ·
                refine ⟨35236217659544841047967449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23490811773029894031978299 35236217659544841047967449)
                ·
                  refine ⟨26427163244658630785975587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35236217659544841047967449 26427163244658630785975587)
                  ·
                    refine ⟨39640744866987946178963381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26427163244658630785975587 39640744866987946178963381)
                    ·
                      refine ⟨3716319831280119954277817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39640744866987946178963381 3716319831280119954277817)
                      ·
                        rfl

theorem cell23_7237507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_7237507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237507 prefixEnd_7237507 := by exact prefixLift 7237507
  have htrace : WordTrace (prefixWord ++ tailWord_7237507) baseStart_7237507 baseEnd_7237507 := by
    simpa [prefixWord, tailWord_7237507, baseEnd_7237507] using wordTrace_append hprefix tailTrace_7237507
  have hstable : (prefixWord ++ tailWord_7237507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237507).length < 2 ^ (prefixWord ++ tailWord_7237507).sum := by decide
  have hdescent : baseEnd_7237507 < baseStart_7237507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237527 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 7]
def baseStart_7237527 : Nat := 118140960795 + 7237527 * 2 ^ 59
def prefixEnd_7237527 : Nat := 4983230072969 + 3 ^ 40 * 7237527 * 2
def baseEnd_7237527 : Nat := 412925566765912208447525

theorem tailTrace_7237527 : CollatzResearch.WordTrace tailWord_7237527 prefixEnd_7237527 412925566765912208447525 := by
  unfold tailWord_7237527
  simp only [CollatzResearch.WordTrace]
  refine ⟨263974296050683225048054835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175982864033788816698703223 263974296050683225048054835)
  ·
    refine ⟨395961444076024837572082253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263974296050683225048054835 395961444076024837572082253)
    ·
      refine ⟨148485541528509314089530845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395961444076024837572082253 148485541528509314089530845)
      ·
        refine ⟨55682078073190992783574067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148485541528509314089530845 55682078073190992783574067)
        ·
          refine ⟨83523117109786489175361101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55682078073190992783574067 83523117109786489175361101)
          ·
            refine ⟨31321168916169933440760413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83523117109786489175361101 31321168916169933440760413)
            ·
              refine ⟨11745438343563725040285155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31321168916169933440760413 11745438343563725040285155)
              ·
                refine ⟨17618157515345587560427733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11745438343563725040285155 17618157515345587560427733)
                ·
                  refine ⟨412925566765912208447525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17618157515345587560427733 412925566765912208447525)
                  ·
                    rfl

theorem cell23_7237527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 7].length) (baseStart_7237527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237527 prefixEnd_7237527 := by exact prefixLift 7237527
  have htrace : WordTrace (prefixWord ++ tailWord_7237527) baseStart_7237527 baseEnd_7237527 := by
    simpa [prefixWord, tailWord_7237527, baseEnd_7237527] using wordTrace_append hprefix tailTrace_7237527
  have hstable : (prefixWord ++ tailWord_7237527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237527).length < 2 ^ (prefixWord ++ tailWord_7237527).sum := by decide
  have hdescent : baseEnd_7237527 < baseStart_7237527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237604 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_7237604 : Nat := 118140960795 + 7237604 * 2 ^ 59
def prefixEnd_7237604 : Nat := 4983230072969 + 3 ^ 40 * 7237604 * 2
def baseEnd_7237604 : Nat := 1238789879634535358254957

theorem tailTrace_7237604 : CollatzResearch.WordTrace tailWord_7237604 prefixEnd_7237604 1238789879634535358254957 := by
  unfold tailWord_7237604
  simp only [CollatzResearch.WordTrace]
  refine ⟨131988552235702133599303933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175984736314269511465738577 131988552235702133599303933)
  ·
    refine ⟨49495707088388300099738975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131988552235702133599303933 49495707088388300099738975)
    ·
      refine ⟨74243560632582450149608463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49495707088388300099738975 74243560632582450149608463)
      ·
        refine ⟨111365340948873675224412695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74243560632582450149608463 111365340948873675224412695)
        ·
          refine ⟨167048011423310512836619043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111365340948873675224412695 167048011423310512836619043)
          ·
            refine ⟨250572017134965769254928565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167048011423310512836619043 250572017134965769254928565)
            ·
              refine ⟨23491126606403040867649553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 250572017134965769254928565 23491126606403040867649553)
              ·
                refine ⟨17618344954802280650737165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23491126606403040867649553 17618344954802280650737165)
                ·
                  refine ⟨6606879358050855244026437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17618344954802280650737165 6606879358050855244026437)
                  ·
                    refine ⟨1238789879634535358254957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6606879358050855244026437 1238789879634535358254957)
                    ·
                      rfl

theorem cell23_7237604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_7237604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237604 prefixEnd_7237604 := by exact prefixLift 7237604
  have htrace : WordTrace (prefixWord ++ tailWord_7237604) baseStart_7237604 baseEnd_7237604 := by
    simpa [prefixWord, tailWord_7237604, baseEnd_7237604] using wordTrace_append hprefix tailTrace_7237604
  have hstable : (prefixWord ++ tailWord_7237604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237604).length < 2 ^ (prefixWord ++ tailWord_7237604).sum := by decide
  have hdescent : baseEnd_7237604 < baseStart_7237604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237637 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_7237637 : Nat := 118140960795 + 7237637 * 2 ^ 59
def prefixEnd_7237637 : Nat := 4983230072969 + 3 ^ 40 * 7237637 * 2
def baseEnd_7237637 : Nat := 3716386583765204445652219

theorem tailTrace_7237637 : CollatzResearch.WordTrace tailWord_7237637 prefixEnd_7237637 3716386583765204445652219 := by
  unfold tailWord_7237637
  simp only [CollatzResearch.WordTrace]
  refine ⟨263978308080284713834559165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175985538720189809223039443 263978308080284713834559165)
  ·
    refine ⟨98991865530106767687959687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263978308080284713834559165 98991865530106767687959687)
    ·
      refine ⟨148487798295160151531939531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98991865530106767687959687 148487798295160151531939531)
      ·
        refine ⟨222731697442740227297909297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148487798295160151531939531 222731697442740227297909297)
        ·
          refine ⟨167048773082055170473431973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222731697442740227297909297 167048773082055170473431973)
          ·
            refine ⟨31321644952885344463768495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167048773082055170473431973 31321644952885344463768495)
            ·
              refine ⟨46982467429328016695652743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31321644952885344463768495 46982467429328016695652743)
              ·
                refine ⟨70473701143992025043479115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46982467429328016695652743 70473701143992025043479115)
                ·
                  refine ⟨105710551715988037565218673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70473701143992025043479115 105710551715988037565218673)
                  ·
                    refine ⟨79282913786991028173914005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105710551715988037565218673 79282913786991028173914005)
                    ·
                      refine ⟨3716386583765204445652219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79282913786991028173914005 3716386583765204445652219)
                      ·
                        rfl

theorem cell23_7237637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_7237637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237637 prefixEnd_7237637 := by exact prefixLift 7237637
  have htrace : WordTrace (prefixWord ++ tailWord_7237637) baseStart_7237637 baseEnd_7237637 := by
    simpa [prefixWord, tailWord_7237637, baseEnd_7237637] using wordTrace_append hprefix tailTrace_7237637
  have hstable : (prefixWord ++ tailWord_7237637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237637).length < 2 ^ (prefixWord ++ tailWord_7237637).sum := by decide
  have hdescent : baseEnd_7237637 < baseStart_7237637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237672 : List Nat := [2, 1, 5, 3, 1, 2, 1, 3, 1, 4]
def baseStart_7237672 : Nat := 118140960795 + 7237672 * 2 ^ 59
def prefixEnd_7237672 : Nat := 4983230072969 + 3 ^ 40 * 7237672 * 2
def baseEnd_7237672 : Nat := 1238801518529370602904853

theorem tailTrace_7237672 : CollatzResearch.WordTrace tailWord_7237672 prefixEnd_7237672 1238801518529370602904853 := by
  unfold tailWord_7237672
  simp only [CollatzResearch.WordTrace]
  refine ⟨131989792317578957406041635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175986389756771943208055513 131989792317578957406041635)
  ·
    refine ⟨197984688476368436109062453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131989792317578957406041635 197984688476368436109062453)
    ·
      refine ⟨18561064544659540885224605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 197984688476368436109062453 18561064544659540885224605)
      ·
        refine ⟨6960399204247327831959227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18561064544659540885224605 6960399204247327831959227)
        ·
          refine ⟨10440598806370991747938841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6960399204247327831959227 10440598806370991747938841)
          ·
            refine ⟨7830449104778243810954131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10440598806370991747938841 7830449104778243810954131)
            ·
              refine ⟨11745673657167365716431197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7830449104778243810954131 11745673657167365716431197)
              ·
                refine ⟨4404627621437762143661699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11745673657167365716431197 4404627621437762143661699)
                ·
                  refine ⟨6606941432156643215492549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404627621437762143661699 6606941432156643215492549)
                  ·
                    refine ⟨1238801518529370602904853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6606941432156643215492549 1238801518529370602904853)
                    ·
                      rfl

theorem cell23_7237672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_7237672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237672 prefixEnd_7237672 := by exact prefixLift 7237672
  have htrace : WordTrace (prefixWord ++ tailWord_7237672) baseStart_7237672 baseEnd_7237672 := by
    simpa [prefixWord, tailWord_7237672, baseEnd_7237672] using wordTrace_append hprefix tailTrace_7237672
  have hstable : (prefixWord ++ tailWord_7237672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237672).length < 2 ^ (prefixWord ++ tailWord_7237672).sum := by decide
  have hdescent : baseEnd_7237672 < baseStart_7237672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237688 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 2, 3, 2]
def baseStart_7237688 : Nat := 118140960795 + 7237688 * 2 ^ 59
def prefixEnd_7237688 : Nat := 4983230072969 + 3 ^ 40 * 7237688 * 2
def baseEnd_7237688 : Nat := 3716412771278583746114485

theorem tailTrace_7237688 : CollatzResearch.WordTrace tailWord_7237688 prefixEnd_7237688 3716412771278583746114485 := by
  unfold tailWord_7237688
  simp only [CollatzResearch.WordTrace]
  refine ⟨131990084101549974772332859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175986778802066633029777145 131990084101549974772332859)
  ·
    refine ⟨197985126152324962158499289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131990084101549974772332859 197985126152324962158499289)
    ·
      refine ⟨148488844614243721618874467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197985126152324962158499289 148488844614243721618874467)
      ·
        refine ⟨222733266921365582428311701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148488844614243721618874467 222733266921365582428311701)
        ·
          refine ⟨10440621886939011676327111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 222733266921365582428311701 10440621886939011676327111)
          ·
            refine ⟨15660932830408517514490667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10440621886939011676327111 15660932830408517514490667)
            ·
              refine ⟨23491399245612776271736001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15660932830408517514490667 23491399245612776271736001)
              ·
                refine ⟨17618549434209582203802001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23491399245612776271736001 17618549434209582203802001)
                ·
                  refine ⟨13213912075657186652851501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17618549434209582203802001 13213912075657186652851501)
                  ·
                    refine ⟨4955217028371444994819313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13213912075657186652851501 4955217028371444994819313)
                    ·
                      refine ⟨3716412771278583746114485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955217028371444994819313 3716412771278583746114485)
                      ·
                        rfl

theorem cell23_7237688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 3, 2].length) (baseStart_7237688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237688 prefixEnd_7237688 := by exact prefixLift 7237688
  have htrace : WordTrace (prefixWord ++ tailWord_7237688) baseStart_7237688 baseEnd_7237688 := by
    simpa [prefixWord, tailWord_7237688, baseEnd_7237688] using wordTrace_append hprefix tailTrace_7237688
  have hstable : (prefixWord ++ tailWord_7237688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237688).length < 2 ^ (prefixWord ++ tailWord_7237688).sum := by decide
  have hdescent : baseEnd_7237688 < baseStart_7237688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237724 : List Nat := [2, 2, 4, 1, 1, 2, 2, 9]
def baseStart_7237724 : Nat := 118140960795 + 7237724 * 2 ^ 59
def prefixEnd_7237724 : Nat := 4983230072969 + 3 ^ 40 * 7237724 * 2
def baseEnd_7237724 : Nat := 137645602095635022417197

theorem tailTrace_7237724 : CollatzResearch.WordTrace tailWord_7237724 prefixEnd_7237724 137645602095635022417197 := by
  unfold tailWord_7237724
  simp only [CollatzResearch.WordTrace]
  refine ⟨131990740615484763846488113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175987654153979685128650817 131990740615484763846488113)
  ·
    refine ⟨98993055461613572884866085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131990740615484763846488113 98993055461613572884866085)
    ·
      refine ⟨18561197899052544915912391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98993055461613572884866085 18561197899052544915912391)
      ·
        refine ⟨27841796848578817373868587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18561197899052544915912391 27841796848578817373868587)
        ·
          refine ⟨41762695272868226060802881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27841796848578817373868587 41762695272868226060802881)
          ·
            refine ⟨31322021454651169545602161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41762695272868226060802881 31322021454651169545602161)
            ·
              refine ⟨23491516090988377159201621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31322021454651169545602161 23491516090988377159201621)
              ·
                refine ⟨137645602095635022417197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23491516090988377159201621 137645602095635022417197)
                ·
                  rfl

theorem cell23_7237724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 9].length) (baseStart_7237724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237724 prefixEnd_7237724 := by exact prefixLift 7237724
  have htrace : WordTrace (prefixWord ++ tailWord_7237724) baseStart_7237724 baseEnd_7237724 := by
    simpa [prefixWord, tailWord_7237724, baseEnd_7237724] using wordTrace_append hprefix tailTrace_7237724
  have hstable : (prefixWord ++ tailWord_7237724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237724).length < 2 ^ (prefixWord ++ tailWord_7237724).sum := by decide
  have hdescent : baseEnd_7237724 < baseStart_7237724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237735 : List Nat := [1, 1, 5, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_7237735 : Nat := 118140960795 + 7237735 * 2 ^ 59
def prefixEnd_7237735 : Nat := 4983230072969 + 3 ^ 40 * 7237735 * 2
def baseEnd_7237735 : Nat := 3716436904869345062226769

theorem tailTrace_7237735 : CollatzResearch.WordTrace tailWord_7237735 prefixEnd_7237735 3716436904869345062226769 := by
  unfold tailWord_7237735
  simp only [CollatzResearch.WordTrace]
  refine ⟨263981882433929676571626659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175987921622619784381084439 263981882433929676571626659)
  ·
    refine ⟨395972823650894514857439989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263981882433929676571626659 395972823650894514857439989)
    ·
      refine ⟨37122452217271360767884999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 395972823650894514857439989 37122452217271360767884999)
      ·
        refine ⟨55683678325907041151827499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37122452217271360767884999 55683678325907041151827499)
        ·
          refine ⟨83525517488860561727741249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55683678325907041151827499 83525517488860561727741249)
          ·
            refine ⟨62644138116645421295805937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83525517488860561727741249 62644138116645421295805937)
            ·
              refine ⟨46983103587484065971854453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62644138116645421295805937 46983103587484065971854453)
              ·
                refine ⟨4404665961326631184861355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46983103587484065971854453 4404665961326631184861355)
                ·
                  refine ⟨6606998941989946777292033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4404665961326631184861355 6606998941989946777292033)
                  ·
                    refine ⟨4955249206492460082969025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6606998941989946777292033 4955249206492460082969025)
                    ·
                      refine ⟨3716436904869345062226769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955249206492460082969025 3716436904869345062226769)
                      ·
                        rfl

theorem cell23_7237735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_7237735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237735 prefixEnd_7237735 := by exact prefixLift 7237735
  have htrace : WordTrace (prefixWord ++ tailWord_7237735) baseStart_7237735 baseEnd_7237735 := by
    simpa [prefixWord, tailWord_7237735, baseEnd_7237735] using wordTrace_append hprefix tailTrace_7237735
  have hstable : (prefixWord ++ tailWord_7237735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237735).length < 2 ^ (prefixWord ++ tailWord_7237735).sum := by decide
  have hdescent : baseEnd_7237735 < baseStart_7237735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237738 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_7237738 : Nat := 118140960795 + 7237738 * 2 ^ 59
def prefixEnd_7237738 : Nat := 4983230072969 + 3 ^ 40 * 7237738 * 2
def baseEnd_7237738 : Nat := 3716438445311308550489255

theorem tailTrace_7237738 : CollatzResearch.WordTrace tailWord_7237738 prefixEnd_7237738 3716438445311308550489255 := by
  unfold tailWord_7237738
  simp only [CollatzResearch.WordTrace]
  refine ⟨65995497963229702020996467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175987994568612538722657245 65995497963229702020996467)
  ·
    refine ⟨98993246944844553031494701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65995497963229702020996467 98993246944844553031494701)
    ·
      refine ⟨37122467604316707386810513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98993246944844553031494701 37122467604316707386810513)
      ·
        refine ⟨27841850703237530540107885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37122467604316707386810513 27841850703237530540107885)
        ·
          refine ⟨10440694013714073952540457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27841850703237530540107885 10440694013714073952540457)
          ·
            refine ⟨7830520510285555464405343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10440694013714073952540457 7830520510285555464405343)
            ·
              refine ⟨11745780765428333196608015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7830520510285555464405343 11745780765428333196608015)
              ·
                refine ⟨17618671148142499794912023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11745780765428333196608015 17618671148142499794912023)
                ·
                  refine ⟨26428006722213749692368035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17618671148142499794912023 26428006722213749692368035)
                  ·
                    refine ⟨39642010083320624538552053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26428006722213749692368035 39642010083320624538552053)
                    ·
                      refine ⟨3716438445311308550489255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39642010083320624538552053 3716438445311308550489255)
                      ·
                        rfl

theorem cell23_7237738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_7237738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237738 prefixEnd_7237738 := by exact prefixLift 7237738
  have htrace : WordTrace (prefixWord ++ tailWord_7237738) baseStart_7237738 baseEnd_7237738 := by
    simpa [prefixWord, tailWord_7237738, baseEnd_7237738] using wordTrace_append hprefix tailTrace_7237738
  have hstable : (prefixWord ++ tailWord_7237738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237738).length < 2 ^ (prefixWord ++ tailWord_7237738).sum := by decide
  have hdescent : baseEnd_7237738 < baseStart_7237738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237747 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 7]
def baseStart_7237747 : Nat := 118140960795 + 7237747 * 2 ^ 59
def prefixEnd_7237747 : Nat := 4983230072969 + 3 ^ 40 * 7237747 * 2
def baseEnd_7237747 : Nat := 3716443066637199015276713

theorem tailTrace_7237747 : CollatzResearch.WordTrace tailWord_7237747 prefixEnd_7237747 3716443066637199015276713 := by
  unfold tailWord_7237747
  simp only [CollatzResearch.WordTrace]
  refine ⟨263982320109886202621063495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175988213406590801747375663 263982320109886202621063495)
  ·
    refine ⟨395973480164829303931595243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263982320109886202621063495 395973480164829303931595243)
    ·
      refine ⟨593960220247243955897392865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395973480164829303931595243 593960220247243955897392865)
      ·
        refine ⟨445470165185432966923044649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593960220247243955897392865 445470165185432966923044649)
        ·
          refine ⟨334102623889074725192283487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445470165185432966923044649 334102623889074725192283487)
          ·
            refine ⟨501153935833612087788425231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334102623889074725192283487 501153935833612087788425231)
            ·
              refine ⟨751730903750418131682637847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501153935833612087788425231 751730903750418131682637847)
              ·
                refine ⟨1127596355625627197523956771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751730903750418131682637847 1127596355625627197523956771)
                ·
                  refine ⟨1691394533438440796285935157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127596355625627197523956771 1691394533438440796285935157)
                  ·
                    refine ⟨158568237509853824651806421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1691394533438440796285935157 158568237509853824651806421)
                    ·
                      refine ⟨3716443066637199015276713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 158568237509853824651806421 3716443066637199015276713)
                      ·
                        rfl

theorem cell23_7237747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_7237747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237747 prefixEnd_7237747 := by exact prefixLift 7237747
  have htrace : WordTrace (prefixWord ++ tailWord_7237747) baseStart_7237747 baseEnd_7237747 := by
    simpa [prefixWord, tailWord_7237747, baseEnd_7237747] using wordTrace_append hprefix tailTrace_7237747
  have hstable : (prefixWord ++ tailWord_7237747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237747).length < 2 ^ (prefixWord ++ tailWord_7237747).sum := by decide
  have hdescent : baseEnd_7237747 < baseStart_7237747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237768 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_7237768 : Nat := 118140960795 + 7237768 * 2 ^ 59
def prefixEnd_7237768 : Nat := 4983230072969 + 3 ^ 40 * 7237768 * 2
def baseEnd_7237768 : Nat := 3716453849730943433114117

theorem tailTrace_7237768 : CollatzResearch.WordTrace tailWord_7237768 prefixEnd_7237768 3716453849730943433114117 := by
  unfold tailWord_7237768
  simp only [CollatzResearch.WordTrace]
  refine ⟨131991543021405061603788979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175988724028540082138385305 131991543021405061603788979)
  ·
    refine ⟨197987314532107592405683469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131991543021405061603788979 197987314532107592405683469)
    ·
      refine ⟨74245242949540347152131301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197987314532107592405683469 74245242949540347152131301)
      ·
        refine ⟨13920983053038815091024619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74245242949540347152131301 13920983053038815091024619)
        ·
          refine ⟨20881474579558222636536929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13920983053038815091024619 20881474579558222636536929)
          ·
            refine ⟨15661105934668666977402697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20881474579558222636536929 15661105934668666977402697)
            ·
              refine ⟨11745829451001500233052023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15661105934668666977402697 11745829451001500233052023)
              ·
                refine ⟨17618744176502250349578035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11745829451001500233052023 17618744176502250349578035)
                ·
                  refine ⟨26428116264753375524367053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17618744176502250349578035 26428116264753375524367053)
                  ·
                    refine ⟨9910543599282515821637645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26428116264753375524367053 9910543599282515821637645)
                    ·
                      refine ⟨3716453849730943433114117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9910543599282515821637645 3716453849730943433114117)
                      ·
                        rfl

theorem cell23_7237768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_7237768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237768 prefixEnd_7237768 := by exact prefixLift 7237768
  have htrace : WordTrace (prefixWord ++ tailWord_7237768) baseStart_7237768 baseEnd_7237768 := by
    simpa [prefixWord, tailWord_7237768, baseEnd_7237768] using wordTrace_append hprefix tailTrace_7237768
  have hstable : (prefixWord ++ tailWord_7237768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237768).length < 2 ^ (prefixWord ++ tailWord_7237768).sum := by decide
  have hdescent : baseEnd_7237768 < baseStart_7237768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237778 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_7237778 : Nat := 118140960795 + 7237778 * 2 ^ 59
def prefixEnd_7237778 : Nat := 4983230072969 + 3 ^ 40 * 7237778 * 2
def baseEnd_7237778 : Nat := 3716458984537488393989071

theorem tailTrace_7237778 : CollatzResearch.WordTrace tailWord_7237778 prefixEnd_7237778 3716458984537488393989071 := by
  unfold tailWord_7237778
  simp only [CollatzResearch.WordTrace]
  refine ⟨65995862693193473728860497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175988967181849263276961325 65995862693193473728860497)
  ·
    refine ⟨49496897019895105296645373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65995862693193473728860497 49496897019895105296645373)
    ·
      refine ⟨18561336382460664486242015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49496897019895105296645373 18561336382460664486242015)
      ·
        refine ⟨27842004573690996729363023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18561336382460664486242015 27842004573690996729363023)
        ·
          refine ⟨41763006860536495094044535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27842004573690996729363023 41763006860536495094044535)
          ·
            refine ⟨62644510290804742641066803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41763006860536495094044535 62644510290804742641066803)
            ·
              refine ⟨93966765436207113961600205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62644510290804742641066803 93966765436207113961600205)
              ·
                refine ⟨35237537038577667735600077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93966765436207113961600205 35237537038577667735600077)
                ·
                  refine ⟨13214076389466625400850029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35237537038577667735600077 13214076389466625400850029)
                  ·
                    refine ⟨4955278646049984525318761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13214076389466625400850029 4955278646049984525318761)
                    ·
                      refine ⟨3716458984537488393989071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955278646049984525318761 3716458984537488393989071)
                      ·
                        rfl

theorem cell23_7237778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_7237778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237778 prefixEnd_7237778 := by exact prefixLift 7237778
  have htrace : WordTrace (prefixWord ++ tailWord_7237778) baseStart_7237778 baseEnd_7237778 := by
    simpa [prefixWord, tailWord_7237778, baseEnd_7237778] using wordTrace_append hprefix tailTrace_7237778
  have hstable : (prefixWord ++ tailWord_7237778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237778).length < 2 ^ (prefixWord ++ tailWord_7237778).sum := by decide
  have hdescent : baseEnd_7237778 < baseStart_7237778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237848 : List Nat := [2, 1, 2, 2, 4, 1, 3, 3, 5]
def baseStart_7237848 : Nat := 118140960795 + 7237848 * 2 ^ 59
def prefixEnd_7237848 : Nat := 4983230072969 + 3 ^ 40 * 7237848 * 2
def baseEnd_7237848 : Nat := 412943880909255902234861

theorem tailTrace_7237848 : CollatzResearch.WordTrace tailWord_7237848 prefixEnd_7237848 412943880909255902234861 := by
  unfold tailWord_7237848
  simp only [CollatzResearch.WordTrace]
  refine ⟨131993001941260148435245099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175990669255013531246993465 131993001941260148435245099)
  ·
    refine ⟨197989502911890222652867649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131993001941260148435245099 197989502911890222652867649)
    ·
      refine ⟨148492127183917666989650737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197989502911890222652867649 148492127183917666989650737)
      ·
        refine ⟨111369095387938250242238053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148492127183917666989650737 111369095387938250242238053)
        ·
          refine ⟨20881705385238421920419635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111369095387938250242238053 20881705385238421920419635)
          ·
            refine ⟨31322558077857632880629453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20881705385238421920419635 31322558077857632880629453)
            ·
              refine ⟨11745959279196612330236045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31322558077857632880629453 11745959279196612330236045)
              ·
                refine ⟨4404734729698729623838517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11745959279196612330236045 4404734729698729623838517)
                ·
                  refine ⟨412943880909255902234861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4404734729698729623838517 412943880909255902234861)
                  ·
                    rfl

theorem cell23_7237848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 5].length) (baseStart_7237848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237848 prefixEnd_7237848 := by exact prefixLift 7237848
  have htrace : WordTrace (prefixWord ++ tailWord_7237848) baseStart_7237848 baseEnd_7237848 := by
    simpa [prefixWord, tailWord_7237848, baseEnd_7237848] using wordTrace_append hprefix tailTrace_7237848
  have hstable : (prefixWord ++ tailWord_7237848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237848).length < 2 ^ (prefixWord ++ tailWord_7237848).sum := by decide
  have hdescent : baseEnd_7237848 < baseStart_7237848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237861 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_7237861 : Nat := 118140960795 + 7237861 * 2 ^ 59
def prefixEnd_7237861 : Nat := 4983230072969 + 3 ^ 40 * 7237861 * 2
def baseEnd_7237861 : Nat := 1238833867810603856417063

theorem tailTrace_7237861 : CollatzResearch.WordTrace tailWord_7237861 prefixEnd_7237861 1238833867810603856417063 := by
  unfold tailWord_7237861
  simp only [CollatzResearch.WordTrace]
  refine ⟨263986478031473200090713437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175990985354315466727142291 263986478031473200090713437)
  ·
    refine ⟨98994929261802450034017539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263986478031473200090713437 98994929261802450034017539)
    ·
      refine ⟨148492393892703675051026309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98994929261802450034017539 148492393892703675051026309)
      ·
        refine ⟨27842323854881939072067433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148492393892703675051026309 27842323854881939072067433)
        ·
          refine ⟨20881742891161454304050575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27842323854881939072067433 20881742891161454304050575)
          ·
            refine ⟨31322614336742181456075863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20881742891161454304050575 31322614336742181456075863)
            ·
              refine ⟨46983921505113272184113795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31322614336742181456075863 46983921505113272184113795)
              ·
                refine ⟨70475882257669908276170693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46983921505113272184113795 70475882257669908276170693)
                ·
                  refine ⟨13214227923313107801782005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70475882257669908276170693 13214227923313107801782005)
                  ·
                    refine ⟨1238833867810603856417063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13214227923313107801782005 1238833867810603856417063)
                    ·
                      rfl

theorem cell23_7237861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_7237861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237861 prefixEnd_7237861 := by exact prefixLift 7237861
  have htrace : WordTrace (prefixWord ++ tailWord_7237861) baseStart_7237861 baseEnd_7237861 := by
    simpa [prefixWord, tailWord_7237861, baseEnd_7237861] using wordTrace_append hprefix tailTrace_7237861
  have hstable : (prefixWord ++ tailWord_7237861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237861).length < 2 ^ (prefixWord ++ tailWord_7237861).sum := by decide
  have hdescent : baseEnd_7237861 < baseStart_7237861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237871 : List Nat := [1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 5]
def baseStart_7237871 : Nat := 118140960795 + 7237871 * 2 ^ 59
def prefixEnd_7237871 : Nat := 4983230072969 + 3 ^ 40 * 7237871 * 2
def baseEnd_7237871 : Nat := 3716506738238356530126143

theorem tailTrace_7237871 : CollatzResearch.WordTrace tailWord_7237871 prefixEnd_7237871 3716506738238356530126143 := by
  unfold tailWord_7237871
  simp only [CollatzResearch.WordTrace]
  refine ⟨263986842761436971798577467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175991228507624647865718311 263986842761436971798577467)
  ·
    refine ⟨395980264142155457697866201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263986842761436971798577467 395980264142155457697866201)
    ·
      refine ⟨296985198106616593273399651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395980264142155457697866201 296985198106616593273399651)
      ·
        refine ⟨445477797159924889910099477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296985198106616593273399651 445477797159924889910099477)
        ·
          refine ⟨20881771741871479214535913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 445477797159924889910099477 20881771741871479214535913)
          ·
            refine ⟨15661328806403609410901935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20881771741871479214535913 15661328806403609410901935)
            ·
              refine ⟨23491993209605414116352903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15661328806403609410901935 23491993209605414116352903)
              ·
                refine ⟨35237989814408121174529355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23491993209605414116352903 35237989814408121174529355)
                ·
                  refine ⟨52856984721612181761794033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35237989814408121174529355 52856984721612181761794033)
                  ·
                    refine ⟨39642738541209136321345525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52856984721612181761794033 39642738541209136321345525)
                    ·
                      refine ⟨3716506738238356530126143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39642738541209136321345525 3716506738238356530126143)
                      ·
                        rfl

theorem cell23_7237871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_7237871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237871 prefixEnd_7237871 := by exact prefixLift 7237871
  have htrace : WordTrace (prefixWord ++ tailWord_7237871) baseStart_7237871 baseEnd_7237871 := by
    simpa [prefixWord, tailWord_7237871, baseEnd_7237871] using wordTrace_append hprefix tailTrace_7237871
  have hstable : (prefixWord ++ tailWord_7237871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237871).length < 2 ^ (prefixWord ++ tailWord_7237871).sum := by decide
  have hdescent : baseEnd_7237871 < baseStart_7237871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237891 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 5, 4]
def baseStart_7237891 : Nat := 118140960795 + 7237891 * 2 ^ 59
def prefixEnd_7237891 : Nat := 4983230072969 + 3 ^ 40 * 7237891 * 2
def baseEnd_7237891 : Nat := 1238839002617148817292017

theorem tailTrace_7237891 : CollatzResearch.WordTrace tailWord_7237891 prefixEnd_7237891 1238839002617148817292017 := by
  unfold tailWord_7237891
  simp only [CollatzResearch.WordTrace]
  refine ⟨263987572221364515214305527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175991714814243010142870351 263987572221364515214305527)
  ·
    refine ⟨395981358332046772821458291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263987572221364515214305527 395981358332046772821458291)
    ·
      refine ⟨593972037498070159232187437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395981358332046772821458291 593972037498070159232187437)
      ·
        refine ⟨222739514061776309712070289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 593972037498070159232187437 222739514061776309712070289)
        ·
          refine ⟨167054635546332232284052717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222739514061776309712070289 167054635546332232284052717)
          ·
            refine ⟨62645488329874587106519769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167054635546332232284052717 62645488329874587106519769)
            ·
              refine ⟨46984116247405940329889827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62645488329874587106519769 46984116247405940329889827)
              ·
                refine ⟨70476174371108910494834741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46984116247405940329889827 70476174371108910494834741)
                ·
                  refine ⟨6607141347291460358890757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70476174371108910494834741 6607141347291460358890757)
                  ·
                    refine ⟨1238839002617148817292017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6607141347291460358890757 1238839002617148817292017)
                    ·
                      rfl

theorem cell23_7237891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 4].length) (baseStart_7237891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237891 prefixEnd_7237891 := by exact prefixLift 7237891
  have htrace : WordTrace (prefixWord ++ tailWord_7237891) baseStart_7237891 baseEnd_7237891 := by
    simpa [prefixWord, tailWord_7237891, baseEnd_7237891] using wordTrace_append hprefix tailTrace_7237891
  have hstable : (prefixWord ++ tailWord_7237891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237891).length < 2 ^ (prefixWord ++ tailWord_7237891).sum := by decide
  have hdescent : baseEnd_7237891 < baseStart_7237891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237895 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 2, 5]
def baseStart_7237895 : Nat := 118140960795 + 7237895 * 2 ^ 59
def prefixEnd_7237895 : Nat := 4983230072969 + 3 ^ 40 * 7237895 * 2
def baseEnd_7237895 : Nat := 1238839687258021478742011

theorem tailTrace_7237895 : CollatzResearch.WordTrace tailWord_7237895 prefixEnd_7237895 1238839687258021478742011 := by
  unfold tailWord_7237895
  simp only [CollatzResearch.WordTrace]
  refine ⟨263987718113350023897451139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175991812075566682598300759 263987718113350023897451139)
  ·
    refine ⟨395981577170025035846176709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263987718113350023897451139 395981577170025035846176709)
    ·
      refine ⟨74246545719379694221158133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 395981577170025035846176709 74246545719379694221158133)
      ·
        refine ⟨6960613661191846333233575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74246545719379694221158133 6960613661191846333233575)
        ·
          refine ⟨10440920491787769499850363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6960613661191846333233575 10440920491787769499850363)
          ·
            refine ⟨15661380737681654249775545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10440920491787769499850363 15661380737681654249775545)
            ·
              refine ⟨11746035553261240687331659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15661380737681654249775545 11746035553261240687331659)
              ·
                refine ⟨17619053329891861030997489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11746035553261240687331659 17619053329891861030997489)
                ·
                  refine ⟨13214289997418895773248117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17619053329891861030997489 13214289997418895773248117)
                  ·
                    refine ⟨1238839687258021478742011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13214289997418895773248117 1238839687258021478742011)
                    ·
                      rfl

theorem cell23_7237895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_7237895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237895 prefixEnd_7237895 := by exact prefixLift 7237895
  have htrace : WordTrace (prefixWord ++ tailWord_7237895) baseStart_7237895 baseEnd_7237895 := by
    simpa [prefixWord, tailWord_7237895, baseEnd_7237895] using wordTrace_append hprefix tailTrace_7237895
  have hstable : (prefixWord ++ tailWord_7237895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237895).length < 2 ^ (prefixWord ++ tailWord_7237895).sum := by decide
  have hdescent : baseEnd_7237895 < baseStart_7237895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237921 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 6]
def baseStart_7237921 : Nat := 118140960795 + 7237921 * 2 ^ 59
def prefixEnd_7237921 : Nat := 4983230072969 + 3 ^ 40 * 7237921 * 2
def baseEnd_7237921 : Nat := 412948045807897926055657

theorem tailTrace_7237921 : CollatzResearch.WordTrace tailWord_7237921 prefixEnd_7237921 412948045807897926055657 := by
  unfold tailWord_7237921
  simp only [CollatzResearch.WordTrace]
  refine ⟨263988666411255830337897617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175992444274170553558598411 263988666411255830337897617)
  ·
    refine ⟨197991499808441872753423213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263988666411255830337897617 197991499808441872753423213)
    ·
      refine ⟨74246812428165702282533705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197991499808441872753423213 74246812428165702282533705)
      ·
        refine ⟨55685109321124276711900279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74246812428165702282533705 55685109321124276711900279)
        ·
          refine ⟨83527663981686415067850419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55685109321124276711900279 83527663981686415067850419)
          ·
            refine ⟨125291495972529622601775629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83527663981686415067850419 125291495972529622601775629)
            ·
              refine ⟨46984310989698608475665861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125291495972529622601775629 46984310989698608475665861)
              ·
                refine ⟨8809558310568489089187349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46984310989698608475665861 8809558310568489089187349)
                ·
                  refine ⟨412948045807897926055657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8809558310568489089187349 412948045807897926055657)
                  ·
                    rfl

theorem cell23_7237921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 6].length) (baseStart_7237921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237921 prefixEnd_7237921 := by exact prefixLift 7237921
  have htrace : WordTrace (prefixWord ++ tailWord_7237921) baseStart_7237921 baseEnd_7237921 := by
    simpa [prefixWord, tailWord_7237921, baseEnd_7237921] using wordTrace_append hprefix tailTrace_7237921
  have hstable : (prefixWord ++ tailWord_7237921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237921).length < 2 ^ (prefixWord ++ tailWord_7237921).sum := by decide
  have hdescent : baseEnd_7237921 < baseStart_7237921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237951 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 3, 5]
def baseStart_7237951 : Nat := 118140960795 + 7237951 * 2 ^ 59
def prefixEnd_7237951 : Nat := 4983230072969 + 3 ^ 40 * 7237951 * 2
def baseEnd_7237951 : Nat := 1238849272230238739041925

theorem tailTrace_7237951 : CollatzResearch.WordTrace tailWord_7237951 prefixEnd_7237951 1238849272230238739041925 := by
  unfold tailWord_7237951
  simp only [CollatzResearch.WordTrace]
  refine ⟨263989760601147145461489707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175993173734098096974326471 263989760601147145461489707)
  ·
    refine ⟨395984640901720718192234561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263989760601147145461489707 395984640901720718192234561)
    ·
      refine ⟨296988480676290538644175921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395984640901720718192234561 296988480676290538644175921)
      ·
        refine ⟨222741360507217903983131941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296988480676290538644175921 222741360507217903983131941)
        ·
          refine ⟨41764005095103356996837239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222741360507217903983131941 41764005095103356996837239)
          ·
            refine ⟨62646007642655035495255859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41764005095103356996837239 62646007642655035495255859)
            ·
              refine ⟨93969011463982553242883789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62646007642655035495255859 93969011463982553242883789)
              ·
                refine ⟨35238379298993457466081421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93969011463982553242883789 35238379298993457466081421)
                ·
                  refine ⟨13214392237122546549780533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35238379298993457466081421 13214392237122546549780533)
                  ·
                    refine ⟨1238849272230238739041925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13214392237122546549780533 1238849272230238739041925)
                    ·
                      rfl

theorem cell23_7237951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_7237951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237951 prefixEnd_7237951 := by exact prefixLift 7237951
  have htrace : WordTrace (prefixWord ++ tailWord_7237951) baseStart_7237951 baseEnd_7237951 := by
    simpa [prefixWord, tailWord_7237951, baseEnd_7237951] using wordTrace_append hprefix tailTrace_7237951
  have hstable : (prefixWord ++ tailWord_7237951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237951).length < 2 ^ (prefixWord ++ tailWord_7237951).sum := by decide
  have hdescent : baseEnd_7237951 < baseStart_7237951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237968 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 1, 5]
def baseStart_7237968 : Nat := 118140960795 + 7237968 * 2 ^ 59
def prefixEnd_7237968 : Nat := 4983230072969 + 3 ^ 40 * 7237968 * 2
def baseEnd_7237968 : Nat := 1238852181953947550204399

theorem tailTrace_7237968 : CollatzResearch.WordTrace tailWord_7237968 prefixEnd_7237968 1238852181953947550204399 := by
  unfold tailWord_7237968
  simp only [CollatzResearch.WordTrace]
  refine ⟨131995190321042778682429279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175993587094723704909905705 131995190321042778682429279)
  ·
    refine ⟨197992785481564168023643919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131995190321042778682429279 197992785481564168023643919)
    ·
      refine ⟨296989178222346252035465879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197992785481564168023643919 296989178222346252035465879)
      ·
        refine ⟨445483767333519378053198819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296989178222346252035465879 445483767333519378053198819)
        ·
          refine ⟨668225651000279067079798229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445483767333519378053198819 668225651000279067079798229)
          ·
            refine ⟨15661538695319040634682771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 668225651000279067079798229 15661538695319040634682771)
            ·
              refine ⟨23492308042978560952024157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15661538695319040634682771 23492308042978560952024157)
              ·
                refine ⟨8809615516116960357009059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23492308042978560952024157 8809615516116960357009059)
                ·
                  refine ⟨13214423274175440535513589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8809615516116960357009059 13214423274175440535513589)
                  ·
                    refine ⟨1238852181953947550204399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13214423274175440535513589 1238852181953947550204399)
                    ·
                      rfl

theorem cell23_7237968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 5].length) (baseStart_7237968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237968 prefixEnd_7237968 := by exact prefixLift 7237968
  have htrace : WordTrace (prefixWord ++ tailWord_7237968) baseStart_7237968 baseEnd_7237968 := by
    simpa [prefixWord, tailWord_7237968, baseEnd_7237968] using wordTrace_append hprefix tailTrace_7237968
  have hstable : (prefixWord ++ tailWord_7237968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237968).length < 2 ^ (prefixWord ++ tailWord_7237968).sum := by decide
  have hdescent : baseEnd_7237968 < baseStart_7237968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7237971 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 4]
def baseStart_7237971 : Nat := 118140960795 + 7237971 * 2 ^ 59
def prefixEnd_7237971 : Nat := 4983230072969 + 3 ^ 40 * 7237971 * 2
def baseEnd_7237971 : Nat := 3716558086303806138875683

theorem tailTrace_7237971 : CollatzResearch.WordTrace tailWord_7237971 prefixEnd_7237971 3716558086303806138875683 := by
  unfold tailWord_7237971
  simp only [CollatzResearch.WordTrace]
  refine ⟨263990490061074688877217767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175993660040716459251478511 263990490061074688877217767)
  ·
    refine ⟨395985735091612033315826651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263990490061074688877217767 395985735091612033315826651)
    ·
      refine ⟨593978602637418049973739977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395985735091612033315826651 593978602637418049973739977)
      ·
        refine ⟨445483951978063537480304983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593978602637418049973739977 445483951978063537480304983)
        ·
          refine ⟨668225927967095306220457475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445483951978063537480304983 668225927967095306220457475)
          ·
            refine ⟨1002338891950642959330686213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668225927967095306220457475 1002338891950642959330686213)
            ·
              refine ⟨187938542240745554874503665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1002338891950642959330686213 187938542240745554874503665)
              ·
                refine ⟨140953906680559166155877749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187938542240745554874503665 140953906680559166155877749)
                ·
                  refine ⟨13214428751302421827113539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140953906680559166155877749 13214428751302421827113539)
                  ·
                    refine ⟨19821643126953632740670309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13214428751302421827113539 19821643126953632740670309)
                    ·
                      refine ⟨3716558086303806138875683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19821643126953632740670309 3716558086303806138875683)
                      ·
                        rfl

theorem cell23_7237971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_7237971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7237971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7237971 prefixEnd_7237971 := by exact prefixLift 7237971
  have htrace : WordTrace (prefixWord ++ tailWord_7237971) baseStart_7237971 baseEnd_7237971 := by
    simpa [prefixWord, tailWord_7237971, baseEnd_7237971] using wordTrace_append hprefix tailTrace_7237971
  have hstable : (prefixWord ++ tailWord_7237971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7237971).length < 2 ^ (prefixWord ++ tailWord_7237971).sum := by decide
  have hdescent : baseEnd_7237971 < baseStart_7237971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7237971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238005 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_7238005 : Nat := 118140960795 + 7238005 * 2 ^ 59
def prefixEnd_7238005 : Nat := 4983230072969 + 3 ^ 40 * 7238005 * 2
def baseEnd_7238005 : Nat := 3716575544646059005850527

theorem tailTrace_7238005 : CollatzResearch.WordTrace tailWord_7238005 prefixEnd_7238005 3716575544646059005850527 := by
  unfold tailWord_7238005
  simp only [CollatzResearch.WordTrace]
  refine ⟨263991730142951512683955469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175994486761967675122636979 263991730142951512683955469)
  ·
    refine ⟨98996898803606817256483301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263991730142951512683955469 98996898803606817256483301)
    ·
      refine ⟨18561918525676278235590619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98996898803606817256483301 18561918525676278235590619)
      ·
        refine ⟨27842877788514417353385929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18561918525676278235590619 27842877788514417353385929)
        ·
          refine ⟨20882158341385813015039447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27842877788514417353385929 20882158341385813015039447)
          ·
            refine ⟨31323237512078719522559171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20882158341385813015039447 31323237512078719522559171)
            ·
              refine ⟨46984856268118079283838757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31323237512078719522559171 46984856268118079283838757)
              ·
                refine ⟨8809660550272139865719767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46984856268118079283838757 8809660550272139865719767)
                ·
                  refine ⟨13214490825408209798579651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8809660550272139865719767 13214490825408209798579651)
                  ·
                    refine ⟨19821736238112314697869477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13214490825408209798579651 19821736238112314697869477)
                    ·
                      refine ⟨3716575544646059005850527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19821736238112314697869477 3716575544646059005850527)
                      ·
                        rfl

theorem cell23_7238005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_7238005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238005 prefixEnd_7238005 := by exact prefixLift 7238005
  have htrace : WordTrace (prefixWord ++ tailWord_7238005) baseStart_7238005 baseEnd_7238005 := by
    simpa [prefixWord, tailWord_7238005, baseEnd_7238005] using wordTrace_append hprefix tailTrace_7238005
  have hstable : (prefixWord ++ tailWord_7238005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238005).length < 2 ^ (prefixWord ++ tailWord_7238005).sum := by decide
  have hdescent : baseEnd_7238005 < baseStart_7238005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238011 : List Nat := [1, 1, 1, 1, 1, 8, 1, 9]
def baseStart_7238011 : Nat := 118140960795 + 7238011 * 2 ^ 59
def prefixEnd_7238011 : Nat := 4983230072969 + 3 ^ 40 * 7238011 * 2
def baseEnd_7238011 : Nat := 137651060204814295643537

theorem tailTrace_7238011 : CollatzResearch.WordTrace tailWord_7238011 prefixEnd_7238011 137651060204814295643537 := by
  unfold tailWord_7238011
  simp only [CollatzResearch.WordTrace]
  refine ⟨263991948980929775708673887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175994632653953183805782591 263991948980929775708673887)
  ·
    refine ⟨395987923471394663563010831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263991948980929775708673887 395987923471394663563010831)
    ·
      refine ⟨593981885207091995344516247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395987923471394663563010831 593981885207091995344516247)
      ·
        refine ⟨890972827810637993016774371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593981885207091995344516247 890972827810637993016774371)
        ·
          refine ⟨1336459241715956989525161557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890972827810637993016774371 1336459241715956989525161557)
          ·
            refine ⟨15661631738858870970997987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1336459241715956989525161557 15661631738858870970997987)
            ·
              refine ⟨23492447608288306456496981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15661631738858870970997987 23492447608288306456496981)
              ·
                refine ⟨137651060204814295643537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23492447608288306456496981 137651060204814295643537)
                ·
                  rfl

theorem cell23_7238011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 9].length) (baseStart_7238011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238011 prefixEnd_7238011 := by exact prefixLift 7238011
  have htrace : WordTrace (prefixWord ++ tailWord_7238011) baseStart_7238011 baseEnd_7238011 := by
    simpa [prefixWord, tailWord_7238011, baseEnd_7238011] using wordTrace_append hprefix tailTrace_7238011
  have hstable : (prefixWord ++ tailWord_7238011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238011).length < 2 ^ (prefixWord ++ tailWord_7238011).sum := by decide
  have hdescent : baseEnd_7238011 < baseStart_7238011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238025 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 1, 2, 3]
def baseStart_7238025 : Nat := 118140960795 + 7238025 * 2 ^ 59
def prefixEnd_7238025 : Nat := 4983230072969 + 3 ^ 40 * 7238025 * 2
def baseEnd_7238025 : Nat := 3716585814259148927600435

theorem tailTrace_7238025 : CollatzResearch.WordTrace tailWord_7238025 prefixEnd_7238025 3716585814259148927600435 := by
  unfold tailWord_7238025
  simp only [CollatzResearch.WordTrace]
  refine ⟨263992459602879056099683529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175994973068586037399789019 263992459602879056099683529)
  ·
    refine ⟨197994344702159292074762647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263992459602879056099683529 197994344702159292074762647)
    ·
      refine ⟨296991517053238938112143971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197994344702159292074762647 296991517053238938112143971)
      ·
        refine ⟨445487275579858407168215957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296991517053238938112143971 445487275579858407168215957)
        ·
          refine ⟨20882216042805862836010123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 445487275579858407168215957 20882216042805862836010123)
          ·
            refine ⟨31323324064208794254015185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20882216042805862836010123 31323324064208794254015185)
            ·
              refine ⟨23492493048156595690511389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31323324064208794254015185 23492493048156595690511389)
              ·
                refine ⟨8809684893058723383941771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23492493048156595690511389 8809684893058723383941771)
                ·
                  refine ⟨13214527339588085075912657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8809684893058723383941771 13214527339588085075912657)
                  ·
                    refine ⟨9910895504691063806934493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13214527339588085075912657 9910895504691063806934493)
                    ·
                      refine ⟨3716585814259148927600435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9910895504691063806934493 3716585814259148927600435)
                      ·
                        rfl

theorem cell23_7238025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 2, 3].length) (baseStart_7238025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238025 prefixEnd_7238025 := by exact prefixLift 7238025
  have htrace : WordTrace (prefixWord ++ tailWord_7238025) baseStart_7238025 baseEnd_7238025 := by
    simpa [prefixWord, tailWord_7238025, baseEnd_7238025] using wordTrace_append hprefix tailTrace_7238025
  have hstable : (prefixWord ++ tailWord_7238025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238025).length < 2 ^ (prefixWord ++ tailWord_7238025).sum := by decide
  have hdescent : baseEnd_7238025 < baseStart_7238025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238041 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 2, 7]
def baseStart_7238041 : Nat := 118140960795 + 7238041 * 2 ^ 59
def prefixEnd_7238041 : Nat := 4983230072969 + 3 ^ 40 * 7238041 * 2
def baseEnd_7238041 : Nat := 1238864676649873621666787

theorem tailTrace_7238041 : CollatzResearch.WordTrace tailWord_7238041 prefixEnd_7238041 1238864676649873621666787 := by
  unfold tailWord_7238041
  simp only [CollatzResearch.WordTrace]
  refine ⟨263993043170821090832265977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175995362113880727221510651 263993043170821090832265977)
  ·
    refine ⟨197994782378115818124199483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263993043170821090832265977 197994782378115818124199483)
    ·
      refine ⟨296992173567173727186299225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197994782378115818124199483 296992173567173727186299225)
      ·
        refine ⟨222744130175380295389724419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296992173567173727186299225 222744130175380295389724419)
        ·
          refine ⟨334116195263070443084586629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222744130175380295389724419 334116195263070443084586629)
          ·
            refine ⟨62646786611825708078359993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334116195263070443084586629 62646786611825708078359993)
            ·
              refine ⟨46985089958869281058769995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62646786611825708078359993 46985089958869281058769995)
              ·
                refine ⟨70477634938303921588154993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46985089958869281058769995 70477634938303921588154993)
                ·
                  refine ⟨52858226203727941191116245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70477634938303921588154993 52858226203727941191116245)
                  ·
                    refine ⟨1238864676649873621666787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52858226203727941191116245 1238864676649873621666787)
                    ·
                      rfl

theorem cell23_7238041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_7238041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238041 prefixEnd_7238041 := by exact prefixLift 7238041
  have htrace : WordTrace (prefixWord ++ tailWord_7238041) baseStart_7238041 baseEnd_7238041 := by
    simpa [prefixWord, tailWord_7238041, baseEnd_7238041] using wordTrace_append hprefix tailTrace_7238041
  have hstable : (prefixWord ++ tailWord_7238041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238041).length < 2 ^ (prefixWord ++ tailWord_7238041).sum := by decide
  have hdescent : baseEnd_7238041 < baseStart_7238041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238091 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 6]
def baseStart_7238091 : Nat := 118140960795 + 7238091 * 2 ^ 59
def prefixEnd_7238091 : Nat := 4983230072969 + 3 ^ 40 * 7238091 * 2
def baseEnd_7238091 : Nat := 3716619703982345669375131

theorem tailTrace_7238091 : CollatzResearch.WordTrace tailWord_7238091 prefixEnd_7238091 3716619703982345669375131 := by
  unfold tailWord_7238091
  simp only [CollatzResearch.WordTrace]
  refine ⟨263994866820639949371586127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175996577880426632914390751 263994866820639949371586127)
  ·
    refine ⟨395992300230959924057379191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 263994866820639949371586127 395992300230959924057379191)
    ·
      refine ⟨593988450346439886086068787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395992300230959924057379191 593988450346439886086068787)
      ·
        refine ⟨890982675519659829129103181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593988450346439886086068787 890982675519659829129103181)
        ·
          refine ⟨334118503319872435923413693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 890982675519659829129103181 334118503319872435923413693)
          ·
            refine ⟨125294438744952163471280135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334118503319872435923413693 125294438744952163471280135)
            ·
              refine ⟨187941658117428245206920203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125294438744952163471280135 187941658117428245206920203)
              ·
                refine ⟨281912487176142367810380305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187941658117428245206920203 281912487176142367810380305)
                ·
                  refine ⟨211434365382106775857785229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281912487176142367810380305 211434365382106775857785229)
                  ·
                    refine ⟨79287887018290040946669461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211434365382106775857785229 79287887018290040946669461)
                    ·
                      refine ⟨3716619703982345669375131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79287887018290040946669461 3716619703982345669375131)
                      ·
                        rfl

theorem cell23_7238091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_7238091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238091 prefixEnd_7238091 := by exact prefixLift 7238091
  have htrace : WordTrace (prefixWord ++ tailWord_7238091) baseStart_7238091 baseEnd_7238091 := by
    simpa [prefixWord, tailWord_7238091, baseEnd_7238091] using wordTrace_append hprefix tailTrace_7238091
  have hstable : (prefixWord ++ tailWord_7238091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238091).length < 2 ^ (prefixWord ++ tailWord_7238091).sum := by decide
  have hdescent : baseEnd_7238091 < baseStart_7238091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238112 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 2, 2, 2]
def baseStart_7238112 : Nat := 118140960795 + 7238112 * 2 ^ 59
def prefixEnd_7238112 : Nat := 4983230072969 + 3 ^ 40 * 7238112 * 2
def baseEnd_7238112 : Nat := 3716630487076090087212535

theorem tailTrace_7238112 : CollatzResearch.WordTrace tailWord_7238112 prefixEnd_7238112 3716630487076090087212535 := by
  unfold tailWord_7238112
  simp only [CollatzResearch.WordTrace]
  refine ⟨131997816376781934979050295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175997088502375913305400393 131997816376781934979050295)
  ·
    refine ⟨197996724565172902468575443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131997816376781934979050295 197996724565172902468575443)
    ·
      refine ⟨296995086847759353702863165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197996724565172902468575443 296995086847759353702863165)
      ·
        refine ⟨111373157567909757638573687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 296995086847759353702863165 111373157567909757638573687)
        ·
          refine ⟨167059736351864636457860531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111373157567909757638573687 167059736351864636457860531)
          ·
            refine ⟨250589604527796954686790797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167059736351864636457860531 250589604527796954686790797)
            ·
              refine ⟨93971101697923858007546549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250589604527796954686790797 93971101697923858007546549)
              ·
                refine ⟨8809790784180361688207489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93971101697923858007546549 8809790784180361688207489)
                ·
                  refine ⟨6607343088135271266155617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8809790784180361688207489 6607343088135271266155617)
                  ·
                    refine ⟨4955507316101453449616713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6607343088135271266155617 4955507316101453449616713)
                    ·
                      refine ⟨3716630487076090087212535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955507316101453449616713 3716630487076090087212535)
                      ·
                        rfl

theorem cell23_7238112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_7238112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238112 prefixEnd_7238112 := by exact prefixLift 7238112
  have htrace : WordTrace (prefixWord ++ tailWord_7238112) baseStart_7238112 baseEnd_7238112 := by
    simpa [prefixWord, tailWord_7238112, baseEnd_7238112] using wordTrace_append hprefix tailTrace_7238112
  have hstable : (prefixWord ++ tailWord_7238112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238112).length < 2 ^ (prefixWord ++ tailWord_7238112).sum := by decide
  have hdescent : baseEnd_7238112 < baseStart_7238112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238128 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 3]
def baseStart_7238128 : Nat := 118140960795 + 7238128 * 2 ^ 59
def prefixEnd_7238128 : Nat := 4983230072969 + 3 ^ 40 * 7238128 * 2
def baseEnd_7238128 : Nat := 3716638702766562024612461

theorem tailTrace_7238128 : CollatzResearch.WordTrace tailWord_7238128 prefixEnd_7238128 3716638702766562024612461 := by
  unfold tailWord_7238128
  simp only [CollatzResearch.WordTrace]
  refine ⟨131998108160752952345341519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175997477547670603127122025 131998108160752952345341519)
  ·
    refine ⟨197997162241129428518012279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131998108160752952345341519 197997162241129428518012279)
    ·
      refine ⟨296995743361694142777018419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197997162241129428518012279 296995743361694142777018419)
      ·
        refine ⟨445493615042541214165527629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296995743361694142777018419 445493615042541214165527629)
        ·
          refine ⟨167060105640952955312072861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445493615042541214165527629 167060105640952955312072861)
          ·
            refine ⟨62647539615357358242027323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167060105640952955312072861 62647539615357358242027323)
            ·
              refine ⟨93971309423036037363040985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62647539615357358242027323 93971309423036037363040985)
              ·
                refine ⟨70478482067277028022280739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93971309423036037363040985 70478482067277028022280739)
                ·
                  refine ⟨105717723100915542033421109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70478482067277028022280739 105717723100915542033421109)
                  ·
                    refine ⟨9911036540710832065633229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 105717723100915542033421109 9911036540710832065633229)
                    ·
                      refine ⟨3716638702766562024612461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9911036540710832065633229 3716638702766562024612461)
                      ·
                        rfl

theorem cell23_7238128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5, 3].length) (baseStart_7238128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238128 prefixEnd_7238128 := by exact prefixLift 7238128
  have htrace : WordTrace (prefixWord ++ tailWord_7238128) baseStart_7238128 baseEnd_7238128 := by
    simpa [prefixWord, tailWord_7238128, baseEnd_7238128] using wordTrace_append hprefix tailTrace_7238128
  have hstable : (prefixWord ++ tailWord_7238128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238128).length < 2 ^ (prefixWord ++ tailWord_7238128).sum := by decide
  have hdescent : baseEnd_7238128 < baseStart_7238128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238133 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_7238133 : Nat := 118140960795 + 7238133 * 2 ^ 59
def prefixEnd_7238133 : Nat := 4983230072969 + 3 ^ 40 * 7238133 * 2
def baseEnd_7238133 : Nat := 3716641270169834505049939

theorem tailTrace_7238133 : CollatzResearch.WordTrace tailWord_7238133 prefixEnd_7238133 3716641270169834505049939 := by
  unfold tailWord_7238133
  simp only [CollatzResearch.WordTrace]
  refine ⟨263996398686487790544615053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175997599124325193696410035 263996398686487790544615053)
  ·
    refine ⟨98998649507432921454230645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263996398686487790544615053 98998649507432921454230645)
    ·
      refine ⟨9281123391321836386334123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98998649507432921454230645 9281123391321836386334123)
      ·
        refine ⟨13921685086982754579501185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9281123391321836386334123 13921685086982754579501185)
        ·
          refine ⟨10441263815237065934625889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13921685086982754579501185 10441263815237065934625889)
          ·
            refine ⟨7830947861427799450969417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10441263815237065934625889 7830947861427799450969417)
            ·
              refine ⟨5873210896070849588227063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7830947861427799450969417 5873210896070849588227063)
              ·
                refine ⟨8809816344106274382340595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873210896070849588227063 8809816344106274382340595)
                ·
                  refine ⟨13214724516159411573510893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8809816344106274382340595 13214724516159411573510893)
                  ·
                    refine ⟨4955521693559779340066585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13214724516159411573510893 4955521693559779340066585)
                    ·
                      refine ⟨3716641270169834505049939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955521693559779340066585 3716641270169834505049939)
                      ·
                        rfl

theorem cell23_7238133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_7238133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238133 prefixEnd_7238133 := by exact prefixLift 7238133
  have htrace : WordTrace (prefixWord ++ tailWord_7238133) baseStart_7238133 baseEnd_7238133 := by
    simpa [prefixWord, tailWord_7238133, baseEnd_7238133] using wordTrace_append hprefix tailTrace_7238133
  have hstable : (prefixWord ++ tailWord_7238133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238133).length < 2 ^ (prefixWord ++ tailWord_7238133).sum := by decide
  have hdescent : baseEnd_7238133 < baseStart_7238133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238145 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_7238145 : Nat := 118140960795 + 7238145 * 2 ^ 59
def prefixEnd_7238145 : Nat := 4983230072969 + 3 ^ 40 * 7238145 * 2
def baseEnd_7238145 : Nat := 3716647431937688458099883

theorem tailTrace_7238145 : CollatzResearch.WordTrace tailWord_7238145 prefixEnd_7238145 3716647431937688458099883 := by
  unfold tailWord_7238145
  simp only [CollatzResearch.WordTrace]
  refine ⟨263996836362444316594051889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175997890908296211062701259 263996836362444316594051889)
  ·
    refine ⟨197997627271833237445538917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263996836362444316594051889 197997627271833237445538917)
    ·
      refine ⟨37124555113468732021038547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 197997627271833237445538917 37124555113468732021038547)
      ·
        refine ⟨55686832670203098031557821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37124555113468732021038547 55686832670203098031557821)
        ·
          refine ⟨20882562251326161761834183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55686832670203098031557821 20882562251326161761834183)
          ·
            refine ⟨31323843376989242642751275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20882562251326161761834183 31323843376989242642751275)
            ·
              refine ⟨46985765065483863964126913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31323843376989242642751275 46985765065483863964126913)
              ·
                refine ⟨35239323799112897973095185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46985765065483863964126913 35239323799112897973095185)
                ·
                  refine ⟨26429492849334673479821389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35239323799112897973095185 26429492849334673479821389)
                  ·
                    refine ⟨9911059818500502554933021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26429492849334673479821389 9911059818500502554933021)
                    ·
                      refine ⟨3716647431937688458099883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9911059818500502554933021 3716647431937688458099883)
                      ·
                        rfl

theorem cell23_7238145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_7238145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238145 prefixEnd_7238145 := by exact prefixLift 7238145
  have htrace : WordTrace (prefixWord ++ tailWord_7238145) baseStart_7238145 baseEnd_7238145 := by
    simpa [prefixWord, tailWord_7238145, baseEnd_7238145] using wordTrace_append hprefix tailTrace_7238145
  have hstable : (prefixWord ++ tailWord_7238145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238145).length < 2 ^ (prefixWord ++ tailWord_7238145).sum := by decide
  have hdescent : baseEnd_7238145 < baseStart_7238145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238146 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_7238146 : Nat := 118140960795 + 7238146 * 2 ^ 59
def prefixEnd_7238146 : Nat := 4983230072969 + 3 ^ 40 * 7238146 * 2
def baseEnd_7238146 : Nat := 3716647945418342954187379

theorem tailTrace_7238146 : CollatzResearch.WordTrace tailWord_7238146 prefixEnd_7238146 3716647945418342954187379 := by
  unfold tailWord_7238146
  simp only [CollatzResearch.WordTrace]
  refine ⟨65999218208860173441209573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175997915223627129176558861 65999218208860173441209573)
  ·
    refine ⟨12374853414161282520226795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65999218208860173441209573 12374853414161282520226795)
    ·
      refine ⟨18562280121241923780340193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12374853414161282520226795 18562280121241923780340193)
      ·
        refine ⟨13921710090931442835255145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18562280121241923780340193 13921710090931442835255145)
        ·
          refine ⟨10441282568198582126441359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13921710090931442835255145 10441282568198582126441359)
          ·
            refine ⟨15661923852297873189662039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10441282568198582126441359 15661923852297873189662039)
            ·
              refine ⟨23492885778446809784493059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15661923852297873189662039 23492885778446809784493059)
              ·
                refine ⟨35239328667670214676739589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23492885778446809784493059 35239328667670214676739589)
                ·
                  refine ⟨6607374125188165251888673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35239328667670214676739589 6607374125188165251888673)
                  ·
                    refine ⟨4955530593891123938916505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6607374125188165251888673 4955530593891123938916505)
                    ·
                      refine ⟨3716647945418342954187379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955530593891123938916505 3716647945418342954187379)
                      ·
                        rfl

theorem cell23_7238146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_7238146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238146 prefixEnd_7238146 := by exact prefixLift 7238146
  have htrace : WordTrace (prefixWord ++ tailWord_7238146) baseStart_7238146 baseEnd_7238146 := by
    simpa [prefixWord, tailWord_7238146, baseEnd_7238146] using wordTrace_append hprefix tailTrace_7238146
  have hstable : (prefixWord ++ tailWord_7238146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238146).length < 2 ^ (prefixWord ++ tailWord_7238146).sum := by decide
  have hdescent : baseEnd_7238146 < baseStart_7238146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238178 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_7238178 : Nat := 118140960795 + 7238178 * 2 ^ 59
def prefixEnd_7238178 : Nat := 4983230072969 + 3 ^ 40 * 7238178 * 2
def baseEnd_7238178 : Nat := 1238888125599762276329077

theorem tailTrace_7238178 : CollatzResearch.WordTrace tailWord_7238178 prefixEnd_7238178 1238888125599762276329077 := by
  unfold tailWord_7238178
  simp only [CollatzResearch.WordTrace]
  refine ⟨65999509992831190807500797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 175998693314216508820002125 65999509992831190807500797)
  ·
    refine ⟨24749816247311696552812799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65999509992831190807500797 24749816247311696552812799)
    ·
      refine ⟨37124724370967544829219199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24749816247311696552812799 37124724370967544829219199)
      ·
        refine ⟨55687086556451317243828799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37124724370967544829219199 55687086556451317243828799)
        ·
          refine ⟨83530629834676975865743199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55687086556451317243828799 83530629834676975865743199)
          ·
            refine ⟨125295944752015463798614799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83530629834676975865743199 125295944752015463798614799)
            ·
              refine ⟨187943917128023195697922199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125295944752015463798614799 187943917128023195697922199)
              ·
                refine ⟨281915875692034793546883299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187943917128023195697922199 281915875692034793546883299)
                ·
                  refine ⟨422873813538052190320324949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281915875692034793546883299 422873813538052190320324949)
                  ·
                    refine ⟨1238888125599762276329077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 422873813538052190320324949 1238888125599762276329077)
                    ·
                      rfl

theorem cell23_7238178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_7238178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238178 prefixEnd_7238178 := by exact prefixLift 7238178
  have htrace : WordTrace (prefixWord ++ tailWord_7238178) baseStart_7238178 baseEnd_7238178 := by
    simpa [prefixWord, tailWord_7238178, baseEnd_7238178] using wordTrace_append hprefix tailTrace_7238178
  have hstable : (prefixWord ++ tailWord_7238178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238178).length < 2 ^ (prefixWord ++ tailWord_7238178).sum := by decide
  have hdescent : baseEnd_7238178 < baseStart_7238178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238208 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 8]
def baseStart_7238208 : Nat := 118140960795 + 7238208 * 2 ^ 59
def prefixEnd_7238208 : Nat := 4983230072969 + 3 ^ 40 * 7238208 * 2
def baseEnd_7238208 : Nat := 412964420135435745734677

theorem tailTrace_7238208 : CollatzResearch.WordTrace tailWord_7238208 prefixEnd_7238208 412964420135435745734677 := by
  unfold tailWord_7238208
  simp only [CollatzResearch.WordTrace]
  refine ⟨131999567080608039176797639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 175999422774144052235730185 131999567080608039176797639)
  ·
    refine ⟨197999350620912058765196459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131999567080608039176797639 197999350620912058765196459)
    ·
      refine ⟨296999025931368088147794689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197999350620912058765196459 296999025931368088147794689)
      ·
        refine ⟨222749269448526066110846017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296999025931368088147794689 222749269448526066110846017)
        ·
          refine ⟨167061952086394549583134513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222749269448526066110846017 167061952086394549583134513)
          ·
            refine ⟨125296464064795912187350885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167061952086394549583134513 125296464064795912187350885)
            ·
              refine ⟨23493087012149233535128291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125296464064795912187350885 23493087012149233535128291)
              ·
                refine ⟨35239630518223850302692437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23493087012149233535128291 35239630518223850302692437)
                ·
                  refine ⟨412964420135435745734677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35239630518223850302692437 412964420135435745734677)
                  ·
                    rfl

theorem cell23_7238208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 8].length) (baseStart_7238208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238208 prefixEnd_7238208 := by exact prefixLift 7238208
  have htrace : WordTrace (prefixWord ++ tailWord_7238208) baseStart_7238208 baseEnd_7238208 := by
    simpa [prefixWord, tailWord_7238208, baseEnd_7238208] using wordTrace_append hprefix tailTrace_7238208
  have hstable : (prefixWord ++ tailWord_7238208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238208).length < 2 ^ (prefixWord ++ tailWord_7238208).sum := by decide
  have hdescent : baseEnd_7238208 < baseStart_7238208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238225 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 6]
def baseStart_7238225 : Nat := 118140960795 + 7238225 * 2 ^ 59
def prefixEnd_7238225 : Nat := 4983230072969 + 3 ^ 40 * 7238225 * 2
def baseEnd_7238225 : Nat := 412965390043338682788835

theorem tailTrace_7238225 : CollatzResearch.WordTrace tailWord_7238225 prefixEnd_7238225 412965390043338682788835 := by
  unfold tailWord_7238225
  simp only [CollatzResearch.WordTrace]
  refine ⟨263999754202154490256964129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 175999836134769660171309419 263999754202154490256964129)
  ·
    refine ⟨197999815651615867692723097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 263999754202154490256964129 197999815651615867692723097)
    ·
      refine ⟨148499861738711900769542323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197999815651615867692723097 148499861738711900769542323)
      ·
        refine ⟨222749792608067851154313485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148499861738711900769542323 222749792608067851154313485)
        ·
          refine ⟨83531172228025444182867557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222749792608067851154313485 83531172228025444182867557)
          ·
            refine ⟨15662094792754770784287667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83531172228025444182867557 15662094792754770784287667)
            ·
              refine ⟨23493142189132156176431501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15662094792754770784287667 23493142189132156176431501)
              ·
                refine ⟨8809928320924558566161813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23493142189132156176431501 8809928320924558566161813)
                ·
                  refine ⟨412965390043338682788835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8809928320924558566161813 412965390043338682788835)
                  ·
                    rfl

theorem cell23_7238225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 6].length) (baseStart_7238225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238225 prefixEnd_7238225 := by exact prefixLift 7238225
  have htrace : WordTrace (prefixWord ++ tailWord_7238225) baseStart_7238225 baseEnd_7238225 := by
    simpa [prefixWord, tailWord_7238225, baseEnd_7238225] using wordTrace_append hprefix tailTrace_7238225
  have hstable : (prefixWord ++ tailWord_7238225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238225).length < 2 ^ (prefixWord ++ tailWord_7238225).sum := by decide
  have hdescent : baseEnd_7238225 < baseStart_7238225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238255 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 1, 5]
def baseStart_7238255 : Nat := 118140960795 + 7238255 * 2 ^ 59
def prefixEnd_7238255 : Nat := 4983230072969 + 3 ^ 40 * 7238255 * 2
def baseEnd_7238255 : Nat := 1238901304936561009241459

theorem tailTrace_7238255 : CollatzResearch.WordTrace tailWord_7238255 prefixEnd_7238255 1238901304936561009241459 := by
  unfold tailWord_7238255
  simp only [CollatzResearch.WordTrace]
  refine ⟨264000848392045805380556219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176000565594697203587037479 264000848392045805380556219)
  ·
    refine ⟨396001272588068708070834329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264000848392045805380556219 396001272588068708070834329)
    ·
      refine ⟨297000954441051531053125747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396001272588068708070834329 297000954441051531053125747)
      ·
        refine ⟨445501431661577296579688621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297000954441051531053125747 445501431661577296579688621)
        ·
          refine ⟨167063036873091486217383233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445501431661577296579688621 167063036873091486217383233)
          ·
            refine ⟨125297277654818614663037425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167063036873091486217383233 125297277654818614663037425)
            ·
              refine ⟨93972958241113960997278069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125297277654818614663037425 93972958241113960997278069)
              ·
                refine ⟨8809964835104433843494819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93972958241113960997278069 8809964835104433843494819)
                ·
                  refine ⟨13214947252656650765242229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8809964835104433843494819 13214947252656650765242229)
                  ·
                    refine ⟨1238901304936561009241459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13214947252656650765242229 1238901304936561009241459)
                    ·
                      rfl

theorem cell23_7238255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 5].length) (baseStart_7238255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238255 prefixEnd_7238255 := by exact prefixLift 7238255
  have htrace : WordTrace (prefixWord ++ tailWord_7238255) baseStart_7238255 baseEnd_7238255 := by
    simpa [prefixWord, tailWord_7238255, baseEnd_7238255] using wordTrace_append hprefix tailTrace_7238255
  have hstable : (prefixWord ++ tailWord_7238255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238255).length < 2 ^ (prefixWord ++ tailWord_7238255).sum := by decide
  have hdescent : baseEnd_7238255 < baseStart_7238255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238275 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 4]
def baseStart_7238275 : Nat := 118140960795 + 7238275 * 2 ^ 59
def prefixEnd_7238275 : Nat := 4983230072969 + 3 ^ 40 * 7238275 * 2
def baseEnd_7238275 : Nat := 3716714184422772949474285

theorem tailTrace_7238275 : CollatzResearch.WordTrace tailWord_7238275 prefixEnd_7238275 3716714184422772949474285 := by
  unfold tailWord_7238275
  simp only [CollatzResearch.WordTrace]
  refine ⟨264001577851973348796284279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176001051901315565864189519 264001577851973348796284279)
  ·
    refine ⟨396002366777960023194426419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264001577851973348796284279 396002366777960023194426419)
    ·
      refine ⟨594003550166940034791639629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396002366777960023194426419 594003550166940034791639629)
      ·
        refine ⟨222751331312602513046864861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594003550166940034791639629 222751331312602513046864861)
        ·
          refine ⟨83531749242225942392574323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222751331312602513046864861 83531749242225942392574323)
          ·
            refine ⟨125297623863338913588861485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83531749242225942392574323 125297623863338913588861485)
            ·
              refine ⟨46986608948752092595823057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125297623863338913588861485 46986608948752092595823057)
              ·
                refine ⟨35239956711564069446867293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46986608948752092595823057 35239956711564069446867293)
                ·
                  refine ⟨13214983766836526042575235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35239956711564069446867293 13214983766836526042575235)
                  ·
                    refine ⟨19822475650254789063862853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13214983766836526042575235 19822475650254789063862853)
                    ·
                      refine ⟨3716714184422772949474285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19822475650254789063862853 3716714184422772949474285)
                      ·
                        rfl

theorem cell23_7238275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_7238275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238275 prefixEnd_7238275 := by exact prefixLift 7238275
  have htrace : WordTrace (prefixWord ++ tailWord_7238275) baseStart_7238275 baseEnd_7238275 := by
    simpa [prefixWord, tailWord_7238275, baseEnd_7238275] using wordTrace_append hprefix tailTrace_7238275
  have hstable : (prefixWord ++ tailWord_7238275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238275).length < 2 ^ (prefixWord ++ tailWord_7238275).sum := by decide
  have hdescent : baseEnd_7238275 < baseStart_7238275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238302 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_7238302 : Nat := 118140960795 + 7238302 * 2 ^ 59
def prefixEnd_7238302 : Nat := 4983230072969 + 3 ^ 40 * 7238302 * 2
def baseEnd_7238302 : Nat := 1238909349466814781278887

theorem tailTrace_7238302 : CollatzResearch.WordTrace tailWord_7238302 prefixEnd_7238302 1238909349466814781278887 := by
  unfold tailWord_7238302
  simp only [CollatzResearch.WordTrace]
  refine ⟨33000320327859441550939645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176001708415250354938344773 33000320327859441550939645)
  ·
    refine ⟨12375120122947290581602367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33000320327859441550939645 12375120122947290581602367)
    ·
      refine ⟨18562680184420935872403551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12375120122947290581602367 18562680184420935872403551)
      ·
        refine ⟨27844020276631403808605327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18562680184420935872403551 27844020276631403808605327)
        ·
          refine ⟨41766030414947105712907991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27844020276631403808605327 41766030414947105712907991)
          ·
            refine ⟨62649045622420658569361987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41766030414947105712907991 62649045622420658569361987)
            ·
              refine ⟨93973568433630987854042981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62649045622420658569361987 93973568433630987854042981)
              ·
                refine ⟨17620044081305810222633059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93973568433630987854042981 17620044081305810222633059)
                ·
                  refine ⟨26430066121958715333949589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17620044081305810222633059 26430066121958715333949589)
                  ·
                    refine ⟨1238909349466814781278887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26430066121958715333949589 1238909349466814781278887)
                    ·
                      rfl

theorem cell23_7238302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_7238302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238302 prefixEnd_7238302 := by exact prefixLift 7238302
  have htrace : WordTrace (prefixWord ++ tailWord_7238302) baseStart_7238302 baseEnd_7238302 := by
    simpa [prefixWord, tailWord_7238302, baseEnd_7238302] using wordTrace_append hprefix tailTrace_7238302
  have hstable : (prefixWord ++ tailWord_7238302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238302).length < 2 ^ (prefixWord ++ tailWord_7238302).sum := by decide
  have hdescent : baseEnd_7238302 < baseStart_7238302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238319 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 2, 4]
def baseStart_7238319 : Nat := 118140960795 + 7238319 * 2 ^ 59
def prefixEnd_7238319 : Nat := 4983230072969 + 3 ^ 40 * 7238319 * 2
def baseEnd_7238319 : Nat := 1238912259190523592441361

theorem tailTrace_7238319 : CollatzResearch.WordTrace tailWord_7238319 prefixEnd_7238319 1238912259190523592441361 := by
  unfold tailWord_7238319
  simp only [CollatzResearch.WordTrace]
  refine ⟨264003182663813944310886011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176002121775875962873924007 264003182663813944310886011)
  ·
    refine ⟨396004773995720916466329017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264003182663813944310886011 396004773995720916466329017)
    ·
      refine ⟨297003580496790687349746763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396004773995720916466329017 297003580496790687349746763)
      ·
        refine ⟨445505370745186031024620145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297003580496790687349746763 445505370745186031024620145)
        ·
          refine ⟨334129028058889523268465109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445505370745186031024620145 334129028058889523268465109)
          ·
            refine ⟨7831149095130223201604651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 334129028058889523268465109 7831149095130223201604651)
            ·
              refine ⟨11746723642695334802406977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831149095130223201604651 11746723642695334802406977)
              ·
                refine ⟨8810042732021501101805233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11746723642695334802406977 8810042732021501101805233)
                ·
                  refine ⟨6607532049016125826353925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8810042732021501101805233 6607532049016125826353925)
                  ·
                    refine ⟨1238912259190523592441361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6607532049016125826353925 1238912259190523592441361)
                    ·
                      rfl

theorem cell23_7238319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 4].length) (baseStart_7238319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238319 prefixEnd_7238319 := by exact prefixLift 7238319
  have htrace : WordTrace (prefixWord ++ tailWord_7238319) baseStart_7238319 baseEnd_7238319 := by
    simpa [prefixWord, tailWord_7238319, baseEnd_7238319] using wordTrace_append hprefix tailTrace_7238319
  have hstable : (prefixWord ++ tailWord_7238319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238319).length < 2 ^ (prefixWord ++ tailWord_7238319).sum := by decide
  have hdescent : baseEnd_7238319 < baseStart_7238319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238349 : List Nat := [1, 6, 2, 1, 2, 1, 1, 9]
def baseStart_7238349 : Nat := 118140960795 + 7238349 * 2 ^ 59
def prefixEnd_7238349 : Nat := 4983230072969 + 3 ^ 40 * 7238349 * 2
def baseEnd_7238349 : Nat := 137657488221896505924035

theorem tailTrace_7238349 : CollatzResearch.WordTrace tailWord_7238349 prefixEnd_7238349 137657488221896505924035 := by
  unfold tailWord_7238349
  simp only [CollatzResearch.WordTrace]
  refine ⟨264004276853705259434478101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176002851235803506289652067 264004276853705259434478101)
  ·
    refine ⟨12375200477517434035991161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 264004276853705259434478101 12375200477517434035991161)
    ·
      refine ⟨9281400358138075526993371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12375200477517434035991161 9281400358138075526993371)
      ·
        refine ⟨13922100537207113290490057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9281400358138075526993371 13922100537207113290490057)
        ·
          refine ⟨10441575402905334967867543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13922100537207113290490057 10441575402905334967867543)
          ·
            refine ⟨15662363104358002451801315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10441575402905334967867543 15662363104358002451801315)
            ·
              refine ⟨23493544656537003677701973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15662363104358002451801315 23493544656537003677701973)
              ·
                refine ⟨137657488221896505924035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23493544656537003677701973 137657488221896505924035)
                ·
                  rfl

theorem cell23_7238349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 9].length) (baseStart_7238349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238349 prefixEnd_7238349 := by exact prefixLift 7238349
  have htrace : WordTrace (prefixWord ++ tailWord_7238349) baseStart_7238349 baseEnd_7238349 := by
    simpa [prefixWord, tailWord_7238349, baseEnd_7238349] using wordTrace_append hprefix tailTrace_7238349
  have hstable : (prefixWord ++ tailWord_7238349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238349).length < 2 ^ (prefixWord ++ tailWord_7238349).sum := by decide
  have hdescent : baseEnd_7238349 < baseStart_7238349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238352 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 7, 3, 2]
def baseStart_7238352 : Nat := 118140960795 + 7238352 * 2 ^ 59
def prefixEnd_7238352 : Nat := 4983230072969 + 3 ^ 40 * 7238352 * 2
def baseEnd_7238352 : Nat := 3716753722433169148211431

theorem tailTrace_7238352 : CollatzResearch.WordTrace tailWord_7238352 prefixEnd_7238352 3716753722433169148211431 := by
  unfold tailWord_7238352
  simp only [CollatzResearch.WordTrace]
  refine ⟨132002193136347195473418655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176002924181796260631224873 132002193136347195473418655)
  ·
    refine ⟨198003289704520793210127983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132002193136347195473418655 198003289704520793210127983)
    ·
      refine ⟨297004934556781189815191975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198003289704520793210127983 297004934556781189815191975)
      ·
        refine ⟨445507401835171784722787963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297004934556781189815191975 445507401835171784722787963)
        ·
          refine ⟨668261102752757677084181945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445507401835171784722787963 668261102752757677084181945)
          ·
            refine ⟨501195827064568257813136459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668261102752757677084181945 501195827064568257813136459)
            ·
              refine ⟨751793740596852386719704689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501195827064568257813136459 751793740596852386719704689)
              ·
                refine ⟨563845305447639290039778517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751793740596852386719704689 563845305447639290039778517)
                ·
                  refine ⟨13215124346429045860307309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 563845305447639290039778517 13215124346429045860307309)
                  ·
                    refine ⟨4955671629910892197615241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13215124346429045860307309 4955671629910892197615241)
                    ·
                      refine ⟨3716753722433169148211431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955671629910892197615241 3716753722433169148211431)
                      ·
                        rfl

theorem cell23_7238352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 7, 3, 2].length) (baseStart_7238352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238352 prefixEnd_7238352 := by exact prefixLift 7238352
  have htrace : WordTrace (prefixWord ++ tailWord_7238352) baseStart_7238352 baseEnd_7238352 := by
    simpa [prefixWord, tailWord_7238352, baseEnd_7238352] using wordTrace_append hprefix tailTrace_7238352
  have hstable : (prefixWord ++ tailWord_7238352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238352).length < 2 ^ (prefixWord ++ tailWord_7238352).sum := by decide
  have hdescent : baseEnd_7238352 < baseStart_7238352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238385 : List Nat := [1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_7238385 : Nat := 118140960795 + 7238385 * 2 ^ 59
def prefixEnd_7238385 : Nat := 4983230072969 + 3 ^ 40 * 7238385 * 2
def baseEnd_7238385 : Nat := 3716770667294767519098779

theorem tailTrace_7238385 : CollatzResearch.WordTrace tailWord_7238385 prefixEnd_7238385 3716770667294767519098779 := by
  unfold tailWord_7238385
  simp only [CollatzResearch.WordTrace]
  refine ⟨264005589881574837582788609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176003726587716558388525739 264005589881574837582788609)
  ·
    refine ⟨198004192411181128187091457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264005589881574837582788609 198004192411181128187091457)
    ·
      refine ⟨148503144308385846140318593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198004192411181128187091457 148503144308385846140318593)
      ·
        refine ⟨111377358231289384605238945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148503144308385846140318593 111377358231289384605238945)
        ·
          refine ⟨83533018673467038453929209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111377358231289384605238945 83533018673467038453929209)
          ·
            refine ⟨62649764005100278840446907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83533018673467038453929209 62649764005100278840446907)
            ·
              refine ⟨93974646007650418260670361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62649764005100278840446907 93974646007650418260670361)
              ·
                refine ⟨70480984505737813695502771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93974646007650418260670361 70480984505737813695502771)
                ·
                  refine ⟨105721476758606720543254157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70480984505737813695502771 105721476758606720543254157)
                  ·
                    refine ⟨39645553784477520203720309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 105721476758606720543254157 39645553784477520203720309)
                    ·
                      refine ⟨3716770667294767519098779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39645553784477520203720309 3716770667294767519098779)
                      ·
                        rfl

theorem cell23_7238385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_7238385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238385 prefixEnd_7238385 := by exact prefixLift 7238385
  have htrace : WordTrace (prefixWord ++ tailWord_7238385) baseStart_7238385 baseEnd_7238385 := by
    simpa [prefixWord, tailWord_7238385, baseEnd_7238385] using wordTrace_append hprefix tailTrace_7238385
  have hstable : (prefixWord ++ tailWord_7238385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238385).length < 2 ^ (prefixWord ++ tailWord_7238385).sum := by decide
  have hdescent : baseEnd_7238385 < baseStart_7238385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238395 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 4]
def baseStart_7238395 : Nat := 118140960795 + 7238395 * 2 ^ 59
def prefixEnd_7238395 : Nat := 4983230072969 + 3 ^ 40 * 7238395 * 2
def baseEnd_7238395 : Nat := 3716775802101312479973733

theorem tailTrace_7238395 : CollatzResearch.WordTrace tailWord_7238395 prefixEnd_7238395 3716775802101312479973733 := by
  unfold tailWord_7238395
  simp only [CollatzResearch.WordTrace]
  refine ⟨264005954611538609290652639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176003969741025739527101759 264005954611538609290652639)
  ·
    refine ⟨396008931917307913935978959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264005954611538609290652639 396008931917307913935978959)
    ·
      refine ⟨594013397875961870903968439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396008931917307913935978959 594013397875961870903968439)
      ·
        refine ⟨891020096813942806355952659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594013397875961870903968439 891020096813942806355952659)
        ·
          refine ⟨1336530145220914209533928989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891020096813942806355952659 1336530145220914209533928989)
          ·
            refine ⟨501198804457842828575223371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1336530145220914209533928989 501198804457842828575223371)
            ·
              refine ⟨751798206686764242862835057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501198804457842828575223371 751798206686764242862835057)
              ·
                refine ⟨563848655015073182147126293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751798206686764242862835057 563848655015073182147126293)
                ·
                  refine ⟨26430405703831555413146545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 563848655015073182147126293 26430405703831555413146545)
                  ·
                    refine ⟨19822804277873666559859909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26430405703831555413146545 19822804277873666559859909)
                    ·
                      refine ⟨3716775802101312479973733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19822804277873666559859909 3716775802101312479973733)
                      ·
                        rfl

theorem cell23_7238395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 4].length) (baseStart_7238395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238395 prefixEnd_7238395 := by exact prefixLift 7238395
  have htrace : WordTrace (prefixWord ++ tailWord_7238395) baseStart_7238395 baseEnd_7238395 := by
    simpa [prefixWord, tailWord_7238395, baseEnd_7238395] using wordTrace_append hprefix tailTrace_7238395
  have hstable : (prefixWord ++ tailWord_7238395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238395).length < 2 ^ (prefixWord ++ tailWord_7238395).sum := by decide
  have hdescent : baseEnd_7238395 < baseStart_7238395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238405 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 7]
def baseStart_7238405 : Nat := 118140960795 + 7238405 * 2 ^ 59
def prefixEnd_7238405 : Nat := 4983230072969 + 3 ^ 40 * 7238405 * 2
def baseEnd_7238405 : Nat := 412975659656428604538743

theorem tailTrace_7238405 : CollatzResearch.WordTrace tailWord_7238405 prefixEnd_7238405 412975659656428604538743 := by
  unfold tailWord_7238405
  simp only [CollatzResearch.WordTrace]
  refine ⟨264006319341502380998516669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176004212894334920665677779 264006319341502380998516669)
  ·
    refine ⟨99002369753063392874443751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264006319341502380998516669 99002369753063392874443751)
    ·
      refine ⟨148503554629595089311665627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99002369753063392874443751 148503554629595089311665627)
      ·
        refine ⟨222755331944392633967498441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148503554629595089311665627 222755331944392633967498441)
        ·
          refine ⟨167066498958294475475623831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222755331944392633967498441 167066498958294475475623831)
          ·
            refine ⟨250599748437441713213435747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167066498958294475475623831 250599748437441713213435747)
            ·
              refine ⟨375899622656162569820153621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250599748437441713213435747 375899622656162569820153621)
              ·
                refine ⟨17620294812007620460319701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 375899622656162569820153621 17620294812007620460319701)
                ·
                  refine ⟨412975659656428604538743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17620294812007620460319701 412975659656428604538743)
                  ·
                    rfl

theorem cell23_7238405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_7238405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238405 prefixEnd_7238405 := by exact prefixLift 7238405
  have htrace : WordTrace (prefixWord ++ tailWord_7238405) baseStart_7238405 baseEnd_7238405 := by
    simpa [prefixWord, tailWord_7238405, baseEnd_7238405] using wordTrace_append hprefix tailTrace_7238405
  have hstable : (prefixWord ++ tailWord_7238405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238405).length < 2 ^ (prefixWord ++ tailWord_7238405).sum := by decide
  have hdescent : baseEnd_7238405 < baseStart_7238405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238435 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 3, 7]
def baseStart_7238435 : Nat := 118140960795 + 7238435 * 2 ^ 59
def prefixEnd_7238435 : Nat := 4983230072969 + 3 ^ 40 * 7238435 * 2
def baseEnd_7238435 : Nat := 1238932113775830774491183

theorem tailTrace_7238435 : CollatzResearch.WordTrace tailWord_7238435 prefixEnd_7238435 1238932113775830774491183 := by
  unfold tailWord_7238435
  simp only [CollatzResearch.WordTrace]
  refine ⟨264007413531393696122108759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176004942354262464081405839 264007413531393696122108759)
  ·
    refine ⟨396011120297090544183163139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264007413531393696122108759 396011120297090544183163139)
    ·
      refine ⟨594016680445635816274744709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396011120297090544183163139 594016680445635816274744709)
      ·
        refine ⟨111378127583556715551514633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 594016680445635816274744709 111378127583556715551514633)
        ·
          refine ⟨83533595687667536663635975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111378127583556715551514633 83533595687667536663635975)
          ·
            refine ⟨125300393531501304995453963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83533595687667536663635975 125300393531501304995453963)
            ·
              refine ⟨187950590297251957493180945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125300393531501304995453963 187950590297251957493180945)
              ·
                refine ⟨140962942722938968119885709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187950590297251957493180945 140962942722938968119885709)
                ·
                  refine ⟨52861103521102113044957141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140962942722938968119885709 52861103521102113044957141)
                  ·
                    refine ⟨1238932113775830774491183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52861103521102113044957141 1238932113775830774491183)
                    ·
                      rfl

theorem cell23_7238435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 7].length) (baseStart_7238435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238435 prefixEnd_7238435 := by exact prefixLift 7238435
  have htrace : WordTrace (prefixWord ++ tailWord_7238435) baseStart_7238435 baseEnd_7238435 := by
    simpa [prefixWord, tailWord_7238435, baseEnd_7238435] using wordTrace_append hprefix tailTrace_7238435
  have hstable : (prefixWord ++ tailWord_7238435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238435).length < 2 ^ (prefixWord ++ tailWord_7238435).sum := by decide
  have hdescent : baseEnd_7238435 < baseStart_7238435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238472 : List Nat := [2, 1, 3, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_7238472 : Nat := 118140960795 + 7238472 * 2 ^ 59
def prefixEnd_7238472 : Nat := 4983230072969 + 3 ^ 40 * 7238472 * 2
def baseEnd_7238472 : Nat := 3716815340111708678710879

theorem tailTrace_7238472 : CollatzResearch.WordTrace tailWord_7238472 prefixEnd_7238472 3716815340111708678710879 := by
  unfold tailWord_7238472
  simp only [CollatzResearch.WordTrace]
  refine ⟨132004381516129825720602835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176005842021506434294137113 132004381516129825720602835)
  ·
    refine ⟨198006572274194738580904253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132004381516129825720602835 198006572274194738580904253)
    ·
      refine ⟨74252464602823026967839095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198006572274194738580904253 74252464602823026967839095)
      ·
        refine ⟨111378696904234540451758643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74252464602823026967839095 111378696904234540451758643)
        ·
          refine ⟨167068045356351810677637965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111378696904234540451758643 167068045356351810677637965)
          ·
            refine ⟨62650517008631929004114237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167068045356351810677637965 62650517008631929004114237)
            ·
              refine ⟨23493943878236973376542839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62650517008631929004114237 23493943878236973376542839)
              ·
                refine ⟨35240915817355460064814259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23493943878236973376542839 35240915817355460064814259)
                ·
                  refine ⟨52861373726033190097221389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35240915817355460064814259 52861373726033190097221389)
                  ·
                    refine ⟨19823015147262446286458021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52861373726033190097221389 19823015147262446286458021)
                    ·
                      refine ⟨3716815340111708678710879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19823015147262446286458021 3716815340111708678710879)
                      ·
                        rfl

theorem cell23_7238472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_7238472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238472 prefixEnd_7238472 := by exact prefixLift 7238472
  have htrace : WordTrace (prefixWord ++ tailWord_7238472) baseStart_7238472 baseEnd_7238472 := by
    simpa [prefixWord, tailWord_7238472, baseEnd_7238472] using wordTrace_append hprefix tailTrace_7238472
  have hstable : (prefixWord ++ tailWord_7238472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238472).length < 2 ^ (prefixWord ++ tailWord_7238472).sum := by decide
  have hdescent : baseEnd_7238472 < baseStart_7238472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238489 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 2, 4, 2]
def baseStart_7238489 : Nat := 118140960795 + 7238489 * 2 ^ 59
def prefixEnd_7238489 : Nat := 4983230072969 + 3 ^ 40 * 7238489 * 2
def baseEnd_7238489 : Nat := 3716824069282835112198301

theorem tailTrace_7238489 : CollatzResearch.WordTrace tailWord_7238489 prefixEnd_7238489 3716824069282835112198301 := by
  unfold tailWord_7238489
  simp only [CollatzResearch.WordTrace]
  refine ⟨264009383073198063344574521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176006255382132042229716347 264009383073198063344574521)
  ·
    refine ⟨198007037304898547508430891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264009383073198063344574521 198007037304898547508430891)
    ·
      refine ⟨297010555957347821262646337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198007037304898547508430891 297010555957347821262646337)
      ·
        refine ⟨222757916968010865946984753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297010555957347821262646337 222757916968010865946984753)
        ·
          refine ⟨167068437726008149460238565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222757916968010865946984753 167068437726008149460238565)
          ·
            refine ⟨31325332073626528023794731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167068437726008149460238565 31325332073626528023794731)
            ·
              refine ⟨46987998110439792035692097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31325332073626528023794731 46987998110439792035692097)
              ·
                refine ⟨35240998582829844026769073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46987998110439792035692097 35240998582829844026769073)
                ·
                  refine ⟨26430748937122383020076805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35240998582829844026769073 26430748937122383020076805)
                  ·
                    refine ⟨4955765425710446816264401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26430748937122383020076805 4955765425710446816264401)
                    ·
                      refine ⟨3716824069282835112198301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955765425710446816264401 3716824069282835112198301)
                      ·
                        rfl

theorem cell23_7238489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 2, 4, 2].length) (baseStart_7238489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238489 prefixEnd_7238489 := by exact prefixLift 7238489
  have htrace : WordTrace (prefixWord ++ tailWord_7238489) baseStart_7238489 baseEnd_7238489 := by
    simpa [prefixWord, tailWord_7238489, baseEnd_7238489] using wordTrace_append hprefix tailTrace_7238489
  have hstable : (prefixWord ++ tailWord_7238489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238489).length < 2 ^ (prefixWord ++ tailWord_7238489).sum := by decide
  have hdescent : baseEnd_7238489 < baseStart_7238489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238499 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 3, 4]
def baseStart_7238499 : Nat := 118140960795 + 7238499 * 2 ^ 59
def prefixEnd_7238499 : Nat := 4983230072969 + 3 ^ 40 * 7238499 * 2
def baseEnd_7238499 : Nat := 1238943068029793357691085

theorem tailTrace_7238499 : CollatzResearch.WordTrace tailWord_7238499 prefixEnd_7238499 1238943068029793357691085 := by
  unfold tailWord_7238499
  simp only [CollatzResearch.WordTrace]
  refine ⟨264009747803161835052438551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176006498535441223368292367 264009747803161835052438551)
  ·
    refine ⟨396014621704742752578657827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264009747803161835052438551 396014621704742752578657827)
    ·
      refine ⟨594021932557114128867986741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396014621704742752578657827 594021932557114128867986741)
      ·
        refine ⟨55689556177229449581373757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 594021932557114128867986741 55689556177229449581373757)
        ·
          refine ⟨20883583566461043593015159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55689556177229449581373757 20883583566461043593015159)
          ·
            refine ⟨31325375349691565389522739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20883583566461043593015159 31325375349691565389522739)
            ·
              refine ⟨46988063024537348084284109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31325375349691565389522739 46988063024537348084284109)
              ·
                refine ⟨17620523634201505531606541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46988063024537348084284109 17620523634201505531606541)
                ·
                  refine ⟨6607696362825564574352453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17620523634201505531606541 6607696362825564574352453)
                  ·
                    refine ⟨1238943068029793357691085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6607696362825564574352453 1238943068029793357691085)
                    ·
                      rfl

theorem cell23_7238499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 4].length) (baseStart_7238499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238499 prefixEnd_7238499 := by exact prefixLift 7238499
  have htrace : WordTrace (prefixWord ++ tailWord_7238499) baseStart_7238499 baseEnd_7238499 := by
    simpa [prefixWord, tailWord_7238499, baseEnd_7238499] using wordTrace_append hprefix tailTrace_7238499
  have hstable : (prefixWord ++ tailWord_7238499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238499).length < 2 ^ (prefixWord ++ tailWord_7238499).sum := by decide
  have hdescent : baseEnd_7238499 < baseStart_7238499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238512 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 6]
def baseStart_7238512 : Nat := 118140960795 + 7238512 * 2 ^ 59
def prefixEnd_7238512 : Nat := 4983230072969 + 3 ^ 40 * 7238512 * 2
def baseEnd_7238512 : Nat := 412981764370876502467855

theorem tailTrace_7238512 : CollatzResearch.WordTrace tailWord_7238512 prefixEnd_7238512 412981764370876502467855 := by
  unfold tailWord_7238512
  simp only [CollatzResearch.WordTrace]
  refine ⟨132005110976057369136330895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176006814634743158848441193 132005110976057369136330895)
  ·
    refine ⟨198007666464086053704496343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132005110976057369136330895 198007666464086053704496343)
    ·
      refine ⟨297011499696129080556744515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198007666464086053704496343 297011499696129080556744515)
      ·
        refine ⟨445517249544193620835116773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297011499696129080556744515 445517249544193620835116773)
        ·
          refine ⟨83534484289536303906584395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445517249544193620835116773 83534484289536303906584395)
          ·
            refine ⟨125301726434304455859876593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83534484289536303906584395 125301726434304455859876593)
            ·
              refine ⟨93976294825728341894907445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125301726434304455859876593 93976294825728341894907445)
              ·
                refine ⟨8810277639912032052647573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93976294825728341894907445 8810277639912032052647573)
                ·
                  refine ⟨412981764370876502467855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8810277639912032052647573 412981764370876502467855)
                  ·
                    rfl

theorem cell23_7238512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 6].length) (baseStart_7238512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238512 prefixEnd_7238512 := by exact prefixLift 7238512
  have htrace : WordTrace (prefixWord ++ tailWord_7238512) baseStart_7238512 baseEnd_7238512 := by
    simpa [prefixWord, tailWord_7238512, baseEnd_7238512] using wordTrace_append hprefix tailTrace_7238512
  have hstable : (prefixWord ++ tailWord_7238512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238512).length < 2 ^ (prefixWord ++ tailWord_7238512).sum := by decide
  have hdescent : baseEnd_7238512 < baseStart_7238512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238522 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3]
def baseStart_7238522 : Nat := 118140960795 + 7238522 * 2 ^ 59
def prefixEnd_7238522 : Nat := 4983230072969 + 3 ^ 40 * 7238522 * 2
def baseEnd_7238522 : Nat := 3716841014144433483085649

theorem tailTrace_7238522 : CollatzResearch.WordTrace tailWord_7238522 prefixEnd_7238522 3716841014144433483085649 := by
  unfold tailWord_7238522
  simp only [CollatzResearch.WordTrace]
  refine ⟨66002646670519627495131455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176007057788052339987017213 66002646670519627495131455)
  ·
    refine ⟨99003970005779441242697183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66002646670519627495131455 99003970005779441242697183)
    ·
      refine ⟨148505955008669161864045775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99003970005779441242697183 148505955008669161864045775)
      ·
        refine ⟨222758932513003742796068663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148505955008669161864045775 222758932513003742796068663)
        ·
          refine ⟨334138398769505614194102995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222758932513003742796068663 334138398769505614194102995)
          ·
            refine ⟨501207598154258421291154493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334138398769505614194102995 501207598154258421291154493)
            ·
              refine ⟨187952849307846907984182935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501207598154258421291154493 187952849307846907984182935)
              ·
                refine ⟨281929273961770361976274403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187952849307846907984182935 281929273961770361976274403)
                ·
                  refine ⟨422893910942655542964411605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281929273961770361976274403 422893910942655542964411605)
                  ·
                    refine ⟨9911576037718489288228397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 422893910942655542964411605 9911576037718489288228397)
                    ·
                      refine ⟨3716841014144433483085649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9911576037718489288228397 3716841014144433483085649)
                      ·
                        rfl

theorem cell23_7238522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_7238522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238522 prefixEnd_7238522 := by exact prefixLift 7238522
  have htrace : WordTrace (prefixWord ++ tailWord_7238522) baseStart_7238522 baseEnd_7238522 := by
    simpa [prefixWord, tailWord_7238522, baseEnd_7238522] using wordTrace_append hprefix tailTrace_7238522
  have hstable : (prefixWord ++ tailWord_7238522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238522).length < 2 ^ (prefixWord ++ tailWord_7238522).sum := by decide
  have hdescent : baseEnd_7238522 < baseStart_7238522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238533 : List Nat := [1, 3, 1, 1, 3, 5, 1, 3, 1, 4]
def baseStart_7238533 : Nat := 118140960795 + 7238533 * 2 ^ 59
def prefixEnd_7238533 : Nat := 4983230072969 + 3 ^ 40 * 7238533 * 2
def baseEnd_7238533 : Nat := 1238948887477210980016033

theorem tailTrace_7238533 : CollatzResearch.WordTrace tailWord_7238533 prefixEnd_7238533 1238948887477210980016033 := by
  unfold tailWord_7238533
  simp only [CollatzResearch.WordTrace]
  refine ⟨264010987885038658859176253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176007325256692439239450835 264010987885038658859176253)
  ·
    refine ⟨99004120456889497072191095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264010987885038658859176253 99004120456889497072191095)
    ·
      refine ⟨148506180685334245608286643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99004120456889497072191095 148506180685334245608286643)
      ·
        refine ⟨222759271028001368412429965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148506180685334245608286643 222759271028001368412429965)
        ·
          refine ⟨83534726635500513154661237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222759271028001368412429965 83534726635500513154661237)
          ·
            refine ⟨7831380622078173108249491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83534726635500513154661237 7831380622078173108249491)
            ·
              refine ⟨11747070933117259662374237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831380622078173108249491 11747070933117259662374237)
              ·
                refine ⟨4405151599918972373390339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11747070933117259662374237 4405151599918972373390339)
                ·
                  refine ⟨6607727399878458560085509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405151599918972373390339 6607727399878458560085509)
                  ·
                    refine ⟨1238948887477210980016033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6607727399878458560085509 1238948887477210980016033)
                    ·
                      rfl

theorem cell23_7238533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_7238533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238533 prefixEnd_7238533 := by exact prefixLift 7238533
  have htrace : WordTrace (prefixWord ++ tailWord_7238533) baseStart_7238533 baseEnd_7238533 := by
    simpa [prefixWord, tailWord_7238533, baseEnd_7238533] using wordTrace_append hprefix tailTrace_7238533
  have hstable : (prefixWord ++ tailWord_7238533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238533).length < 2 ^ (prefixWord ++ tailWord_7238533).sum := by decide
  have hdescent : baseEnd_7238533 < baseStart_7238533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238539 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 5, 1, 3]
def baseStart_7238539 : Nat := 118140960795 + 7238539 * 2 ^ 59
def prefixEnd_7238539 : Nat := 4983230072969 + 3 ^ 40 * 7238539 * 2
def baseEnd_7238539 : Nat := 3716849743315559916573071

theorem tailTrace_7238539 : CollatzResearch.WordTrace tailWord_7238539 prefixEnd_7238539 3716849743315559916573071 := by
  unfold tailWord_7238539
  simp only [CollatzResearch.WordTrace]
  refine ⟨264011206723016921883894671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176007471148677947922596447 264011206723016921883894671)
  ·
    refine ⟨396016810084525382825842007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264011206723016921883894671 396016810084525382825842007)
    ·
      refine ⟨594025215126788074238763011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396016810084525382825842007 594025215126788074238763011)
      ·
        refine ⟨891037822690182111358144517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594025215126788074238763011 891037822690182111358144517)
        ·
          refine ⟨167069591754409145879652097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 891037822690182111358144517 167069591754409145879652097)
          ·
            refine ⟨125302193815806859409739073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167069591754409145879652097 125302193815806859409739073)
            ·
              refine ⟨93976645361855144557304305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125302193815806859409739073 93976645361855144557304305)
              ·
                refine ⟨70482484021391358417978229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93976645361855144557304305 70482484021391358417978229)
                ·
                  refine ⟨6607732877005439851685459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70482484021391358417978229 6607732877005439851685459)
                  ·
                    refine ⟨9911599315508159777528189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6607732877005439851685459 9911599315508159777528189)
                    ·
                      refine ⟨3716849743315559916573071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9911599315508159777528189 3716849743315559916573071)
                      ·
                        rfl

theorem cell23_7238539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 1, 3].length) (baseStart_7238539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238539 prefixEnd_7238539 := by exact prefixLift 7238539
  have htrace : WordTrace (prefixWord ++ tailWord_7238539) baseStart_7238539 baseEnd_7238539 := by
    simpa [prefixWord, tailWord_7238539, baseEnd_7238539] using wordTrace_append hprefix tailTrace_7238539
  have hstable : (prefixWord ++ tailWord_7238539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238539).length < 2 ^ (prefixWord ++ tailWord_7238539).sum := by decide
  have hdescent : baseEnd_7238539 < baseStart_7238539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238550 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_7238550 : Nat := 118140960795 + 7238550 * 2 ^ 59
def prefixEnd_7238550 : Nat := 4983230072969 + 3 ^ 40 * 7238550 * 2
def baseEnd_7238550 : Nat := 1238951797200919791178507

theorem tailTrace_7238550 : CollatzResearch.WordTrace tailWord_7238550 prefixEnd_7238550 1238951797200919791178507 := by
  unfold tailWord_7238550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16500725495373566922659069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176007738617318047175030069 16500725495373566922659069)
  ·
    refine ⟨6187772060765087595997151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16500725495373566922659069 6187772060765087595997151)
    ·
      refine ⟨9281658091147631393995727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6187772060765087595997151 9281658091147631393995727)
      ·
        refine ⟨13922487136721447090993591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9281658091147631393995727 13922487136721447090993591)
        ·
          refine ⟨20883730705082170636490387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13922487136721447090993591 20883730705082170636490387)
          ·
            refine ⟨31325596057623255954735581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20883730705082170636490387 31325596057623255954735581)
            ·
              refine ⟨11747098521608720983025843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31325596057623255954735581 11747098521608720983025843)
              ·
                refine ⟨17620647782413081474538765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11747098521608720983025843 17620647782413081474538765)
                ·
                  refine ⟨6607742918404905552952037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17620647782413081474538765 6607742918404905552952037)
                  ·
                    refine ⟨1238951797200919791178507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6607742918404905552952037 1238951797200919791178507)
                    ·
                      rfl

theorem cell23_7238550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_7238550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238550 prefixEnd_7238550 := by exact prefixLift 7238550
  have htrace : WordTrace (prefixWord ++ tailWord_7238550) baseStart_7238550 baseEnd_7238550 := by
    simpa [prefixWord, tailWord_7238550, baseEnd_7238550] using wordTrace_append hprefix tailTrace_7238550
  have hstable : (prefixWord ++ tailWord_7238550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238550).length < 2 ^ (prefixWord ++ tailWord_7238550).sum := by decide
  have hdescent : baseEnd_7238550 < baseStart_7238550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238579 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 4]
def baseStart_7238579 : Nat := 118140960795 + 7238579 * 2 ^ 59
def prefixEnd_7238579 : Nat := 4983230072969 + 3 ^ 40 * 7238579 * 2
def baseEnd_7238579 : Nat := 3716870282541739760072887

theorem tailTrace_7238579 : CollatzResearch.WordTrace tailWord_7238579 prefixEnd_7238579 3716870282541739760072887 := by
  unfold tailWord_7238579
  simp only [CollatzResearch.WordTrace]
  refine ⟨264012665642872008715350791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176008443761914672476900527 264012665642872008715350791)
  ·
    refine ⟨396018998464308013073026187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264012665642872008715350791 396018998464308013073026187)
    ·
      refine ⟨594028497696462019609539281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396018998464308013073026187 594028497696462019609539281)
      ·
        refine ⟨445521373272346514707154461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594028497696462019609539281 445521373272346514707154461)
        ·
          refine ⟨167070514977129943015182923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445521373272346514707154461 167070514977129943015182923)
          ·
            refine ⟨250605772465694914522774385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167070514977129943015182923 250605772465694914522774385)
            ·
              refine ⟨187954329349271185892080789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250605772465694914522774385 187954329349271185892080789)
              ·
                refine ⟨8810359188247086838691287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187954329349271185892080789 8810359188247086838691287)
                ·
                  refine ⟨13215538782370630258036931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8810359188247086838691287 13215538782370630258036931)
                  ·
                    refine ⟨19823308173555945387055397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13215538782370630258036931 19823308173555945387055397)
                    ·
                      refine ⟨3716870282541739760072887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19823308173555945387055397 3716870282541739760072887)
                      ·
                        rfl

theorem cell23_7238579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 4].length) (baseStart_7238579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238579 prefixEnd_7238579 := by exact prefixLift 7238579
  have htrace : WordTrace (prefixWord ++ tailWord_7238579) baseStart_7238579 baseEnd_7238579 := by
    simpa [prefixWord, tailWord_7238579, baseEnd_7238579] using wordTrace_append hprefix tailTrace_7238579
  have hstable : (prefixWord ++ tailWord_7238579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238579).length < 2 ^ (prefixWord ++ tailWord_7238579).sum := by decide
  have hdescent : baseEnd_7238579 < baseStart_7238579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238599 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_7238599 : Nat := 118140960795 + 7238599 * 2 ^ 59
def prefixEnd_7238599 : Nat := 4983230072969 + 3 ^ 40 * 7238599 * 2
def baseEnd_7238599 : Nat := 3716880552154829681822795

theorem tailTrace_7238599 : CollatzResearch.WordTrace tailWord_7238599 prefixEnd_7238599 3716880552154829681822795 := by
  unfold tailWord_7238599
  simp only [CollatzResearch.WordTrace]
  refine ⟨264013395102799552131078851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176008930068533034754052567 264013395102799552131078851)
  ·
    refine ⟨396020092654199328196618277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264013395102799552131078851 396020092654199328196618277)
    ·
      refine ⟨74253767372662374036865927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396020092654199328196618277 74253767372662374036865927)
      ·
        refine ⟨111380651058993561055298891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74253767372662374036865927 111380651058993561055298891)
        ·
          refine ⟨167070976588490341582948337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111380651058993561055298891 167070976588490341582948337)
          ·
            refine ⟨125303232441367756187211253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167070976588490341582948337 125303232441367756187211253)
            ·
              refine ⟨11747178041378227142551055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125303232441367756187211253 11747178041378227142551055)
              ·
                refine ⟨17620767062067340713826583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11747178041378227142551055 17620767062067340713826583)
                ·
                  refine ⟨26431150593101011070739875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17620767062067340713826583 26431150593101011070739875)
                  ·
                    refine ⟨39646725889651516606109813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26431150593101011070739875 39646725889651516606109813)
                    ·
                      refine ⟨3716880552154829681822795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39646725889651516606109813 3716880552154829681822795)
                      ·
                        rfl

theorem cell23_7238599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_7238599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238599 prefixEnd_7238599 := by exact prefixLift 7238599
  have htrace : WordTrace (prefixWord ++ tailWord_7238599) baseStart_7238599 baseEnd_7238599 := by
    simpa [prefixWord, tailWord_7238599, baseEnd_7238599] using wordTrace_append hprefix tailTrace_7238599
  have hstable : (prefixWord ++ tailWord_7238599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238599).length < 2 ^ (prefixWord ++ tailWord_7238599).sum := by decide
  have hdescent : baseEnd_7238599 < baseStart_7238599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238606 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_7238606 : Nat := 118140960795 + 7238606 * 2 ^ 59
def prefixEnd_7238606 : Nat := 4983230072969 + 3 ^ 40 * 7238606 * 2
def baseEnd_7238606 : Nat := 1238961382173137051478421

theorem tailTrace_7238606 : CollatzResearch.WordTrace tailWord_7238606 prefixEnd_7238606 1238961382173137051478421 := by
  unfold tailWord_7238606
  simp only [CollatzResearch.WordTrace]
  refine ⟨33001706301721774040822959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176009100275849461551055781 33001706301721774040822959)
  ·
    refine ⟨49502559452582661061234439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33001706301721774040822959 49502559452582661061234439)
    ·
      refine ⟨74253839178873991591851659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49502559452582661061234439 74253839178873991591851659)
      ·
        refine ⟨111380758768310987387777489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74253839178873991591851659 111380758768310987387777489)
        ·
          refine ⟨83535569076233240540833117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111380758768310987387777489 83535569076233240540833117)
          ·
            refine ⟨31325838403587465202812419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83535569076233240540833117 31325838403587465202812419)
            ·
              refine ⟨46988757605381197804218629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31325838403587465202812419 46988757605381197804218629)
              ·
                refine ⟨8810392051008974588290993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46988757605381197804218629 8810392051008974588290993)
                ·
                  refine ⟨6607794038256730941218245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8810392051008974588290993 6607794038256730941218245)
                  ·
                    refine ⟨1238961382173137051478421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6607794038256730941218245 1238961382173137051478421)
                    ·
                      rfl

theorem cell23_7238606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_7238606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238606 prefixEnd_7238606 := by exact prefixLift 7238606
  have htrace : WordTrace (prefixWord ++ tailWord_7238606) baseStart_7238606 baseEnd_7238606 := by
    simpa [prefixWord, tailWord_7238606, baseEnd_7238606] using wordTrace_append hprefix tailTrace_7238606
  have hstable : (prefixWord ++ tailWord_7238606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238606).length < 2 ^ (prefixWord ++ tailWord_7238606).sum := by decide
  have hdescent : baseEnd_7238606 < baseStart_7238606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238674 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7238674 : Nat := 118140960795 + 7238674 * 2 ^ 59
def prefixEnd_7238674 : Nat := 4983230072969 + 3 ^ 40 * 7238674 * 2
def baseEnd_7238674 : Nat := 1238973021067972296128317

theorem tailTrace_7238674 : CollatzResearch.WordTrace tailWord_7238674 prefixEnd_7238674 1238973021067972296128317 := by
  unfold tailWord_7238674
  simp only [CollatzResearch.WordTrace]
  refine ⟨66004032644381959985014769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176010753718351893293372717 66004032644381959985014769)
  ·
    refine ⟨49503024483286469988761077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66004032644381959985014769 49503024483286469988761077)
    ·
      refine ⟨4640908545308106561446351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49503024483286469988761077 4640908545308106561446351)
      ·
        refine ⟨6961362817962159842169527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4640908545308106561446351 6961362817962159842169527)
        ·
          refine ⟨10442044226943239763254291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6961362817962159842169527 10442044226943239763254291)
          ·
            refine ⟨15663066340414859644881437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10442044226943239763254291 15663066340414859644881437)
            ·
              refine ⟨5873649877655572366830539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15663066340414859644881437 5873649877655572366830539)
              ·
                refine ⟨8810474816483358550245809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873649877655572366830539 8810474816483358550245809)
                ·
                  refine ⟨6607856112362518912684357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8810474816483358550245809 6607856112362518912684357)
                  ·
                    refine ⟨1238973021067972296128317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6607856112362518912684357 1238973021067972296128317)
                    ·
                      rfl

theorem cell23_7238674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7238674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238674 prefixEnd_7238674 := by exact prefixLift 7238674
  have htrace : WordTrace (prefixWord ++ tailWord_7238674) baseStart_7238674 baseEnd_7238674 := by
    simpa [prefixWord, tailWord_7238674, baseEnd_7238674] using wordTrace_append hprefix tailTrace_7238674
  have hstable : (prefixWord ++ tailWord_7238674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238674).length < 2 ^ (prefixWord ++ tailWord_7238674).sum := by decide
  have hdescent : baseEnd_7238674 < baseStart_7238674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238680 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 2, 1, 3]
def baseStart_7238680 : Nat := 118140960795 + 7238680 * 2 ^ 59
def prefixEnd_7238680 : Nat := 4983230072969 + 3 ^ 40 * 7238680 * 2
def baseEnd_7238680 : Nat := 3716922144087843864909923

theorem tailTrace_7238680 : CollatzResearch.WordTrace tailWord_7238680 prefixEnd_7238680 3716922144087843864909923 := by
  unfold tailWord_7238680
  simp only [CollatzResearch.WordTrace]
  refine ⟨132008174707753051482388747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176010899610337401976518329 132008174707753051482388747)
  ·
    refine ⟨198012262061629577223583121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132008174707753051482388747 198012262061629577223583121)
    ·
      refine ⟨148509196546222182917687341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198012262061629577223583121 148509196546222182917687341)
      ·
        refine ⟨55690948704833318594132753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148509196546222182917687341 55690948704833318594132753)
        ·
          refine ⟨41768211528624988945599565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55690948704833318594132753 41768211528624988945599565)
          ·
            refine ⟨15663079323234370854599837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41768211528624988945599565 15663079323234370854599837)
            ·
              refine ⟨5873654746212889070474939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15663079323234370854599837 5873654746212889070474939)
              ·
                refine ⟨8810482119319333605712409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873654746212889070474939 8810482119319333605712409)
                ·
                  refine ⟨6607861589489500204284307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8810482119319333605712409 6607861589489500204284307)
                  ·
                    refine ⟨9911792384234250306426461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6607861589489500204284307 9911792384234250306426461)
                    ·
                      refine ⟨3716922144087843864909923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9911792384234250306426461 3716922144087843864909923)
                      ·
                        rfl

theorem cell23_7238680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_7238680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238680 prefixEnd_7238680 := by exact prefixLift 7238680
  have htrace : WordTrace (prefixWord ++ tailWord_7238680) baseStart_7238680 baseEnd_7238680 := by
    simpa [prefixWord, tailWord_7238680, baseEnd_7238680] using wordTrace_append hprefix tailTrace_7238680
  have hstable : (prefixWord ++ tailWord_7238680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238680).length < 2 ^ (prefixWord ++ tailWord_7238680).sum := by decide
  have hdescent : baseEnd_7238680 < baseStart_7238680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238690 : List Nat := [3, 3, 1, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_7238690 : Nat := 118140960795 + 7238690 * 2 ^ 59
def prefixEnd_7238690 : Nat := 4983230072969 + 3 ^ 40 * 7238690 * 2
def baseEnd_7238690 : Nat := 3716927278894388825784877

theorem tailTrace_7238690 : CollatzResearch.WordTrace tailWord_7238690 prefixEnd_7238690 3716927278894388825784877 := by
  unfold tailWord_7238690
  simp only [CollatzResearch.WordTrace]
  refine ⟨66004178536367468668160381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176011142763646583115094349 66004178536367468668160381)
  ·
    refine ⟨24751566951137800750560143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66004178536367468668160381 24751566951137800750560143)
    ·
      refine ⟨37127350426706701125840215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24751566951137800750560143 37127350426706701125840215)
      ·
        refine ⟨55691025640060051688760323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37127350426706701125840215 55691025640060051688760323)
        ·
          refine ⟨83536538460090077533140485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55691025640060051688760323 83536538460090077533140485)
          ·
            refine ⟨15663100961266889537463841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83536538460090077533140485 15663100961266889537463841)
            ·
              refine ⟨11747325720950167153097881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15663100961266889537463841 11747325720950167153097881)
              ·
                refine ⟨8810494290712625364823411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11747325720950167153097881 8810494290712625364823411)
                ·
                  refine ⟨13215741436068938047235117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8810494290712625364823411 13215741436068938047235117)
                  ·
                    refine ⟨4955903038525851767713169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13215741436068938047235117 4955903038525851767713169)
                    ·
                      refine ⟨3716927278894388825784877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955903038525851767713169 3716927278894388825784877)
                      ·
                        rfl

theorem cell23_7238690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_7238690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238690 prefixEnd_7238690 := by exact prefixLift 7238690
  have htrace : WordTrace (prefixWord ++ tailWord_7238690) baseStart_7238690 baseEnd_7238690 := by
    simpa [prefixWord, tailWord_7238690, baseEnd_7238690] using wordTrace_append hprefix tailTrace_7238690
  have hstable : (prefixWord ++ tailWord_7238690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238690).length < 2 ^ (prefixWord ++ tailWord_7238690).sum := by decide
  have hdescent : baseEnd_7238690 < baseStart_7238690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238746 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2]
def baseStart_7238746 : Nat := 118140960795 + 7238746 * 2 ^ 59
def prefixEnd_7238746 : Nat := 4983230072969 + 3 ^ 40 * 7238746 * 2
def baseEnd_7238746 : Nat := 3716956033811040606684619

theorem tailTrace_7238746 : CollatzResearch.WordTrace tailWord_7238746 prefixEnd_7238746 3716956033811040606684619 := by
  unfold tailWord_7238746
  simp only [CollatzResearch.WordTrace]
  refine ⟨66004689158316749059170023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176012504422177997491120061 66004689158316749059170023)
  ·
    refine ⟨99007033737475123588755035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66004689158316749059170023 99007033737475123588755035)
    ·
      refine ⟨148510550606212685383132553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99007033737475123588755035 148510550606212685383132553)
      ·
        refine ⟨111382912954659514037349415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148510550606212685383132553 111382912954659514037349415)
        ·
          refine ⟨167074369431989271056024123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111382912954659514037349415 167074369431989271056024123)
          ·
            refine ⟨250611554147983906584036185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167074369431989271056024123 250611554147983906584036185)
            ·
              refine ⟨187958665610987929938027139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250611554147983906584036185 187958665610987929938027139)
              ·
                refine ⟨281937998416481894907040709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187958665610987929938027139 281937998416481894907040709)
                ·
                  refine ⟨52863374703090355295070133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281937998416481894907040709 52863374703090355295070133)
                  ·
                    refine ⟨4955941378414720808912825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52863374703090355295070133 4955941378414720808912825)
                    ·
                      refine ⟨3716956033811040606684619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955941378414720808912825 3716956033811040606684619)
                      ·
                        rfl

theorem cell23_7238746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_7238746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238746 prefixEnd_7238746 := by exact prefixLift 7238746
  have htrace : WordTrace (prefixWord ++ tailWord_7238746) baseStart_7238746 baseEnd_7238746 := by
    simpa [prefixWord, tailWord_7238746, baseEnd_7238746] using wordTrace_append hprefix tailTrace_7238746
  have hstable : (prefixWord ++ tailWord_7238746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238746).length < 2 ^ (prefixWord ++ tailWord_7238746).sum := by decide
  have hdescent : baseEnd_7238746 < baseStart_7238746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238766 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_7238766 : Nat := 118140960795 + 7238766 * 2 ^ 59
def prefixEnd_7238766 : Nat := 4983230072969 + 3 ^ 40 * 7238766 * 2
def baseEnd_7238766 : Nat := 3716966303424130528434527

theorem tailTrace_7238766 : CollatzResearch.WordTrace tailWord_7238766 prefixEnd_7238766 3716966303424130528434527 := by
  unfold tailWord_7238766
  simp only [CollatzResearch.WordTrace]
  refine ⟨33002435761649317456551019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176012990728796359768272101 33002435761649317456551019)
  ·
    refine ⟨49503653642473976184826529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33002435761649317456551019 49503653642473976184826529)
    ·
      refine ⟨37127740231855482138619897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49503653642473976184826529 37127740231855482138619897)
      ·
        refine ⟨27845805173891611603964923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37127740231855482138619897 27845805173891611603964923)
        ·
          refine ⟨41768707760837417405947385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27845805173891611603964923 41768707760837417405947385)
          ·
            refine ⟨31326530820628063054460539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41768707760837417405947385 31326530820628063054460539)
            ·
              refine ⟨46989796230942094581690809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31326530820628063054460539 46989796230942094581690809)
              ·
                refine ⟨35242347173206570936268107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46989796230942094581690809 35242347173206570936268107)
                ·
                  refine ⟨52863520759809856404402161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35242347173206570936268107 52863520759809856404402161)
                  ·
                    refine ⟨39647640569857392303301621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52863520759809856404402161 39647640569857392303301621)
                    ·
                      refine ⟨3716966303424130528434527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39647640569857392303301621 3716966303424130528434527)
                      ·
                        rfl

theorem cell23_7238766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_7238766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238766 prefixEnd_7238766 := by exact prefixLift 7238766
  have htrace : WordTrace (prefixWord ++ tailWord_7238766) baseStart_7238766 baseEnd_7238766 := by
    simpa [prefixWord, tailWord_7238766, baseEnd_7238766] using wordTrace_append hprefix tailTrace_7238766
  have hstable : (prefixWord ++ tailWord_7238766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238766).length < 2 ^ (prefixWord ++ tailWord_7238766).sum := by decide
  have hdescent : baseEnd_7238766 < baseStart_7238766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238776 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 2, 1, 4]
def baseStart_7238776 : Nat := 118140960795 + 7238776 * 2 ^ 59
def prefixEnd_7238776 : Nat := 4983230072969 + 3 ^ 40 * 7238776 * 2
def baseEnd_7238776 : Nat := 3716971438230675489309481

theorem tailTrace_7238776 : CollatzResearch.WordTrace tailWord_7238776 prefixEnd_7238776 3716971438230675489309481 := by
  unfold tailWord_7238776
  simp only [CollatzResearch.WordTrace]
  refine ⟨132009925411579155680136091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176013233882105540906848121 132009925411579155680136091)
  ·
    refine ⟨198014888117368733520204137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132009925411579155680136091 198014888117368733520204137)
    ·
      refine ⟨148511166088026550140153103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198014888117368733520204137 148511166088026550140153103)
      ·
        refine ⟨222766749132039825210229655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148511166088026550140153103 222766749132039825210229655)
        ·
          refine ⟨334150123698059737815344483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222766749132039825210229655 334150123698059737815344483)
          ·
            refine ⟨501225185547089606723016725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334150123698059737815344483 501225185547089606723016725)
            ·
              refine ⟨23494930572519825315141409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 501225185547089606723016725 23494930572519825315141409)
              ·
                refine ⟨17621197929389868986356057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23494930572519825315141409 17621197929389868986356057)
                ·
                  refine ⟨13215898447042401739767043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17621197929389868986356057 13215898447042401739767043)
                  ·
                    refine ⟨19823847670563602609650565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13215898447042401739767043 19823847670563602609650565)
                    ·
                      refine ⟨3716971438230675489309481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19823847670563602609650565 3716971438230675489309481)
                      ·
                        rfl

theorem cell23_7238776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_7238776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238776 prefixEnd_7238776 := by exact prefixLift 7238776
  have htrace : WordTrace (prefixWord ++ tailWord_7238776) baseStart_7238776 baseEnd_7238776 := by
    simpa [prefixWord, tailWord_7238776, baseEnd_7238776] using wordTrace_append hprefix tailTrace_7238776
  have hstable : (prefixWord ++ tailWord_7238776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238776).length < 2 ^ (prefixWord ++ tailWord_7238776).sum := by decide
  have hdescent : baseEnd_7238776 < baseStart_7238776 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238777 : List Nat := [1, 2, 1, 3, 6, 1, 2, 2, 5]
def baseStart_7238777 : Nat := 118140960795 + 7238777 * 2 ^ 59
def prefixEnd_7238777 : Nat := 4983230072969 + 3 ^ 40 * 7238777 * 2
def baseEnd_7238777 : Nat := 412996883523481109488553

theorem tailTrace_7238777 : CollatzResearch.WordTrace tailWord_7238777 prefixEnd_7238777 412996883523481109488553 := by
  unfold tailWord_7238777
  simp only [CollatzResearch.WordTrace]
  refine ⟨264019887296154688531058585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176013258197436459020705723 264019887296154688531058585)
  ·
    refine ⟨198014915472116016398293939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264019887296154688531058585 198014915472116016398293939)
    ·
      refine ⟨297022373208174024597440909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198014915472116016398293939 297022373208174024597440909)
      ·
        refine ⟨111383389953065259224040341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297022373208174024597440909 111383389953065259224040341)
        ·
          refine ⟨5221096404049934026126891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111383389953065259224040341 5221096404049934026126891)
          ·
            refine ⟨7831644606074901039190337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221096404049934026126891 7831644606074901039190337)
            ·
              refine ⟨5873733454556175779392753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7831644606074901039190337 5873733454556175779392753)
              ·
                refine ⟨4405300090917131834544565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5873733454556175779392753 4405300090917131834544565)
                ·
                  refine ⟨412996883523481109488553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4405300090917131834544565 412996883523481109488553)
                  ·
                    rfl

theorem cell23_7238777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 5].length) (baseStart_7238777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238777 prefixEnd_7238777 := by exact prefixLift 7238777
  have htrace : WordTrace (prefixWord ++ tailWord_7238777) baseStart_7238777 baseEnd_7238777 := by
    simpa [prefixWord, tailWord_7238777, baseEnd_7238777] using wordTrace_append hprefix tailTrace_7238777
  have hstable : (prefixWord ++ tailWord_7238777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238777).length < 2 ^ (prefixWord ++ tailWord_7238777).sum := by decide
  have hdescent : baseEnd_7238777 < baseStart_7238777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238793 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 2, 4, 2]
def baseStart_7238793 : Nat := 118140960795 + 7238793 * 2 ^ 59
def prefixEnd_7238793 : Nat := 4983230072969 + 3 ^ 40 * 7238793 * 2
def baseEnd_7238793 : Nat := 3716980167401801922796903

theorem tailTrace_7238793 : CollatzResearch.WordTrace tailWord_7238793 prefixEnd_7238793 3716980167401801922796903 := by
  unfold tailWord_7238793
  simp only [CollatzResearch.WordTrace]
  refine ⟨264020470864096723263641033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176013647242731148842427355 264020470864096723263641033)
  ·
    refine ⟨198015353148072542447730775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264020470864096723263641033 198015353148072542447730775)
    ·
      refine ⟨297023029722108813671596163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198015353148072542447730775 297023029722108813671596163)
      ·
        refine ⟨445534544583163220507394245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297023029722108813671596163 445534544583163220507394245)
        ·
          refine ⟨83537727109343103845136421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445534544583163220507394245 83537727109343103845136421)
          ·
            refine ⟨15663323833001831970963079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83537727109343103845136421 15663323833001831970963079)
            ·
              refine ⟨23494985749502747956444619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15663323833001831970963079 23494985749502747956444619)
              ·
                refine ⟨35242478624254121934666929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23494985749502747956444619 35242478624254121934666929)
                ·
                  refine ⟨26431858968190591451000197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35242478624254121934666929 26431858968190591451000197)
                  ·
                    refine ⟨4955973556535735897062537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26431858968190591451000197 4955973556535735897062537)
                    ·
                      refine ⟨3716980167401801922796903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4955973556535735897062537 3716980167401801922796903)
                      ·
                        rfl

theorem cell23_7238793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 4, 2].length) (baseStart_7238793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238793 prefixEnd_7238793 := by exact prefixLift 7238793
  have htrace : WordTrace (prefixWord ++ tailWord_7238793) baseStart_7238793 baseEnd_7238793 := by
    simpa [prefixWord, tailWord_7238793, baseEnd_7238793] using wordTrace_append hprefix tailTrace_7238793
  have hstable : (prefixWord ++ tailWord_7238793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238793).length < 2 ^ (prefixWord ++ tailWord_7238793).sum := by decide
  have hdescent : baseEnd_7238793 < baseStart_7238793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238796 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 4, 2, 3]
def baseStart_7238796 : Nat := 118140960795 + 7238796 * 2 ^ 59
def prefixEnd_7238796 : Nat := 4983230072969 + 3 ^ 40 * 7238796 * 2
def baseEnd_7238796 : Nat := 3716981707843765411059389

theorem tailTrace_7238796 : CollatzResearch.WordTrace tailWord_7238796 prefixEnd_7238796 3716981707843765411059389 := by
  unfold tailWord_7238796
  simp only [CollatzResearch.WordTrace]
  refine ⟨132010290141542927388000121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176013720188723903184000161 132010290141542927388000121)
  ·
    refine ⟨99007717606157195541000091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132010290141542927388000121 99007717606157195541000091)
    ·
      refine ⟨148511576409235793311500137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99007717606157195541000091 148511576409235793311500137)
      ·
        refine ⟨111383682306926844983625103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148511576409235793311500137 111383682306926844983625103)
        ·
          refine ⟨167075523460390267475437655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111383682306926844983625103 167075523460390267475437655)
          ·
            refine ⟨250613285190585401213156483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167075523460390267475437655 250613285190585401213156483)
            ·
              refine ⟨375919927785878101819734725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250613285190585401213156483 375919927785878101819734725)
              ·
                refine ⟨70484986459852144091200261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 375919927785878101819734725 70484986459852144091200261)
                ·
                  refine ⟨13215934961222277017100049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70484986459852144091200261 13215934961222277017100049)
                  ·
                    refine ⟨9911951220916707762825037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13215934961222277017100049 9911951220916707762825037)
                    ·
                      refine ⟨3716981707843765411059389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9911951220916707762825037 3716981707843765411059389)
                      ·
                        rfl

theorem cell23_7238796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_7238796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238796 prefixEnd_7238796 := by exact prefixLift 7238796
  have htrace : WordTrace (prefixWord ++ tailWord_7238796) baseStart_7238796 baseEnd_7238796 := by
    simpa [prefixWord, tailWord_7238796, baseEnd_7238796] using wordTrace_append hprefix tailTrace_7238796
  have hstable : (prefixWord ++ tailWord_7238796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238796).length < 2 ^ (prefixWord ++ tailWord_7238796).sum := by decide
  have hdescent : baseEnd_7238796 < baseStart_7238796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238810 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4]
def baseStart_7238810 : Nat := 118140960795 + 7238810 * 2 ^ 59
def prefixEnd_7238810 : Nat := 4983230072969 + 3 ^ 40 * 7238810 * 2
def baseEnd_7238810 : Nat := 3716988896572928356284325

theorem tailTrace_7238810 : CollatzResearch.WordTrace tailWord_7238810 prefixEnd_7238810 3716988896572928356284325 := by
  unfold tailWord_7238810
  simp only [CollatzResearch.WordTrace]
  refine ⟨66005272726258783791752471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176014060603356756778006589 66005272726258783791752471)
  ·
    refine ⟨99007909089388175687628707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66005272726258783791752471 99007909089388175687628707)
    ·
      refine ⟨148511863634082263531443061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99007909089388175687628707 148511863634082263531443061)
      ·
        refine ⟨13922987215695212206072787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148511863634082263531443061 13922987215695212206072787)
        ·
          refine ⟨20884480823542818309109181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13922987215695212206072787 20884480823542818309109181)
          ·
            refine ⟨7831680308828556865915943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20884480823542818309109181 7831680308828556865915943)
            ·
              refine ⟨11747520463242835298873915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831680308828556865915943 11747520463242835298873915)
              ·
                refine ⟨17621280694864252948310873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11747520463242835298873915 17621280694864252948310873)
                ·
                  refine ⟨13215960521148189711233155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17621280694864252948310873 13215960521148189711233155)
                  ·
                    refine ⟨19823940781722284566849733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13215960521148189711233155 19823940781722284566849733)
                    ·
                      refine ⟨3716988896572928356284325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19823940781722284566849733 3716988896572928356284325)
                      ·
                        rfl

theorem cell23_7238810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_7238810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238810 prefixEnd_7238810 := by exact prefixLift 7238810
  have htrace : WordTrace (prefixWord ++ tailWord_7238810) baseStart_7238810 baseEnd_7238810 := by
    simpa [prefixWord, tailWord_7238810, baseEnd_7238810] using wordTrace_append hprefix tailTrace_7238810
  have hstable : (prefixWord ++ tailWord_7238810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238810).length < 2 ^ (prefixWord ++ tailWord_7238810).sum := by decide
  have hdescent : baseEnd_7238810 < baseStart_7238810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238819 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 6]
def baseStart_7238819 : Nat := 118140960795 + 7238819 * 2 ^ 59
def prefixEnd_7238819 : Nat := 4983230072969 + 3 ^ 40 * 7238819 * 2
def baseEnd_7238819 : Nat := 3716993517898818821071783

theorem tailTrace_7238819 : CollatzResearch.WordTrace tailWord_7238819 prefixEnd_7238819 3716993517898818821071783 := by
  unfold tailWord_7238819
  simp only [CollatzResearch.WordTrace]
  refine ⟨264021419162002529704087511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176014279441335019802725007 264021419162002529704087511)
  ·
    refine ⟨396032128743003794556131267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264021419162002529704087511 396032128743003794556131267)
    ·
      refine ⟨594048193114505691834196901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396032128743003794556131267 594048193114505691834196901)
      ·
        refine ⟨111384036208969817218911919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 594048193114505691834196901 111384036208969817218911919)
        ·
          refine ⟨167076054313454725828367879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111384036208969817218911919 167076054313454725828367879)
          ·
            refine ⟨250614081470182088742551819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167076054313454725828367879 250614081470182088742551819)
            ·
              refine ⟨375921122205273133113827729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250614081470182088742551819 375921122205273133113827729)
              ·
                refine ⟨281940841653954849835370797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375921122205273133113827729 281940841653954849835370797)
                ·
                  refine ⟨105727815620233068688264049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 281940841653954849835370797 105727815620233068688264049)
                  ·
                    refine ⟨79295861715174801516198037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 105727815620233068688264049 79295861715174801516198037)
                    ·
                      refine ⟨3716993517898818821071783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79295861715174801516198037 3716993517898818821071783)
                      ·
                        rfl

theorem cell23_7238819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_7238819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238819 prefixEnd_7238819 := by exact prefixLift 7238819
  have htrace : WordTrace (prefixWord ++ tailWord_7238819) baseStart_7238819 baseEnd_7238819 := by
    simpa [prefixWord, tailWord_7238819, baseEnd_7238819] using wordTrace_append hprefix tailTrace_7238819
  have hstable : (prefixWord ++ tailWord_7238819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238819).length < 2 ^ (prefixWord ++ tailWord_7238819).sum := by decide
  have hdescent : baseEnd_7238819 < baseStart_7238819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238820 : List Nat := [2, 3, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_7238820 : Nat := 118140960795 + 7238820 * 2 ^ 59
def prefixEnd_7238820 : Nat := 4983230072969 + 3 ^ 40 * 7238820 * 2
def baseEnd_7238820 : Nat := 1238998010459824439053093

theorem tailTrace_7238820 : CollatzResearch.WordTrace tailWord_7238820 prefixEnd_7238820 1238998010459824439053093 := by
  unfold tailWord_7238820
  simp only [CollatzResearch.WordTrace]
  refine ⟨132010727817499453437436957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176014303756665937916582609 132010727817499453437436957)
  ·
    refine ⟨49504022931562295039038859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132010727817499453437436957 49504022931562295039038859)
    ·
      refine ⟨74256034397343442558558289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49504022931562295039038859 74256034397343442558558289)
      ·
        refine ⟨55692025798007581918918717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74256034397343442558558289 55692025798007581918918717)
        ·
          refine ⟨20884509674252843219594519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55692025798007581918918717 20884509674252843219594519)
          ·
            refine ⟨31326764511379264829391779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20884509674252843219594519 31326764511379264829391779)
            ·
              refine ⟨46990146767068897244087669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31326764511379264829391779 46990146767068897244087669)
              ·
                refine ⟨4405326259412709116633219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46990146767068897244087669 4405326259412709116633219)
                ·
                  refine ⟨6607989389119063674949829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405326259412709116633219 6607989389119063674949829)
                  ·
                    refine ⟨1238998010459824439053093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6607989389119063674949829 1238998010459824439053093)
                    ·
                      rfl

theorem cell23_7238820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_7238820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238820 prefixEnd_7238820 := by exact prefixLift 7238820
  have htrace : WordTrace (prefixWord ++ tailWord_7238820) baseStart_7238820 baseEnd_7238820 := by
    simpa [prefixWord, tailWord_7238820, baseEnd_7238820] using wordTrace_append hprefix tailTrace_7238820
  have hstable : (prefixWord ++ tailWord_7238820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238820).length < 2 ^ (prefixWord ++ tailWord_7238820).sum := by decide
  have hdescent : baseEnd_7238820 < baseStart_7238820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238833 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 6]
def baseStart_7238833 : Nat := 118140960795 + 7238833 * 2 ^ 59
def prefixEnd_7238833 : Nat := 4983230072969 + 3 ^ 40 * 7238833 * 2
def baseEnd_7238833 : Nat := 413000078514220196255191

theorem tailTrace_7238833 : CollatzResearch.WordTrace tailWord_7238833 prefixEnd_7238833 413000078514220196255191 := by
  unfold tailWord_7238833
  simp only [CollatzResearch.WordTrace]
  refine ⟨264021929783951810095097153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176014619855967873396731435 264021929783951810095097153)
  ·
    refine ⟨198016447337963857571322865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264021929783951810095097153 198016447337963857571322865)
    ·
      refine ⟨148512335503472893178492149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198016447337963857571322865 148512335503472893178492149)
      ·
        refine ⟨13923031453450583735483639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148512335503472893178492149 13923031453450583735483639)
        ·
          refine ⟨20884547180175875603225459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13923031453450583735483639 20884547180175875603225459)
          ·
            refine ⟨31326820770263813404838189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20884547180175875603225459 31326820770263813404838189)
            ·
              refine ⟨11747557788848930026814321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31326820770263813404838189 11747557788848930026814321)
              ·
                refine ⟨8810668341636697520110741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11747557788848930026814321 8810668341636697520110741)
                ·
                  refine ⟨413000078514220196255191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8810668341636697520110741 413000078514220196255191)
                  ·
                    rfl

theorem cell23_7238833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 6].length) (baseStart_7238833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238833 prefixEnd_7238833 := by exact prefixLift 7238833
  have htrace : WordTrace (prefixWord ++ tailWord_7238833) baseStart_7238833 baseEnd_7238833 := by
    simpa [prefixWord, tailWord_7238833, baseEnd_7238833] using wordTrace_append hprefix tailTrace_7238833
  have hstable : (prefixWord ++ tailWord_7238833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238833).length < 2 ^ (prefixWord ++ tailWord_7238833).sum := by decide
  have hdescent : baseEnd_7238833 < baseStart_7238833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238887 : List Nat := [1, 1, 5, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_7238887 : Nat := 118140960795 + 7238887 * 2 ^ 59
def prefixEnd_7238887 : Nat := 4983230072969 + 3 ^ 40 * 7238887 * 2
def baseEnd_7238887 : Nat := 3717028434583324555021471

theorem tailTrace_7238887 : CollatzResearch.WordTrace tailWord_7238887 prefixEnd_7238887 3717028434583324555021471 := by
  unfold tailWord_7238887
  simp only [CollatzResearch.WordTrace]
  refine ⟨264023899325756177317562915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176015932883837451545041943 264023899325756177317562915)
  ·
    refine ⟨396035848988634265976344373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264023899325756177317562915 396035848988634265976344373)
    ·
      refine ⟨37128360842684462435282285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 396035848988634265976344373 37128360842684462435282285)
      ·
        refine ⟨13923135316006673413230857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37128360842684462435282285 13923135316006673413230857)
        ·
          refine ⟨10442351487005005059923143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13923135316006673413230857 10442351487005005059923143)
          ·
            refine ⟨15663527230507507589884715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10442351487005005059923143 15663527230507507589884715)
            ·
              refine ⟨23495290845761261384827073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15663527230507507589884715 23495290845761261384827073)
              ·
                refine ⟨17621468134320946038620305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23495290845761261384827073 17621468134320946038620305)
                ·
                  refine ⟨13216101100740709528965229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17621468134320946038620305 13216101100740709528965229)
                  ·
                    refine ⟨4956037912777766073361961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13216101100740709528965229 4956037912777766073361961)
                    ·
                      refine ⟨3717028434583324555021471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956037912777766073361961 3717028434583324555021471)
                      ·
                        rfl

theorem cell23_7238887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_7238887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238887 prefixEnd_7238887 := by exact prefixLift 7238887
  have htrace : WordTrace (prefixWord ++ tailWord_7238887) baseStart_7238887 baseEnd_7238887 := by
    simpa [prefixWord, tailWord_7238887, baseEnd_7238887] using wordTrace_append hprefix tailTrace_7238887
  have hstable : (prefixWord ++ tailWord_7238887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238887).length < 2 ^ (prefixWord ++ tailWord_7238887).sum := by decide
  have hdescent : baseEnd_7238887 < baseStart_7238887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238906 : List Nat := [3, 1, 1, 1, 1, 4, 4, 8]
def baseStart_7238906 : Nat := 118140960795 + 7238906 * 2 ^ 59
def prefixEnd_7238906 : Nat := 4983230072969 + 3 ^ 40 * 7238906 * 2
def baseEnd_7238906 : Nat := 137668081137620740025329

theorem tailTrace_7238906 : CollatzResearch.WordTrace tailWord_7238906 prefixEnd_7238906 137668081137620740025329 := by
  unfold tailWord_7238906
  simp only [CollatzResearch.WordTrace]
  refine ⟨66006148078171835890626143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176016394875124895708336381 66006148078171835890626143)
  ·
    refine ⟨99009222117257753835939215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66006148078171835890626143 99009222117257753835939215)
    ·
      refine ⟨148513833175886630753908823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99009222117257753835939215 148513833175886630753908823)
      ·
        refine ⟨222770749763829946130863235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148513833175886630753908823 222770749763829946130863235)
        ·
          refine ⟨334156124645744919196294853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222770749763829946130863235 334156124645744919196294853)
          ·
            refine ⟨62654273371077172349305285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334156124645744919196294853 62654273371077172349305285)
            ·
              refine ⟨11747676257076969815494741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62654273371077172349305285 11747676257076969815494741)
              ·
                refine ⟨137668081137620740025329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11747676257076969815494741 137668081137620740025329)
                ·
                  rfl

theorem cell23_7238906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 8].length) (baseStart_7238906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238906 prefixEnd_7238906 := by exact prefixLift 7238906
  have htrace : WordTrace (prefixWord ++ tailWord_7238906) baseStart_7238906 baseEnd_7238906 := by
    simpa [prefixWord, tailWord_7238906, baseEnd_7238906] using wordTrace_append hprefix tailTrace_7238906
  have hstable : (prefixWord ++ tailWord_7238906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238906).length < 2 ^ (prefixWord ++ tailWord_7238906).sum := by decide
  have hdescent : baseEnd_7238906 < baseStart_7238906 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238914 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_7238914 : Nat := 118140960795 + 7238914 * 2 ^ 59
def prefixEnd_7238914 : Nat := 4983230072969 + 3 ^ 40 * 7238914 * 2
def baseEnd_7238914 : Nat := 1239014099520331983127949

theorem tailTrace_7238914 : CollatzResearch.WordTrace tailWord_7238914 prefixEnd_7238914 1239014099520331983127949 := by
  unfold tailWord_7238914
  simp only [CollatzResearch.WordTrace]
  refine ⟨66006221024164590232198949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176016589397772240619197197 66006221024164590232198949)
  ·
    refine ⟨12376166442030860668537303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66006221024164590232198949 12376166442030860668537303)
    ·
      refine ⟨18564249663046291002805955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12376166442030860668537303 18564249663046291002805955)
      ·
        refine ⟨27846374494569436504208933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18564249663046291002805955 27846374494569436504208933)
        ·
          refine ⟨5221195217731769344539175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27846374494569436504208933 5221195217731769344539175)
          ·
            refine ⟨7831792826597654016808763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221195217731769344539175 7831792826597654016808763)
            ·
              refine ⟨11747689239896481025213145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831792826597654016808763 11747689239896481025213145)
              ·
                refine ⟨8810766929922360768909859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11747689239896481025213145 8810766929922360768909859)
                ·
                  refine ⟨13216150394883541153364789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8810766929922360768909859 13216150394883541153364789)
                  ·
                    refine ⟨1239014099520331983127949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13216150394883541153364789 1239014099520331983127949)
                    ·
                      rfl

theorem cell23_7238914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_7238914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238914 prefixEnd_7238914 := by exact prefixLift 7238914
  have htrace : WordTrace (prefixWord ++ tailWord_7238914) baseStart_7238914 baseEnd_7238914 := by
    simpa [prefixWord, tailWord_7238914, baseEnd_7238914] using wordTrace_append hprefix tailTrace_7238914
  have hstable : (prefixWord ++ tailWord_7238914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238914).length < 2 ^ (prefixWord ++ tailWord_7238914).sum := by decide
  have hdescent : baseEnd_7238914 < baseStart_7238914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238920 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 3, 2, 3]
def baseStart_7238920 : Nat := 118140960795 + 7238920 * 2 ^ 59
def prefixEnd_7238920 : Nat := 4983230072969 + 3 ^ 40 * 7238920 * 2
def baseEnd_7238920 : Nat := 3717045379444922925908819

theorem tailTrace_7238920 : CollatzResearch.WordTrace tailWord_7238920 prefixEnd_7238920 3717045379444922925908819 := by
  unfold tailWord_7238920
  simp only [CollatzResearch.WordTrace]
  refine ⟨132012551467318311976757107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176016735289757749302342809 132012551467318311976757107)
  ·
    refine ⟨198018827200977467965135661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132012551467318311976757107 198018827200977467965135661)
    ·
      refine ⟨74257060200366550486925873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198018827200977467965135661 74257060200366550486925873)
      ·
        refine ⟨55692795150274912865194405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74257060200366550486925873 55692795150274912865194405)
        ·
          refine ⟨10442399090676546162223951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55692795150274912865194405 10442399090676546162223951)
          ·
            refine ⟨15663598636014819243335927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10442399090676546162223951 15663598636014819243335927)
            ·
              refine ⟨23495397954022228865003891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15663598636014819243335927 23495397954022228865003891)
              ·
                refine ⟨35243096931033343297505837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23495397954022228865003891 35243096931033343297505837)
                ·
                  refine ⟨13216161349137503736564689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35243096931033343297505837 13216161349137503736564689)
                  ·
                    refine ⟨9912121011853127802423517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13216161349137503736564689 9912121011853127802423517)
                    ·
                      refine ⟨3717045379444922925908819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9912121011853127802423517 3717045379444922925908819)
                      ·
                        rfl

theorem cell23_7238920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_7238920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238920 prefixEnd_7238920 := by exact prefixLift 7238920
  have htrace : WordTrace (prefixWord ++ tailWord_7238920) baseStart_7238920 baseEnd_7238920 := by
    simpa [prefixWord, tailWord_7238920, baseEnd_7238920] using wordTrace_append hprefix tailTrace_7238920
  have hstable : (prefixWord ++ tailWord_7238920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238920).length < 2 ^ (prefixWord ++ tailWord_7238920).sum := by decide
  have hdescent : baseEnd_7238920 < baseStart_7238920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238977 : List Nat := [1, 2, 5, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7238977 : Nat := 118140960795 + 7238977 * 2 ^ 59
def prefixEnd_7238977 : Nat := 4983230072969 + 3 ^ 40 * 7238977 * 2
def baseEnd_7238977 : Nat := 3717074647842229202896057

theorem tailTrace_7238977 : CollatzResearch.WordTrace tailWord_7238977 prefixEnd_7238977 3717074647842229202896057 := by
  unfold tailWord_7238977
  simp only [CollatzResearch.WordTrace]
  refine ⟨264027181895430122688339185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176018121263620081792226123 264027181895430122688339185)
  ·
    refine ⟨198020386421572592016254389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264027181895430122688339185 198020386421572592016254389)
    ·
      refine ⟨18564411227022430501523849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198020386421572592016254389 18564411227022430501523849)
      ·
        refine ⟨13923308420266822876142887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18564411227022430501523849 13923308420266822876142887)
        ·
          refine ⟨20884962630400234314214331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13923308420266822876142887 20884962630400234314214331)
          ·
            refine ⟨31327443945600351471321497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20884962630400234314214331 31327443945600351471321497)
            ·
              refine ⟨23495582959200263603491123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31327443945600351471321497 23495582959200263603491123)
              ·
                refine ⟨35243374438800395405236685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23495582959200263603491123 35243374438800395405236685)
                ·
                  refine ⟨13216265414550148276963757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35243374438800395405236685 13216265414550148276963757)
                  ·
                    refine ⟨4956099530456305603861409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13216265414550148276963757 4956099530456305603861409)
                    ·
                      refine ⟨3717074647842229202896057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956099530456305603861409 3717074647842229202896057)
                      ·
                        rfl

theorem cell23_7238977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7238977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238977 prefixEnd_7238977 := by exact prefixLift 7238977
  have htrace : WordTrace (prefixWord ++ tailWord_7238977) baseStart_7238977 baseEnd_7238977 := by
    simpa [prefixWord, tailWord_7238977, baseEnd_7238977] using wordTrace_append hprefix tailTrace_7238977
  have hstable : (prefixWord ++ tailWord_7238977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238977).length < 2 ^ (prefixWord ++ tailWord_7238977).sum := by decide
  have hdescent : baseEnd_7238977 < baseStart_7238977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7238990 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2]
def baseStart_7238990 : Nat := 118140960795 + 7238990 * 2 ^ 59
def prefixEnd_7238990 : Nat := 4983230072969 + 3 ^ 40 * 7238990 * 2
def baseEnd_7238990 : Nat := 3717081323090737652033497

theorem tailTrace_7238990 : CollatzResearch.WordTrace tailWord_7238990 prefixEnd_7238990 3717081323090737652033497 := by
  unfold tailWord_7238990
  simp only [CollatzResearch.WordTrace]
  refine ⟨33003457005547878238570303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176018437362922017272374949 33003457005547878238570303)
  ·
    refine ⟨49505185508321817357855455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33003457005547878238570303 49505185508321817357855455)
    ·
      refine ⟨74257778262482726036783183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49505185508321817357855455 74257778262482726036783183)
      ·
        refine ⟨111386667393724089055174775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74257778262482726036783183 111386667393724089055174775)
        ·
          refine ⟨167080001090586133582762163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111386667393724089055174775 167080001090586133582762163)
          ·
            refine ⟨250620001635879200374143245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167080001090586133582762163 250620001635879200374143245)
            ·
              refine ⟨93982500613454700140303717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250620001635879200374143245 93982500613454700140303717)
              ·
                refine ⟨17621718865022756276306947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93982500613454700140303717 17621718865022756276306947)
                ·
                  refine ⟨26432578297534134414460421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17621718865022756276306947 26432578297534134414460421)
                  ·
                    refine ⟨4956108430787650202711329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26432578297534134414460421 4956108430787650202711329)
                    ·
                      refine ⟨3717081323090737652033497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956108430787650202711329 3717081323090737652033497)
                      ·
                        rfl

theorem cell23_7238990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_7238990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7238990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7238990 prefixEnd_7238990 := by exact prefixLift 7238990
  have htrace : WordTrace (prefixWord ++ tailWord_7238990) baseStart_7238990 baseEnd_7238990 := by
    simpa [prefixWord, tailWord_7238990, baseEnd_7238990] using wordTrace_append hprefix tailTrace_7238990
  have hstable : (prefixWord ++ tailWord_7238990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7238990).length < 2 ^ (prefixWord ++ tailWord_7238990).sum := by decide
  have hdescent : baseEnd_7238990 < baseStart_7238990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7238990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239013 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 7]
def baseStart_7239013 : Nat := 118140960795 + 7239013 * 2 ^ 59
def prefixEnd_7239013 : Nat := 4983230072969 + 3 ^ 40 * 7239013 * 2
def baseEnd_7239013 : Nat := 413010348127310118005099

theorem tailTrace_7239013 : CollatzResearch.WordTrace tailWord_7239013 prefixEnd_7239013 413010348127310118005099 := by
  unfold tailWord_7239013
  simp only [CollatzResearch.WordTrace]
  refine ⟨264028494923299700836649693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176018996615533133891099795 264028494923299700836649693)
  ·
    refine ⟨99010685596237387813743635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264028494923299700836649693 99010685596237387813743635)
    ·
      refine ⟨148516028394356081720615453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99010685596237387813743635 148516028394356081720615453)
      ·
        refine ⟨55693510647883530645230795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148516028394356081720615453 55693510647883530645230795)
        ·
          refine ⟨83540265971825295967846193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55693510647883530645230795 83540265971825295967846193)
          ·
            refine ⟨62655199478868971975884645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83540265971825295967846193 62655199478868971975884645)
            ·
              refine ⟨11747849902287932245478371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62655199478868971975884645 11747849902287932245478371)
              ·
                refine ⟨17621774853431898368217557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11747849902287932245478371 17621774853431898368217557)
                ·
                  refine ⟨413010348127310118005099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17621774853431898368217557 413010348127310118005099)
                  ·
                    rfl

theorem cell23_7239013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_7239013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239013 prefixEnd_7239013 := by exact prefixLift 7239013
  have htrace : WordTrace (prefixWord ++ tailWord_7239013) baseStart_7239013 baseEnd_7239013 := by
    simpa [prefixWord, tailWord_7239013, baseEnd_7239013] using wordTrace_append hprefix tailTrace_7239013
  have hstable : (prefixWord ++ tailWord_7239013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239013).length < 2 ^ (prefixWord ++ tailWord_7239013).sum := by decide
  have hdescent : baseEnd_7239013 < baseStart_7239013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239023 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 3]
def baseStart_7239023 : Nat := 118140960795 + 7239023 * 2 ^ 59
def prefixEnd_7239023 : Nat := 4983230072969 + 3 ^ 40 * 7239023 * 2
def baseEnd_7239023 : Nat := 3717098267952336022920845

theorem tailTrace_7239023 : CollatzResearch.WordTrace tailWord_7239023 prefixEnd_7239023 3717098267952336022920845 := by
  unfold tailWord_7239023
  simp only [CollatzResearch.WordTrace]
  refine ⟨264028859653263472544513723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176019239768842315029675815 264028859653263472544513723)
  ·
    refine ⟨396043289479895208816770585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264028859653263472544513723 396043289479895208816770585)
    ·
      refine ⟨297032467109921406612577939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396043289479895208816770585 297032467109921406612577939)
      ·
        refine ⟨445548700664882109918866909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297032467109921406612577939 445548700664882109918866909)
        ·
          refine ⟨167080762749330791219575091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445548700664882109918866909 167080762749330791219575091)
          ·
            refine ⟨250621144123996186829362637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167080762749330791219575091 250621144123996186829362637)
            ·
              refine ⟨93982929046498570061010989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250621144123996186829362637 93982929046498570061010989)
              ·
                refine ⟨35243598392436963772879121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93982929046498570061010989 35243598392436963772879121)
                ·
                  refine ⟨26432698794327722829659341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35243598392436963772879121 26432698794327722829659341)
                  ·
                    refine ⟨9912262047872896061122253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26432698794327722829659341 9912262047872896061122253)
                    ·
                      refine ⟨3717098267952336022920845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9912262047872896061122253 3717098267952336022920845)
                      ·
                        rfl

theorem cell23_7239023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 3].length) (baseStart_7239023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239023 prefixEnd_7239023 := by exact prefixLift 7239023
  have htrace : WordTrace (prefixWord ++ tailWord_7239023) baseStart_7239023 baseEnd_7239023 := by
    simpa [prefixWord, tailWord_7239023, baseEnd_7239023] using wordTrace_append hprefix tailTrace_7239023
  have hstable : (prefixWord ++ tailWord_7239023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239023).length < 2 ^ (prefixWord ++ tailWord_7239023).sum := by decide
  have hdescent : baseEnd_7239023 < baseStart_7239023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239024 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 2, 2, 2]
def baseStart_7239024 : Nat := 118140960795 + 7239024 * 2 ^ 59
def prefixEnd_7239024 : Nat := 4983230072969 + 3 ^ 40 * 7239024 * 2
def baseEnd_7239024 : Nat := 3717098781432990519008341

theorem tailTrace_7239024 : CollatzResearch.WordTrace tailWord_7239024 prefixEnd_7239024 3717098781432990519008341 := by
  unfold tailWord_7239024
  simp only [CollatzResearch.WordTrace]
  refine ⟨132014448063129924857650063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176019264084173233143533417 132014448063129924857650063)
  ·
    refine ⟨198021672094694887286475095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132014448063129924857650063 198021672094694887286475095)
    ·
      refine ⟨297032508142042330929712643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198021672094694887286475095 297032508142042330929712643)
      ·
        refine ⟨445548762213063496394568965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297032508142042330929712643 445548762213063496394568965)
        ·
          refine ⟨83540392914949405573981681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445548762213063496394568965 83540392914949405573981681)
          ·
            refine ⟨62655294686212054180486261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83540392914949405573981681 62655294686212054180486261)
            ·
              refine ⟨5873933876832380079420587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62655294686212054180486261 5873933876832380079420587)
              ·
                refine ⟨8810900815248570119130881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5873933876832380079420587 8810900815248570119130881)
                ·
                  refine ⟨6608175611436427589348161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8810900815248570119130881 6608175611436427589348161)
                  ·
                    refine ⟨4956131708577320692011121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6608175611436427589348161 4956131708577320692011121)
                    ·
                      refine ⟨3717098781432990519008341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956131708577320692011121 3717098781432990519008341)
                      ·
                        rfl

theorem cell23_7239024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 2, 2, 2].length) (baseStart_7239024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239024 prefixEnd_7239024 := by exact prefixLift 7239024
  have htrace : WordTrace (prefixWord ++ tailWord_7239024) baseStart_7239024 baseEnd_7239024 := by
    simpa [prefixWord, tailWord_7239024, baseEnd_7239024] using wordTrace_append hprefix tailTrace_7239024
  have hstable : (prefixWord ++ tailWord_7239024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239024).length < 2 ^ (prefixWord ++ tailWord_7239024).sum := by decide
  have hdescent : baseEnd_7239024 < baseStart_7239024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239043 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 1, 7]
def baseStart_7239043 : Nat := 118140960795 + 7239043 * 2 ^ 59
def prefixEnd_7239043 : Nat := 4983230072969 + 3 ^ 40 * 7239043 * 2
def baseEnd_7239043 : Nat := 1239036179188475314890251

theorem tailTrace_7239043 : CollatzResearch.WordTrace tailWord_7239043 prefixEnd_7239043 1239036179188475314890251 := by
  unfold tailWord_7239043
  simp only [CollatzResearch.WordTrace]
  refine ⟨264029589113191015960241783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176019726075460677306827855 264029589113191015960241783)
  ·
    refine ⟨396044383669786523940362675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264029589113191015960241783 396044383669786523940362675)
    ·
      refine ⟨594066575504679785910544013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396044383669786523940362675 594066575504679785910544013)
      ·
        refine ⟨222774965814254919716454005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594066575504679785910544013 222774965814254919716454005)
        ·
          refine ⟨20885153045086398723417563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 222774965814254919716454005 20885153045086398723417563)
          ·
            refine ⟨31327729567629598085126345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20885153045086398723417563 31327729567629598085126345)
            ·
              refine ⟨23495797175722198563844759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31327729567629598085126345 23495797175722198563844759)
              ·
                refine ⟨35243695763583297845767139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23495797175722198563844759 35243695763583297845767139)
                ·
                  refine ⟨52865543645374946768650709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35243695763583297845767139 52865543645374946768650709)
                  ·
                    refine ⟨1239036179188475314890251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52865543645374946768650709 1239036179188475314890251)
                    ·
                      rfl

theorem cell23_7239043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 7].length) (baseStart_7239043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239043 prefixEnd_7239043 := by exact prefixLift 7239043
  have htrace : WordTrace (prefixWord ++ tailWord_7239043) baseStart_7239043 baseEnd_7239043 := by
    simpa [prefixWord, tailWord_7239043, baseEnd_7239043] using wordTrace_append hprefix tailTrace_7239043
  have hstable : (prefixWord ++ tailWord_7239043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239043).length < 2 ^ (prefixWord ++ tailWord_7239043).sum := by decide
  have hdescent : baseEnd_7239043 < baseStart_7239043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239047 : List Nat := [1, 1, 4, 2, 2, 4, 1, 3, 5]
def baseStart_7239047 : Nat := 118140960795 + 7239047 * 2 ^ 59
def prefixEnd_7239047 : Nat := 4983230072969 + 3 ^ 40 * 7239047 * 2
def baseEnd_7239047 : Nat := 413012287943115992113415

theorem tailTrace_7239047 : CollatzResearch.WordTrace tailWord_7239047 prefixEnd_7239047 413012287943115992113415 := by
  unfold tailWord_7239047
  simp only [CollatzResearch.WordTrace]
  refine ⟨264029735005176524643387395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176019823336784349762258263 264029735005176524643387395)
  ·
    refine ⟨396044602507764786965081093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264029735005176524643387395 396044602507764786965081093)
    ·
      refine ⟨74258362970205897555952705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396044602507764786965081093 74258362970205897555952705)
      ·
        refine ⟨55693772227654423166964529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74258362970205897555952705 55693772227654423166964529)
        ·
          refine ⟨41770329170740817375223397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55693772227654423166964529 41770329170740817375223397)
          ·
            refine ⟨7831936719513903257854387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41770329170740817375223397 7831936719513903257854387)
            ·
              refine ⟨11747905079270854886781581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7831936719513903257854387 11747905079270854886781581)
              ·
                refine ⟨4405464404726570582543093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11747905079270854886781581 4405464404726570582543093)
                ·
                  refine ⟨413012287943115992113415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4405464404726570582543093 413012287943115992113415)
                  ·
                    rfl

theorem cell23_7239047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 5].length) (baseStart_7239047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239047 prefixEnd_7239047 := by exact prefixLift 7239047
  have htrace : WordTrace (prefixWord ++ tailWord_7239047) baseStart_7239047 baseEnd_7239047 := by
    simpa [prefixWord, tailWord_7239047, baseEnd_7239047] using wordTrace_append hprefix tailTrace_7239047
  have hstable : (prefixWord ++ tailWord_7239047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239047).length < 2 ^ (prefixWord ++ tailWord_7239047).sum := by decide
  have hdescent : baseEnd_7239047 < baseStart_7239047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239060 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_7239060 : Nat := 118140960795 + 7239060 * 2 ^ 59
def prefixEnd_7239060 : Nat := 4983230072969 + 3 ^ 40 * 7239060 * 2
def baseEnd_7239060 : Nat := 1239039088912184126052725

theorem tailTrace_7239060 : CollatzResearch.WordTrace tailWord_7239060 prefixEnd_7239060 1239039088912184126052725 := by
  unfold tailWord_7239060
  simp only [CollatzResearch.WordTrace]
  refine ⟨132015104577064713931805317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176020139436086285242407089 132015104577064713931805317)
  ·
    refine ⟨24752832108199633862213497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132015104577064713931805317 24752832108199633862213497)
    ·
      refine ⟨18564624081149725396660123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24752832108199633862213497 18564624081149725396660123)
      ·
        refine ⟨27846936121724588094990185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18564624081149725396660123 27846936121724588094990185)
        ·
          refine ⟨20885202091293441071242639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27846936121724588094990185 20885202091293441071242639)
          ·
            refine ⟨31327803136940161606863959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20885202091293441071242639 31327803136940161606863959)
            ·
              refine ⟨46991704705410242410295939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31327803136940161606863959 46991704705410242410295939)
              ·
                refine ⟨70487557058115363615443909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46991704705410242410295939 70487557058115363615443909)
                ·
                  refine ⟨13216416948396630677895733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70487557058115363615443909 13216416948396630677895733)
                  ·
                    refine ⟨1239039088912184126052725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13216416948396630677895733 1239039088912184126052725)
                    ·
                      rfl

theorem cell23_7239060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_7239060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239060 prefixEnd_7239060 := by exact prefixLift 7239060
  have htrace : WordTrace (prefixWord ++ tailWord_7239060) baseStart_7239060 baseEnd_7239060 := by
    simpa [prefixWord, tailWord_7239060, baseEnd_7239060] using wordTrace_append hprefix tailTrace_7239060
  have hstable : (prefixWord ++ tailWord_7239060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239060).length < 2 ^ (prefixWord ++ tailWord_7239060).sum := by decide
  have hdescent : baseEnd_7239060 < baseStart_7239060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239064 : List Nat := [2, 1, 2, 5, 2, 1, 3, 2, 5]
def baseStart_7239064 : Nat := 118140960795 + 7239064 * 2 ^ 59
def prefixEnd_7239064 : Nat := 4983230072969 + 3 ^ 40 * 7239064 * 2
def baseEnd_7239064 : Nat := 413013257851018929167573

theorem tailTrace_7239064 : CollatzResearch.WordTrace tailWord_7239064 prefixEnd_7239064 413013257851018929167573 := by
  unfold tailWord_7239064
  simp only [CollatzResearch.WordTrace]
  refine ⟨132015177523057468273378123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176020236697409957697837497 132015177523057468273378123)
  ·
    refine ⟨198022766284586202410067185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132015177523057468273378123 198022766284586202410067185)
    ·
      refine ⟨148517074713439651807550389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198022766284586202410067185 148517074713439651807550389)
      ·
        refine ⟨13923475754384967356957849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148517074713439651807550389 13923475754384967356957849)
        ·
          refine ⟨10442606815788725517718387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13923475754384967356957849 10442606815788725517718387)
          ·
            refine ⟨15663910223683088276577581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10442606815788725517718387 15663910223683088276577581)
            ·
              refine ⟨5873966333881158103716593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15663910223683088276577581 5873966333881158103716593)
              ·
                refine ⟨4405474750410868577787445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5873966333881158103716593 4405474750410868577787445)
                ·
                  refine ⟨413013257851018929167573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4405474750410868577787445 413013257851018929167573)
                  ·
                    rfl

theorem cell23_7239064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 5].length) (baseStart_7239064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239064 prefixEnd_7239064 := by exact prefixLift 7239064
  have htrace : WordTrace (prefixWord ++ tailWord_7239064) baseStart_7239064 baseEnd_7239064 := by
    simpa [prefixWord, tailWord_7239064, baseEnd_7239064] using wordTrace_append hprefix tailTrace_7239064
  have hstable : (prefixWord ++ tailWord_7239064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239064).length < 2 ^ (prefixWord ++ tailWord_7239064).sum := by decide
  have hdescent : baseEnd_7239064 < baseStart_7239064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239097 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 4]
def baseStart_7239097 : Nat := 118140960795 + 7239097 * 2 ^ 59
def prefixEnd_7239097 : Nat := 4983230072969 + 3 ^ 40 * 7239097 * 2
def baseEnd_7239097 : Nat := 3717136265520768733395505

theorem tailTrace_7239097 : CollatzResearch.WordTrace tailWord_7239097 prefixEnd_7239097 3717136265520768733395505 := by
  unfold tailWord_7239097
  simp only [CollatzResearch.WordTrace]
  refine ⟨264031558654995383182707545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176021039103330255455138363 264031558654995383182707545)
  ·
    refine ⟨198023668991246537387030659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264031558654995383182707545 198023668991246537387030659)
    ·
      refine ⟨297035503486869806080545989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198023668991246537387030659 297035503486869806080545989)
      ·
        refine ⟨55694156903788088640102373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297035503486869806080545989 55694156903788088640102373)
        ·
          refine ⟨10442654419460266620019195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55694156903788088640102373 10442654419460266620019195)
          ·
            refine ⟨15663981629190399930028793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10442654419460266620019195 15663981629190399930028793)
            ·
              refine ⟨11747986221892799947521595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15663981629190399930028793 11747986221892799947521595)
              ·
                refine ⟨17621979332839199921282393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11747986221892799947521595 17621979332839199921282393)
                ·
                  refine ⟨13216484499629399940961795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17621979332839199921282393 13216484499629399940961795)
                  ·
                    refine ⟨19824726749444099911442693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13216484499629399940961795 19824726749444099911442693)
                    ·
                      refine ⟨3717136265520768733395505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19824726749444099911442693 3717136265520768733395505)
                      ·
                        rfl

theorem cell23_7239097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_7239097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239097 prefixEnd_7239097 := by exact prefixLift 7239097
  have htrace : WordTrace (prefixWord ++ tailWord_7239097) baseStart_7239097 baseEnd_7239097 := by
    simpa [prefixWord, tailWord_7239097, baseEnd_7239097] using wordTrace_append hprefix tailTrace_7239097
  have hstable : (prefixWord ++ tailWord_7239097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239097).length < 2 ^ (prefixWord ++ tailWord_7239097).sum := by decide
  have hdescent : baseEnd_7239097 < baseStart_7239097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239150 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_7239150 : Nat := 118140960795 + 7239150 * 2 ^ 59
def prefixEnd_7239150 : Nat := 4983230072969 + 3 ^ 40 * 7239150 * 2
def baseEnd_7239150 : Nat := 1239054493331819008677587

theorem tailTrace_7239150 : CollatzResearch.WordTrace tailWord_7239150 prefixEnd_7239150 1239054493331819008677587 := by
  unfold tailWord_7239150
  simp only [CollatzResearch.WordTrace]
  refine ⟨33004186465475421654298363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176022327815868915489591269 33004186465475421654298363)
  ·
    refine ⟨49506279698213132481447545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33004186465475421654298363 49506279698213132481447545)
    ·
      refine ⟨37129709773659849361085659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49506279698213132481447545 37129709773659849361085659)
      ·
        refine ⟨55694564660489774041628489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37129709773659849361085659 55694564660489774041628489)
        ·
          refine ⟨41770923495367330531221367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55694564660489774041628489 41770923495367330531221367)
          ·
            refine ⟨62656385243050995796832051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41770923495367330531221367 62656385243050995796832051)
            ·
              refine ⟨93984577864576493695248077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62656385243050995796832051 93984577864576493695248077)
              ·
                refine ⟨35244216699216185135718029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93984577864576493695248077 35244216699216185135718029)
                ·
                  refine ⟨13216581262206069425894261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35244216699216185135718029 13216581262206069425894261)
                  ·
                    refine ⟨1239054493331819008677587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13216581262206069425894261 1239054493331819008677587)
                    ·
                      rfl

theorem cell23_7239150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_7239150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239150 prefixEnd_7239150 := by exact prefixLift 7239150
  have htrace : WordTrace (prefixWord ++ tailWord_7239150) baseStart_7239150 baseEnd_7239150 := by
    simpa [prefixWord, tailWord_7239150, baseEnd_7239150] using wordTrace_append hprefix tailTrace_7239150
  have hstable : (prefixWord ++ tailWord_7239150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239150).length < 2 ^ (prefixWord ++ tailWord_7239150).sum := by decide
  have hdescent : baseEnd_7239150 < baseStart_7239150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239164 : List Nat := [2, 2, 2, 1, 2, 1, 3, 5, 1, 1, 3]
def baseStart_7239164 : Nat := 118140960795 + 7239164 * 2 ^ 59
def prefixEnd_7239164 : Nat := 4983230072969 + 3 ^ 40 * 7239164 * 2
def baseEnd_7239164 : Nat := 3717170668724619971257697

theorem tailTrace_7239164 : CollatzResearch.WordTrace tailWord_7239164 prefixEnd_7239164 3717170668724619971257697 := by
  unfold tailWord_7239164
  simp only [CollatzResearch.WordTrace]
  refine ⟨132017001172876326812698273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176022668230501769083597697 132017001172876326812698273)
  ·
    refine ⟨99012750879657245109523705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132017001172876326812698273 99012750879657245109523705)
    ·
      refine ⟨74259563159742933832142779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99012750879657245109523705 74259563159742933832142779)
      ·
        refine ⟨111389344739614400748214169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74259563159742933832142779 111389344739614400748214169)
        ·
          refine ⟨83542008554710800561160627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111389344739614400748214169 83542008554710800561160627)
          ·
            refine ⟨125313012832066200841740941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83542008554710800561160627 125313012832066200841740941)
            ·
              refine ⟨46992379812024825315652853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125313012832066200841740941 46992379812024825315652853)
              ·
                refine ⟨4405535607377327373342455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46992379812024825315652853 4405535607377327373342455)
                ·
                  refine ⟨6608303411065991060013683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405535607377327373342455 6608303411065991060013683)
                  ·
                    refine ⟨9912455116598986590020525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6608303411065991060013683 9912455116598986590020525)
                    ·
                      refine ⟨3717170668724619971257697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9912455116598986590020525 3717170668724619971257697)
                      ·
                        rfl

theorem cell23_7239164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_7239164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239164 prefixEnd_7239164 := by exact prefixLift 7239164
  have htrace : WordTrace (prefixWord ++ tailWord_7239164) baseStart_7239164 baseEnd_7239164 := by
    simpa [prefixWord, tailWord_7239164, baseEnd_7239164] using wordTrace_append hprefix tailTrace_7239164
  have hstable : (prefixWord ++ tailWord_7239164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239164).length < 2 ^ (prefixWord ++ tailWord_7239164).sum := by decide
  have hdescent : baseEnd_7239164 < baseStart_7239164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239210 : List Nat := [3, 1, 4, 1, 1, 1, 3, 9]
def baseStart_7239210 : Nat := 118140960795 + 7239210 * 2 ^ 59
def prefixEnd_7239210 : Nat := 4983230072969 + 3 ^ 40 * 7239210 * 2
def baseEnd_7239210 : Nat := 137673862549434325603055

theorem tailTrace_7239210 : CollatzResearch.WordTrace tailWord_7239210 prefixEnd_7239210 137673862549434325603055 := by
  unfold tailWord_7239210
  simp only [CollatzResearch.WordTrace]
  refine ⟨66008920025896500870392771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176023786735724002321047389 66008920025896500870392771)
  ·
    refine ⟨99013380038844751305589157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66008920025896500870392771 99013380038844751305589157)
    ·
      refine ⟨18565008757283390869797967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99013380038844751305589157 18565008757283390869797967)
      ·
        refine ⟨27847513135925086304696951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18565008757283390869797967 27847513135925086304696951)
        ·
          refine ⟨41771269703887629457045427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27847513135925086304696951 41771269703887629457045427)
          ·
            refine ⟨62656904555831444185568141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41771269703887629457045427 62656904555831444185568141)
            ·
              refine ⟨23496339208436791569588053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62656904555831444185568141 23496339208436791569588053)
              ·
                refine ⟨137673862549434325603055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23496339208436791569588053 137673862549434325603055)
                ·
                  rfl

theorem cell23_7239210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 9].length) (baseStart_7239210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239210 prefixEnd_7239210 := by exact prefixLift 7239210
  have htrace : WordTrace (prefixWord ++ tailWord_7239210) baseStart_7239210 baseEnd_7239210 := by
    simpa [prefixWord, tailWord_7239210, baseEnd_7239210] using wordTrace_append hprefix tailTrace_7239210
  have hstable : (prefixWord ++ tailWord_7239210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239210).length < 2 ^ (prefixWord ++ tailWord_7239210).sum := by decide
  have hdescent : baseEnd_7239210 < baseStart_7239210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239237 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 4, 1, 3]
def baseStart_7239237 : Nat := 118140960795 + 7239237 * 2 ^ 59
def prefixEnd_7239237 : Nat := 4983230072969 + 3 ^ 40 * 7239237 * 2
def baseEnd_7239237 : Nat := 3717208152812398185644861

theorem tailTrace_7239237 : CollatzResearch.WordTrace tailWord_7239237 prefixEnd_7239237 3717208152812398185644861 := by
  unfold tailWord_7239237
  simp only [CollatzResearch.WordTrace]
  refine ⟨264036664874488187092803965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176024443249658791395202643 264036664874488187092803965)
  ·
    refine ⟨99013749327933070159801487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264036664874488187092803965 99013749327933070159801487)
    ·
      refine ⟨148520623991899605239702231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99013749327933070159801487 148520623991899605239702231)
      ·
        refine ⟨222780935987849407859553347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148520623991899605239702231 222780935987849407859553347)
        ·
          refine ⟨334171403981774111789330021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222780935987849407859553347 334171403981774111789330021)
          ·
            refine ⟨62657138246582645960499379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334171403981774111789330021 62657138246582645960499379)
            ·
              refine ⟨93985707369873968940749069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62657138246582645960499379 93985707369873968940749069)
              ·
                refine ⟨35244640263702738352780901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93985707369873968940749069 35244640263702738352780901)
                ·
                  refine ⟨6608370049444263441146419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35244640263702738352780901 6608370049444263441146419)
                  ·
                    refine ⟨9912555074166395161719629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6608370049444263441146419 9912555074166395161719629)
                    ·
                      refine ⟨3717208152812398185644861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9912555074166395161719629 3717208152812398185644861)
                      ·
                        rfl

theorem cell23_7239237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_7239237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239237 prefixEnd_7239237 := by exact prefixLift 7239237
  have htrace : WordTrace (prefixWord ++ tailWord_7239237) baseStart_7239237 baseEnd_7239237 := by
    simpa [prefixWord, tailWord_7239237, baseEnd_7239237] using wordTrace_append hprefix tailTrace_7239237
  have hstable : (prefixWord ++ tailWord_7239237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239237).length < 2 ^ (prefixWord ++ tailWord_7239237).sum := by decide
  have hdescent : baseEnd_7239237 < baseStart_7239237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239247 : List Nat := [1, 1, 2, 1, 1, 2, 3, 4, 3, 3, 2]
def baseStart_7239247 : Nat := 118140960795 + 7239247 * 2 ^ 59
def prefixEnd_7239247 : Nat := 4983230072969 + 3 ^ 40 * 7239247 * 2
def baseEnd_7239247 : Nat := 3717213287618943146519815

theorem tailTrace_7239247 : CollatzResearch.WordTrace tailWord_7239247 prefixEnd_7239247 3717213287618943146519815 := by
  unfold tailWord_7239247
  simp only [CollatzResearch.WordTrace]
  refine ⟨264037029604451958800667995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176024686402967972533778663 264037029604451958800667995)
  ·
    refine ⟨396055544406677938201001993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264037029604451958800667995 396055544406677938201001993)
    ·
      refine ⟨297041658305008453650751495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396055544406677938201001993 297041658305008453650751495)
      ·
        refine ⟨445562487457512680476127243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297041658305008453650751495 445562487457512680476127243)
        ·
          refine ⟨668343731186269020714190865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445562487457512680476127243 668343731186269020714190865)
          ·
            refine ⟨501257798389701765535643149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668343731186269020714190865 501257798389701765535643149)
            ·
              refine ⟨187971674396138162075866181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501257798389701765535643149 187971674396138162075866181)
              ·
                refine ⟨35244688949275905389224909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187971674396138162075866181 35244688949275905389224909)
                ·
                  refine ⟨13216758355978464520959341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35244688949275905389224909 13216758355978464520959341)
                  ·
                    refine ⟨4956284383491924195359753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13216758355978464520959341 4956284383491924195359753)
                    ·
                      refine ⟨3717213287618943146519815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956284383491924195359753 3717213287618943146519815)
                      ·
                        rfl

theorem cell23_7239247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 3, 2].length) (baseStart_7239247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239247 prefixEnd_7239247 := by exact prefixLift 7239247
  have htrace : WordTrace (prefixWord ++ tailWord_7239247) baseStart_7239247 baseEnd_7239247 := by
    simpa [prefixWord, tailWord_7239247, baseEnd_7239247] using wordTrace_append hprefix tailTrace_7239247
  have hstable : (prefixWord ++ tailWord_7239247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239247).length < 2 ^ (prefixWord ++ tailWord_7239247).sum := by decide
  have hdescent : baseEnd_7239247 < baseStart_7239247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239297 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_7239297 : Nat := 118140960795 + 7239297 * 2 ^ 59
def prefixEnd_7239297 : Nat := 4983230072969 + 3 ^ 40 * 7239297 * 2
def baseEnd_7239297 : Nat := 3717238961651667950894585

theorem tailTrace_7239297 : CollatzResearch.WordTrace tailWord_7239297 prefixEnd_7239297 3717238961651667950894585 := by
  unfold tailWord_7239297
  simp only [CollatzResearch.WordTrace]
  refine ⟨264038853254270817339988145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176025902169513878226658763 264038853254270817339988145)
  ·
    refine ⟨198029139940703113004991109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264038853254270817339988145 198029139940703113004991109)
    ·
      refine ⟨37130463738881833688435833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198029139940703113004991109 37130463738881833688435833)
      ·
        refine ⟨27847847804161375266326875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37130463738881833688435833 27847847804161375266326875)
        ·
          refine ⟨41771771706242062899490313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27847847804161375266326875 41771771706242062899490313)
          ·
            refine ⟨31328828779681547174617735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41771771706242062899490313 31328828779681547174617735)
            ·
              refine ⟨46993243169522320761926603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31328828779681547174617735 46993243169522320761926603)
              ·
                refine ⟨70489864754283481142889905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46993243169522320761926603 70489864754283481142889905)
                ·
                  refine ⟨52867398565712610857167429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70489864754283481142889905 52867398565712610857167429)
                  ·
                    refine ⟨9912637231071114535718893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52867398565712610857167429 9912637231071114535718893)
                    ·
                      refine ⟨3717238961651667950894585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9912637231071114535718893 3717238961651667950894585)
                      ·
                        rfl

theorem cell23_7239297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_7239297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239297 prefixEnd_7239297 := by exact prefixLift 7239297
  have htrace : WordTrace (prefixWord ++ tailWord_7239297) baseStart_7239297 baseEnd_7239297 := by
    simpa [prefixWord, tailWord_7239297, baseEnd_7239297] using wordTrace_append hprefix tailTrace_7239297
  have hstable : (prefixWord ++ tailWord_7239297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239297).length < 2 ^ (prefixWord ++ tailWord_7239297).sum := by decide
  have hdescent : baseEnd_7239297 < baseStart_7239297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239304 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 2, 6]
def baseStart_7239304 : Nat := 118140960795 + 7239304 * 2 ^ 59
def prefixEnd_7239304 : Nat := 4983230072969 + 3 ^ 40 * 7239304 * 2
def baseEnd_7239304 : Nat := 1239080852005416474502351

theorem tailTrace_7239304 : CollatzResearch.WordTrace tailWord_7239304 prefixEnd_7239304 1239080852005416474502351 := by
  unfold tailWord_7239304
  simp only [CollatzResearch.WordTrace]
  refine ⟨132019554282622728767746483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176026072376830305023661977 132019554282622728767746483)
  ·
    refine ⟨198029331423934093151619725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132019554282622728767746483 198029331423934093151619725)
    ·
      refine ⟨74260999283975284931857397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198029331423934093151619725 74260999283975284931857397)
      ·
        refine ⟨6961968682872682962361631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74260999283975284931857397 6961968682872682962361631)
        ·
          refine ⟨10442953024309024443542447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6961968682872682962361631 10442953024309024443542447)
          ·
            refine ⟨15664429536463536665313671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10442953024309024443542447 15664429536463536665313671)
            ·
              refine ⟨23496644304695304997970507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15664429536463536665313671 23496644304695304997970507)
              ·
                refine ⟨35244966457042957496955761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23496644304695304997970507 35244966457042957496955761)
                ·
                  refine ⟨26433724842782218122716821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35244966457042957496955761 26433724842782218122716821)
                  ·
                    refine ⟨1239080852005416474502351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26433724842782218122716821 1239080852005416474502351)
                    ·
                      rfl

theorem cell23_7239304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_7239304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239304 prefixEnd_7239304 := by exact prefixLift 7239304
  have htrace : WordTrace (prefixWord ++ tailWord_7239304) baseStart_7239304 baseEnd_7239304 := by
    simpa [prefixWord, tailWord_7239304, baseEnd_7239304] using wordTrace_append hprefix tailTrace_7239304
  have hstable : (prefixWord ++ tailWord_7239304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239304).length < 2 ^ (prefixWord ++ tailWord_7239304).sum := by decide
  have hdescent : baseEnd_7239304 < baseStart_7239304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239362 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_7239362 : Nat := 118140960795 + 7239362 * 2 ^ 59
def prefixEnd_7239362 : Nat := 4983230072969 + 3 ^ 40 * 7239362 * 2
def baseEnd_7239362 : Nat := 3717272337894210196581787

theorem tailTrace_7239362 : CollatzResearch.WordTrace tailWord_7239362 prefixEnd_7239362 3717272337894210196581787 := by
  unfold tailWord_7239362
  simp only [CollatzResearch.WordTrace]
  refine ⟨66010305999758833360276085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176027482666023555627402893 66010305999758833360276085)
  ·
    refine ⟨6188466187477390627525883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66010305999758833360276085 6188466187477390627525883)
    ·
      refine ⟨9282699281216085941288825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6188466187477390627525883 9282699281216085941288825)
      ·
        refine ⟨6962024460912064455966619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9282699281216085941288825 6962024460912064455966619)
        ·
          refine ⟨10443036691368096683949929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962024460912064455966619 10443036691368096683949929)
          ·
            refine ⟨7832277518526072512962447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10443036691368096683949929 7832277518526072512962447)
            ·
              refine ⟨11748416277789108769443671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7832277518526072512962447 11748416277789108769443671)
              ·
                refine ⟨17622624416683663154165507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11748416277789108769443671 17622624416683663154165507)
                ·
                  refine ⟨26433936625025494731248261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17622624416683663154165507 26433936625025494731248261)
                  ·
                    refine ⟨4956363117192280262109049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26433936625025494731248261 4956363117192280262109049)
                    ·
                      refine ⟨3717272337894210196581787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956363117192280262109049 3717272337894210196581787)
                      ·
                        rfl

theorem cell23_7239362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_7239362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239362 prefixEnd_7239362 := by exact prefixLift 7239362
  have htrace : WordTrace (prefixWord ++ tailWord_7239362) baseStart_7239362 baseEnd_7239362 := by
    simpa [prefixWord, tailWord_7239362, baseEnd_7239362] using wordTrace_append hprefix tailTrace_7239362
  have hstable : (prefixWord ++ tailWord_7239362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239362).length < 2 ^ (prefixWord ++ tailWord_7239362).sum := by decide
  have hdescent : baseEnd_7239362 < baseStart_7239362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239407 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 6]
def baseStart_7239407 : Nat := 118140960795 + 7239407 * 2 ^ 59
def prefixEnd_7239407 : Nat := 4983230072969 + 3 ^ 40 * 7239407 * 2
def baseEnd_7239407 : Nat := 413032827169295835613231

theorem tailTrace_7239407 : CollatzResearch.WordTrace tailWord_7239407 prefixEnd_7239407 413032827169295835613231 := by
  unfold tailWord_7239407
  simp only [CollatzResearch.WordTrace]
  refine ⟨264042865283872306126492475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176028576855914870750994983 264042865283872306126492475)
  ·
    refine ⟨396064297925808459189738713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264042865283872306126492475 396064297925808459189738713)
    ·
      refine ⟨297048223444356344392304035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396064297925808459189738713 297048223444356344392304035)
      ·
        refine ⟨445572335166534516588456053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297048223444356344392304035 445572335166534516588456053)
        ·
          refine ⟨41772406421862610930167755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 445572335166534516588456053 41772406421862610930167755)
          ·
            refine ⟨62658609632793916395251633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41772406421862610930167755 62658609632793916395251633)
            ·
              refine ⟨46993957224595437296438725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62658609632793916395251633 46993957224595437296438725)
              ·
                refine ⟨8811366979611644493082261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46993957224595437296438725 8811366979611644493082261)
                ·
                  refine ⟨413032827169295835613231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8811366979611644493082261 413032827169295835613231)
                  ·
                    rfl

theorem cell23_7239407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 6].length) (baseStart_7239407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239407 prefixEnd_7239407 := by exact prefixLift 7239407
  have htrace : WordTrace (prefixWord ++ tailWord_7239407) baseStart_7239407 baseEnd_7239407 := by
    simpa [prefixWord, tailWord_7239407, baseEnd_7239407] using wordTrace_append hprefix tailTrace_7239407
  have hstable : (prefixWord ++ tailWord_7239407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239407).length < 2 ^ (prefixWord ++ tailWord_7239407).sum := by decide
  have hdescent : baseEnd_7239407 < baseStart_7239407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239461 : List Nat := [1, 3, 1, 2, 3, 2, 2, 2, 2, 3, 2]
def baseStart_7239461 : Nat := 118140960795 + 7239461 * 2 ^ 59
def prefixEnd_7239461 : Nat := 4983230072969 + 3 ^ 40 * 7239461 * 2
def baseEnd_7239461 : Nat := 3717323172479005309243831

theorem tailTrace_7239461 : CollatzResearch.WordTrace tailWord_7239461 prefixEnd_7239461 3717323172479005309243831 := by
  unfold tailWord_7239461
  simp only [CollatzResearch.WordTrace]
  refine ⟨264044834825676673348958237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176029889883784448899305491 264044834825676673348958237)
  ·
    refine ⟨99016813059628752505859339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264044834825676673348958237 99016813059628752505859339)
    ·
      refine ⟨148525219589443128758789009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99016813059628752505859339 148525219589443128758789009)
      ·
        refine ⟨111393914692082346569091757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148525219589443128758789009 111393914692082346569091757)
        ·
          refine ⟨41772718009530879963409409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111393914692082346569091757 41772718009530879963409409)
          ·
            refine ⟨31329538507148159972557057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41772718009530879963409409 31329538507148159972557057)
            ·
              refine ⟨23497153880361119979417793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31329538507148159972557057 23497153880361119979417793)
              ·
                refine ⟨17622865410270839984563345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23497153880361119979417793 17622865410270839984563345)
                ·
                  refine ⟨13217149057703129988422509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17622865410270839984563345 13217149057703129988422509)
                  ·
                    refine ⟨4956430896638673745658441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13217149057703129988422509 4956430896638673745658441)
                    ·
                      refine ⟨3717323172479005309243831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956430896638673745658441 3717323172479005309243831)
                      ·
                        rfl

theorem cell23_7239461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_7239461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239461 prefixEnd_7239461 := by exact prefixLift 7239461
  have htrace : WordTrace (prefixWord ++ tailWord_7239461) baseStart_7239461 baseEnd_7239461 := by
    simpa [prefixWord, tailWord_7239461, baseEnd_7239461] using wordTrace_append hprefix tailTrace_7239461
  have hstable : (prefixWord ++ tailWord_7239461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239461).length < 2 ^ (prefixWord ++ tailWord_7239461).sum := by decide
  have hdescent : baseEnd_7239461 < baseStart_7239461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239468 : List Nat := [2, 2, 1, 1, 1, 6, 1, 4, 1, 1, 3]
def baseStart_7239468 : Nat := 118140960795 + 7239468 * 2 ^ 59
def prefixEnd_7239468 : Nat := 4983230072969 + 3 ^ 40 * 7239468 * 2
def baseEnd_7239468 : Nat := 3717326766843586781856299

theorem tailTrace_7239468 : CollatzResearch.WordTrace tailWord_7239468 prefixEnd_7239468 3717326766843586781856299 := by
  unfold tailWord_7239468
  simp only [CollatzResearch.WordTrace]
  refine ⟨132022545068325656772231529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176030060091100875696308705 132022545068325656772231529)
  ·
    refine ⟨99016908801244242579173647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132022545068325656772231529 99016908801244242579173647)
    ·
      refine ⟨148525363201866363868760471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99016908801244242579173647 148525363201866363868760471)
      ·
        refine ⟨222788044802799545803140707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148525363201866363868760471 222788044802799545803140707)
        ·
          refine ⟨334182067204199318704711061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222788044802799545803140707 334182067204199318704711061)
          ·
            refine ⟨15664784400196843064283331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 334182067204199318704711061 15664784400196843064283331)
            ·
              refine ⟨23497176600295264596424997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15664784400196843064283331 23497176600295264596424997)
              ·
                refine ⟨4405720612555362111829687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23497176600295264596424997 4405720612555362111829687)
                ·
                  refine ⟨6608580918833043167744531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405720612555362111829687 6608580918833043167744531)
                  ·
                    refine ⟨9912871378249564751616797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6608580918833043167744531 9912871378249564751616797)
                    ·
                      refine ⟨3717326766843586781856299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9912871378249564751616797 3717326766843586781856299)
                      ·
                        rfl

theorem cell23_7239468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 1, 1, 3].length) (baseStart_7239468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239468 prefixEnd_7239468 := by exact prefixLift 7239468
  have htrace : WordTrace (prefixWord ++ tailWord_7239468) baseStart_7239468 baseEnd_7239468 := by
    simpa [prefixWord, tailWord_7239468, baseEnd_7239468] using wordTrace_append hprefix tailTrace_7239468
  have hstable : (prefixWord ++ tailWord_7239468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239468).length < 2 ^ (prefixWord ++ tailWord_7239468).sum := by decide
  have hdescent : baseEnd_7239468 < baseStart_7239468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239474 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_7239474 : Nat := 118140960795 + 7239474 * 2 ^ 59
def prefixEnd_7239474 : Nat := 4983230072969 + 3 ^ 40 * 7239474 * 2
def baseEnd_7239474 : Nat := 3717329847727513758381271

theorem tailTrace_7239474 : CollatzResearch.WordTrace tailWord_7239474 prefixEnd_7239474 3717329847727513758381271 := by
  unfold tailWord_7239474
  simp only [CollatzResearch.WordTrace]
  refine ⟨66011327243657394142295369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176030205983086384379454317 66011327243657394142295369)
  ·
    refine ⟨49508495432743045606721527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66011327243657394142295369 49508495432743045606721527)
    ·
      refine ⟨74262743149114568410082291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49508495432743045606721527 74262743149114568410082291)
      ·
        refine ⟨111394114723671852615123437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74262743149114568410082291 111394114723671852615123437)
        ·
          refine ⟨41772793021376944730671289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111394114723671852615123437 41772793021376944730671289)
          ·
            refine ⟨31329594766032708548003467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41772793021376944730671289 31329594766032708548003467)
            ·
              refine ⟨46994392149049062822005201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31329594766032708548003467 46994392149049062822005201)
              ·
                refine ⟨35245794111786797116503901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46994392149049062822005201 35245794111786797116503901)
                ·
                  refine ⟨13217172791920048918688963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35245794111786797116503901 13217172791920048918688963)
                  ·
                    refine ⟨19825759187880073378033445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13217172791920048918688963 19825759187880073378033445)
                    ·
                      refine ⟨3717329847727513758381271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19825759187880073378033445 3717329847727513758381271)
                      ·
                        rfl

theorem cell23_7239474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_7239474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239474 prefixEnd_7239474 := by exact prefixLift 7239474
  have htrace : WordTrace (prefixWord ++ tailWord_7239474) baseStart_7239474 baseEnd_7239474 := by
    simpa [prefixWord, tailWord_7239474, baseEnd_7239474] using wordTrace_append hprefix tailTrace_7239474
  have hstable : (prefixWord ++ tailWord_7239474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239474).length < 2 ^ (prefixWord ++ tailWord_7239474).sum := by decide
  have hdescent : baseEnd_7239474 < baseStart_7239474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239491 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 5, 2, 2]
def baseStart_7239491 : Nat := 118140960795 + 7239491 * 2 ^ 59
def prefixEnd_7239491 : Nat := 4983230072969 + 3 ^ 40 * 7239491 * 2
def baseEnd_7239491 : Nat := 3717338576898640191868693

theorem tailTrace_7239491 : CollatzResearch.WordTrace tailWord_7239491 prefixEnd_7239491 3717338576898640191868693 := by
  unfold tailWord_7239491
  simp only [CollatzResearch.WordTrace]
  refine ⟨264045929015567988472550327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176030619343711992315033551 264045929015567988472550327)
  ·
    refine ⟨396068893523351982708825491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264045929015567988472550327 396068893523351982708825491)
    ·
      refine ⟨594103340285027974063238237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396068893523351982708825491 594103340285027974063238237)
      ·
        refine ⟨222788752606885490273714339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594103340285027974063238237 222788752606885490273714339)
        ·
          refine ⟨334183128910328235410571509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222788752606885490273714339 334183128910328235410571509)
          ·
            refine ⟨31329668335343272069741079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 334183128910328235410571509 31329668335343272069741079)
            ·
              refine ⟨46994502503014908104611619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31329668335343272069741079 46994502503014908104611619)
              ·
                refine ⟨70491753754522362156917429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46994502503014908104611619 70491753754522362156917429)
                ·
                  refine ⟨6608601914486471452211009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70491753754522362156917429 6608601914486471452211009)
                  ·
                    refine ⟨4956451435864853589158257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6608601914486471452211009 4956451435864853589158257)
                    ·
                      refine ⟨3717338576898640191868693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956451435864853589158257 3717338576898640191868693)
                      ·
                        rfl

theorem cell23_7239491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5, 2, 2].length) (baseStart_7239491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239491 prefixEnd_7239491 := by exact prefixLift 7239491
  have htrace : WordTrace (prefixWord ++ tailWord_7239491) baseStart_7239491 baseEnd_7239491 := by
    simpa [prefixWord, tailWord_7239491, baseEnd_7239491] using wordTrace_append hprefix tailTrace_7239491
  have hstable : (prefixWord ++ tailWord_7239491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239491).length < 2 ^ (prefixWord ++ tailWord_7239491).sum := by decide
  have hdescent : baseEnd_7239491 < baseStart_7239491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239501 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_7239501 : Nat := 118140960795 + 7239501 * 2 ^ 59
def prefixEnd_7239501 : Nat := 4983230072969 + 3 ^ 40 * 7239501 * 2
def baseEnd_7239501 : Nat := 1239114570568395050914549

theorem tailTrace_7239501 : CollatzResearch.WordTrace tailWord_7239501 prefixEnd_7239501 1239114570568395050914549 := by
  unfold tailWord_7239501
  simp only [CollatzResearch.WordTrace]
  refine ⟨264046293745531760180414357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176030862497021173453609571 264046293745531760180414357)
  ·
    refine ⟨12377170019321801258456923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 264046293745531760180414357 12377170019321801258456923)
    ·
      refine ⟨18565755028982701887685385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12377170019321801258456923 18565755028982701887685385)
      ·
        refine ⟨13924316271737026415764039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18565755028982701887685385 13924316271737026415764039)
        ·
          refine ⟨20886474407605539623646059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13924316271737026415764039 20886474407605539623646059)
          ·
            refine ⟨31329711611408309435469089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20886474407605539623646059 31329711611408309435469089)
            ·
              refine ⟨23497283708556232076601817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31329711611408309435469089 23497283708556232076601817)
              ·
                refine ⟨17622962781417174057451363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23497283708556232076601817 17622962781417174057451363)
                ·
                  refine ⟨26434444172125761086177045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17622962781417174057451363 26434444172125761086177045)
                  ·
                    refine ⟨1239114570568395050914549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26434444172125761086177045 1239114570568395050914549)
                    ·
                      rfl

theorem cell23_7239501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_7239501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239501 prefixEnd_7239501 := by exact prefixLift 7239501
  have htrace : WordTrace (prefixWord ++ tailWord_7239501) baseStart_7239501 baseEnd_7239501 := by
    simpa [prefixWord, tailWord_7239501, baseEnd_7239501] using wordTrace_append hprefix tailTrace_7239501
  have hstable : (prefixWord ++ tailWord_7239501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239501).length < 2 ^ (prefixWord ++ tailWord_7239501).sum := by decide
  have hdescent : baseEnd_7239501 < baseStart_7239501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239508 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_7239508 : Nat := 118140960795 + 7239508 * 2 ^ 59
def prefixEnd_7239508 : Nat := 4983230072969 + 3 ^ 40 * 7239508 * 2
def baseEnd_7239508 : Nat := 3717347306069766625356115

theorem tailTrace_7239508 : CollatzResearch.WordTrace tailWord_7239508 prefixEnd_7239508 3717347306069766625356115 := by
  unfold tailWord_7239508
  simp only [CollatzResearch.WordTrace]
  refine ⟨132023274528253200187959589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176031032704337600250612785 132023274528253200187959589)
  ·
    refine ⟨24754363974047475035242423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132023274528253200187959589 24754363974047475035242423)
    ·
      refine ⟨37131545961071212552863635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24754363974047475035242423 37131545961071212552863635)
      ·
        refine ⟨55697318941606818829295453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37131545961071212552863635 55697318941606818829295453)
        ·
          refine ⟨20886494603102557060985795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55697318941606818829295453 20886494603102557060985795)
          ·
            refine ⟨31329741904653835591478693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20886494603102557060985795 31329741904653835591478693)
            ·
              refine ⟨5874326607122594173402255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31329741904653835591478693 5874326607122594173402255)
              ·
                refine ⟨8811489910683891260103383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874326607122594173402255 8811489910683891260103383)
                ·
                  refine ⟨13217234866025836890155075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8811489910683891260103383 13217234866025836890155075)
                  ·
                    refine ⟨19825852299038755335232613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13217234866025836890155075 19825852299038755335232613)
                    ·
                      refine ⟨3717347306069766625356115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19825852299038755335232613 3717347306069766625356115)
                      ·
                        rfl

theorem cell23_7239508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_7239508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239508 prefixEnd_7239508 := by exact prefixLift 7239508
  have htrace : WordTrace (prefixWord ++ tailWord_7239508) baseStart_7239508 baseEnd_7239508 := by
    simpa [prefixWord, tailWord_7239508, baseEnd_7239508] using wordTrace_append hprefix tailTrace_7239508
  have hstable : (prefixWord ++ tailWord_7239508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239508).length < 2 ^ (prefixWord ++ tailWord_7239508).sum := by decide
  have hdescent : baseEnd_7239508 < baseStart_7239508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239559 : List Nat := [1, 1, 4, 2, 5, 1, 1, 3, 1, 2, 2]
def baseStart_7239559 : Nat := 118140960795 + 7239559 * 2 ^ 59
def prefixEnd_7239559 : Nat := 4983230072969 + 3 ^ 40 * 7239559 * 2
def baseEnd_7239559 : Nat := 3717373493583145925818381

theorem tailTrace_7239559 : CollatzResearch.WordTrace tailWord_7239559 prefixEnd_7239559 3717373493583145925818381 := by
  unfold tailWord_7239559
  simp only [CollatzResearch.WordTrace]
  refine ⟨264048409179321636086025731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176032272786214424057350487 264048409179321636086025731)
  ·
    refine ⟨396072613768982454129038597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264048409179321636086025731 396072613768982454129038597)
    ·
      refine ⟨74263615081684210149194737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 396072613768982454129038597 74263615081684210149194737)
      ·
        refine ⟨55697711311263157611896053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74263615081684210149194737 55697711311263157611896053)
        ·
          refine ⟨5221660435430921026115255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55697711311263157611896053 5221660435430921026115255)
          ·
            refine ⟨7832490653146381539172883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221660435430921026115255 7832490653146381539172883)
            ·
              refine ⟨11748735979719572308759325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7832490653146381539172883 11748735979719572308759325)
              ·
                refine ⟨4405775992394839615784747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11748735979719572308759325 4405775992394839615784747)
                ·
                  refine ⟨6608663988592259423677121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4405775992394839615784747 6608663988592259423677121)
                  ·
                    refine ⟨4956497991444194567757841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6608663988592259423677121 4956497991444194567757841)
                    ·
                      refine ⟨3717373493583145925818381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956497991444194567757841 3717373493583145925818381)
                      ·
                        rfl

theorem cell23_7239559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_7239559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239559 prefixEnd_7239559 := by exact prefixLift 7239559
  have htrace : WordTrace (prefixWord ++ tailWord_7239559) baseStart_7239559 baseEnd_7239559 := by
    simpa [prefixWord, tailWord_7239559, baseEnd_7239559] using wordTrace_append hprefix tailTrace_7239559
  have hstable : (prefixWord ++ tailWord_7239559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239559).length < 2 ^ (prefixWord ++ tailWord_7239559).sum := by decide
  have hdescent : baseEnd_7239559 < baseStart_7239559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239584 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 3]
def baseStart_7239584 : Nat := 118140960795 + 7239584 * 2 ^ 59
def prefixEnd_7239584 : Nat := 4983230072969 + 3 ^ 40 * 7239584 * 2
def baseEnd_7239584 : Nat := 3717386330599508328005765

theorem tailTrace_7239584 : CollatzResearch.WordTrace tailWord_7239584 prefixEnd_7239584 3717386330599508328005765 := by
  unfold tailWord_7239584
  simp only [CollatzResearch.WordTrace]
  refine ⟨132024660502115532677842903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176032880669487376903790537 132024660502115532677842903)
  ·
    refine ⟨198036990753173299016764355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132024660502115532677842903 198036990753173299016764355)
    ·
      refine ⟨297055486129759948525146533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198036990753173299016764355 297055486129759948525146533)
      ·
        refine ⟨55697903649329990348464975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297055486129759948525146533 55697903649329990348464975)
        ·
          refine ⟨83546855473994985522697463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55697903649329990348464975 83546855473994985522697463)
          ·
            refine ⟨125320283210992478284046195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83546855473994985522697463 125320283210992478284046195)
            ·
              refine ⟨187980424816488717426069293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125320283210992478284046195 187980424816488717426069293)
              ·
                refine ⟨70492659306183269034775985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187980424816488717426069293 70492659306183269034775985)
                ·
                  refine ⟨52869494479637451776081989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70492659306183269034775985 52869494479637451776081989)
                  ·
                    refine ⟨9913030214932022208015373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52869494479637451776081989 9913030214932022208015373)
                    ·
                      refine ⟨3717386330599508328005765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9913030214932022208015373 3717386330599508328005765)
                      ·
                        rfl

theorem cell23_7239584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_7239584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239584 prefixEnd_7239584 := by exact prefixLift 7239584
  have htrace : WordTrace (prefixWord ++ tailWord_7239584) baseStart_7239584 baseEnd_7239584 := by
    simpa [prefixWord, tailWord_7239584, baseEnd_7239584] using wordTrace_append hprefix tailTrace_7239584
  have hstable : (prefixWord ++ tailWord_7239584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239584).length < 2 ^ (prefixWord ++ tailWord_7239584).sum := by decide
  have hdescent : baseEnd_7239584 < baseStart_7239584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239592 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7239592 : Nat := 118140960795 + 7239592 * 2 ^ 59
def prefixEnd_7239592 : Nat := 4983230072969 + 3 ^ 40 * 7239592 * 2
def baseEnd_7239592 : Nat := 3717390438444744296705729

theorem tailTrace_7239592 : CollatzResearch.WordTrace tailWord_7239592 prefixEnd_7239592 3717390438444744296705729 := by
  unfold tailWord_7239592
  simp only [CollatzResearch.WordTrace]
  refine ⟨132024806394101041360988515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176033075192134721814651353 132024806394101041360988515)
  ·
    refine ⟨198037209591151562041482773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132024806394101041360988515 198037209591151562041482773)
    ·
      refine ⟨9282994199585229470694505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198037209591151562041482773 9282994199585229470694505)
      ·
        refine ⟨6962245649688922103020879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9282994199585229470694505 6962245649688922103020879)
        ·
          refine ⟨10443368474533383154531319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962245649688922103020879 10443368474533383154531319)
          ·
            refine ⟨15665052711800074731796979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10443368474533383154531319 15665052711800074731796979)
            ·
              refine ⟨23497579067700112097695469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15665052711800074731796979 23497579067700112097695469)
              ·
                refine ⟨8811592150387542036635801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23497579067700112097695469 8811592150387542036635801)
                ·
                  refine ⟨6608694112790656527476851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8811592150387542036635801 6608694112790656527476851)
                  ·
                    refine ⟨9913041169185984791215277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6608694112790656527476851 9913041169185984791215277)
                    ·
                      refine ⟨3717390438444744296705729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9913041169185984791215277 3717390438444744296705729)
                      ·
                        rfl

theorem cell23_7239592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7239592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239592 prefixEnd_7239592 := by exact prefixLift 7239592
  have htrace : WordTrace (prefixWord ++ tailWord_7239592) baseStart_7239592 baseEnd_7239592 := by
    simpa [prefixWord, tailWord_7239592, baseEnd_7239592] using wordTrace_append hprefix tailTrace_7239592
  have hstable : (prefixWord ++ tailWord_7239592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239592).length < 2 ^ (prefixWord ++ tailWord_7239592).sum := by decide
  have hdescent : baseEnd_7239592 < baseStart_7239592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239681 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 5, 4]
def baseStart_7239681 : Nat := 118140960795 + 7239681 * 2 ^ 59
def prefixEnd_7239681 : Nat := 4983230072969 + 3 ^ 40 * 7239681 * 2
def baseEnd_7239681 : Nat := 1239145379407664816164273

theorem tailTrace_7239681 : CollatzResearch.WordTrace tailWord_7239681 prefixEnd_7239681 1239145379407664816164273 := by
  unfold tailWord_7239681
  simp only [CollatzResearch.WordTrace]
  refine ⟨264052858884879650921966897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176035239256586433947977931 264052858884879650921966897)
  ·
    refine ⟨198039644163659738191475173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264052858884879650921966897 198039644163659738191475173)
    ·
      refine ⟨37132433280686200910901595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198039644163659738191475173 37132433280686200910901595)
      ·
        refine ⟨55698649921029301366352393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37132433280686200910901595 55698649921029301366352393)
        ·
          refine ⟨41773987440771976024764295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55698649921029301366352393 41773987440771976024764295)
          ·
            refine ⟨62660981161157964037146443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41773987440771976024764295 62660981161157964037146443)
            ·
              refine ⟨93991471741736946055719665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62660981161157964037146443 93991471741736946055719665)
              ·
                refine ⟨70493603806302709541789749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93991471741736946055719665 70493603806302709541789749)
                ·
                  refine ⟨6608775356840879019542789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70493603806302709541789749 6608775356840879019542789)
                  ·
                    refine ⟨1239145379407664816164273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6608775356840879019542789 1239145379407664816164273)
                    ·
                      rfl

theorem cell23_7239681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_7239681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239681 prefixEnd_7239681 := by exact prefixLift 7239681
  have htrace : WordTrace (prefixWord ++ tailWord_7239681) baseStart_7239681 baseEnd_7239681 := by
    simpa [prefixWord, tailWord_7239681, baseEnd_7239681] using wordTrace_append hprefix tailTrace_7239681
  have hstable : (prefixWord ++ tailWord_7239681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239681).length < 2 ^ (prefixWord ++ tailWord_7239681).sum := by decide
  have hdescent : baseEnd_7239681 < baseStart_7239681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239691 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 3]
def baseStart_7239691 : Nat := 118140960795 + 7239691 * 2 ^ 59
def prefixEnd_7239691 : Nat := 4983230072969 + 3 ^ 40 * 7239691 * 2
def baseEnd_7239691 : Nat := 3717441273029539409367773

theorem tailTrace_7239691 : CollatzResearch.WordTrace tailWord_7239691 prefixEnd_7239691 3717441273029539409367773 := by
  unfold tailWord_7239691
  simp only [CollatzResearch.WordTrace]
  refine ⟨264053223614843422629830927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176035482409895615086553951 264053223614843422629830927)
  ·
    refine ⟨396079835422265133944746391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264053223614843422629830927 396079835422265133944746391)
    ·
      refine ⟨594119753133397700917119587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396079835422265133944746391 594119753133397700917119587)
      ·
        refine ⟨891179629700096551375679381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594119753133397700917119587 891179629700096551375679381)
        ·
          refine ⟨41774045142192025845734971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 891179629700096551375679381 41774045142192025845734971)
          ·
            refine ⟨62661067713288038768602457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41774045142192025845734971 62661067713288038768602457)
            ·
              refine ⟨46995800784966029076451843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62661067713288038768602457 46995800784966029076451843)
              ·
                refine ⟨70493701177449043614677765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46995800784966029076451843 70493701177449043614677765)
                ·
                  refine ⟨13217568970771695677752081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70493701177449043614677765 13217568970771695677752081)
                  ·
                    refine ⟨9913176728078771758314061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13217568970771695677752081 9913176728078771758314061)
                    ·
                      refine ⟨3717441273029539409367773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9913176728078771758314061 3717441273029539409367773)
                      ·
                        rfl

theorem cell23_7239691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 3].length) (baseStart_7239691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239691 prefixEnd_7239691 := by exact prefixLift 7239691
  have htrace : WordTrace (prefixWord ++ tailWord_7239691) baseStart_7239691 baseEnd_7239691 := by
    simpa [prefixWord, tailWord_7239691, baseEnd_7239691] using wordTrace_append hprefix tailTrace_7239691
  have hstable : (prefixWord ++ tailWord_7239691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239691).length < 2 ^ (prefixWord ++ tailWord_7239691).sum := by decide
  have hdescent : baseEnd_7239691 < baseStart_7239691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239761 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_7239761 : Nat := 118140960795 + 7239761 * 2 ^ 59
def prefixEnd_7239761 : Nat := 4983230072969 + 3 ^ 40 * 7239761 * 2
def baseEnd_7239761 : Nat := 3717477216675354135492451

theorem tailTrace_7239761 : CollatzResearch.WordTrace tailWord_7239761 prefixEnd_7239761 3717477216675354135492451 := by
  unfold tailWord_7239761
  simp only [CollatzResearch.WordTrace]
  refine ⟨264055776724589824584879137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176037184483059883056586091 264055776724589824584879137)
  ·
    refine ⟨198041832543442368438659353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264055776724589824584879137 198041832543442368438659353)
    ·
      refine ⟨148531374407581776328994515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198041832543442368438659353 148531374407581776328994515)
      ·
        refine ⟨222797061611372664493491773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148531374407581776328994515 222797061611372664493491773)
        ·
          refine ⟨83548898104264749185059415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222797061611372664493491773 83548898104264749185059415)
          ·
            refine ⟨125323347156397123777589123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83548898104264749185059415 125323347156397123777589123)
            ·
              refine ⟨187985020734595685666383685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125323347156397123777589123 187985020734595685666383685)
              ·
                refine ⟨35247191387736691062446941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187985020734595685666383685 35247191387736691062446941)
                ·
                  refine ⟨13217696770401259148417603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35247191387736691062446941 13217696770401259148417603)
                  ·
                    refine ⟨19826545155601888722626405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13217696770401259148417603 19826545155601888722626405)
                    ·
                      refine ⟨3717477216675354135492451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19826545155601888722626405 3717477216675354135492451)
                      ·
                        rfl

theorem cell23_7239761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_7239761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239761 prefixEnd_7239761 := by exact prefixLift 7239761
  have htrace : WordTrace (prefixWord ++ tailWord_7239761) baseStart_7239761 baseEnd_7239761 := by
    simpa [prefixWord, tailWord_7239761, baseEnd_7239761] using wordTrace_append hprefix tailTrace_7239761
  have hstable : (prefixWord ++ tailWord_7239761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239761).length < 2 ^ (prefixWord ++ tailWord_7239761).sum := by decide
  have hdescent : baseEnd_7239761 < baseStart_7239761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239762 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 6]
def baseStart_7239762 : Nat := 118140960795 + 7239762 * 2 ^ 59
def prefixEnd_7239762 : Nat := 4983230072969 + 3 ^ 40 * 7239762 * 2
def baseEnd_7239762 : Nat := 413053081128445403508883

theorem tailTrace_7239762 : CollatzResearch.WordTrace tailWord_7239762 prefixEnd_7239762 413053081128445403508883 := by
  unfold tailWord_7239762
  simp only [CollatzResearch.WordTrace]
  refine ⟨66013953299396550438916385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176037208798390801170443693 66013953299396550438916385)
  ·
    refine ⟨49510464974547412829187289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66013953299396550438916385 49510464974547412829187289)
    ·
      refine ⟨37132848730910559621890467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49510464974547412829187289 37132848730910559621890467)
      ·
        refine ⟨55699273096365839432835701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37132848730910559621890467 55699273096365839432835701)
        ·
          refine ⟨5221806852784297446828347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55699273096365839432835701 5221806852784297446828347)
          ·
            refine ⟨7832710279176446170242521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221806852784297446828347 7832710279176446170242521)
            ·
              refine ⟨5874532709382334627681891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7832710279176446170242521 5874532709382334627681891)
              ·
                refine ⟨8811799064073501941522837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874532709382334627681891 8811799064073501941522837)
                ·
                  refine ⟨413053081128445403508883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8811799064073501941522837 413053081128445403508883)
                  ·
                    rfl

theorem cell23_7239762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_7239762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239762 prefixEnd_7239762 := by exact prefixLift 7239762
  have htrace : WordTrace (prefixWord ++ tailWord_7239762) baseStart_7239762 baseEnd_7239762 := by
    simpa [prefixWord, tailWord_7239762, baseEnd_7239762] using wordTrace_append hprefix tailTrace_7239762
  have hstable : (prefixWord ++ tailWord_7239762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239762).length < 2 ^ (prefixWord ++ tailWord_7239762).sum := by decide
  have hdescent : baseEnd_7239762 < baseStart_7239762 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239791 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 4]
def baseStart_7239791 : Nat := 118140960795 + 7239791 * 2 ^ 59
def prefixEnd_7239791 : Nat := 4983230072969 + 3 ^ 40 * 7239791 * 2
def baseEnd_7239791 : Nat := 3717492621094989018117313

theorem tailTrace_7239791 : CollatzResearch.WordTrace tailWord_7239791 prefixEnd_7239791 3717492621094989018117313 := by
  unfold tailWord_7239791
  simp only [CollatzResearch.WordTrace]
  refine ⟨264056870914481139708471227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176037913942987426472314151 264056870914481139708471227)
  ·
    refine ⟨396085306371721709562706841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264056870914481139708471227 396085306371721709562706841)
    ·
      refine ⟨297063979778791282172030131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396085306371721709562706841 297063979778791282172030131)
      ·
        refine ⟨445595969668186923258045197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297063979778791282172030131 445595969668186923258045197)
        ·
          refine ⟨167098488625570096221766949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445595969668186923258045197 167098488625570096221766949)
          ·
            refine ⟨31330966617294393041581303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167098488625570096221766949 31330966617294393041581303)
            ·
              refine ⟨46996449925941589562371955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31330966617294393041581303 46996449925941589562371955)
              ·
                refine ⟨70494674888912384343557933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46996449925941589562371955 70494674888912384343557933)
                ·
                  refine ⟨26435503083342144128834225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70494674888912384343557933 26435503083342144128834225)
                  ·
                    refine ⟨19826627312506608096625669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26435503083342144128834225 19826627312506608096625669)
                    ·
                      refine ⟨3717492621094989018117313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19826627312506608096625669 3717492621094989018117313)
                      ·
                        rfl

theorem cell23_7239791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_7239791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239791 prefixEnd_7239791 := by exact prefixLift 7239791
  have htrace : WordTrace (prefixWord ++ tailWord_7239791) baseStart_7239791 baseEnd_7239791 := by
    simpa [prefixWord, tailWord_7239791, baseEnd_7239791] using wordTrace_append hprefix tailTrace_7239791
  have hstable : (prefixWord ++ tailWord_7239791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239791).length < 2 ^ (prefixWord ++ tailWord_7239791).sum := by decide
  have hdescent : baseEnd_7239791 < baseStart_7239791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239805 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_7239805 : Nat := 118140960795 + 7239805 * 2 ^ 59
def prefixEnd_7239805 : Nat := 4983230072969 + 3 ^ 40 * 7239805 * 2
def baseEnd_7239805 : Nat := 1239166603274717321114083

theorem tailTrace_7239805 : CollatzResearch.WordTrace tailWord_7239805 prefixEnd_7239805 1239166603274717321114083 := by
  unfold tailWord_7239805
  simp only [CollatzResearch.WordTrace]
  refine ⟨264057381536430420099480869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176038254357620280066320579 264057381536430420099480869)
  ·
    refine ⟨49510759038080703768652663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264057381536430420099480869 49510759038080703768652663)
    ·
      refine ⟨74266138557121055652978995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49510759038080703768652663 74266138557121055652978995)
      ·
        refine ⟨111399207835681583479468493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74266138557121055652978995 111399207835681583479468493)
        ·
          refine ⟨41774702938380593804800685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111399207835681583479468493 41774702938380593804800685)
          ·
            refine ⟨15665513601892722676800257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41774702938380593804800685 15665513601892722676800257)
            ·
              refine ⟨11749135201419542007600193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15665513601892722676800257 11749135201419542007600193)
              ·
                refine ⟨8811851401064656505700145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11749135201419542007600193 8811851401064656505700145)
                ·
                  refine ⟨6608888550798492379275109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8811851401064656505700145 6608888550798492379275109)
                  ·
                    refine ⟨1239166603274717321114083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6608888550798492379275109 1239166603274717321114083)
                    ·
                      rfl

theorem cell23_7239805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_7239805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239805 prefixEnd_7239805 := by exact prefixLift 7239805
  have htrace : WordTrace (prefixWord ++ tailWord_7239805) baseStart_7239805 baseEnd_7239805 := by
    simpa [prefixWord, tailWord_7239805, baseEnd_7239805] using wordTrace_append hprefix tailTrace_7239805
  have hstable : (prefixWord ++ tailWord_7239805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239805).length < 2 ^ (prefixWord ++ tailWord_7239805).sum := by decide
  have hdescent : baseEnd_7239805 < baseStart_7239805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239818 : List Nat := [3, 1, 2, 3, 1, 4, 1, 8]
def baseStart_7239818 : Nat := 118140960795 + 7239818 * 2 ^ 59
def prefixEnd_7239818 : Nat := 4983230072969 + 3 ^ 40 * 7239818 * 2
def baseEnd_7239818 : Nat := 137685425373061496758507

theorem tailTrace_7239818 : CollatzResearch.WordTrace tailWord_7239818 prefixEnd_7239818 137685425373061496758507 := by
  unfold tailWord_7239818
  simp only [CollatzResearch.WordTrace]
  refine ⟨66014463921345830829926027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176038570456922215546469405 66014463921345830829926027)
  ·
    refine ⟨99021695882018746244889041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66014463921345830829926027 99021695882018746244889041)
    ·
      refine ⟨74266271911514059683666781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99021695882018746244889041 74266271911514059683666781)
      ·
        refine ⟨27849851966817772381375043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74266271911514059683666781 27849851966817772381375043)
        ·
          refine ⟨41774777950226658572062565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27849851966817772381375043 41774777950226658572062565)
          ·
            refine ⟨7832770865667498482261731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41774777950226658572062565 7832770865667498482261731)
            ·
              refine ⟨11749156298501247723392597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7832770865667498482261731 11749156298501247723392597)
              ·
                refine ⟨137685425373061496758507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11749156298501247723392597 137685425373061496758507)
                ·
                  rfl

theorem cell23_7239818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 8].length) (baseStart_7239818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239818 prefixEnd_7239818 := by exact prefixLift 7239818
  have htrace : WordTrace (prefixWord ++ tailWord_7239818) baseStart_7239818 baseEnd_7239818 := by
    simpa [prefixWord, tailWord_7239818, baseEnd_7239818] using wordTrace_append hprefix tailTrace_7239818
  have hstable : (prefixWord ++ tailWord_7239818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239818).length < 2 ^ (prefixWord ++ tailWord_7239818).sum := by decide
  have hdescent : baseEnd_7239818 < baseStart_7239818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239871 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 5]
def baseStart_7239871 : Nat := 118140960795 + 7239871 * 2 ^ 59
def prefixEnd_7239871 : Nat := 4983230072969 + 3 ^ 40 * 7239871 * 2
def baseEnd_7239871 : Nat := 3717533699547348705116945

theorem tailTrace_7239871 : CollatzResearch.WordTrace tailWord_7239871 prefixEnd_7239871 3717533699547348705116945 := by
  unfold tailWord_7239871
  simp only [CollatzResearch.WordTrace]
  refine ⟨264059788754191313371383467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176039859169460875580922311 264059788754191313371383467)
  ·
    refine ⟨396089683131286970057075201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264059788754191313371383467 396089683131286970057075201)
    ·
      refine ⟨297067262348465227542806401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396089683131286970057075201 297067262348465227542806401)
      ·
        refine ⟨222800446761348920657104801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297067262348465227542806401 222800446761348920657104801)
        ·
          refine ⟨167100335071011690492828601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222800446761348920657104801 167100335071011690492828601)
          ·
            refine ⟨125325251303258767869621451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167100335071011690492828601 125325251303258767869621451)
            ·
              refine ⟨187987876954888151804432177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125325251303258767869621451 187987876954888151804432177)
              ·
                refine ⟨140990907716166113853324133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187987876954888151804432177 140990907716166113853324133)
                ·
                  refine ⟨26435795196781146347498275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140990907716166113853324133 26435795196781146347498275)
                  ·
                    refine ⟨39653692795171719521247413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26435795196781146347498275 39653692795171719521247413)
                    ·
                      refine ⟨3717533699547348705116945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39653692795171719521247413 3717533699547348705116945)
                      ·
                        rfl

theorem cell23_7239871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_7239871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239871 prefixEnd_7239871 := by exact prefixLift 7239871
  have htrace : WordTrace (prefixWord ++ tailWord_7239871) baseStart_7239871 baseEnd_7239871 := by
    simpa [prefixWord, tailWord_7239871, baseEnd_7239871] using wordTrace_append hprefix tailTrace_7239871
  have hstable : (prefixWord ++ tailWord_7239871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239871).length < 2 ^ (prefixWord ++ tailWord_7239871).sum := by decide
  have hdescent : baseEnd_7239871 < baseStart_7239871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239881 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 4]
def baseStart_7239881 : Nat := 118140960795 + 7239881 * 2 ^ 59
def prefixEnd_7239881 : Nat := 4983230072969 + 3 ^ 40 * 7239881 * 2
def baseEnd_7239881 : Nat := 3717538834353893665991899

theorem tailTrace_7239881 : CollatzResearch.WordTrace tailWord_7239881 prefixEnd_7239881 3717538834353893665991899 := by
  unfold tailWord_7239881
  simp only [CollatzResearch.WordTrace]
  refine ⟨264060153484155085079247497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176040102322770056719498331 264060153484155085079247497)
  ·
    refine ⟨198045115113116313809435623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264060153484155085079247497 198045115113116313809435623)
    ·
      refine ⟨297067672669674470714153435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198045115113116313809435623 297067672669674470714153435)
      ·
        refine ⟨445601509004511706071230153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297067672669674470714153435 445601509004511706071230153)
        ·
          refine ⟨334201131753383779553422615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445601509004511706071230153 334201131753383779553422615)
          ·
            refine ⟨501301697630075669330133923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334201131753383779553422615 501301697630075669330133923)
            ·
              refine ⟨751952546445113503995200885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501301697630075669330133923 751952546445113503995200885)
              ·
                refine ⟨70495551229229390999550083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 751952546445113503995200885 70495551229229390999550083)
                ·
                  refine ⟨105743326843844086499325125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70495551229229390999550083 105743326843844086499325125)
                  ·
                    refine ⟨19826873783220766218623461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105743326843844086499325125 19826873783220766218623461)
                    ·
                      refine ⟨3717538834353893665991899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19826873783220766218623461 3717538834353893665991899)
                      ·
                        rfl

theorem cell23_7239881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_7239881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239881 prefixEnd_7239881 := by exact prefixLift 7239881
  have htrace : WordTrace (prefixWord ++ tailWord_7239881) baseStart_7239881 baseEnd_7239881 := by
    simpa [prefixWord, tailWord_7239881, baseEnd_7239881] using wordTrace_append hprefix tailTrace_7239881
  have hstable : (prefixWord ++ tailWord_7239881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239881).length < 2 ^ (prefixWord ++ tailWord_7239881).sum := by decide
  have hdescent : baseEnd_7239881 < baseStart_7239881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239951 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 2, 8]
def baseStart_7239951 : Nat := 118140960795 + 7239951 * 2 ^ 59
def prefixEnd_7239951 : Nat := 4983230072969 + 3 ^ 40 * 7239951 * 2
def baseEnd_7239951 : Nat := 1239191592666569464038859

theorem tailTrace_7239951 : CollatzResearch.WordTrace tailWord_7239951 prefixEnd_7239951 1239191592666569464038859 := by
  unfold tailWord_7239951
  simp only [CollatzResearch.WordTrace]
  refine ⟨264062706593901487034295707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176041804395934324689530471 264062706593901487034295707)
  ·
    refine ⟨396094059890852230551443561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264062706593901487034295707 396094059890852230551443561)
    ·
      refine ⟨297070544918139172913582671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396094059890852230551443561 297070544918139172913582671)
      ·
        refine ⟨445605817377208759370374007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297070544918139172913582671 445605817377208759370374007)
        ·
          refine ⟨668408726065813139055561011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445605817377208759370374007 668408726065813139055561011)
          ·
            refine ⟨1002613089098719708583341517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668408726065813139055561011 1002613089098719708583341517)
            ·
              refine ⟨375979908412019890718753069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1002613089098719708583341517 375979908412019890718753069)
              ·
                refine ⟨140992465654507459019532401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375979908412019890718753069 140992465654507459019532401)
                ·
                  refine ⟨105744349240880594264649301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 140992465654507459019532401 105744349240880594264649301)
                  ·
                    refine ⟨1239191592666569464038859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105744349240880594264649301 1239191592666569464038859)
                    ·
                      rfl

theorem cell23_7239951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_7239951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239951 prefixEnd_7239951 := by exact prefixLift 7239951
  have htrace : WordTrace (prefixWord ++ tailWord_7239951) baseStart_7239951 baseEnd_7239951 := by
    simpa [prefixWord, tailWord_7239951, baseEnd_7239951] using wordTrace_append hprefix tailTrace_7239951
  have hstable : (prefixWord ++ tailWord_7239951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239951).length < 2 ^ (prefixWord ++ tailWord_7239951).sum := by decide
  have hdescent : baseEnd_7239951 < baseStart_7239951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239961 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_7239961 : Nat := 118140960795 + 7239961 * 2 ^ 59
def prefixEnd_7239961 : Nat := 4983230072969 + 3 ^ 40 * 7239961 * 2
def baseEnd_7239961 : Nat := 3717579912806253352991531

theorem tailTrace_7239961 : CollatzResearch.WordTrace tailWord_7239961 prefixEnd_7239961 3717579912806253352991531 := by
  unfold tailWord_7239961
  simp only [CollatzResearch.WordTrace]
  refine ⟨264063071323865258742159737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176042047549243505828106491 264063071323865258742159737)
  ·
    refine ⟨198047303492898944056619803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264063071323865258742159737 198047303492898944056619803)
    ·
      refine ⟨297070955239348416084929705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198047303492898944056619803 297070955239348416084929705)
      ·
        refine ⟨222803216429511312063697279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297070955239348416084929705 222803216429511312063697279)
        ·
          refine ⟨334204824644266968095545919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222803216429511312063697279 334204824644266968095545919)
          ·
            refine ⟨501307236966400452143318879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334204824644266968095545919 501307236966400452143318879)
            ·
              refine ⟨751960855449600678214978319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501307236966400452143318879 751960855449600678214978319)
              ·
                refine ⟨1127941283174401017322467479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751960855449600678214978319 1127941283174401017322467479)
                ·
                  refine ⟨1691911924761601525983701219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1127941283174401017322467479 1691911924761601525983701219)
                  ·
                    refine ⟨2537867887142402288975551829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1691911924761601525983701219 2537867887142402288975551829)
                    ·
                      refine ⟨3717579912806253352991531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2537867887142402288975551829 3717579912806253352991531)
                      ·
                        rfl

theorem cell23_7239961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_7239961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239961 prefixEnd_7239961 := by exact prefixLift 7239961
  have htrace : WordTrace (prefixWord ++ tailWord_7239961) baseStart_7239961 baseEnd_7239961 := by
    simpa [prefixWord, tailWord_7239961, baseEnd_7239961] using wordTrace_append hprefix tailTrace_7239961
  have hstable : (prefixWord ++ tailWord_7239961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239961).length < 2 ^ (prefixWord ++ tailWord_7239961).sum := by decide
  have hdescent : baseEnd_7239961 < baseStart_7239961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7239976 : List Nat := [2, 1, 5, 1, 4, 1, 2, 2, 5]
def baseStart_7239976 : Nat := 118140960795 + 7239976 * 2 ^ 59
def prefixEnd_7239976 : Nat := 4983230072969 + 3 ^ 40 * 7239976 * 2
def baseEnd_7239976 : Nat := 413065290557341199367107

theorem tailTrace_7239976 : CollatzResearch.WordTrace tailWord_7239976 prefixEnd_7239976 413065290557341199367107 := by
  unfold tailWord_7239976
  simp only [CollatzResearch.WordTrace]
  refine ⟨132031809209405458151977891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176042412279207277535970521 132031809209405458151977891)
  ·
    refine ⟨198047713814108187227966837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132031809209405458151977891 198047713814108187227966837)
    ·
      refine ⟨18566973170072642552621891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198047713814108187227966837 18566973170072642552621891)
      ·
        refine ⟨27850459755108963828932837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18566973170072642552621891 27850459755108963828932837)
        ·
          refine ⟨5221961204082930717924907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27850459755108963828932837 5221961204082930717924907)
          ·
            refine ⟨7832941806124396076887361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221961204082930717924907 7832941806124396076887361)
            ·
              refine ⟨5874706354593297057665521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7832941806124396076887361 5874706354593297057665521)
              ·
                refine ⟨4406029765944972793249141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5874706354593297057665521 4406029765944972793249141)
                ·
                  refine ⟨413065290557341199367107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4406029765944972793249141 413065290557341199367107)
                  ·
                    rfl

theorem cell23_7239976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 5].length) (baseStart_7239976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7239976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7239976 prefixEnd_7239976 := by exact prefixLift 7239976
  have htrace : WordTrace (prefixWord ++ tailWord_7239976) baseStart_7239976 baseEnd_7239976 := by
    simpa [prefixWord, tailWord_7239976, baseEnd_7239976] using wordTrace_append hprefix tailTrace_7239976
  have hstable : (prefixWord ++ tailWord_7239976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7239976).length < 2 ^ (prefixWord ++ tailWord_7239976).sum := by decide
  have hdescent : baseEnd_7239976 < baseStart_7239976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7239976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240025 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 7, 1, 3]
def baseStart_7240025 : Nat := 118140960795 + 7240025 * 2 ^ 59
def prefixEnd_7240025 : Nat := 4983230072969 + 3 ^ 40 * 7240025 * 2
def baseEnd_7240025 : Nat := 3717612775568141102591237

theorem tailTrace_7240025 : CollatzResearch.WordTrace tailWord_7240025 prefixEnd_7240025 3717612775568141102591237 := by
  unfold tailWord_7240025
  simp only [CollatzResearch.WordTrace]
  refine ⟨264065405595633397672489529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176043603730422265114993019 264065405595633397672489529)
  ·
    refine ⟨198049054196725048254367147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264065405595633397672489529 198049054196725048254367147)
    ·
      refine ⟨297073581295087572381550721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198049054196725048254367147 297073581295087572381550721)
      ·
        refine ⟨222805185971315679286163041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297073581295087572381550721 222805185971315679286163041)
        ·
          refine ⟨167103889478486759464622281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222805185971315679286163041 167103889478486759464622281)
          ·
            refine ⟨125327917108865069598466711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167103889478486759464622281 125327917108865069598466711)
            ·
              refine ⟨187991875663297604397700067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125327917108865069598466711 187991875663297604397700067)
              ·
                refine ⟨281987813494946406596550101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187991875663297604397700067 281987813494946406596550101)
                ·
                  refine ⟨6609089378787806404606643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 281987813494946406596550101 6609089378787806404606643)
                  ·
                    refine ⟨9913634068181709606909965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6609089378787806404606643 9913634068181709606909965)
                    ·
                      refine ⟨3717612775568141102591237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9913634068181709606909965 3717612775568141102591237)
                      ·
                        rfl

theorem cell23_7240025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_7240025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240025 prefixEnd_7240025 := by exact prefixLift 7240025
  have htrace : WordTrace (prefixWord ++ tailWord_7240025) baseStart_7240025 baseEnd_7240025 := by
    simpa [prefixWord, tailWord_7240025, baseEnd_7240025] using wordTrace_append hprefix tailTrace_7240025
  have hstable : (prefixWord ++ tailWord_7240025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240025).length < 2 ^ (prefixWord ++ tailWord_7240025).sum := by decide
  have hdescent : baseEnd_7240025 < baseStart_7240025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240032 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 6]
def baseStart_7240032 : Nat := 118140960795 + 7240032 * 2 ^ 59
def prefixEnd_7240032 : Nat := 4983230072969 + 3 ^ 40 * 7240032 * 2
def baseEnd_7240032 : Nat := 413068485548080286133745

theorem tailTrace_7240032 : CollatzResearch.WordTrace tailWord_7240032 prefixEnd_7240032 413068485548080286133745 := by
  unfold tailWord_7240032
  simp only [CollatzResearch.WordTrace]
  refine ⟨132032830453304018933997175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176043773937738691911996233 132032830453304018933997175)
  ·
    refine ⟨198049245679956028400995763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132032830453304018933997175 198049245679956028400995763)
    ·
      refine ⟨297073868519934042601493645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198049245679956028400995763 297073868519934042601493645)
      ·
        refine ⟨111402700694975265975560117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297073868519934042601493645 111402700694975265975560117)
        ·
          refine ⟨10444003190153931185208761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111402700694975265975560117 10444003190153931185208761)
          ·
            refine ⟨7833002392615448388906571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10444003190153931185208761 7833002392615448388906571)
            ·
              refine ⟨11749503588923172583359857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7833002392615448388906571 11749503588923172583359857)
              ·
                refine ⟨8812127691692379437519893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11749503588923172583359857 8812127691692379437519893)
                ·
                  refine ⟨413068485548080286133745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8812127691692379437519893 413068485548080286133745)
                  ·
                    rfl

theorem cell23_7240032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 6].length) (baseStart_7240032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240032 prefixEnd_7240032 := by exact prefixLift 7240032
  have htrace : WordTrace (prefixWord ++ tailWord_7240032) baseStart_7240032 baseEnd_7240032 := by
    simpa [prefixWord, tailWord_7240032, baseEnd_7240032] using wordTrace_append hprefix tailTrace_7240032
  have hstable : (prefixWord ++ tailWord_7240032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240032).length < 2 ^ (prefixWord ++ tailWord_7240032).sum := by decide
  have hdescent : baseEnd_7240032 < baseStart_7240032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240075 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 4, 4]
def baseStart_7240075 : Nat := 118140960795 + 7240075 * 2 ^ 59
def prefixEnd_7240075 : Nat := 4983230072969 + 3 ^ 40 * 7240075 * 2
def baseEnd_7240075 : Nat := 1239212816533621968988669

theorem tailTrace_7240075 : CollatzResearch.WordTrace tailWord_7240075 prefixEnd_7240075 1239212816533621968988669 := by
  unfold tailWord_7240075
  simp only [CollatzResearch.WordTrace]
  refine ⟨264067229245452256211809679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176044819496968170807873119 264067229245452256211809679)
  ·
    refine ⟨396100843868178384317714519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264067229245452256211809679 396100843868178384317714519)
    ·
      refine ⟨594151265802267576476571779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396100843868178384317714519 594151265802267576476571779)
      ·
        refine ⟨891226898703401364714857669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594151265802267576476571779 891226898703401364714857669)
        ·
          refine ⟨167105043506887755884035813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 891226898703401364714857669 167105043506887755884035813)
          ·
            refine ⟨31332195657541454228256715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167105043506887755884035813 31332195657541454228256715)
            ·
              refine ⟨46998293486312181342385073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31332195657541454228256715 46998293486312181342385073)
              ·
                refine ⟨35248720114734136006788805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46998293486312181342385073 35248720114734136006788805)
                ·
                  refine ⟨6609135021512650501272901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35248720114734136006788805 6609135021512650501272901)
                  ·
                    refine ⟨1239212816533621968988669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6609135021512650501272901 1239212816533621968988669)
                    ·
                      rfl

theorem cell23_7240075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 4].length) (baseStart_7240075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240075 prefixEnd_7240075 := by exact prefixLift 7240075
  have htrace : WordTrace (prefixWord ++ tailWord_7240075) baseStart_7240075 baseEnd_7240075 := by
    simpa [prefixWord, tailWord_7240075, baseEnd_7240075] using wordTrace_append hprefix tailTrace_7240075
  have hstable : (prefixWord ++ tailWord_7240075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240075).length < 2 ^ (prefixWord ++ tailWord_7240075).sum := by decide
  have hdescent : baseEnd_7240075 < baseStart_7240075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240076 : List Nat := [2, 2, 1, 2, 1, 6, 1, 3, 1, 1, 3]
def baseStart_7240076 : Nat := 118140960795 + 7240076 * 2 ^ 59
def prefixEnd_7240076 : Nat := 4983230072969 + 3 ^ 40 * 7240076 * 2
def baseEnd_7240076 : Nat := 3717638963081520403053503

theorem tailTrace_7240076 : CollatzResearch.WordTrace tailWord_7240076 prefixEnd_7240076 3717638963081520403053503 := by
  unfold tailWord_7240076
  simp only [CollatzResearch.WordTrace]
  refine ⟨132033632859224316691298041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176044843812299088921730721 132033632859224316691298041)
  ·
    refine ⟨99025224644418237518473531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132033632859224316691298041 99025224644418237518473531)
    ·
      refine ⟨148537836966627356277710297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99025224644418237518473531 148537836966627356277710297)
      ·
        refine ⟨111403377724970517208282723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148537836966627356277710297 111403377724970517208282723)
        ·
          refine ⟨167105066587455775812424085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111403377724970517208282723 167105066587455775812424085)
          ·
            refine ⟨7833049996286989491207379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167105066587455775812424085 7833049996286989491207379)
            ·
              refine ⟨11749574994430484236811069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7833049996286989491207379 11749574994430484236811069)
              ·
                refine ⟨4406090622911431588804151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11749574994430484236811069 4406090622911431588804151)
                ·
                  refine ⟨6609135934367147383206227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406090622911431588804151 6609135934367147383206227)
                  ·
                    refine ⟨9913703901550721074809341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6609135934367147383206227 9913703901550721074809341)
                    ·
                      refine ⟨3717638963081520403053503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9913703901550721074809341 3717638963081520403053503)
                      ·
                        rfl

theorem cell23_7240076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_7240076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240076 prefixEnd_7240076 := by exact prefixLift 7240076
  have htrace : WordTrace (prefixWord ++ tailWord_7240076) baseStart_7240076 baseEnd_7240076 := by
    simpa [prefixWord, tailWord_7240076, baseEnd_7240076] using wordTrace_append hprefix tailTrace_7240076
  have hstable : (prefixWord ++ tailWord_7240076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240076).length < 2 ^ (prefixWord ++ tailWord_7240076).sum := by decide
  have hdescent : baseEnd_7240076 < baseStart_7240076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240085 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 5, 2, 3]
def baseStart_7240085 : Nat := 118140960795 + 7240085 * 2 ^ 59
def prefixEnd_7240085 : Nat := 4983230072969 + 3 ^ 40 * 7240085 * 2
def baseEnd_7240085 : Nat := 3717643584407410867840961

theorem tailTrace_7240085 : CollatzResearch.WordTrace tailWord_7240085 prefixEnd_7240085 3717643584407410867840961 := by
  unfold tailWord_7240085
  simp only [CollatzResearch.WordTrace]
  refine ⟨264067593975416027919673709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176045062650277351946449139 264067593975416027919673709)
  ·
    refine ⟨99025347740781010469877641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264067593975416027919673709 99025347740781010469877641)
    ·
      refine ⟨74269010805585757852408231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99025347740781010469877641 74269010805585757852408231)
      ·
        refine ⟨111403516208378636778612347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74269010805585757852408231 111403516208378636778612347)
        ·
          refine ⟨167105274312567955167918521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111403516208378636778612347 167105274312567955167918521)
          ·
            refine ⟨125328955734425966375938891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167105274312567955167918521 125328955734425966375938891)
            ·
              refine ⟨187993433601638949563908337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125328955734425966375938891 187993433601638949563908337)
              ·
                refine ⟨140995075201229212172931253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187993433601638949563908337 140995075201229212172931253)
                ·
                  refine ⟨13218288300115238641212305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 140995075201229212172931253 13218288300115238641212305)
                  ·
                    refine ⟨9913716225086428980909229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13218288300115238641212305 9913716225086428980909229)
                    ·
                      refine ⟨3717643584407410867840961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9913716225086428980909229 3717643584407410867840961)
                      ·
                        rfl

theorem cell23_7240085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_7240085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240085 prefixEnd_7240085 := by exact prefixLift 7240085
  have htrace : WordTrace (prefixWord ++ tailWord_7240085) baseStart_7240085 baseEnd_7240085 := by
    simpa [prefixWord, tailWord_7240085, baseEnd_7240085] using wordTrace_append hprefix tailTrace_7240085
  have hstable : (prefixWord ++ tailWord_7240085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240085).length < 2 ^ (prefixWord ++ tailWord_7240085).sum := by decide
  have hdescent : baseEnd_7240085 < baseStart_7240085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240093 : List Nat := [1, 4, 2, 1, 4, 1, 3, 2, 1, 1, 3]
def baseStart_7240093 : Nat := 118140960795 + 7240093 * 2 ^ 59
def prefixEnd_7240093 : Nat := 4983230072969 + 3 ^ 40 * 7240093 * 2
def baseEnd_7240093 : Nat := 3717647692252646836540925

theorem tailTrace_7240093 : CollatzResearch.WordTrace tailWord_7240093 prefixEnd_7240093 3717647692252646836540925 := by
  unfold tailWord_7240093
  simp only [CollatzResearch.WordTrace]
  refine ⟨264067885759387045285964933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176045257172924696857309955 264067885759387045285964933)
  ·
    refine ⟨49512728579885070991118425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264067885759387045285964933 49512728579885070991118425)
    ·
      refine ⟨37134546434913803243338819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49512728579885070991118425 37134546434913803243338819)
      ·
        refine ⟨55701819652370704865008229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37134546434913803243338819 55701819652370704865008229)
        ·
          refine ⟨10444091184819507162189043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55701819652370704865008229 10444091184819507162189043)
          ·
            refine ⟨15666136777229260743283565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444091184819507162189043 15666136777229260743283565)
            ·
              refine ⟨5874801291460972778731337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15666136777229260743283565 5874801291460972778731337)
              ·
                refine ⟨4406100968595729584048503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5874801291460972778731337 4406100968595729584048503)
                ·
                  refine ⟨6609151452893594376072755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406100968595729584048503 6609151452893594376072755)
                  ·
                    refine ⟨9913727179340391564109133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6609151452893594376072755 9913727179340391564109133)
                    ·
                      refine ⟨3717647692252646836540925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9913727179340391564109133 3717647692252646836540925)
                      ·
                        rfl

theorem cell23_7240093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 1, 1, 3].length) (baseStart_7240093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240093 prefixEnd_7240093 := by exact prefixLift 7240093
  have htrace : WordTrace (prefixWord ++ tailWord_7240093) baseStart_7240093 baseEnd_7240093 := by
    simpa [prefixWord, tailWord_7240093, baseEnd_7240093] using wordTrace_append hprefix tailTrace_7240093
  have hstable : (prefixWord ++ tailWord_7240093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240093).length < 2 ^ (prefixWord ++ tailWord_7240093).sum := by decide
  have hdescent : baseEnd_7240093 < baseStart_7240093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240099 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 3, 2, 2]
def baseStart_7240099 : Nat := 118140960795 + 7240099 * 2 ^ 59
def prefixEnd_7240099 : Nat := 4983230072969 + 3 ^ 40 * 7240099 * 2
def baseEnd_7240099 : Nat := 3717650773136573813065897

theorem tailTrace_7240099 : CollatzResearch.WordTrace tailWord_7240099 prefixEnd_7240099 3717650773136573813065897 := by
  unfold tailWord_7240099
  simp only [CollatzResearch.WordTrace]
  refine ⟨264068104597365308310683351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176045403064910205540455567 264068104597365308310683351)
  ·
    refine ⟨396102156896047962466025027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264068104597365308310683351 396102156896047962466025027)
    ·
      refine ⟨594153235344071943699037541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396102156896047962466025027 594153235344071943699037541)
      ·
        refine ⟨111403731627013489443569539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 594153235344071943699037541 111403731627013489443569539)
        ·
          refine ⟨167105597440520234165354309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111403731627013489443569539 167105597440520234165354309)
          ·
            refine ⟨31332299520097543906003933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167105597440520234165354309 31332299520097543906003933)
            ·
              refine ⟨11749612320036578964751475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31332299520097543906003933 11749612320036578964751475)
              ·
                refine ⟨17624418480054868447127213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11749612320036578964751475 17624418480054868447127213)
                ·
                  refine ⟨6609156930020575667672705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17624418480054868447127213 6609156930020575667672705)
                  ·
                    refine ⟨4956867697515431750754529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6609156930020575667672705 4956867697515431750754529)
                    ·
                      refine ⟨3717650773136573813065897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956867697515431750754529 3717650773136573813065897)
                      ·
                        rfl

theorem cell23_7240099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_7240099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240099 prefixEnd_7240099 := by exact prefixLift 7240099
  have htrace : WordTrace (prefixWord ++ tailWord_7240099) baseStart_7240099 baseEnd_7240099 := by
    simpa [prefixWord, tailWord_7240099, baseEnd_7240099] using wordTrace_append hprefix tailTrace_7240099
  have hstable : (prefixWord ++ tailWord_7240099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240099).length < 2 ^ (prefixWord ++ tailWord_7240099).sum := by decide
  have hdescent : baseEnd_7240099 < baseStart_7240099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240108 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_7240108 : Nat := 118140960795 + 7240108 * 2 ^ 59
def prefixEnd_7240108 : Nat := 4983230072969 + 3 ^ 40 * 7240108 * 2
def baseEnd_7240108 : Nat := 3717655394462464277853355

theorem tailTrace_7240108 : CollatzResearch.WordTrace tailWord_7240108 prefixEnd_7240108 3717655394462464277853355 := by
  unfold tailWord_7240108
  simp only [CollatzResearch.WordTrace]
  refine ⟨132034216427166351423880489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176045621902888468565173985 132034216427166351423880489)
  ·
    refine ⟨99025662320374763567910367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132034216427166351423880489 99025662320374763567910367)
    ·
      refine ⟨148538493480562145351865551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99025662320374763567910367 148538493480562145351865551)
      ·
        refine ⟨222807740220843218027798327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148538493480562145351865551 222807740220843218027798327)
        ·
          refine ⟨334211610331264827041697491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222807740220843218027798327 334211610331264827041697491)
          ·
            refine ⟨501317415496897240562546237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334211610331264827041697491 501317415496897240562546237)
            ·
              refine ⟨187994030811336465210954839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 501317415496897240562546237 187994030811336465210954839)
              ·
                refine ⟨281991046217004697816432259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187994030811336465210954839 281991046217004697816432259)
                ·
                  refine ⟨422986569325507046724648389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 281991046217004697816432259 422986569325507046724648389)
                  ·
                    refine ⟨79309981748532571260871573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 422986569325507046724648389 79309981748532571260871573)
                    ·
                      refine ⟨3717655394462464277853355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79309981748532571260871573 3717655394462464277853355)
                      ·
                        rfl

theorem cell23_7240108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_7240108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240108 prefixEnd_7240108 := by exact prefixLift 7240108
  have htrace : WordTrace (prefixWord ++ tailWord_7240108) baseStart_7240108 baseEnd_7240108 := by
    simpa [prefixWord, tailWord_7240108, baseEnd_7240108] using wordTrace_append hprefix tailTrace_7240108
  have hstable : (prefixWord ++ tailWord_7240108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240108).length < 2 ^ (prefixWord ++ tailWord_7240108).sum := by decide
  have hdescent : baseEnd_7240108 < baseStart_7240108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240116 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_7240116 : Nat := 118140960795 + 7240116 * 2 ^ 59
def prefixEnd_7240116 : Nat := 4983230072969 + 3 ^ 40 * 7240116 * 2
def baseEnd_7240116 : Nat := 3717659502307700246553319

theorem tailTrace_7240116 : CollatzResearch.WordTrace tailWord_7240116 prefixEnd_7240116 3717659502307700246553319 := by
  unfold tailWord_7240116
  simp only [CollatzResearch.WordTrace]
  refine ⟨132034362319151860107026101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176045816425535813476034801 132034362319151860107026101)
  ·
    refine ⟨12378221467420486885033697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132034362319151860107026101 12378221467420486885033697)
    ·
      refine ⟨9283666100565365163775273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12378221467420486885033697 9283666100565365163775273)
      ·
        refine ⟨6962749575424023872831455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9283666100565365163775273 6962749575424023872831455)
        ·
          refine ⟨10444124363136035809247183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6962749575424023872831455 10444124363136035809247183)
          ·
            refine ⟨15666186544704053713870775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444124363136035809247183 15666186544704053713870775)
            ·
              refine ⟨23499279817056080570806163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15666186544704053713870775 23499279817056080570806163)
              ·
                refine ⟨35248919725584120856209245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23499279817056080570806163 35248919725584120856209245)
                ·
                  refine ⟨13218344897094045321078467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35248919725584120856209245 13218344897094045321078467)
                  ·
                    refine ⟨19827517345641067981617701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13218344897094045321078467 19827517345641067981617701)
                    ·
                      refine ⟨3717659502307700246553319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19827517345641067981617701 3717659502307700246553319)
                      ·
                        rfl

theorem cell23_7240116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_7240116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240116 prefixEnd_7240116 := by exact prefixLift 7240116
  have htrace : WordTrace (prefixWord ++ tailWord_7240116) baseStart_7240116 baseEnd_7240116 := by
    simpa [prefixWord, tailWord_7240116, baseEnd_7240116] using wordTrace_append hprefix tailTrace_7240116
  have hstable : (prefixWord ++ tailWord_7240116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240116).length < 2 ^ (prefixWord ++ tailWord_7240116).sum := by decide
  have hdescent : baseEnd_7240116 < baseStart_7240116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240119 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 1, 2, 3]
def baseStart_7240119 : Nat := 118140960795 + 7240119 * 2 ^ 59
def prefixEnd_7240119 : Nat := 4983230072969 + 3 ^ 40 * 7240119 * 2
def baseEnd_7240119 : Nat := 3717661042749663734815805

theorem tailTrace_7240119 : CollatzResearch.WordTrace tailWord_7240119 prefixEnd_7240119 3717661042749663734815805 := by
  unfold tailWord_7240119
  simp only [CollatzResearch.WordTrace]
  refine ⟨264068834057292851726411411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176045889371528567817607607 264068834057292851726411411)
  ·
    refine ⟨396103251085939277589617117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264068834057292851726411411 396103251085939277589617117)
    ·
      refine ⟨148538719157227229096106419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396103251085939277589617117 148538719157227229096106419)
      ·
        refine ⟨222808078735840843644159629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148538719157227229096106419 222808078735840843644159629)
        ·
          refine ⟨83553029525940316366559861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222808078735840843644159629 83553029525940316366559861)
          ·
            refine ⟨7833096518056904659364987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 83553029525940316366559861 7833096518056904659364987)
            ·
              refine ⟨11749644777085356989047481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7833096518056904659364987 11749644777085356989047481)
              ·
                refine ⟨8812233582814017741785611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11749644777085356989047481 8812233582814017741785611)
                ·
                  refine ⟨13218350374221026612678417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8812233582814017741785611 13218350374221026612678417)
                  ·
                    refine ⟨9913762780665769959508813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13218350374221026612678417 9913762780665769959508813)
                    ·
                      refine ⟨3717661042749663734815805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9913762780665769959508813 3717661042749663734815805)
                      ·
                        rfl

theorem cell23_7240119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_7240119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240119 prefixEnd_7240119 := by exact prefixLift 7240119
  have htrace : WordTrace (prefixWord ++ tailWord_7240119) baseStart_7240119 baseEnd_7240119 := by
    simpa [prefixWord, tailWord_7240119, baseEnd_7240119] using wordTrace_append hprefix tailTrace_7240119
  have hstable : (prefixWord ++ tailWord_7240119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240119).length < 2 ^ (prefixWord ++ tailWord_7240119).sum := by decide
  have hdescent : baseEnd_7240119 < baseStart_7240119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240149 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 2, 1, 3]
def baseStart_7240149 : Nat := 118140960795 + 7240149 * 2 ^ 59
def prefixEnd_7240149 : Nat := 4983230072969 + 3 ^ 40 * 7240149 * 2
def baseEnd_7240149 : Nat := 3717676447169298617440667

theorem tailTrace_7240149 : CollatzResearch.WordTrace tailWord_7240149 prefixEnd_7240149 3717676447169298617440667 := by
  unfold tailWord_7240149
  simp only [CollatzResearch.WordTrace]
  refine ⟨264069928247184166850003501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176046618831456111233335667 264069928247184166850003501)
  ·
    refine ⟨99026223092694062568751313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264069928247184166850003501 99026223092694062568751313)
    ·
      refine ⟨74269667319520546926563485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99026223092694062568751313 74269667319520546926563485)
      ·
        refine ⟨27851125244820205097461307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74269667319520546926563485 27851125244820205097461307)
        ·
          refine ⟨41776687867230307646191961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27851125244820205097461307 41776687867230307646191961)
          ·
            refine ⟨31332515900422730734643971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41776687867230307646191961 31332515900422730734643971)
            ·
              refine ⟨46998773850634096101965957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31332515900422730734643971 46998773850634096101965957)
              ·
                refine ⟨8812270096993893019118617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46998773850634096101965957 8812270096993893019118617)
                ·
                  refine ⟨6609202572745419764338963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8812270096993893019118617 6609202572745419764338963)
                  ·
                    refine ⟨9913803859118129646508445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6609202572745419764338963 9913803859118129646508445)
                    ·
                      refine ⟨3717676447169298617440667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9913803859118129646508445 3717676447169298617440667)
                      ·
                        rfl

theorem cell23_7240149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_7240149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240149 prefixEnd_7240149 := by exact prefixLift 7240149
  have htrace : WordTrace (prefixWord ++ tailWord_7240149) baseStart_7240149 baseEnd_7240149 := by
    simpa [prefixWord, tailWord_7240149, baseEnd_7240149] using wordTrace_append hprefix tailTrace_7240149
  have hstable : (prefixWord ++ tailWord_7240149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240149).length < 2 ^ (prefixWord ++ tailWord_7240149).sum := by decide
  have hdescent : baseEnd_7240149 < baseStart_7240149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240175 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 3]
def baseStart_7240175 : Nat := 118140960795 + 7240175 * 2 ^ 59
def prefixEnd_7240175 : Nat := 4983230072969 + 3 ^ 40 * 7240175 * 2
def baseEnd_7240175 : Nat := 3717689797666315515715547

theorem tailTrace_7240175 : CollatzResearch.WordTrace tailWord_7240175 prefixEnd_7240175 3717689797666315515715547 := by
  unfold tailWord_7240175
  simp only [CollatzResearch.WordTrace]
  refine ⟨264070876545089973290449979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176047251030059982193633319 264070876545089973290449979)
  ·
    refine ⟨396106314817634959935674969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264070876545089973290449979 396106314817634959935674969)
    ·
      refine ⟨297079736113226219951756227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396106314817634959935674969 297079736113226219951756227)
      ·
        refine ⟨445619604169839329927634341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297079736113226219951756227 445619604169839329927634341)
        ·
          refine ⟨83553675781844874361431439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445619604169839329927634341 83553675781844874361431439)
          ·
            refine ⟨125330513672767311542147159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83553675781844874361431439 125330513672767311542147159)
            ·
              refine ⟨187995770509150967313220739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125330513672767311542147159 187995770509150967313220739)
              ·
                refine ⟨281993655763726450969831109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187995770509150967313220739 281993655763726450969831109)
                ·
                  refine ⟨52873810455698709556843333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 281993655763726450969831109 52873810455698709556843333)
                  ·
                    refine ⟨9913839460443508041908125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52873810455698709556843333 9913839460443508041908125)
                    ·
                      refine ⟨3717689797666315515715547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9913839460443508041908125 3717689797666315515715547)
                      ·
                        rfl

theorem cell23_7240175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 3].length) (baseStart_7240175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240175 prefixEnd_7240175 := by exact prefixLift 7240175
  have htrace : WordTrace (prefixWord ++ tailWord_7240175) baseStart_7240175 baseEnd_7240175 := by
    simpa [prefixWord, tailWord_7240175, baseEnd_7240175] using wordTrace_append hprefix tailTrace_7240175
  have hstable : (prefixWord ++ tailWord_7240175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240175).length < 2 ^ (prefixWord ++ tailWord_7240175).sum := by decide
  have hdescent : baseEnd_7240175 < baseStart_7240175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240189 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 4, 2, 2]
def baseStart_7240189 : Nat := 118140960795 + 7240189 * 2 ^ 59
def prefixEnd_7240189 : Nat := 4983230072969 + 3 ^ 40 * 7240189 * 2
def baseEnd_7240189 : Nat := 3717696986395478460940483

theorem tailTrace_7240189 : CollatzResearch.WordTrace tailWord_7240189 prefixEnd_7240189 3717696986395478460940483 := by
  unfold tailWord_7240189
  simp only [CollatzResearch.WordTrace]
  refine ⟨264071387167039253681459621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176047591444692835787639747 264071387167039253681459621)
  ·
    refine ⟨49513385093819860065273679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264071387167039253681459621 49513385093819860065273679)
    ·
      refine ⟨74270077640729790097910519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49513385093819860065273679 74270077640729790097910519)
      ·
        refine ⟨111405116461094685146865779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74270077640729790097910519 111405116461094685146865779)
        ·
          refine ⟨167107674691642027720298669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111405116461094685146865779 167107674691642027720298669)
          ·
            refine ⟨62665378009365760395112001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167107674691642027720298669 62665378009365760395112001)
            ·
              refine ⟨46999033507024320296334001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62665378009365760395112001 46999033507024320296334001)
              ·
                refine ⟨35249275130268240222250501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46999033507024320296334001 35249275130268240222250501)
                ·
                  refine ⟨6609239086925295041671969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35249275130268240222250501 6609239086925295041671969)
                  ·
                    refine ⟨4956929315193971281253977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6609239086925295041671969 4956929315193971281253977)
                    ·
                      refine ⟨3717696986395478460940483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956929315193971281253977 3717696986395478460940483)
                      ·
                        rfl

theorem cell23_7240189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_7240189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240189 prefixEnd_7240189 := by exact prefixLift 7240189
  have htrace : WordTrace (prefixWord ++ tailWord_7240189) baseStart_7240189 baseEnd_7240189 := by
    simpa [prefixWord, tailWord_7240189, baseEnd_7240189] using wordTrace_append hprefix tailTrace_7240189
  have hstable : (prefixWord ++ tailWord_7240189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240189).length < 2 ^ (prefixWord ++ tailWord_7240189).sum := by decide
  have hdescent : baseEnd_7240189 < baseStart_7240189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240193 : List Nat := [1, 2, 4, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_7240193 : Nat := 118140960795 + 7240193 * 2 ^ 59
def prefixEnd_7240193 : Nat := 4983230072969 + 3 ^ 40 * 7240193 * 2
def baseEnd_7240193 : Nat := 3717699040318096445290465

theorem tailTrace_7240193 : CollatzResearch.WordTrace tailWord_7240193 prefixEnd_7240193 3717699040318096445290465 := by
  unfold tailWord_7240193
  simp only [CollatzResearch.WordTrace]
  refine ⟨264071533059024762364605233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176047688706016508243070155 264071533059024762364605233)
  ·
    refine ⟨198053649794268571773453925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264071533059024762364605233 198053649794268571773453925)
    ·
      refine ⟨37135059336425357207522611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198053649794268571773453925 37135059336425357207522611)
      ·
        refine ⟨55702589004638035811283917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37135059336425357207522611 55702589004638035811283917)
        ·
          refine ⟨20888470876739263429231469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55702589004638035811283917 20888470876739263429231469)
          ·
            refine ⟨7833176578777223785961801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20888470876739263429231469 7833176578777223785961801)
            ·
              refine ⟨5874882434082917839471351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7833176578777223785961801 5874882434082917839471351)
              ·
                refine ⟨8812323651124376759207027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5874882434082917839471351 8812323651124376759207027)
                ·
                  refine ⟨13218485476686565138810541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8812323651124376759207027 13218485476686565138810541)
                  ·
                    refine ⟨4956932053757461927053953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13218485476686565138810541 4956932053757461927053953)
                    ·
                      refine ⟨3717699040318096445290465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956932053757461927053953 3717699040318096445290465)
                      ·
                        rfl

theorem cell23_7240193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_7240193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240193 prefixEnd_7240193 := by exact prefixLift 7240193
  have htrace : WordTrace (prefixWord ++ tailWord_7240193) baseStart_7240193 baseEnd_7240193 := by
    simpa [prefixWord, tailWord_7240193, baseEnd_7240193] using wordTrace_append hprefix tailTrace_7240193
  have hstable : (prefixWord ++ tailWord_7240193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240193).length < 2 ^ (prefixWord ++ tailWord_7240193).sum := by decide
  have hdescent : baseEnd_7240193 < baseStart_7240193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240206 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2]
def baseStart_7240206 : Nat := 118140960795 + 7240206 * 2 ^ 59
def prefixEnd_7240206 : Nat := 4983230072969 + 3 ^ 40 * 7240206 * 2
def baseEnd_7240206 : Nat := 3717705715566604894427905

theorem tailTrace_7240206 : CollatzResearch.WordTrace tailWord_7240206 prefixEnd_7240206 3717705715566604894427905 := by
  unfold tailWord_7240206
  simp only [CollatzResearch.WordTrace]
  refine ⟨33009000900997208198103559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176048004805318443723218981 33009000900997208198103559)
  ·
    refine ⟨49513501351495812297155339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33009000900997208198103559 49513501351495812297155339)
    ·
      refine ⟨74270252027243718445733009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49513501351495812297155339 74270252027243718445733009)
      ·
        refine ⟨55702689020432788834299757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74270252027243718445733009 55702689020432788834299757)
        ·
          refine ⟨20888508382662295812862409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55702689020432788834299757 20888508382662295812862409)
          ·
            refine ⟨15666381286996721859646807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20888508382662295812862409 15666381286996721859646807)
            ·
              refine ⟨23499571930495082789470211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15666381286996721859646807 23499571930495082789470211)
              ·
                refine ⟨35249357895742624184205317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23499571930495082789470211 35249357895742624184205317)
                ·
                  refine ⟨6609254605451742034538497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35249357895742624184205317 6609254605451742034538497)
                  ·
                    refine ⟨4956940954088806525903873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6609254605451742034538497 4956940954088806525903873)
                    ·
                      refine ⟨3717705715566604894427905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4956940954088806525903873 3717705715566604894427905)
                      ·
                        rfl

theorem cell23_7240206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_7240206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240206 prefixEnd_7240206 := by exact prefixLift 7240206
  have htrace : WordTrace (prefixWord ++ tailWord_7240206) baseStart_7240206 baseEnd_7240206 := by
    simpa [prefixWord, tailWord_7240206, baseEnd_7240206] using wordTrace_append hprefix tailTrace_7240206
  have hstable : (prefixWord ++ tailWord_7240206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240206).length < 2 ^ (prefixWord ++ tailWord_7240206).sum := by decide
  have hdescent : baseEnd_7240206 < baseStart_7240206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240225 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 3, 7]
def baseStart_7240225 : Nat := 118140960795 + 7240225 * 2 ^ 59
def prefixEnd_7240225 : Nat := 4983230072969 + 3 ^ 40 * 7240225 * 2
def baseEnd_7240225 : Nat := 1239238490566346773363439

theorem tailTrace_7240225 : CollatzResearch.WordTrace tailWord_7240225 prefixEnd_7240225 1239238490566346773363439 := by
  unfold tailWord_7240225
  simp only [CollatzResearch.WordTrace]
  refine ⟨264072700194908831829770129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176048466796605887886513419 264072700194908831829770129)
  ·
    refine ⟨198054525146181623872327597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264072700194908831829770129 198054525146181623872327597)
    ·
      refine ⟨74270446929818108952122849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198054525146181623872327597 74270446929818108952122849)
      ·
        refine ⟨55702835197363581714092137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74270446929818108952122849 55702835197363581714092137)
        ·
          refine ⟨41777126398022686285569103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55702835197363581714092137 41777126398022686285569103)
          ·
            refine ⟨62665689597034029428353655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41777126398022686285569103 62665689597034029428353655)
            ·
              refine ⟨93998534395551044142530483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62665689597034029428353655 93998534395551044142530483)
              ·
                refine ⟨140997801593326566213795725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93998534395551044142530483 140997801593326566213795725)
                ·
                  refine ⟨52874175597497462330173397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 140997801593326566213795725 52874175597497462330173397)
                  ·
                    refine ⟨1239238490566346773363439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52874175597497462330173397 1239238490566346773363439)
                    ·
                      rfl

theorem cell23_7240225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_7240225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240225 prefixEnd_7240225 := by exact prefixLift 7240225
  have htrace : WordTrace (prefixWord ++ tailWord_7240225) baseStart_7240225 baseEnd_7240225 := by
    simpa [prefixWord, tailWord_7240225, baseEnd_7240225] using wordTrace_append hprefix tailTrace_7240225
  have hstable : (prefixWord ++ tailWord_7240225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240225).length < 2 ^ (prefixWord ++ tailWord_7240225).sum := by decide
  have hdescent : baseEnd_7240225 < baseStart_7240225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240246 : List Nat := [5, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_7240246 : Nat := 118140960795 + 7240246 * 2 ^ 59
def prefixEnd_7240246 : Nat := 4983230072969 + 3 ^ 40 * 7240246 * 2
def baseEnd_7240246 : Nat := 413080694976976081991969

theorem tailTrace_7240246 : CollatzResearch.WordTrace tailWord_7240246 prefixEnd_7240246 413080694976976081991969 := by
  unfold tailWord_7240246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16504591632989547026017787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176048977418555168277523061 16504591632989547026017787)
  ·
    refine ⟨24756887449484320539026681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16504591632989547026017787 24756887449484320539026681)
    ·
      refine ⟨18567665587113240404270011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24756887449484320539026681 18567665587113240404270011)
      ·
        refine ⟨27851498380669860606405017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18567665587113240404270011 27851498380669860606405017)
        ·
          refine ⟨20888623785502395454803763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27851498380669860606405017 20888623785502395454803763)
          ·
            refine ⟨31332935678253593182205645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20888623785502395454803763 31332935678253593182205645)
            ·
              refine ⟨11749850879345097443327117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31332935678253593182205645 11749850879345097443327117)
              ·
                refine ⟨4406194079754411541247669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11749850879345097443327117 4406194079754411541247669)
                ·
                  refine ⟨413080694976976081991969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4406194079754411541247669 413080694976976081991969)
                  ·
                    rfl

theorem cell23_7240246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_7240246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240246 prefixEnd_7240246 := by exact prefixLift 7240246
  have htrace : WordTrace (prefixWord ++ tailWord_7240246) baseStart_7240246 baseEnd_7240246 := by
    simpa [prefixWord, tailWord_7240246, baseEnd_7240246] using wordTrace_append hprefix tailTrace_7240246
  have hstable : (prefixWord ++ tailWord_7240246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240246).length < 2 ^ (prefixWord ++ tailWord_7240246).sum := by decide
  have hdescent : baseEnd_7240246 < baseStart_7240246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240269 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_7240269 : Nat := 118140960795 + 7240269 * 2 ^ 59
def prefixEnd_7240269 : Nat := 4983230072969 + 3 ^ 40 * 7240269 * 2
def baseEnd_7240269 : Nat := 3717738064847838147940115

theorem tailTrace_7240269 : CollatzResearch.WordTrace tailWord_7240269 prefixEnd_7240269 3717738064847838147940115 := by
  unfold tailWord_7240269
  simp only [CollatzResearch.WordTrace]
  refine ⟨264074305006749427344371861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176049536671166284896247907 264074305006749427344371861)
  ·
    refine ⟨12378483047191379406767431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 264074305006749427344371861 12378483047191379406767431)
    ·
      refine ⟨18567724570787069110151147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12378483047191379406767431 18567724570787069110151147)
      ·
        refine ⟨27851586856180603665226721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18567724570787069110151147 27851586856180603665226721)
        ·
          refine ⟨20888690142135452748920041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27851586856180603665226721 20888690142135452748920041)
          ·
            refine ⟨15666517606601589561690031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20888690142135452748920041 15666517606601589561690031)
            ·
              refine ⟨23499776409902384342535047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15666517606601589561690031 23499776409902384342535047)
              ·
                refine ⟨35249664614853576513802571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23499776409902384342535047 35249664614853576513802571)
                ·
                  refine ⟨52874496922280364770703857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35249664614853576513802571 52874496922280364770703857)
                  ·
                    refine ⟨39655872691710273578027893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52874496922280364770703857 39655872691710273578027893)
                    ·
                      refine ⟨3717738064847838147940115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39655872691710273578027893 3717738064847838147940115)
                      ·
                        rfl

theorem cell23_7240269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_7240269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240269 prefixEnd_7240269 := by exact prefixLift 7240269
  have htrace : WordTrace (prefixWord ++ tailWord_7240269) baseStart_7240269 baseEnd_7240269 := by
    simpa [prefixWord, tailWord_7240269, baseEnd_7240269] using wordTrace_append hprefix tailTrace_7240269
  have hstable : (prefixWord ++ tailWord_7240269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240269).length < 2 ^ (prefixWord ++ tailWord_7240269).sum := by decide
  have hdescent : baseEnd_7240269 < baseStart_7240269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240272 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 3, 4]
def baseStart_7240272 : Nat := 118140960795 + 7240272 * 2 ^ 59
def prefixEnd_7240272 : Nat := 4983230072969 + 3 ^ 40 * 7240272 * 2
def baseEnd_7240272 : Nat := 1239246535096600545400867

theorem tailTrace_7240272 : CollatzResearch.WordTrace tailWord_7240272 prefixEnd_7240272 1239246535096600545400867 := by
  unfold tailWord_7240272
  simp only [CollatzResearch.WordTrace]
  refine ⟨132037207212869279428365535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176049609617159039237820713 132037207212869279428365535)
  ·
    refine ⟨198055810819303919142548303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132037207212869279428365535 198055810819303919142548303)
    ·
      refine ⟨297083716228955878713822455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198055810819303919142548303 297083716228955878713822455)
      ·
        refine ⟨445625574343433818070733683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297083716228955878713822455 445625574343433818070733683)
        ·
          refine ⟨668438361515150727106100525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445625574343433818070733683 668438361515150727106100525)
          ·
            refine ⟨250664385568181522664787697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 668438361515150727106100525 250664385568181522664787697)
            ·
              refine ⟨187998289176136141998590773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250664385568181522664787697 187998289176136141998590773)
              ·
                refine ⟨17624839610262763312367885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187998289176136141998590773 17624839610262763312367885)
                ·
                  refine ⟨6609314853848536242137957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17624839610262763312367885 6609314853848536242137957)
                  ·
                    refine ⟨1239246535096600545400867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6609314853848536242137957 1239246535096600545400867)
                    ·
                      rfl

theorem cell23_7240272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3, 4].length) (baseStart_7240272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240272 prefixEnd_7240272 := by exact prefixLift 7240272
  have htrace : WordTrace (prefixWord ++ tailWord_7240272) baseStart_7240272 baseEnd_7240272 := by
    simpa [prefixWord, tailWord_7240272, baseEnd_7240272] using wordTrace_append hprefix tailTrace_7240272
  have hstable : (prefixWord ++ tailWord_7240272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240272).length < 2 ^ (prefixWord ++ tailWord_7240272).sum := by decide
  have hdescent : baseEnd_7240272 < baseStart_7240272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240296 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_7240296 : Nat := 118140960795 + 7240296 * 2 ^ 59
def prefixEnd_7240296 : Nat := 4983230072969 + 3 ^ 40 * 7240296 * 2
def baseEnd_7240296 : Nat := 3717751928825509542302491

theorem tailTrace_7240296 : CollatzResearch.WordTrace tailWord_7240296 prefixEnd_7240296 3717751928825509542302491 := by
  unfold tailWord_7240296
  simp only [CollatzResearch.WordTrace]
  refine ⟨132037644888825805477802371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176050193185101073970403161 132037644888825805477802371)
  ·
    refine ⟨198056467333238708216703557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132037644888825805477802371 198056467333238708216703557)
    ·
      refine ⟨37135587624982257790631917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198056467333238708216703557 37135587624982257790631917)
      ·
        refine ⟨13925845359368346671486969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37135587624982257790631917 13925845359368346671486969)
        ·
          refine ⟨10444384019526260003615227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13925845359368346671486969 10444384019526260003615227)
          ·
            refine ⟨15666576029289390005422841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444384019526260003615227 15666576029289390005422841)
            ·
              refine ⟨11749932021967042504067131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15666576029289390005422841 11749932021967042504067131)
              ·
                refine ⟨17624898032950563756100697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11749932021967042504067131 17624898032950563756100697)
                ·
                  refine ⟨13218673524712922817075523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17624898032950563756100697 13218673524712922817075523)
                  ·
                    refine ⟨19828010287069384225613285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13218673524712922817075523 19828010287069384225613285)
                    ·
                      refine ⟨3717751928825509542302491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19828010287069384225613285 3717751928825509542302491)
                      ·
                        rfl

theorem cell23_7240296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_7240296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240296 prefixEnd_7240296 := by exact prefixLift 7240296
  have htrace : WordTrace (prefixWord ++ tailWord_7240296) baseStart_7240296 baseEnd_7240296 := by
    simpa [prefixWord, tailWord_7240296, baseEnd_7240296] using wordTrace_append hprefix tailTrace_7240296
  have hstable : (prefixWord ++ tailWord_7240296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240296).length < 2 ^ (prefixWord ++ tailWord_7240296).sum := by decide
  have hdescent : baseEnd_7240296 < baseStart_7240296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240305 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_7240305 : Nat := 118140960795 + 7240305 * 2 ^ 59
def prefixEnd_7240305 : Nat := 4983230072969 + 3 ^ 40 * 7240305 * 2
def baseEnd_7240305 : Nat := 3717756550151400007089949

theorem tailTrace_7240305 : CollatzResearch.WordTrace tailWord_7240305 prefixEnd_7240305 3717756550151400007089949 := by
  unfold tailWord_7240305
  simp only [CollatzResearch.WordTrace]
  refine ⟨264075618034619005492682369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176050412023079336995121579 264075618034619005492682369)
  ·
    refine ⟨198056713525964254119511777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264075618034619005492682369 198056713525964254119511777)
    ·
      refine ⟨148542535144473190589633833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198056713525964254119511777 148542535144473190589633833)
      ·
        refine ⟨111406901358354892942225375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148542535144473190589633833 111406901358354892942225375)
        ·
          refine ⟨167110352037532339413338063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111406901358354892942225375 167110352037532339413338063)
          ·
            refine ⟨250665528056298509120007095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167110352037532339413338063 250665528056298509120007095)
            ·
              refine ⟨375998292084447763680010643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250665528056298509120007095 375998292084447763680010643)
              ·
                refine ⟨563997438126671645520015965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375998292084447763680010643 563997438126671645520015965)
                ·
                  refine ⟨211499039297501867070005987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 563997438126671645520015965 211499039297501867070005987)
                  ·
                    refine ⟨317248558946252800605008981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 211499039297501867070005987 317248558946252800605008981)
                    ·
                      refine ⟨3717756550151400007089949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 317248558946252800605008981 3717756550151400007089949)
                      ·
                        rfl

theorem cell23_7240305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_7240305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240305 prefixEnd_7240305 := by exact prefixLift 7240305
  have htrace : WordTrace (prefixWord ++ tailWord_7240305) baseStart_7240305 baseEnd_7240305 := by
    simpa [prefixWord, tailWord_7240305, baseEnd_7240305] using wordTrace_append hprefix tailTrace_7240305
  have hstable : (prefixWord ++ tailWord_7240305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240305).length < 2 ^ (prefixWord ++ tailWord_7240305).sum := by decide
  have hdescent : baseEnd_7240305 < baseStart_7240305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240329 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 3, 1, 3]
def baseStart_7240329 : Nat := 118140960795 + 7240329 * 2 ^ 59
def prefixEnd_7240329 : Nat := 4983230072969 + 3 ^ 40 * 7240329 * 2
def baseEnd_7240329 : Nat := 3717768873687107913189839

theorem tailTrace_7240329 : CollatzResearch.WordTrace tailWord_7240329 prefixEnd_7240329 3717768873687107913189839 := by
  unfold tailWord_7240329
  simp only [CollatzResearch.WordTrace]
  refine ⟨264076493386532057591556041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176050995591021371727704027 264076493386532057591556041)
  ·
    refine ⟨198057370039899043193667031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264076493386532057591556041 198057370039899043193667031)
    ·
      refine ⟨297086055059848564790500547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198057370039899043193667031 297086055059848564790500547)
      ·
        refine ⟨445629082589772847185750821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297086055059848564790500547 445629082589772847185750821)
        ·
          refine ⟨83555452985582408847328279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 445629082589772847185750821 83555452985582408847328279)
          ·
            refine ⟨125333179478373613270992419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83555452985582408847328279 125333179478373613270992419)
            ·
              refine ⟨187999769217560419906488629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125333179478373613270992419 187999769217560419906488629)
              ·
                refine ⟨17624978364146289366233309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 187999769217560419906488629 17624978364146289366233309)
                ·
                  refine ⟨6609366886554858512337491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17624978364146289366233309 6609366886554858512337491)
                  ·
                    refine ⟨9914050329832287768506237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6609366886554858512337491 9914050329832287768506237)
                    ·
                      refine ⟨3717768873687107913189839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9914050329832287768506237 3717768873687107913189839)
                      ·
                        rfl

theorem cell23_7240329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 1, 3].length) (baseStart_7240329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240329 prefixEnd_7240329 := by exact prefixLift 7240329
  have htrace : WordTrace (prefixWord ++ tailWord_7240329) baseStart_7240329 baseEnd_7240329 := by
    simpa [prefixWord, tailWord_7240329, baseEnd_7240329] using wordTrace_append hprefix tailTrace_7240329
  have hstable : (prefixWord ++ tailWord_7240329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240329).length < 2 ^ (prefixWord ++ tailWord_7240329).sum := by decide
  have hdescent : baseEnd_7240329 < baseStart_7240329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240396 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 1, 6]
def baseStart_7240396 : Nat := 118140960795 + 7240396 * 2 ^ 59
def prefixEnd_7240396 : Nat := 4983230072969 + 3 ^ 40 * 7240396 * 2
def baseEnd_7240396 : Nat := 1239267758963653050350677

theorem tailTrace_7240396 : CollatzResearch.WordTrace tailWord_7240396 prefixEnd_7240396 1239267758963653050350677 := by
  unfold tailWord_7240396
  simp only [CollatzResearch.WordTrace]
  refine ⟨132039468538644664017122521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176052624718192885356163361 132039468538644664017122521)
  ·
    refine ⟨99029601403983498012841891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132039468538644664017122521 99029601403983498012841891)
    ·
      refine ⟨148544402105975247019262837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99029601403983498012841891 148544402105975247019262837)
      ·
        refine ⟨13926037697435179408055891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148544402105975247019262837 13926037697435179408055891)
        ·
          refine ⟨20889056546152769112083837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13926037697435179408055891 20889056546152769112083837)
          ·
            refine ⟨7833396204807288417031439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20889056546152769112083837 7833396204807288417031439)
            ·
              refine ⟨11750094307210932625547159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7833396204807288417031439 11750094307210932625547159)
              ·
                refine ⟨17625141460816398938320739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11750094307210932625547159 17625141460816398938320739)
                ·
                  refine ⟨26437712191224598407481109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17625141460816398938320739 26437712191224598407481109)
                  ·
                    refine ⟨1239267758963653050350677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26437712191224598407481109 1239267758963653050350677)
                    ·
                      rfl

theorem cell23_7240396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_7240396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240396 prefixEnd_7240396 := by exact prefixLift 7240396
  have htrace : WordTrace (prefixWord ++ tailWord_7240396) baseStart_7240396 baseEnd_7240396 := by
    simpa [prefixWord, tailWord_7240396, baseEnd_7240396] using wordTrace_append hprefix tailTrace_7240396
  have hstable : (prefixWord ++ tailWord_7240396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240396).length < 2 ^ (prefixWord ++ tailWord_7240396).sum := by decide
  have hdescent : baseEnd_7240396 < baseStart_7240396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240420 : List Nat := [2, 3, 1, 1, 1, 4, 3, 3, 1, 2, 2]
def baseStart_7240420 : Nat := 118140960795 + 7240420 * 2 ^ 59
def prefixEnd_7240420 : Nat := 4983230072969 + 3 ^ 40 * 7240420 * 2
def baseEnd_7240420 : Nat := 3717815600426667057151921

theorem tailTrace_7240420 : CollatzResearch.WordTrace tailWord_7240420 prefixEnd_7240420 3717815600426667057151921 := by
  unfold tailWord_7240420
  simp only [CollatzResearch.WordTrace]
  refine ⟨132039906214601190066559357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176053208286134920088745809 132039906214601190066559357)
  ·
    refine ⟨49514964830475446274959759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132039906214601190066559357 49514964830475446274959759)
    ·
      refine ⟨74272447245713169412439639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49514964830475446274959759 74272447245713169412439639)
      ·
        refine ⟨111408670868569754118659459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74272447245713169412439639 111408670868569754118659459)
        ·
          refine ⟨167113006302854631177989189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111408670868569754118659459 167113006302854631177989189)
          ·
            refine ⟨31333688681785243345872973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167113006302854631177989189 31333688681785243345872973)
            ·
              refine ⟨11750133255669466254702365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31333688681785243345872973 11750133255669466254702365)
              ·
                refine ⟨4406299970876049845513387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11750133255669466254702365 4406299970876049845513387)
                ·
                  refine ⟨6609449956314074768270081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406299970876049845513387 6609449956314074768270081)
                  ·
                    refine ⟨4957087467235556076202561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6609449956314074768270081 4957087467235556076202561)
                    ·
                      refine ⟨3717815600426667057151921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4957087467235556076202561 3717815600426667057151921)
                      ·
                        rfl

theorem cell23_7240420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_7240420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240420 prefixEnd_7240420 := by exact prefixLift 7240420
  have htrace : WordTrace (prefixWord ++ tailWord_7240420) baseStart_7240420 baseEnd_7240420 := by
    simpa [prefixWord, tailWord_7240420, baseEnd_7240420] using wordTrace_append hprefix tailTrace_7240420
  have hstable : (prefixWord ++ tailWord_7240420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240420).length < 2 ^ (prefixWord ++ tailWord_7240420).sum := by decide
  have hdescent : baseEnd_7240420 < baseStart_7240420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240432 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_7240432 : Nat := 118140960795 + 7240432 * 2 ^ 59
def prefixEnd_7240432 : Nat := 4983230072969 + 3 ^ 40 * 7240432 * 2
def baseEnd_7240432 : Nat := 3717821762194521010201865

theorem tailTrace_7240432 : CollatzResearch.WordTrace tailWord_7240432 prefixEnd_7240432 3717821762194521010201865 := by
  unfold tailWord_7240432
  simp only [CollatzResearch.WordTrace]
  refine ⟨132040125052579453091277775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176053500070105937455037033 132040125052579453091277775)
  ·
    refine ⟨198060187578869179636916663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132040125052579453091277775 198060187578869179636916663)
    ·
      refine ⟨297090281368303769455374995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198060187578869179636916663 297090281368303769455374995)
      ·
        refine ⟨445635422052455654183062493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297090281368303769455374995 445635422052455654183062493)
        ·
          refine ⟨167113283269670870318648435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445635422052455654183062493 167113283269670870318648435)
          ·
            refine ⟨250669924904506305477972653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167113283269670870318648435 250669924904506305477972653)
            ·
              refine ⟨94001221839189864554239745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250669924904506305477972653 94001221839189864554239745)
              ·
                refine ⟨70500916379392398415679809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94001221839189864554239745 70500916379392398415679809)
                ·
                  refine ⟨52875687284544298811759857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70500916379392398415679809 52875687284544298811759857)
                  ·
                    refine ⟨39656765463408224108819893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52875687284544298811759857 39656765463408224108819893)
                    ·
                      refine ⟨3717821762194521010201865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39656765463408224108819893 3717821762194521010201865)
                      ·
                        rfl

theorem cell23_7240432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_7240432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240432 prefixEnd_7240432 := by exact prefixLift 7240432
  have htrace : WordTrace (prefixWord ++ tailWord_7240432) baseStart_7240432 baseEnd_7240432 := by
    simpa [prefixWord, tailWord_7240432, baseEnd_7240432] using wordTrace_append hprefix tailTrace_7240432
  have hstable : (prefixWord ++ tailWord_7240432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240432).length < 2 ^ (prefixWord ++ tailWord_7240432).sum := by decide
  have hdescent : baseEnd_7240432 < baseStart_7240432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240476 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_7240476 : Nat := 118140960795 + 7240476 * 2 ^ 59
def prefixEnd_7240476 : Nat := 4983230072969 + 3 ^ 40 * 7240476 * 2
def baseEnd_7240476 : Nat := 3717844355343318838051663

theorem tailTrace_7240476 : CollatzResearch.WordTrace tailWord_7240476 prefixEnd_7240476 3717844355343318838051663 := by
  unfold tailWord_7240476
  simp only [CollatzResearch.WordTrace]
  refine ⟨132040927458499750848578641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176054569944666334464771521 132040927458499750848578641)
  ·
    refine ⟨99030695593874813136433981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132040927458499750848578641 99030695593874813136433981)
    ·
      refine ⟨37136510847703054926162743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99030695593874813136433981 37136510847703054926162743)
      ·
        refine ⟨55704766271554582389244115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37136510847703054926162743 55704766271554582389244115)
        ·
          refine ⟨83557149407331873583866173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55704766271554582389244115 83557149407331873583866173)
          ·
            refine ⟨31333931027749452593949815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83557149407331873583866173 31333931027749452593949815)
            ·
              refine ⟨47000896541624178890924723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31333931027749452593949815 47000896541624178890924723)
              ·
                refine ⟨70501344812436268336387085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47000896541624178890924723 70501344812436268336387085)
                ·
                  refine ⟨26438004304663600626145157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70501344812436268336387085 26438004304663600626145157)
                  ·
                    refine ⟨4957125807124425117402217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26438004304663600626145157 4957125807124425117402217)
                    ·
                      refine ⟨3717844355343318838051663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4957125807124425117402217 3717844355343318838051663)
                      ·
                        rfl

theorem cell23_7240476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_7240476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240476 prefixEnd_7240476 := by exact prefixLift 7240476
  have htrace : WordTrace (prefixWord ++ tailWord_7240476) baseStart_7240476 baseEnd_7240476 := by
    simpa [prefixWord, tailWord_7240476, baseEnd_7240476] using wordTrace_append hprefix tailTrace_7240476
  have hstable : (prefixWord ++ tailWord_7240476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240476).length < 2 ^ (prefixWord ++ tailWord_7240476).sum := by decide
  have hdescent : baseEnd_7240476 < baseStart_7240476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240479 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 5]
def baseStart_7240479 : Nat := 118140960795 + 7240479 * 2 ^ 59
def prefixEnd_7240479 : Nat := 4983230072969 + 3 ^ 40 * 7240479 * 2
def baseEnd_7240479 : Nat := 3717845895785282326314149

theorem tailTrace_7240479 : CollatzResearch.WordTrace tailWord_7240479 prefixEnd_7240479 3717845895785282326314149 := by
  unfold tailWord_7240479
  simp only [CollatzResearch.WordTrace]
  refine ⟨264081964335988633209516491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176054642890659088806344327 264081964335988633209516491)
  ·
    refine ⟨396122946503982949814274737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264081964335988633209516491 396122946503982949814274737)
    ·
      refine ⟨297092209877987212360706053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396122946503982949814274737 297092209877987212360706053)
      ·
        refine ⟨55704789352122602317632385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297092209877987212360706053 55704789352122602317632385)
        ·
          refine ⟨41778592014091951738224289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55704789352122602317632385 41778592014091951738224289)
          ·
            refine ⟨31333944010568963803668217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41778592014091951738224289 31333944010568963803668217)
            ·
              refine ⟨23500458007926722852751163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31333944010568963803668217 23500458007926722852751163)
              ·
                refine ⟨35250687011890084279126745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23500458007926722852751163 35250687011890084279126745)
                ·
                  refine ⟨26438015258917563209345059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35250687011890084279126745 26438015258917563209345059)
                  ·
                    refine ⟨39657022888376344814017589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26438015258917563209345059 39657022888376344814017589)
                    ·
                      refine ⟨3717845895785282326314149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39657022888376344814017589 3717845895785282326314149)
                      ·
                        rfl

theorem cell23_7240479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_7240479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240479 prefixEnd_7240479 := by exact prefixLift 7240479
  have htrace : WordTrace (prefixWord ++ tailWord_7240479) baseStart_7240479 baseEnd_7240479 := by
    simpa [prefixWord, tailWord_7240479, baseEnd_7240479] using wordTrace_append hprefix tailTrace_7240479
  have hstable : (prefixWord ++ tailWord_7240479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240479).length < 2 ^ (prefixWord ++ tailWord_7240479).sum := by decide
  have hdescent : baseEnd_7240479 < baseStart_7240479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240480 : List Nat := [2, 1, 1, 5, 1, 3, 3, 1, 1, 3, 2]
def baseStart_7240480 : Nat := 118140960795 + 7240480 * 2 ^ 59
def prefixEnd_7240480 : Nat := 4983230072969 + 3 ^ 40 * 7240480 * 2
def baseEnd_7240480 : Nat := 3717846409265936822401645

theorem tailTrace_7240480 : CollatzResearch.WordTrace tailWord_7240480 prefixEnd_7240480 3717846409265936822401645 := by
  unfold tailWord_7240480
  simp only [CollatzResearch.WordTrace]
  refine ⟨132041000404492505190151447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176054667205990006920201929 132041000404492505190151447)
  ·
    refine ⟨198061500606738757785227171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132041000404492505190151447 198061500606738757785227171)
    ·
      refine ⟨297092250910108136677840757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198061500606738757785227171 297092250910108136677840757)
      ·
        refine ⟨27852398522822637813547571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 297092250910108136677840757 27852398522822637813547571)
        ·
          refine ⟨41778597784233956720321357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27852398522822637813547571 41778597784233956720321357)
          ·
            refine ⟨15666974169087733770120509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41778597784233956720321357 15666974169087733770120509)
            ·
              refine ⟨5875115313407900163795191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15666974169087733770120509 5875115313407900163795191)
              ·
                refine ⟨8812672970111850245692787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5875115313407900163795191 8812672970111850245692787)
                ·
                  refine ⟨13219009455167775368539181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8812672970111850245692787 13219009455167775368539181)
                  ·
                    refine ⟨4957128545687915763202193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13219009455167775368539181 4957128545687915763202193)
                    ·
                      refine ⟨3717846409265936822401645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4957128545687915763202193 3717846409265936822401645)
                      ·
                        rfl

theorem cell23_7240480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_7240480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240480 prefixEnd_7240480 := by exact prefixLift 7240480
  have htrace : WordTrace (prefixWord ++ tailWord_7240480) baseStart_7240480 baseEnd_7240480 := by
    simpa [prefixWord, tailWord_7240480, baseEnd_7240480] using wordTrace_append hprefix tailTrace_7240480
  have hstable : (prefixWord ++ tailWord_7240480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240480).length < 2 ^ (prefixWord ++ tailWord_7240480).sum := by decide
  have hdescent : baseEnd_7240480 < baseStart_7240480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240506 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4]
def baseStart_7240506 : Nat := 118140960795 + 7240506 * 2 ^ 59
def prefixEnd_7240506 : Nat := 4983230072969 + 3 ^ 40 * 7240506 * 2
def baseEnd_7240506 : Nat := 3717859759762953720676525

theorem tailTrace_7240506 : CollatzResearch.WordTrace tailWord_7240506 prefixEnd_7240506 3717859759762953720676525 := by
  unfold tailWord_7240506
  simp only [CollatzResearch.WordTrace]
  refine ⟨66020737276722704205187343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176055299404593877880499581 66020737276722704205187343)
  ·
    refine ⟨99031105915084056307781015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66020737276722704205187343 99031105915084056307781015)
    ·
      refine ⟨148546658872626084461671523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99031105915084056307781015 148546658872626084461671523)
      ·
        refine ⟨222819988308939126692507285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148546658872626084461671523 222819988308939126692507285)
        ·
          refine ⟨10444686951981521563711279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 222819988308939126692507285 10444686951981521563711279)
          ·
            refine ⟨15667030427972282345566919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444686951981521563711279 15667030427972282345566919)
            ·
              refine ⟨23500545641958423518350379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15667030427972282345566919 23500545641958423518350379)
              ·
                refine ⟨35250818462937635277525569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23500545641958423518350379 35250818462937635277525569)
                ·
                  refine ⟨26438113847203226458144177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35250818462937635277525569 26438113847203226458144177)
                  ·
                    refine ⟨19828585385402419843608133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26438113847203226458144177 19828585385402419843608133)
                    ·
                      refine ⟨3717859759762953720676525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19828585385402419843608133 3717859759762953720676525)
                      ·
                        rfl

theorem cell23_7240506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_7240506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240506 prefixEnd_7240506 := by exact prefixLift 7240506
  have htrace : WordTrace (prefixWord ++ tailWord_7240506) baseStart_7240506 baseEnd_7240506 := by
    simpa [prefixWord, tailWord_7240506, baseEnd_7240506] using wordTrace_append hprefix tailTrace_7240506
  have hstable : (prefixWord ++ tailWord_7240506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240506).length < 2 ^ (prefixWord ++ tailWord_7240506).sum := by decide
  have hdescent : baseEnd_7240506 < baseStart_7240506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240510 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 1, 4, 2]
def baseStart_7240510 : Nat := 118140960795 + 7240510 * 2 ^ 59
def prefixEnd_7240510 : Nat := 4983230072969 + 3 ^ 40 * 7240510 * 2
def baseEnd_7240510 : Nat := 3717861813685571705026507

theorem tailTrace_7240510 : CollatzResearch.WordTrace tailWord_7240510 prefixEnd_7240510 3717861813685571705026507 := by
  unfold tailWord_7240510
  simp only [CollatzResearch.WordTrace]
  refine ⟨33010386874859540687986873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176055396665917550335929989 33010386874859540687986873)
  ·
    refine ⟨24757790156144655515990155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33010386874859540687986873 24757790156144655515990155)
    ·
      refine ⟨37136685234216983273985233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24757790156144655515990155 37136685234216983273985233)
      ·
        refine ⟨27852513925662737455488925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37136685234216983273985233 27852513925662737455488925)
        ·
          refine ⟨10444692722123526545808347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27852513925662737455488925 10444692722123526545808347)
          ·
            refine ⟨15667039083185289818712521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10444692722123526545808347 15667039083185289818712521)
            ·
              refine ⟨11750279312388967364034391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15667039083185289818712521 11750279312388967364034391)
              ·
                refine ⟨17625418968583451046051587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11750279312388967364034391 17625418968583451046051587)
                ·
                  refine ⟨26438128452875176569077381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17625418968583451046051587 26438128452875176569077381)
                  ·
                    refine ⟨4957149084914095606702009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26438128452875176569077381 4957149084914095606702009)
                    ·
                      refine ⟨3717861813685571705026507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4957149084914095606702009 3717861813685571705026507)
                      ·
                        rfl

theorem cell23_7240510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_7240510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240510 prefixEnd_7240510 := by exact prefixLift 7240510
  have htrace : WordTrace (prefixWord ++ tailWord_7240510) baseStart_7240510 baseEnd_7240510 := by
    simpa [prefixWord, tailWord_7240510, baseEnd_7240510] using wordTrace_append hprefix tailTrace_7240510
  have hstable : (prefixWord ++ tailWord_7240510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240510).length < 2 ^ (prefixWord ++ tailWord_7240510).sum := by decide
  have hdescent : baseEnd_7240510 < baseStart_7240510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240579 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 4]
def baseStart_7240579 : Nat := 118140960795 + 7240579 * 2 ^ 59
def prefixEnd_7240579 : Nat := 4983230072969 + 3 ^ 40 * 7240579 * 2
def baseEnd_7240579 : Nat := 3717897243850731935063689

theorem tailTrace_7240579 : CollatzResearch.WordTrace tailWord_7240579 prefixEnd_7240579 3717897243850731935063689 := by
  unfold tailWord_7240579
  simp only [CollatzResearch.WordTrace]
  refine ⟨264085611635626350288156791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176057074423750900192104527 264085611635626350288156791)
  ·
    refine ⟨396128417453439525432235187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264085611635626350288156791 396128417453439525432235187)
    ·
      refine ⟨594192626180159288148352781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396128417453439525432235187 594192626180159288148352781)
      ·
        refine ⟨222822234817559733055632293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594192626180159288148352781 222822234817559733055632293)
        ·
          refine ⟨41779169028292449947931055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 222822234817559733055632293 41779169028292449947931055)
          ·
            refine ⟨62668753542438674921896583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41779169028292449947931055 62668753542438674921896583)
            ·
              refine ⟨94003130313658012382844875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62668753542438674921896583 94003130313658012382844875)
              ·
                refine ⟨141004695470487018574267313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94003130313658012382844875 141004695470487018574267313)
                ·
                  refine ⟨105753521602865263930700485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141004695470487018574267313 105753521602865263930700485)
                  ·
                    refine ⟨19828785300537236987006341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 105753521602865263930700485 19828785300537236987006341)
                    ·
                      refine ⟨3717897243850731935063689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19828785300537236987006341 3717897243850731935063689)
                      ·
                        rfl

theorem cell23_7240579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_7240579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240579 prefixEnd_7240579 := by exact prefixLift 7240579
  have htrace : WordTrace (prefixWord ++ tailWord_7240579) baseStart_7240579 baseEnd_7240579 := by
    simpa [prefixWord, tailWord_7240579, baseEnd_7240579] using wordTrace_append hprefix tailTrace_7240579
  have hstable : (prefixWord ++ tailWord_7240579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240579).length < 2 ^ (prefixWord ++ tailWord_7240579).sum := by decide
  have hdescent : baseEnd_7240579 < baseStart_7240579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240610 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_7240610 : Nat := 118140960795 + 7240610 * 2 ^ 59
def prefixEnd_7240610 : Nat := 4983230072969 + 3 ^ 40 * 7240610 * 2
def baseEnd_7240610 : Nat := 1239304387250340437925349

theorem tailTrace_7240610 : CollatzResearch.WordTrace tailWord_7240610 prefixEnd_7240610 1239304387250340437925349 := by
  unfold tailWord_7240610
  simp only [CollatzResearch.WordTrace]
  refine ⟨66021685574628510645633821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176057828199009361721690189 66021685574628510645633821)
  ·
    refine ⟨24758132090485691492112683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66021685574628510645633821 24758132090485691492112683)
    ·
      refine ⟨37137198135728537238169025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24758132090485691492112683 37137198135728537238169025)
      ·
        refine ⟨27852898601796402928626769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37137198135728537238169025 27852898601796402928626769)
        ·
          refine ⟨20889673951347302196470077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27852898601796402928626769 20889673951347302196470077)
          ·
            refine ⟨7833627731755238323676279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20889673951347302196470077 7833627731755238323676279)
            ·
              refine ⟨11750441597632857485514419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7833627731755238323676279 11750441597632857485514419)
              ·
                refine ⟨17625662396449286228271629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11750441597632857485514419 17625662396449286228271629)
                ·
                  refine ⟨6609623398668482335601861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17625662396449286228271629 6609623398668482335601861)
                  ·
                    refine ⟨1239304387250340437925349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6609623398668482335601861 1239304387250340437925349)
                    ·
                      rfl

theorem cell23_7240610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_7240610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240610 prefixEnd_7240610 := by exact prefixLift 7240610
  have htrace : WordTrace (prefixWord ++ tailWord_7240610) baseStart_7240610 baseEnd_7240610 := by
    simpa [prefixWord, tailWord_7240610, baseEnd_7240610] using wordTrace_append hprefix tailTrace_7240610
  have hstable : (prefixWord ++ tailWord_7240610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240610).length < 2 ^ (prefixWord ++ tailWord_7240610).sum := by decide
  have hdescent : baseEnd_7240610 < baseStart_7240610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240619 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 5, 5]
def baseStart_7240619 : Nat := 118140960795 + 7240619 * 2 ^ 59
def prefixEnd_7240619 : Nat := 4983230072969 + 3 ^ 40 * 7240619 * 2
def baseEnd_7240619 : Nat := 1239305927692303926187835

theorem tailTrace_7240619 : CollatzResearch.WordTrace tailWord_7240619 prefixEnd_7240619 1239305927692303926187835 := by
  unfold tailWord_7240619
  simp only [CollatzResearch.WordTrace]
  refine ⟨264087070555481437119612911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176058047036987624746408607 264087070555481437119612911)
  ·
    refine ⟨396130605833222155679419367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264087070555481437119612911 396130605833222155679419367)
    ·
      refine ⟨594195908749833233519129051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396130605833222155679419367 594195908749833233519129051)
      ·
        refine ⟨891293863124749850278693577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594195908749833233519129051 891293863124749850278693577)
        ·
          refine ⟨668470397343562387709020183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 891293863124749850278693577 668470397343562387709020183)
          ·
            refine ⟨1002705596015343581563530275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668470397343562387709020183 1002705596015343581563530275)
            ·
              refine ⟨1504058394023015372345295413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002705596015343581563530275 1504058394023015372345295413)
              ·
                refine ⟨141005474439657691157371445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1504058394023015372345295413 141005474439657691157371445)
                ·
                  refine ⟨13219263228717908546003573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141005474439657691157371445 13219263228717908546003573)
                  ·
                    refine ⟨1239305927692303926187835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13219263228717908546003573 1239305927692303926187835)
                    ·
                      rfl

theorem cell23_7240619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 5].length) (baseStart_7240619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240619 prefixEnd_7240619 := by exact prefixLift 7240619
  have htrace : WordTrace (prefixWord ++ tailWord_7240619) baseStart_7240619 baseEnd_7240619 := by
    simpa [prefixWord, tailWord_7240619, baseEnd_7240619] using wordTrace_append hprefix tailTrace_7240619
  have hstable : (prefixWord ++ tailWord_7240619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240619).length < 2 ^ (prefixWord ++ tailWord_7240619).sum := by decide
  have hdescent : baseEnd_7240619 < baseStart_7240619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240650 : List Nat := [3, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3]
def baseStart_7240650 : Nat := 118140960795 + 7240650 * 2 ^ 59
def prefixEnd_7240650 : Nat := 4983230072969 + 3 ^ 40 * 7240650 * 2
def baseEnd_7240650 : Nat := 3717933700977201157275863

theorem tailTrace_7240650 : CollatzResearch.WordTrace tailWord_7240650 prefixEnd_7240650 3717933700977201157275863 := by
  unfold tailWord_7240650
  simp only [CollatzResearch.WordTrace]
  refine ⟨66022050304592282353497851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176058800812246086275994269 66022050304592282353497851)
  ·
    refine ⟨99033075456888423530246777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66022050304592282353497851 99033075456888423530246777)
    ·
      refine ⟨74274806592666317647685083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99033075456888423530246777 74274806592666317647685083)
      ·
        refine ⟨111412209888999476471527625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74274806592666317647685083 111412209888999476471527625)
        ·
          refine ⟨83559157416749607353645719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111412209888999476471527625 83559157416749607353645719)
          ·
            refine ⟨125338736125124411030468579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83559157416749607353645719 125338736125124411030468579)
            ·
              refine ⟨188008104187686616545702869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125338736125124411030468579 188008104187686616545702869)
              ·
                refine ⟨4406439941898905075289911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 188008104187686616545702869 4406439941898905075289911)
                ·
                  refine ⟨6609659912848357612934867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406439941898905075289911 6609659912848357612934867)
                  ·
                    refine ⟨9914489869272536419402301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6609659912848357612934867 9914489869272536419402301)
                    ·
                      refine ⟨3717933700977201157275863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9914489869272536419402301 3717933700977201157275863)
                      ·
                        rfl

theorem cell23_7240650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_7240650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240650 prefixEnd_7240650 := by exact prefixLift 7240650
  have htrace : WordTrace (prefixWord ++ tailWord_7240650) baseStart_7240650 baseEnd_7240650 := by
    simpa [prefixWord, tailWord_7240650, baseEnd_7240650] using wordTrace_append hprefix tailTrace_7240650
  have hstable : (prefixWord ++ tailWord_7240650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240650).length < 2 ^ (prefixWord ++ tailWord_7240650).sum := by decide
  have hdescent : baseEnd_7240650 < baseStart_7240650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240660 : List Nat := [2, 4, 1, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_7240660 : Nat := 118140960795 + 7240660 * 2 ^ 59
def prefixEnd_7240660 : Nat := 4983230072969 + 3 ^ 40 * 7240660 * 2
def baseEnd_7240660 : Nat := 3717938835783746118150817

theorem tailTrace_7240660 : CollatzResearch.WordTrace tailWord_7240660 prefixEnd_7240660 3717938835783746118150817 := by
  unfold tailWord_7240660
  simp only [CollatzResearch.WordTrace]
  refine ⟨132044282974166450560927717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176059043965555267414570289 132044282974166450560927717)
  ·
    refine ⟨24758303057656209480173947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132044282974166450560927717 24758303057656209480173947)
    ·
      refine ⟨37137454586484314220260921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24758303057656209480173947 37137454586484314220260921)
      ·
        refine ⟨27853090939863235665195691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37137454586484314220260921 27853090939863235665195691)
        ·
          refine ⟨41779636409794853497793537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27853090939863235665195691 41779636409794853497793537)
          ·
            refine ⟨31334727307346140123345153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41779636409794853497793537 31334727307346140123345153)
            ·
              refine ⟨23501045480509605092508865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31334727307346140123345153 23501045480509605092508865)
              ·
                refine ⟨17625784110382203819381649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23501045480509605092508865 17625784110382203819381649)
                ·
                  refine ⟨13219338082786652864536237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17625784110382203819381649 13219338082786652864536237)
                  ·
                    refine ⟨4957251781044994824201089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13219338082786652864536237 4957251781044994824201089)
                    ·
                      refine ⟨3717938835783746118150817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4957251781044994824201089 3717938835783746118150817)
                      ·
                        rfl

theorem cell23_7240660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_7240660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240660 prefixEnd_7240660 := by exact prefixLift 7240660
  have htrace : WordTrace (prefixWord ++ tailWord_7240660) baseStart_7240660 baseEnd_7240660 := by
    simpa [prefixWord, tailWord_7240660, baseEnd_7240660] using wordTrace_append hprefix tailTrace_7240660
  have hstable : (prefixWord ++ tailWord_7240660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240660).length < 2 ^ (prefixWord ++ tailWord_7240660).sum := by decide
  have hdescent : baseEnd_7240660 < baseStart_7240660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240740 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_7240740 : Nat := 118140960795 + 7240740 * 2 ^ 59
def prefixEnd_7240740 : Nat := 4983230072969 + 3 ^ 40 * 7240740 * 2
def baseEnd_7240740 : Nat := 3717979914236105805150449

theorem tailTrace_7240740 : CollatzResearch.WordTrace tailWord_7240740 prefixEnd_7240740 3717979914236105805150449 := by
  unfold tailWord_7240740
  simp only [CollatzResearch.WordTrace]
  refine ⟨132045741894021537392383837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176060989192028716523178449 132045741894021537392383837)
  ·
    refine ⟨49517153210258076522143939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132045741894021537392383837 49517153210258076522143939)
    ·
      refine ⟨74275729815387114783215909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49517153210258076522143939 74275729815387114783215909)
      ·
        refine ⟨13926699340385084021852983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74275729815387114783215909 13926699340385084021852983)
        ·
          refine ⟨20890049010577626032779475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13926699340385084021852983 20890049010577626032779475)
          ·
            refine ⟨31335073515866439049169213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20890049010577626032779475 31335073515866439049169213)
            ·
              refine ⟨11750652568449914643438455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31335073515866439049169213 11750652568449914643438455)
              ·
                refine ⟨17625978852674871965157683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11750652568449914643438455 17625978852674871965157683)
                ·
                  refine ⟨26438968279012307947736525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17625978852674871965157683 26438968279012307947736525)
                  ·
                    refine ⟨9914613104629615480401197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26438968279012307947736525 9914613104629615480401197)
                    ·
                      refine ⟨3717979914236105805150449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9914613104629615480401197 3717979914236105805150449)
                      ·
                        rfl

theorem cell23_7240740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_7240740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240740 prefixEnd_7240740 := by exact prefixLift 7240740
  have htrace : WordTrace (prefixWord ++ tailWord_7240740) baseStart_7240740 baseEnd_7240740 := by
    simpa [prefixWord, tailWord_7240740, baseEnd_7240740] using wordTrace_append hprefix tailTrace_7240740
  have hstable : (prefixWord ++ tailWord_7240740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240740).length < 2 ^ (prefixWord ++ tailWord_7240740).sum := by decide
  have hdescent : baseEnd_7240740 < baseStart_7240740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240873 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 8, 2, 3]
def baseStart_7240873 : Nat := 118140960795 + 7240873 * 2 ^ 59
def prefixEnd_7240873 : Nat := 4983230072969 + 3 ^ 40 * 7240873 * 2
def baseEnd_7240873 : Nat := 3718048207163153784787337

theorem tailTrace_7240873 : CollatzResearch.WordTrace tailWord_7240873 prefixEnd_7240873 3718048207163153784787337 := by
  unfold tailWord_7240873
  simp only [CollatzResearch.WordTrace]
  refine ⟨264096334696561238499359273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176064223131040825666239515 264096334696561238499359273)
  ·
    refine ⟨198072251022420928874519455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264096334696561238499359273 198072251022420928874519455)
    ·
      refine ⟨297108376533631393311779183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198072251022420928874519455 297108376533631393311779183)
      ·
        refine ⟨445662564800447089967668775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297108376533631393311779183 445662564800447089967668775)
        ·
          refine ⟨668493847200670634951503163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445662564800447089967668775 668493847200670634951503163)
          ·
            refine ⟨1002740770801005952427254745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668493847200670634951503163 1002740770801005952427254745)
            ·
              refine ⟨752055578100754464320441059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002740770801005952427254745 752055578100754464320441059)
              ·
                refine ⟨1128083367151131696480661589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752055578100754464320441059 1128083367151131696480661589)
                ·
                  refine ⟨13219726958802324568132753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1128083367151131696480661589 13219726958802324568132753)
                  ·
                    refine ⟨9914795219101743426099565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13219726958802324568132753 9914795219101743426099565)
                    ·
                      refine ⟨3718048207163153784787337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9914795219101743426099565 3718048207163153784787337)
                      ·
                        rfl

theorem cell23_7240873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2, 3].length) (baseStart_7240873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240873 prefixEnd_7240873 := by exact prefixLift 7240873
  have htrace : WordTrace (prefixWord ++ tailWord_7240873) baseStart_7240873 baseEnd_7240873 := by
    simpa [prefixWord, tailWord_7240873, baseEnd_7240873] using wordTrace_append hprefix tailTrace_7240873
  have hstable : (prefixWord ++ tailWord_7240873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240873).length < 2 ^ (prefixWord ++ tailWord_7240873).sum := by decide
  have hdescent : baseEnd_7240873 < baseStart_7240873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240897 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 3, 4]
def baseStart_7240897 : Nat := 118140960795 + 7240897 * 2 ^ 59
def prefixEnd_7240897 : Nat := 4983230072969 + 3 ^ 40 * 7240897 * 2
def baseEnd_7240897 : Nat := 1239353510232953896962409

theorem tailTrace_7240897 : CollatzResearch.WordTrace tailWord_7240897 prefixEnd_7240897 1239353510232953896962409 := by
  unfold tailWord_7240897
  simp only [CollatzResearch.WordTrace]
  refine ⟨264097210048474290598232945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176064806698982860398821963 264097210048474290598232945)
  ·
    refine ⟨198072907536355717948674709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264097210048474290598232945 198072907536355717948674709)
    ·
      refine ⟨9284667540766674278844127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198072907536355717948674709 9284667540766674278844127)
      ·
        refine ⟨13927001311150011418266191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9284667540766674278844127 13927001311150011418266191)
        ·
          refine ⟨20890501966725017127399287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13927001311150011418266191 20890501966725017127399287)
          ·
            refine ⟨31335752950087525691098931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20890501966725017127399287 31335752950087525691098931)
            ·
              refine ⟨47003629425131288536648397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31335752950087525691098931 47003629425131288536648397)
              ·
                refine ⟨17626361034424233201243149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47003629425131288536648397 17626361034424233201243149)
                ·
                  refine ⟨6609885387909087450466181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17626361034424233201243149 6609885387909087450466181)
                  ·
                    refine ⟨1239353510232953896962409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6609885387909087450466181 1239353510232953896962409)
                    ·
                      rfl

theorem cell23_7240897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_7240897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240897 prefixEnd_7240897 := by exact prefixLift 7240897
  have htrace : WordTrace (prefixWord ++ tailWord_7240897) baseStart_7240897 baseEnd_7240897 := by
    simpa [prefixWord, tailWord_7240897, baseEnd_7240897] using wordTrace_append hprefix tailTrace_7240897
  have hstable : (prefixWord ++ tailWord_7240897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240897).length < 2 ^ (prefixWord ++ tailWord_7240897).sum := by decide
  have hdescent : baseEnd_7240897 < baseStart_7240897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240940 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 1, 5]
def baseStart_7240940 : Nat := 118140960795 + 7240940 * 2 ^ 59
def prefixEnd_7240940 : Nat := 4983230072969 + 3 ^ 40 * 7240940 * 2
def baseEnd_7240940 : Nat := 1239360870122335007549843

theorem tailTrace_7240940 : CollatzResearch.WordTrace tailWord_7240940 prefixEnd_7240940 1239360870122335007549843 := by
  unfold tailWord_7240940
  simp only [CollatzResearch.WordTrace]
  refine ⟨132049389193659254471024137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176065852258212339294698849 132049389193659254471024137)
  ·
    refine ⟨99037041895244440853268103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132049389193659254471024137 99037041895244440853268103)
    ·
      refine ⟨148555562842866661279902155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99037041895244440853268103 148555562842866661279902155)
      ·
        refine ⟨222833344264299991919853233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148555562842866661279902155 222833344264299991919853233)
        ·
          refine ⟨167125008198224993939889925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222833344264299991919853233 167125008198224993939889925)
          ·
            refine ⟨31335939037167186363729361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167125008198224993939889925 31335939037167186363729361)
            ·
              refine ⟨23501954277875389772797021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31335939037167186363729361 23501954277875389772797021)
              ·
                refine ⟨8813232854203271164798883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23501954277875389772797021 8813232854203271164798883)
                ·
                  refine ⟨13219849281304906747198325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8813232854203271164798883 13219849281304906747198325)
                  ·
                    refine ⟨1239360870122335007549843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13219849281304906747198325 1239360870122335007549843)
                    ·
                      rfl

theorem cell23_7240940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_7240940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240940 prefixEnd_7240940 := by exact prefixLift 7240940
  have htrace : WordTrace (prefixWord ++ tailWord_7240940) baseStart_7240940 baseEnd_7240940 := by
    simpa [prefixWord, tailWord_7240940, baseEnd_7240940] using wordTrace_append hprefix tailTrace_7240940
  have hstable : (prefixWord ++ tailWord_7240940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240940).length < 2 ^ (prefixWord ++ tailWord_7240940).sum := by decide
  have hdescent : baseEnd_7240940 < baseStart_7240940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240947 : List Nat := [1, 1, 1, 2, 2, 6, 1, 2, 2, 3, 2]
def baseStart_7240947 : Nat := 118140960795 + 7240947 * 2 ^ 59
def prefixEnd_7240947 : Nat := 4983230072969 + 3 ^ 40 * 7240947 * 2
def baseEnd_7240947 : Nat := 3718086204731586495261997

theorem tailTrace_7240947 : CollatzResearch.WordTrace tailWord_7240947 prefixEnd_7240947 3718086204731586495261997 := by
  unfold tailWord_7240947
  simp only [CollatzResearch.WordTrace]
  refine ⟨264099033698293149137553095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176066022465528766091702063 264099033698293149137553095)
  ·
    refine ⟨396148550547439723706329643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264099033698293149137553095 396148550547439723706329643)
    ·
      refine ⟨594222825821159585559494465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396148550547439723706329643 594222825821159585559494465)
      ·
        refine ⟨445667119365869689169620849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594222825821159585559494465 445667119365869689169620849)
        ·
          refine ⟨334250339524402266877215637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 445667119365869689169620849 334250339524402266877215637)
          ·
            refine ⟨15667984665206356259869483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 334250339524402266877215637 15667984665206356259869483)
            ·
              refine ⟨23501976997809534389804225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15667984665206356259869483 23501976997809534389804225)
              ·
                refine ⟨17626482748357150792353169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23501976997809534389804225 17626482748357150792353169)
                ·
                  refine ⟨13219862061267863094264877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17626482748357150792353169 13219862061267863094264877)
                  ·
                    refine ⟨4957448272975448660349329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13219862061267863094264877 4957448272975448660349329)
                    ·
                      refine ⟨3718086204731586495261997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4957448272975448660349329 3718086204731586495261997)
                      ·
                        rfl

theorem cell23_7240947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 2, 2, 3, 2].length) (baseStart_7240947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240947 prefixEnd_7240947 := by exact prefixLift 7240947
  have htrace : WordTrace (prefixWord ++ tailWord_7240947) baseStart_7240947 baseEnd_7240947 := by
    simpa [prefixWord, tailWord_7240947, baseEnd_7240947] using wordTrace_append hprefix tailTrace_7240947
  have hstable : (prefixWord ++ tailWord_7240947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240947).length < 2 ^ (prefixWord ++ tailWord_7240947).sum := by decide
  have hdescent : baseEnd_7240947 < baseStart_7240947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240948 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7240948 : Nat := 118140960795 + 7240948 * 2 ^ 59
def prefixEnd_7240948 : Nat := 4983230072969 + 3 ^ 40 * 7240948 * 2
def baseEnd_7240948 : Nat := 1239362239404080330449831

theorem tailTrace_7240948 : CollatzResearch.WordTrace tailWord_7240948 prefixEnd_7240948 1239362239404080330449831 := by
  unfold tailWord_7240948
  simp only [CollatzResearch.WordTrace]
  refine ⟨132049535085644763154169749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176066046780859684205559665 132049535085644763154169749)
  ·
    refine ⟨6189821957139598272851707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 132049535085644763154169749 6189821957139598272851707)
    ·
      refine ⟨9284732935709397409277561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6189821957139598272851707 9284732935709397409277561)
      ·
        refine ⟨6963549701782048056958171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9284732935709397409277561 6963549701782048056958171)
        ·
          refine ⟨10445324552673072085437257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6963549701782048056958171 10445324552673072085437257)
          ·
            refine ⟨7833993414504804064077943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10445324552673072085437257 7833993414504804064077943)
            ·
              refine ⟨11750990121757206096116915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7833993414504804064077943 11750990121757206096116915)
              ·
                refine ⟨17626485182635809144175373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11750990121757206096116915 17626485182635809144175373)
                ·
                  refine ⟨6609931943488428429065765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17626485182635809144175373 6609931943488428429065765)
                  ·
                    refine ⟨1239362239404080330449831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6609931943488428429065765 1239362239404080330449831)
                    ·
                      rfl

theorem cell23_7240948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7240948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240948 prefixEnd_7240948 := by exact prefixLift 7240948
  have htrace : WordTrace (prefixWord ++ tailWord_7240948) baseStart_7240948 baseEnd_7240948 := by
    simpa [prefixWord, tailWord_7240948, baseEnd_7240948] using wordTrace_append hprefix tailTrace_7240948
  have hstable : (prefixWord ++ tailWord_7240948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240948).length < 2 ^ (prefixWord ++ tailWord_7240948).sum := by decide
  have hdescent : baseEnd_7240948 < baseStart_7240948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240977 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 5, 2, 2]
def baseStart_7240977 : Nat := 118140960795 + 7240977 * 2 ^ 59
def prefixEnd_7240977 : Nat := 4983230072969 + 3 ^ 40 * 7240977 * 2
def baseEnd_7240977 : Nat := 3718101609151221377886859

theorem tailTrace_7240977 : CollatzResearch.WordTrace tailWord_7240977 prefixEnd_7240977 3718101609151221377886859 := by
  unfold tailWord_7240977
  simp only [CollatzResearch.WordTrace]
  refine ⟨264100127888184464261145185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176066751925456309507430123 264100127888184464261145185)
  ·
    refine ⟨198075095916138348195858889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264100127888184464261145185 198075095916138348195858889)
    ·
      refine ⟨148556321937103761146894167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198075095916138348195858889 148556321937103761146894167)
      ·
        refine ⟨222834482905655641720341251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148556321937103761146894167 222834482905655641720341251)
        ·
          refine ⟨334251724358483462580511877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222834482905655641720341251 334251724358483462580511877)
          ·
            refine ⟨62672198317215649233845977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 334251724358483462580511877 62672198317215649233845977)
            ·
              refine ⟨47004148737911736925384483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62672198317215649233845977 47004148737911736925384483)
              ·
                refine ⟨70506223106867605388076725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47004148737911736925384483 70506223106867605388076725)
                ·
                  refine ⟨6609958416268838005132193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 70506223106867605388076725 6609958416268838005132193)
                  ·
                    refine ⟨4957468812201628503849145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6609958416268838005132193 4957468812201628503849145)
                    ·
                      refine ⟨3718101609151221377886859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4957468812201628503849145 3718101609151221377886859)
                      ·
                        rfl

theorem cell23_7240977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 2, 2].length) (baseStart_7240977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240977 prefixEnd_7240977 := by exact prefixLift 7240977
  have htrace : WordTrace (prefixWord ++ tailWord_7240977) baseStart_7240977 baseEnd_7240977 := by
    simpa [prefixWord, tailWord_7240977, baseEnd_7240977] using wordTrace_append hprefix tailTrace_7240977
  have hstable : (prefixWord ++ tailWord_7240977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240977).length < 2 ^ (prefixWord ++ tailWord_7240977).sum := by decide
  have hdescent : baseEnd_7240977 < baseStart_7240977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240983 : List Nat := [1, 1, 3, 4, 1, 1, 1, 11]
def baseStart_7240983 : Nat := 118140960795 + 7240983 * 2 ^ 59
def prefixEnd_7240983 : Nat := 4983230072969 + 3 ^ 40 * 7240983 * 2
def baseEnd_7240983 : Nat := 137707581112412902015253

theorem tailTrace_7240983 : CollatzResearch.WordTrace tailWord_7240983 prefixEnd_7240983 137707581112412902015253 := by
  unfold tailWord_7240983
  simp only [CollatzResearch.WordTrace]
  refine ⟨264100346726162727285863603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176066897817441818190575735 264100346726162727285863603)
  ·
    refine ⟨396150520089244090928795405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264100346726162727285863603 396150520089244090928795405)
    ·
      refine ⟨148556445033466534098298277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 396150520089244090928795405 148556445033466534098298277)
      ·
        refine ⟨27854333443774975143430927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148556445033466534098298277 27854333443774975143430927)
        ·
          refine ⟨41781500165662462715146391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27854333443774975143430927 41781500165662462715146391)
          ·
            refine ⟨62672250248493694072719587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41781500165662462715146391 62672250248493694072719587)
            ·
              refine ⟨94008375372740541109079381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62672250248493694072719587 94008375372740541109079381)
              ·
                refine ⟨137707581112412902015253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 94008375372740541109079381 137707581112412902015253)
                ·
                  rfl

theorem cell23_7240983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 11].length) (baseStart_7240983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240983 prefixEnd_7240983 := by exact prefixLift 7240983
  have htrace : WordTrace (prefixWord ++ tailWord_7240983) baseStart_7240983 baseEnd_7240983 := by
    simpa [prefixWord, tailWord_7240983, baseEnd_7240983] using wordTrace_append hprefix tailTrace_7240983
  have hstable : (prefixWord ++ tailWord_7240983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240983).length < 2 ^ (prefixWord ++ tailWord_7240983).sum := by decide
  have hdescent : baseEnd_7240983 < baseStart_7240983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7240997 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 5]
def baseStart_7240997 : Nat := 118140960795 + 7240997 * 2 ^ 59
def prefixEnd_7240997 : Nat := 4983230072969 + 3 ^ 40 * 7240997 * 2
def baseEnd_7240997 : Nat := 3718111878764311299636767

theorem tailTrace_7240997 : CollatzResearch.WordTrace tailWord_7240997 prefixEnd_7240997 3718111878764311299636767 := by
  unfold tailWord_7240997
  simp only [CollatzResearch.WordTrace]
  refine ⟨264100857348112007676873245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176067238232074671784582163 264100857348112007676873245)
  ·
    refine ⟨99037821505542002878827467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264100857348112007676873245 99037821505542002878827467)
    ·
      refine ⟨148556732258313004318241201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99037821505542002878827467 148556732258313004318241201)
      ·
        refine ⟨111417549193734753238680901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148556732258313004318241201 111417549193734753238680901)
        ·
          refine ⟨20890790473825266232252669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111417549193734753238680901 20890790473825266232252669)
          ·
            refine ⟨7834046427684474837094751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20890790473825266232252669 7834046427684474837094751)
            ·
              refine ⟨11751069641526712255642127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7834046427684474837094751 11751069641526712255642127)
              ·
                refine ⟨17626604462290068383463191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11751069641526712255642127 17626604462290068383463191)
                ·
                  refine ⟨26439906693435102575194787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17626604462290068383463191 26439906693435102575194787)
                  ·
                    refine ⟨39659860040152653862792181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26439906693435102575194787 39659860040152653862792181)
                    ·
                      refine ⟨3718111878764311299636767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39659860040152653862792181 3718111878764311299636767)
                      ·
                        rfl

theorem cell23_7240997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_7240997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7240997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7240997 prefixEnd_7240997 := by exact prefixLift 7240997
  have htrace : WordTrace (prefixWord ++ tailWord_7240997) baseStart_7240997 baseEnd_7240997 := by
    simpa [prefixWord, tailWord_7240997, baseEnd_7240997] using wordTrace_append hprefix tailTrace_7240997
  have hstable : (prefixWord ++ tailWord_7240997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7240997).length < 2 ^ (prefixWord ++ tailWord_7240997).sum := by decide
  have hdescent : baseEnd_7240997 < baseStart_7240997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7240997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241005 : List Nat := [1, 5, 3, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_7241005 : Nat := 118140960795 + 7241005 * 2 ^ 59
def prefixEnd_7241005 : Nat := 4983230072969 + 3 ^ 40 * 7241005 * 2
def baseEnd_7241005 : Nat := 3718115986609547268336731

theorem tailTrace_7241005 : CollatzResearch.WordTrace tailWord_7241005 prefixEnd_7241005 3718115986609547268336731 := by
  unfold tailWord_7241005
  simp only [CollatzResearch.WordTrace]
  refine ⟨264101149132083025043164469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176067432754722016695442979 264101149132083025043164469)
  ·
    refine ⟨24759482731132783597796669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 264101149132083025043164469 24759482731132783597796669)
    ·
      refine ⟨9284806024174793849173751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24759482731132783597796669 9284806024174793849173751)
      ·
        refine ⟨13927209036262190773760627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9284806024174793849173751 13927209036262190773760627)
        ·
          refine ⟨20890813554393286160640941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13927209036262190773760627 20890813554393286160640941)
          ·
            refine ⟨7834055082897482310240353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20890813554393286160640941 7834055082897482310240353)
            ·
              refine ⟨5875541312173111732680265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7834055082897482310240353 5875541312173111732680265)
              ·
                refine ⟨4406655984129833799510199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5875541312173111732680265 4406655984129833799510199)
                ·
                  refine ⟨6609983976194750699265299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406655984129833799510199 6609983976194750699265299)
                  ·
                    refine ⟨9914975964292126048897949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6609983976194750699265299 9914975964292126048897949)
                    ·
                      refine ⟨3718115986609547268336731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9914975964292126048897949 3718115986609547268336731)
                      ·
                        rfl

theorem cell23_7241005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_7241005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241005 prefixEnd_7241005 := by exact prefixLift 7241005
  have htrace : WordTrace (prefixWord ++ tailWord_7241005) baseStart_7241005 baseEnd_7241005 := by
    simpa [prefixWord, tailWord_7241005, baseEnd_7241005] using wordTrace_append hprefix tailTrace_7241005
  have hstable : (prefixWord ++ tailWord_7241005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241005).length < 2 ^ (prefixWord ++ tailWord_7241005).sum := by decide
  have hdescent : baseEnd_7241005 < baseStart_7241005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241011 : List Nat := [1, 1, 1, 2, 5, 3, 1, 4, 1, 2, 2]
def baseStart_7241011 : Nat := 118140960795 + 7241011 * 2 ^ 59
def prefixEnd_7241011 : Nat := 4983230072969 + 3 ^ 40 * 7241011 * 2
def baseEnd_7241011 : Nat := 3718119067493474244861703

theorem tailTrace_7241011 : CollatzResearch.WordTrace tailWord_7241011 prefixEnd_7241011 3718119067493474244861703 := by
  unfold tailWord_7241011
  simp only [CollatzResearch.WordTrace]
  refine ⟨264101367970061288067882887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176067578646707525378588591 264101367970061288067882887)
  ·
    refine ⟨396152051955091932101824331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264101367970061288067882887 396152051955091932101824331)
    ·
      refine ⟨594228077932637898152736497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396152051955091932101824331 594228077932637898152736497)
      ·
        refine ⟨445671058449478423614552373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594228077932637898152736497 445671058449478423614552373)
        ·
          refine ⟨41781661729638602213864285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 445671058449478423614552373 41781661729638602213864285)
          ·
            refine ⟨15668123148614475830199107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41781661729638602213864285 15668123148614475830199107)
            ·
              refine ⟨23502184722921713745298661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15668123148614475830199107 23502184722921713745298661)
              ·
                refine ⟨4406659635547821327243499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23502184722921713745298661 4406659635547821327243499)
                ·
                  refine ⟨6609989453321731990865249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406659635547821327243499 6609989453321731990865249)
                  ·
                    refine ⟨4957492089991298993148937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6609989453321731990865249 4957492089991298993148937)
                    ·
                      refine ⟨3718119067493474244861703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4957492089991298993148937 3718119067493474244861703)
                      ·
                        rfl

theorem cell23_7241011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 1, 2, 2].length) (baseStart_7241011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241011 prefixEnd_7241011 := by exact prefixLift 7241011
  have htrace : WordTrace (prefixWord ++ tailWord_7241011) baseStart_7241011 baseEnd_7241011 := by
    simpa [prefixWord, tailWord_7241011, baseEnd_7241011] using wordTrace_append hprefix tailTrace_7241011
  have hstable : (prefixWord ++ tailWord_7241011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241011).length < 2 ^ (prefixWord ++ tailWord_7241011).sum := by decide
  have hdescent : baseEnd_7241011 < baseStart_7241011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241017 : List Nat := [1, 2, 1, 6, 2, 2, 1, 8]
def baseStart_7241017 : Nat := 118140960795 + 7241017 * 2 ^ 59
def prefixEnd_7241017 : Nat := 4983230072969 + 3 ^ 40 * 7241017 * 2
def baseEnd_7241017 : Nat := 137708227717681526718025

theorem tailTrace_7241017 : CollatzResearch.WordTrace tailWord_7241017 prefixEnd_7241017 137708227717681526718025 := by
  unfold tailWord_7241017
  simp only [CollatzResearch.WordTrace]
  refine ⟨264101586808039551092601305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176067724538693034061734203 264101586808039551092601305)
  ·
    refine ⟨198076190106029663319450979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264101586808039551092601305 198076190106029663319450979)
    ·
      refine ⟨297114285159044494979176469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198076190106029663319450979 297114285159044494979176469)
      ·
        refine ⟨13927232116830210702148897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 297114285159044494979176469 13927232116830210702148897)
        ·
          refine ⟨10445424087622658026611673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13927232116830210702148897 10445424087622658026611673)
          ·
            refine ⟨7834068065716993519958755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10445424087622658026611673 7834068065716993519958755)
            ·
              refine ⟨11751102098575490279938133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7834068065716993519958755 11751102098575490279938133)
              ·
                refine ⟨137708227717681526718025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11751102098575490279938133 137708227717681526718025)
                ·
                  rfl

theorem cell23_7241017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 8].length) (baseStart_7241017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241017 prefixEnd_7241017 := by exact prefixLift 7241017
  have htrace : WordTrace (prefixWord ++ tailWord_7241017) baseStart_7241017 baseEnd_7241017 := by
    simpa [prefixWord, tailWord_7241017, baseEnd_7241017] using wordTrace_append hprefix tailTrace_7241017
  have hstable : (prefixWord ++ tailWord_7241017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241017).length < 2 ^ (prefixWord ++ tailWord_7241017).sum := by decide
  have hdescent : baseEnd_7241017 < baseStart_7241017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241043 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 1, 8]
def baseStart_7241043 : Nat := 118140960795 + 7241043 * 2 ^ 59
def prefixEnd_7241043 : Nat := 4983230072969 + 3 ^ 40 * 7241043 * 2
def baseEnd_7241043 : Nat := 1239378499624806039887185

theorem tailTrace_7241043 : CollatzResearch.WordTrace tailWord_7241043 prefixEnd_7241043 1239378499624806039887185 := by
  unfold tailWord_7241043
  simp only [CollatzResearch.WordTrace]
  refine ⟨264102535105945357533047783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176068356737296905022031855 264102535105945357533047783)
  ·
    refine ⟨396153802658918036299571675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264102535105945357533047783 396153802658918036299571675)
    ·
      refine ⟨594230703988377054449357513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396153802658918036299571675 594230703988377054449357513)
      ·
        refine ⟨445673027991282790837018135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594230703988377054449357513 445673027991282790837018135)
        ·
          refine ⟨668509541986924186255527203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445673027991282790837018135 668509541986924186255527203)
          ·
            refine ⟨1002764312980386279383290805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668509541986924186255527203 1002764312980386279383290805)
            ·
              refine ⟨94009154341911213692183513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1002764312980386279383290805 94009154341911213692183513)
              ·
                refine ⟨70506865756433410269137635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94009154341911213692183513 70506865756433410269137635)
                ·
                  refine ⟨105760298634650115403706453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70506865756433410269137635 105760298634650115403706453)
                  ·
                    refine ⟨1239378499624806039887185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 105760298634650115403706453 1239378499624806039887185)
                    ·
                      rfl

theorem cell23_7241043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 8].length) (baseStart_7241043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241043 prefixEnd_7241043 := by exact prefixLift 7241043
  have htrace : WordTrace (prefixWord ++ tailWord_7241043) baseStart_7241043 baseEnd_7241043 := by
    simpa [prefixWord, tailWord_7241043, baseEnd_7241043] using wordTrace_append hprefix tailTrace_7241043
  have hstable : (prefixWord ++ tailWord_7241043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241043).length < 2 ^ (prefixWord ++ tailWord_7241043).sum := by decide
  have hdescent : baseEnd_7241043 < baseStart_7241043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241060 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_7241060 : Nat := 118140960795 + 7241060 * 2 ^ 59
def prefixEnd_7241060 : Nat := 4983230072969 + 3 ^ 40 * 7241060 * 2
def baseEnd_7241060 : Nat := 1239381409348514851049659

theorem tailTrace_7241060 : CollatzResearch.WordTrace tailWord_7241060 prefixEnd_7241060 1239381409348514851049659 := by
  unfold tailWord_7241060
  simp only [CollatzResearch.WordTrace]
  refine ⟨132051577573441884718208317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176068770097922512957611089 132051577573441884718208317)
  ·
    refine ⟨49519341590040706769328119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132051577573441884718208317 49519341590040706769328119)
    ·
      refine ⟨74279012385061060153992179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49519341590040706769328119 74279012385061060153992179)
      ·
        refine ⟨111418518577591590230988269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74279012385061060153992179 111418518577591590230988269)
        ·
          refine ⟨41781944466596846336620601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111418518577591590230988269 41781944466596846336620601)
          ·
            refine ⟨31336458349947634752465451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41781944466596846336620601 31336458349947634752465451)
            ·
              refine ⟨47004687524921452128698177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31336458349947634752465451 47004687524921452128698177)
              ·
                refine ⟨35253515643691089096523633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47004687524921452128698177 35253515643691089096523633)
                ·
                  refine ⟨26440136732768316822392725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35253515643691089096523633 26440136732768316822392725)
                  ·
                    refine ⟨1239381409348514851049659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26440136732768316822392725 1239381409348514851049659)
                    ·
                      rfl

theorem cell23_7241060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_7241060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241060 prefixEnd_7241060 := by exact prefixLift 7241060
  have htrace : WordTrace (prefixWord ++ tailWord_7241060) baseStart_7241060 baseEnd_7241060 := by
    simpa [prefixWord, tailWord_7241060, baseEnd_7241060] using wordTrace_append hprefix tailTrace_7241060
  have hstable : (prefixWord ++ tailWord_7241060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241060).length < 2 ^ (prefixWord ++ tailWord_7241060).sum := by decide
  have hdescent : baseEnd_7241060 < baseStart_7241060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241218 : List Nat := [3, 4, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_7241218 : Nat := 118140960795 + 7241218 * 2 ^ 59
def prefixEnd_7241218 : Nat := 4983230072969 + 3 ^ 40 * 7241218 * 2
def baseEnd_7241218 : Nat := 1239408452662984978324417

theorem tailTrace_7241218 : CollatzResearch.WordTrace tailWord_7241218 prefixEnd_7241218 1239408452662984978324417 := by
  unfold tailWord_7241218
  simp only [CollatzResearch.WordTrace]
  refine ⟨66027229470077840605167077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176072611920207574947112205 66027229470077840605167077)
  ·
    refine ⟨12380105525639595113468827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66027229470077840605167077 12380105525639595113468827)
    ·
      refine ⟨18570158288459392670203241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12380105525639595113468827 18570158288459392670203241)
      ·
        refine ⟨13927618716344544502652431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18570158288459392670203241 13927618716344544502652431)
        ·
          refine ⟨20891428074516816753978647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13927618716344544502652431 20891428074516816753978647)
          ·
            refine ⟨31337142111775225130967971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20891428074516816753978647 31337142111775225130967971)
            ·
              refine ⟨47005713167662837696451957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31337142111775225130967971 47005713167662837696451957)
              ·
                refine ⟨4406785609468391034042371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47005713167662837696451957 4406785609468391034042371)
                ·
                  refine ⟨6610178414202586551063557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4406785609468391034042371 6610178414202586551063557)
                  ·
                    refine ⟨1239408452662984978324417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6610178414202586551063557 1239408452662984978324417)
                    ·
                      rfl

theorem cell23_7241218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_7241218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241218 prefixEnd_7241218 := by exact prefixLift 7241218
  have htrace : WordTrace (prefixWord ++ tailWord_7241218) baseStart_7241218 baseEnd_7241218 := by
    simpa [prefixWord, tailWord_7241218, baseEnd_7241218] using wordTrace_append hprefix tailTrace_7241218
  have hstable : (prefixWord ++ tailWord_7241218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241218).length < 2 ^ (prefixWord ++ tailWord_7241218).sum := by decide
  have hdescent : baseEnd_7241218 < baseStart_7241218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241247 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 4]
def baseStart_7241247 : Nat := 118140960795 + 7241247 * 2 ^ 59
def prefixEnd_7241247 : Nat := 4983230072969 + 3 ^ 40 * 7241247 * 2
def baseEnd_7241247 : Nat := 3718240248927935321510617

theorem tailTrace_7241247 : CollatzResearch.WordTrace tailWord_7241247 prefixEnd_7241247 3718240248927935321510617 := by
  unfold tailWord_7241247
  simp only [CollatzResearch.WordTrace]
  refine ⟨264109975597206300373473995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176073317064804200248982663 264109975597206300373473995)
  ·
    refine ⟨396164963395809450560210993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264109975597206300373473995 396164963395809450560210993)
    ·
      refine ⟨297123722546857087920158245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 396164963395809450560210993 297123722546857087920158245)
      ·
        refine ⟨55710697977535703985029671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297123722546857087920158245 55710697977535703985029671)
        ·
          refine ⟨83566046966303555977544507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55710697977535703985029671 83566046966303555977544507)
          ·
            refine ⟨125349070449455333966316761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83566046966303555977544507 125349070449455333966316761)
            ·
              refine ⟨94011802837091500474737571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125349070449455333966316761 94011802837091500474737571)
              ·
                refine ⟨141017704255637250712106357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94011802837091500474737571 141017704255637250712106357)
                ·
                  refine ⟨13220409773965992254259971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141017704255637250712106357 13220409773965992254259971)
                  ·
                    refine ⟨19830614660948988381389957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13220409773965992254259971 19830614660948988381389957)
                    ·
                      refine ⟨3718240248927935321510617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19830614660948988381389957 3718240248927935321510617)
                      ·
                        rfl

theorem cell23_7241247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_7241247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241247 prefixEnd_7241247 := by exact prefixLift 7241247
  have htrace : WordTrace (prefixWord ++ tailWord_7241247) baseStart_7241247 baseEnd_7241247 := by
    simpa [prefixWord, tailWord_7241247, baseEnd_7241247] using wordTrace_append hprefix tailTrace_7241247
  have hstable : (prefixWord ++ tailWord_7241247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241247).length < 2 ^ (prefixWord ++ tailWord_7241247).sum := by decide
  have hdescent : baseEnd_7241247 < baseStart_7241247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241298 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 3, 2, 2]
def baseStart_7241298 : Nat := 118140960795 + 7241298 * 2 ^ 59
def prefixEnd_7241298 : Nat := 4983230072969 + 3 ^ 40 * 7241298 * 2
def baseEnd_7241298 : Nat := 3718266436441314621972883

theorem tailTrace_7241298 : CollatzResearch.WordTrace tailWord_7241298 prefixEnd_7241298 3718266436441314621972883 := by
  unfold tailWord_7241298
  simp only [CollatzResearch.WordTrace]
  refine ⟨66027958930005384020895137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176074557146681024055720365 66027958930005384020895137)
  ·
    refine ⟨49520969197504038015671353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66027958930005384020895137 49520969197504038015671353)
    ·
      refine ⟨37140726898128028511753515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49520969197504038015671353 37140726898128028511753515)
      ·
        refine ⟨55711090347192042767630273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37140726898128028511753515 55711090347192042767630273)
        ·
          refine ⟨41783317760394032075722705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55711090347192042767630273 41783317760394032075722705)
          ·
            refine ⟨31337488320295524056792029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41783317760394032075722705 31337488320295524056792029)
            ·
              refine ⟨11751558120110821521297011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31337488320295524056792029 11751558120110821521297011)
              ·
                refine ⟨17627337180166232281945517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11751558120110821521297011 17627337180166232281945517)
                ·
                  refine ⟨6610251442562337105729569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17627337180166232281945517 6610251442562337105729569)
                  ·
                    refine ⟨4957688581921752829297177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6610251442562337105729569 4957688581921752829297177)
                    ·
                      refine ⟨3718266436441314621972883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4957688581921752829297177 3718266436441314621972883)
                      ·
                        rfl

theorem cell23_7241298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_7241298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241298 prefixEnd_7241298 := by exact prefixLift 7241298
  have htrace : WordTrace (prefixWord ++ tailWord_7241298) baseStart_7241298 baseEnd_7241298 := by
    simpa [prefixWord, tailWord_7241298, baseEnd_7241298] using wordTrace_append hprefix tailTrace_7241298
  have hstable : (prefixWord ++ tailWord_7241298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241298).length < 2 ^ (prefixWord ++ tailWord_7241298).sum := by decide
  have hdescent : baseEnd_7241298 < baseStart_7241298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241308 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 2, 4]
def baseStart_7241308 : Nat := 118140960795 + 7241308 * 2 ^ 59
def prefixEnd_7241308 : Nat := 4983230072969 + 3 ^ 40 * 7241308 * 2
def baseEnd_7241308 : Nat := 1239423857082619860949279

theorem tailTrace_7241308 : CollatzResearch.WordTrace tailWord_7241308 prefixEnd_7241308 1239423857082619860949279 := by
  unfold tailWord_7241308
  simp only [CollatzResearch.WordTrace]
  refine ⟨132056100224992653895722289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176074800299990205194296385 132056100224992653895722289)
  ·
    refine ⟨99042075168744490421791717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132056100224992653895722289 99042075168744490421791717)
    ·
      refine ⟨18570389094139591954085947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99042075168744490421791717 18570389094139591954085947)
      ·
        refine ⟨27855583641209387931128921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18570389094139591954085947 27855583641209387931128921)
        ·
          refine ⟨20891687730907040948346691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27855583641209387931128921 20891687730907040948346691)
          ·
            refine ⟨31337531596360561422520037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20891687730907040948346691 31337531596360561422520037)
            ·
              refine ⟨5875787174317605266722507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31337531596360561422520037 5875787174317605266722507)
              ·
                refine ⟨8813680761476407900083761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5875787174317605266722507 8813680761476407900083761)
                ·
                  refine ⟨6610260571107305925062821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8813680761476407900083761 6610260571107305925062821)
                  ·
                    refine ⟨1239423857082619860949279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6610260571107305925062821 1239423857082619860949279)
                    ·
                      rfl

theorem cell23_7241308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_7241308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241308 prefixEnd_7241308 := by exact prefixLift 7241308
  have htrace : WordTrace (prefixWord ++ tailWord_7241308) baseStart_7241308 baseEnd_7241308 := by
    simpa [prefixWord, tailWord_7241308, baseEnd_7241308] using wordTrace_append hprefix tailTrace_7241308
  have hstable : (prefixWord ++ tailWord_7241308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241308).length < 2 ^ (prefixWord ++ tailWord_7241308).sum := by decide
  have hdescent : baseEnd_7241308 < baseStart_7241308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7241347 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 2, 6]
def baseStart_7241347 : Nat := 118140960795 + 7241347 * 2 ^ 59
def prefixEnd_7241347 : Nat := 4983230072969 + 3 ^ 40 * 7241347 * 2
def baseEnd_7241347 : Nat := 1239430532331128310086719

theorem tailTrace_7241347 : CollatzResearch.WordTrace tailWord_7241347 prefixEnd_7241347 1239430532331128310086719 := by
  unfold tailWord_7241347
  simp only [CollatzResearch.WordTrace]
  refine ⟨264113622896844017452114295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176075748597896011634742863 264113622896844017452114295)
  ·
    refine ⟨396170434345266026178171443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264113622896844017452114295 396170434345266026178171443)
    ·
      refine ⟨594255651517899039267257165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396170434345266026178171443 594255651517899039267257165)
      ·
        refine ⟨222845869319212139725221437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 594255651517899039267257165 222845869319212139725221437)
        ·
          refine ⟨83567200994704552396958039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222845869319212139725221437 83567200994704552396958039)
          ·
            refine ⟨125350801492056828595437059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83567200994704552396958039 125350801492056828595437059)
            ·
              refine ⟨188026202238085242893155589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125350801492056828595437059 188026202238085242893155589)
              ·
                refine ⟨35254912919640983042466673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188026202238085242893155589 35254912919640983042466673)
                ·
                  refine ⟨26441184689730737281850005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35254912919640983042466673 26441184689730737281850005)
                  ·
                    refine ⟨1239430532331128310086719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26441184689730737281850005 1239430532331128310086719)
                    ·
                      rfl

theorem cell23_7241347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 6].length) (baseStart_7241347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7241347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7241347 prefixEnd_7241347 := by exact prefixLift 7241347
  have htrace : WordTrace (prefixWord ++ tailWord_7241347) baseStart_7241347 baseEnd_7241347 := by
    simpa [prefixWord, tailWord_7241347, baseEnd_7241347] using wordTrace_append hprefix tailTrace_7241347
  have hstable : (prefixWord ++ tailWord_7241347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7241347).length < 2 ^ (prefixWord ++ tailWord_7241347).sum := by decide
  have hdescent : baseEnd_7241347 < baseStart_7241347 := by decide
  rcases family_descends (prefixWord ++ tailWord_7241347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
