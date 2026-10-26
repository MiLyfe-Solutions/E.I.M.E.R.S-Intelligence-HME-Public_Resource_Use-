import V185TrunkScan23Chunk0569

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3370567 : List Nat := [1, 1, 4, 1, 6, 1, 2, 2, 5]
def baseStart_3370567 : Nat := 118140960795 + 3370567 * 2 ^ 59
def prefixEnd_3370567 : Nat := 4983230072969 + 3 ^ 40 * 3370567 * 2
def baseEnd_3370567 : Nat := 192302327687002152756839

theorem tailTrace_3370567 : CollatzResearch.WordTrace tailWord_3370567 prefixEnd_3370567 192302327687002152756839 := by
  unfold tailWord_3370567
  simp only [CollatzResearch.WordTrace]
  refine ⟨122934677980018880859109955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81956451986679253906073303 122934677980018880859109955)
  ·
    refine ⟨184402016970028321288664933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122934677980018880859109955 184402016970028321288664933)
    ·
      refine ⟨34575378181880310241624675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184402016970028321288664933 34575378181880310241624675)
      ·
        refine ⟨51863067272820465362437013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34575378181880310241624675 51863067272820465362437013)
        ·
          refine ⟨2431081278413459313864235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51863067272820465362437013 2431081278413459313864235)
          ·
            refine ⟨3646621917620188970796353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431081278413459313864235 3646621917620188970796353)
            ·
              refine ⟨2734966438215141728097265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3646621917620188970796353 2734966438215141728097265)
              ·
                refine ⟨2051224828661356296072949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2734966438215141728097265 2051224828661356296072949)
                ·
                  refine ⟨192302327687002152756839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2051224828661356296072949 192302327687002152756839)
                  ·
                    rfl

theorem cell23_3370567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 2, 5].length) (baseStart_3370567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370567 prefixEnd_3370567 := by exact prefixLift 3370567
  have htrace : WordTrace (prefixWord ++ tailWord_3370567) baseStart_3370567 baseEnd_3370567 := by
    simpa [prefixWord, tailWord_3370567, baseEnd_3370567] using wordTrace_append hprefix tailTrace_3370567
  have hstable : (prefixWord ++ tailWord_3370567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370567).length < 2 ^ (prefixWord ++ tailWord_3370567).sum := by decide
  have hdescent : baseEnd_3370567 < baseStart_3370567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370576 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 3, 4]
def baseStart_3370576 : Nat := 118140960795 + 3370576 * 2 ^ 59
def prefixEnd_3370576 : Nat := 4983230072969 + 3 ^ 40 * 3370576 * 2
def baseEnd_3370576 : Nat := 576908523502969946533003

theorem tailTrace_3370576 : CollatzResearch.WordTrace tailWord_3370576 prefixEnd_3370576 576908523502969946533003 := by
  unfold tailWord_3370576
  simp only [CollatzResearch.WordTrace]
  refine ⟨61467503118493137698093791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81956670824657516930791721 61467503118493137698093791)
  ·
    refine ⟨92201254677739706547140687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61467503118493137698093791 92201254677739706547140687)
    ·
      refine ⟨138301882016609559820711031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92201254677739706547140687 138301882016609559820711031)
      ·
        refine ⟨207452823024914339731066547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138301882016609559820711031 207452823024914339731066547)
        ·
          refine ⟨311179234537371509596599821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207452823024914339731066547 311179234537371509596599821)
          ·
            refine ⟨116692212951514316098724933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311179234537371509596599821 116692212951514316098724933)
            ·
              refine ⟨21879789928408934268510925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116692212951514316098724933 21879789928408934268510925)
              ·
                refine ⟨8204921223153350350691597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21879789928408934268510925 8204921223153350350691597)
                ·
                  refine ⟨3076845458682506381509349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8204921223153350350691597 3076845458682506381509349)
                  ·
                    refine ⟨576908523502969946533003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3076845458682506381509349 576908523502969946533003)
                    ·
                      rfl

theorem cell23_3370576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 3, 4].length) (baseStart_3370576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370576 prefixEnd_3370576 := by exact prefixLift 3370576
  have htrace : WordTrace (prefixWord ++ tailWord_3370576) baseStart_3370576 baseEnd_3370576 := by
    simpa [prefixWord, tailWord_3370576, baseEnd_3370576] using wordTrace_append hprefix tailTrace_3370576
  have hstable : (prefixWord ++ tailWord_3370576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370576).length < 2 ^ (prefixWord ++ tailWord_3370576).sum := by decide
  have hdescent : baseEnd_3370576 < baseStart_3370576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370583 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 2, 4, 2]
def baseStart_3370583 : Nat := 118140960795 + 3370583 * 2 ^ 59
def prefixEnd_3370583 : Nat := 4983230072969 + 3 ^ 40 * 3370583 * 2
def baseEnd_3370583 : Nat := 1730729164873491312211477

theorem tailTrace_3370583 : CollatzResearch.WordTrace tailWord_3370583 prefixEnd_3370583 1730729164873491312211477 := by
  unfold tailWord_3370583
  simp only [CollatzResearch.WordTrace]
  refine ⟨122935261547960915591692403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81956841031973943727794935 122935261547960915591692403)
  ·
    refine ⟨184402892321941373387538605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122935261547960915591692403 184402892321941373387538605)
    ·
      refine ⟨69151084620728015020326977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184402892321941373387538605 69151084620728015020326977)
      ·
        refine ⟨51863313465546011265245233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69151084620728015020326977 51863313465546011265245233)
        ·
          refine ⟨38897485099159508448933925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51863313465546011265245233 38897485099159508448933925)
          ·
            refine ⟨7293278456092407834175111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38897485099159508448933925 7293278456092407834175111)
            ·
              refine ⟨10939917684138611751262667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7293278456092407834175111 10939917684138611751262667)
              ·
                refine ⟨16409876526207917626894001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10939917684138611751262667 16409876526207917626894001)
                ·
                  refine ⟨12307407394655938220170501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16409876526207917626894001 12307407394655938220170501)
                  ·
                    refine ⟨2307638886497988416281969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12307407394655938220170501 2307638886497988416281969)
                    ·
                      refine ⟨1730729164873491312211477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307638886497988416281969 1730729164873491312211477)
                      ·
                        rfl

theorem cell23_3370583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_3370583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370583 prefixEnd_3370583 := by exact prefixLift 3370583
  have htrace : WordTrace (prefixWord ++ tailWord_3370583) baseStart_3370583 baseEnd_3370583 := by
    simpa [prefixWord, tailWord_3370583, baseEnd_3370583] using wordTrace_append hprefix tailTrace_3370583
  have hstable : (prefixWord ++ tailWord_3370583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370583).length < 2 ^ (prefixWord ++ tailWord_3370583).sum := by decide
  have hdescent : baseEnd_3370583 < baseStart_3370583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370586 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3]
def baseStart_3370586 : Nat := 118140960795 + 3370586 * 2 ^ 59
def prefixEnd_3370586 : Nat := 4983230072969 + 3 ^ 40 * 3370586 * 2
def baseEnd_3370586 : Nat := 1730730705315454800473963

theorem tailTrace_3370586 : CollatzResearch.WordTrace tailWord_3370586 prefixEnd_3370586 1730730705315454800473963 := by
  unfold tailWord_3370586
  simp only [CollatzResearch.WordTrace]
  refine ⟨30733842741737511776012903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81956913977966698069367741 30733842741737511776012903)
  ·
    refine ⟨46100764112606267664019355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30733842741737511776012903 46100764112606267664019355)
    ·
      refine ⟨69151146168909401496029033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46100764112606267664019355 69151146168909401496029033)
      ·
        refine ⟨51863359626682051122021775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69151146168909401496029033 51863359626682051122021775)
        ·
          refine ⟨77795039440023076683032663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51863359626682051122021775 77795039440023076683032663)
          ·
            refine ⟨116692559160034615024548995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77795039440023076683032663 116692559160034615024548995)
            ·
              refine ⟨175038838740051922536823493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116692559160034615024548995 175038838740051922536823493)
              ·
                refine ⟨32819782263759735475654405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175038838740051922536823493 32819782263759735475654405)
                ·
                  refine ⟨6153709174454950401685201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32819782263759735475654405 6153709174454950401685201)
                  ·
                    refine ⟨4615281880841212801263901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6153709174454950401685201 4615281880841212801263901)
                    ·
                      refine ⟨1730730705315454800473963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4615281880841212801263901 1730730705315454800473963)
                      ·
                        rfl

theorem cell23_3370586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_3370586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370586 prefixEnd_3370586 := by exact prefixLift 3370586
  have htrace : WordTrace (prefixWord ++ tailWord_3370586) baseStart_3370586 baseEnd_3370586 := by
    simpa [prefixWord, tailWord_3370586, baseEnd_3370586] using wordTrace_append hprefix tailTrace_3370586
  have hstable : (prefixWord ++ tailWord_3370586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370586).length < 2 ^ (prefixWord ++ tailWord_3370586).sum := by decide
  have hdescent : baseEnd_3370586 < baseStart_3370586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370600 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_3370600 : Nat := 118140960795 + 3370600 * 2 ^ 59
def prefixEnd_3370600 : Nat := 4983230072969 + 3 ^ 40 * 3370600 * 2
def baseEnd_3370600 : Nat := 1730737894044617745698899

theorem tailTrace_3370600 : CollatzResearch.WordTrace tailWord_3370600 prefixEnd_3370600 1730737894044617745698899 := by
  unfold tailWord_3370600
  simp only [CollatzResearch.WordTrace]
  refine ⟨61467940794449663747530627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81957254392599551663374169 61467940794449663747530627)
  ·
    refine ⟨92201911191674495621295941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61467940794449663747530627 92201911191674495621295941)
    ·
      refine ⟨17287858348438967928992989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92201911191674495621295941 17287858348438967928992989)
      ·
        refine ⟨6482946880664612973372371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17287858348438967928992989 6482946880664612973372371)
        ·
          refine ⟨9724420320996919460058557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6482946880664612973372371 9724420320996919460058557)
          ·
            refine ⟨3646657620373844797521959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9724420320996919460058557 3646657620373844797521959)
            ·
              refine ⟨5469986430560767196282939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646657620373844797521959 5469986430560767196282939)
              ·
                refine ⟨8204979645841150794424409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5469986430560767196282939 8204979645841150794424409)
                ·
                  refine ⟨6153734734380863095818307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8204979645841150794424409 6153734734380863095818307)
                  ·
                    refine ⟨9230602101571294643727461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6153734734380863095818307 9230602101571294643727461)
                    ·
                      refine ⟨1730737894044617745698899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9230602101571294643727461 1730737894044617745698899)
                      ·
                        rfl

theorem cell23_3370600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_3370600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370600 prefixEnd_3370600 := by exact prefixLift 3370600
  have htrace : WordTrace (prefixWord ++ tailWord_3370600) baseStart_3370600 baseEnd_3370600 := by
    simpa [prefixWord, tailWord_3370600, baseEnd_3370600] using wordTrace_append hprefix tailTrace_3370600
  have hstable : (prefixWord ++ tailWord_3370600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370600).length < 2 ^ (prefixWord ++ tailWord_3370600).sum := by decide
  have hdescent : baseEnd_3370600 < baseStart_3370600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370609 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3370609 : Nat := 118140960795 + 3370609 * 2 ^ 59
def prefixEnd_3370609 : Nat := 4983230072969 + 3 ^ 40 * 3370609 * 2
def baseEnd_3370609 : Nat := 1730742515370508210486357

theorem tailTrace_3370609 : CollatzResearch.WordTrace tailWord_3370609 prefixEnd_3370609 1730742515370508210486357 := by
  unfold tailWord_3370609
  simp only [CollatzResearch.WordTrace]
  refine ⟨122936209845866722032138881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81957473230577814688092587 122936209845866722032138881)
  ·
    refine ⟨92202157384400041524104161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122936209845866722032138881 92202157384400041524104161)
    ·
      refine ⟨69151618038300031143078121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92202157384400041524104161 69151618038300031143078121)
      ·
        refine ⟨51863713528725023357308591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69151618038300031143078121 51863713528725023357308591)
        ·
          refine ⟨77795570293087535035962887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51863713528725023357308591 77795570293087535035962887)
          ·
            refine ⟨116693355439631302553944331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77795570293087535035962887 116693355439631302553944331)
            ·
              refine ⟨175040033159446953830916497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116693355439631302553944331 175040033159446953830916497)
              ·
                refine ⟨131280024869585215373187373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175040033159446953830916497 131280024869585215373187373)
                ·
                  refine ⟨49230009326094455764945265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131280024869585215373187373 49230009326094455764945265)
                  ·
                    refine ⟨36922506994570841823708949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49230009326094455764945265 36922506994570841823708949)
                    ·
                      refine ⟨1730742515370508210486357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36922506994570841823708949 1730742515370508210486357)
                      ·
                        rfl

theorem cell23_3370609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3370609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370609 prefixEnd_3370609 := by exact prefixLift 3370609
  have htrace : WordTrace (prefixWord ++ tailWord_3370609) baseStart_3370609 baseEnd_3370609 := by
    simpa [prefixWord, tailWord_3370609, baseEnd_3370609] using wordTrace_append hprefix tailTrace_3370609
  have hstable : (prefixWord ++ tailWord_3370609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370609).length < 2 ^ (prefixWord ++ tailWord_3370609).sum := by decide
  have hdescent : baseEnd_3370609 < baseStart_3370609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370610 : List Nat := [3, 2, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_3370610 : Nat := 118140960795 + 3370610 * 2 ^ 59
def prefixEnd_3370610 : Nat := 4983230072969 + 3 ^ 40 * 3370610 * 2
def baseEnd_3370610 : Nat := 576914342950387568857951

theorem tailTrace_3370610 : CollatzResearch.WordTrace tailWord_3370610 prefixEnd_3370610 576914342950387568857951 := by
  unfold tailWord_3370610
  simp only [CollatzResearch.WordTrace]
  refine ⟨30734061579715774800731321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81957497545908732801950189 30734061579715774800731321)
  ·
    refine ⟨23050546184786831100548491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30734061579715774800731321 23050546184786831100548491)
    ·
      refine ⟨34575819277180246650822737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23050546184786831100548491 34575819277180246650822737)
      ·
        refine ⟨25931864457885184988117053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34575819277180246650822737 25931864457885184988117053)
        ·
          refine ⟨9724449171706944370543895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25931864457885184988117053 9724449171706944370543895)
          ·
            refine ⟨14586673757560416555815843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9724449171706944370543895 14586673757560416555815843)
            ·
              refine ⟨21880010636340624833723765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14586673757560416555815843 21880010636340624833723765)
              ·
                refine ⟨2051250997156933578161603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21880010636340624833723765 2051250997156933578161603)
                ·
                  refine ⟨3076876495735400367242405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051250997156933578161603 3076876495735400367242405)
                  ·
                    refine ⟨576914342950387568857951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3076876495735400367242405 576914342950387568857951)
                    ·
                      rfl

theorem cell23_3370610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_3370610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370610 prefixEnd_3370610 := by exact prefixLift 3370610
  have htrace : WordTrace (prefixWord ++ tailWord_3370610) baseStart_3370610 baseEnd_3370610 := by
    simpa [prefixWord, tailWord_3370610, baseEnd_3370610] using wordTrace_append hprefix tailTrace_3370610
  have hstable : (prefixWord ++ tailWord_3370610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370610).length < 2 ^ (prefixWord ++ tailWord_3370610).sum := by decide
  have hdescent : baseEnd_3370610 < baseStart_3370610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370633 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 3, 1, 3]
def baseStart_3370633 : Nat := 118140960795 + 3370633 * 2 ^ 59
def prefixEnd_3370633 : Nat := 4983230072969 + 3 ^ 40 * 3370633 * 2
def baseEnd_3370633 : Nat := 1730754838906216116586247

theorem tailTrace_3370633 : CollatzResearch.WordTrace tailWord_3370633 prefixEnd_3370633 1730754838906216116586247 := by
  unfold tailWord_3370633
  simp only [CollatzResearch.WordTrace]
  refine ⟨122937085197779774131012553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81958056798519849420675035 122937085197779774131012553)
  ·
    refine ⟨92202813898334830598259415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122937085197779774131012553 92202813898334830598259415)
    ·
      refine ⟨138304220847502245897389123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92202813898334830598259415 138304220847502245897389123)
      ·
        refine ⟨207456331271253368846083685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138304220847502245897389123 207456331271253368846083685)
        ·
          refine ⟨38898062113360006658640691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207456331271253368846083685 38898062113360006658640691)
          ·
            refine ⟨58347093170040009987961037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38898062113360006658640691 58347093170040009987961037)
            ·
              refine ⟨21880159938765003745485389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58347093170040009987961037 21880159938765003745485389)
              ·
                refine ⟨8205059977036876404557021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21880159938765003745485389 8205059977036876404557021)
                ·
                  refine ⟨3076897491388828651708883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8205059977036876404557021 3076897491388828651708883)
                  ·
                    refine ⟨4615346237083242977563325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3076897491388828651708883 4615346237083242977563325)
                    ·
                      refine ⟨1730754838906216116586247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4615346237083242977563325 1730754838906216116586247)
                      ·
                        rfl

theorem cell23_3370633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 1, 3].length) (baseStart_3370633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370633 prefixEnd_3370633 := by exact prefixLift 3370633
  have htrace : WordTrace (prefixWord ++ tailWord_3370633) baseStart_3370633 baseEnd_3370633 := by
    simpa [prefixWord, tailWord_3370633, baseEnd_3370633] using wordTrace_append hprefix tailTrace_3370633
  have hstable : (prefixWord ++ tailWord_3370633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370633).length < 2 ^ (prefixWord ++ tailWord_3370633).sum := by decide
  have hdescent : baseEnd_3370633 < baseStart_3370633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370677 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_3370677 : Nat := 118140960795 + 3370677 * 2 ^ 59
def prefixEnd_3370677 : Nat := 4983230072969 + 3 ^ 40 * 3370677 * 2
def baseEnd_3370677 : Nat := 1730777432055013944436045

theorem tailTrace_3370677 : CollatzResearch.WordTrace tailWord_3370677 prefixEnd_3370677 1730777432055013944436045 := by
  unfold tailWord_3370677
  simp only [CollatzResearch.WordTrace]
  refine ⟨122938690009620369645614285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81959126673080246430409523 122938690009620369645614285)
  ·
    refine ⟨46102008753607638617105357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122938690009620369645614285 46102008753607638617105357)
    ·
      refine ⟨17288253282602864481414509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46102008753607638617105357 17288253282602864481414509)
      ·
        refine ⟨6483094980976074180530441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17288253282602864481414509 6483094980976074180530441)
        ·
          refine ⟨4862321235732055635397831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6483094980976074180530441 4862321235732055635397831)
          ·
            refine ⟨7293481853598083453096747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4862321235732055635397831 7293481853598083453096747)
            ·
              refine ⟨10940222780397125179645121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7293481853598083453096747 10940222780397125179645121)
              ·
                refine ⟨8205167085297843884733841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10940222780397125179645121 8205167085297843884733841)
                ·
                  refine ⟨6153875313973382913550381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8205167085297843884733841 6153875313973382913550381)
                  ·
                    refine ⟨2307703242740018592581393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6153875313973382913550381 2307703242740018592581393)
                    ·
                      refine ⟨1730777432055013944436045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307703242740018592581393 1730777432055013944436045)
                      ·
                        rfl

theorem cell23_3370677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_3370677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370677 prefixEnd_3370677 := by exact prefixLift 3370677
  have htrace : WordTrace (prefixWord ++ tailWord_3370677) baseStart_3370677 baseEnd_3370677 := by
    simpa [prefixWord, tailWord_3370677, baseEnd_3370677] using wordTrace_append hprefix tailTrace_3370677
  have hstable : (prefixWord ++ tailWord_3370677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370677).length < 2 ^ (prefixWord ++ tailWord_3370677).sum := by decide
  have hdescent : baseEnd_3370677 < baseStart_3370677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370684 : List Nat := [2, 2, 2, 3, 1, 3, 3, 2, 1, 1, 3]
def baseStart_3370684 : Nat := 118140960795 + 3370684 * 2 ^ 59
def prefixEnd_3370684 : Nat := 4983230072969 + 3 ^ 40 * 3370684 * 2
def baseEnd_3370684 : Nat := 1730781026419595417048513

theorem tailTrace_3370684 : CollatzResearch.WordTrace tailWord_3370684 prefixEnd_3370684 1730781026419595417048513 := by
  unfold tailWord_3370684
  simp only [CollatzResearch.WordTrace]
  refine ⟨61469472660297504920559553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81959296880396673227412737 61469472660297504920559553)
  ·
    refine ⟨46102104495223128690419665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61469472660297504920559553 46102104495223128690419665)
    ·
      refine ⟨34576578371417346517814749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46102104495223128690419665 34576578371417346517814749)
      ·
        refine ⟨12966216889281504944180531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34576578371417346517814749 12966216889281504944180531)
        ·
          refine ⟨19449325333922257416270797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12966216889281504944180531 19449325333922257416270797)
          ·
            refine ⟨7293497000220846531101549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19449325333922257416270797 7293497000220846531101549)
            ·
              refine ⟨2735061375082817449163081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7293497000220846531101549 2735061375082817449163081)
              ·
                refine ⟨2051296031312113086872311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2735061375082817449163081 2051296031312113086872311)
                ·
                  refine ⟨3076944046968169630308467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051296031312113086872311 3076944046968169630308467)
                  ·
                    refine ⟨4615416070452254445462701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3076944046968169630308467 4615416070452254445462701)
                    ·
                      refine ⟨1730781026419595417048513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4615416070452254445462701 1730781026419595417048513)
                      ·
                        rfl

theorem cell23_3370684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_3370684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370684 prefixEnd_3370684 := by exact prefixLift 3370684
  have htrace : WordTrace (prefixWord ++ tailWord_3370684) baseStart_3370684 baseEnd_3370684 := by
    simpa [prefixWord, tailWord_3370684, baseEnd_3370684] using wordTrace_append hprefix tailTrace_3370684
  have hstable : (prefixWord ++ tailWord_3370684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370684).length < 2 ^ (prefixWord ++ tailWord_3370684).sum := by decide
  have hdescent : baseEnd_3370684 < baseStart_3370684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370696 : List Nat := [2, 1, 3, 1, 2, 2, 4, 8]
def baseStart_3370696 : Nat := 118140960795 + 3370696 * 2 ^ 59
def prefixEnd_3370696 : Nat := 4983230072969 + 3 ^ 40 * 3370696 * 2
def baseEnd_3370696 : Nat := 64103229192127754448091

theorem tailTrace_3370696 : CollatzResearch.WordTrace tailWord_3370696 prefixEnd_3370696 64103229192127754448091 := by
  unfold tailWord_3370696
  simp only [CollatzResearch.WordTrace]
  refine ⟨61469691498275767945277971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81959588664367690593703961 61469691498275767945277971)
  ·
    refine ⟨92204537247413651917916957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61469691498275767945277971 92204537247413651917916957)
    ·
      refine ⟨34576701467780119469218859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92204537247413651917916957 34576701467780119469218859)
      ·
        refine ⟨51865052201670179203828289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34576701467780119469218859 51865052201670179203828289)
        ·
          refine ⟨38898789151252634402871217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51865052201670179203828289 38898789151252634402871217)
          ·
            refine ⟨29174091863439475802153413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38898789151252634402871217 29174091863439475802153413)
            ·
              refine ⟨5470142224394901712903765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29174091863439475802153413 5470142224394901712903765)
              ·
                refine ⟨64103229192127754448091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5470142224394901712903765 64103229192127754448091)
                ·
                  rfl

theorem cell23_3370696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 4, 8].length) (baseStart_3370696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370696 prefixEnd_3370696 := by exact prefixLift 3370696
  have htrace : WordTrace (prefixWord ++ tailWord_3370696) baseStart_3370696 baseEnd_3370696 := by
    simpa [prefixWord, tailWord_3370696, baseEnd_3370696] using wordTrace_append hprefix tailTrace_3370696
  have hstable : (prefixWord ++ tailWord_3370696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370696).length < 2 ^ (prefixWord ++ tailWord_3370696).sum := by decide
  have hdescent : baseEnd_3370696 < baseStart_3370696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370727 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3370727 : Nat := 118140960795 + 3370727 * 2 ^ 59
def prefixEnd_3370727 : Nat := 4983230072969 + 3 ^ 40 * 3370727 * 2
def baseEnd_3370727 : Nat := 1730803106087738748810815

theorem tailTrace_3370727 : CollatzResearch.WordTrace tailWord_3370727 prefixEnd_3370727 1730803106087738748810815 := by
  unfold tailWord_3370727
  simp only [CollatzResearch.WordTrace]
  refine ⟨122940513659439228184934435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81960342439626152123289623 122940513659439228184934435)
  ·
    refine ⟨184410770489158842277401653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122940513659439228184934435 184410770489158842277401653)
    ·
      refine ⟨17288509733358641463506405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184410770489158842277401653 17288509733358641463506405)
      ·
        refine ⟨3241595575004745274407451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17288509733358641463506405 3241595575004745274407451)
        ·
          refine ⟨4862393362507117911611177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3241595575004745274407451 4862393362507117911611177)
          ·
            refine ⟨3646795021880338433708383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4862393362507117911611177 3646795021880338433708383)
            ·
              refine ⟨5470192532820507650562575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646795021880338433708383 5470192532820507650562575)
              ·
                refine ⟨8205288799230761475843863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5470192532820507650562575 8205288799230761475843863)
                ·
                  refine ⟨12307933198846142213765795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8205288799230761475843863 12307933198846142213765795)
                  ·
                    refine ⟨18461899798269213320648693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12307933198846142213765795 18461899798269213320648693)
                    ·
                      refine ⟨1730803106087738748810815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18461899798269213320648693 1730803106087738748810815)
                      ·
                        rfl

theorem cell23_3370727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3370727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370727 prefixEnd_3370727 := by exact prefixLift 3370727
  have htrace : WordTrace (prefixWord ++ tailWord_3370727) baseStart_3370727 baseEnd_3370727 := by
    simpa [prefixWord, tailWord_3370727, baseEnd_3370727] using wordTrace_append hprefix tailTrace_3370727
  have hstable : (prefixWord ++ tailWord_3370727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370727).length < 2 ^ (prefixWord ++ tailWord_3370727).sum := by decide
  have hdescent : baseEnd_3370727 < baseStart_3370727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370780 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_3370780 : Nat := 118140960795 + 3370780 * 2 ^ 59
def prefixEnd_3370780 : Nat := 4983230072969 + 3 ^ 40 * 3370780 * 2
def baseEnd_3370780 : Nat := 1730830320562427041448071

theorem tailTrace_3370780 : CollatzResearch.WordTrace tailWord_3370780 prefixEnd_3370780 1730830320562427041448071 := by
  unfold tailWord_3370780
  simp only [CollatzResearch.WordTrace]
  refine ⟨61471223364123609118306897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81961631152164812157742529 61471223364123609118306897)
  ·
    refine ⟨46103417523092706838730173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61471223364123609118306897 46103417523092706838730173)
    ·
      refine ⟨17288781571159765064523815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46103417523092706838730173 17288781571159765064523815)
      ·
        refine ⟨25933172356739647596785723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17288781571159765064523815 25933172356739647596785723)
        ·
          refine ⟨38899758535109471395178585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25933172356739647596785723 38899758535109471395178585)
          ·
            refine ⟨29174818901332103546383939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38899758535109471395178585 29174818901332103546383939)
            ·
              refine ⟨43762228351998155319575909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29174818901332103546383939 43762228351998155319575909)
              ·
                refine ⟨8205417815999654122420483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43762228351998155319575909 8205417815999654122420483)
                ·
                  refine ⟨12308126723999481183630725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8205417815999654122420483 12308126723999481183630725)
                  ·
                    refine ⟨2307773760749902721930761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12308126723999481183630725 2307773760749902721930761)
                    ·
                      refine ⟨1730830320562427041448071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307773760749902721930761 1730830320562427041448071)
                      ·
                        rfl

theorem cell23_3370780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_3370780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370780 prefixEnd_3370780 := by exact prefixLift 3370780
  have htrace : WordTrace (prefixWord ++ tailWord_3370780) baseStart_3370780 baseEnd_3370780 := by
    simpa [prefixWord, tailWord_3370780, baseEnd_3370780] using wordTrace_append hprefix tailTrace_3370780
  have hstable : (prefixWord ++ tailWord_3370780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370780).length < 2 ^ (prefixWord ++ tailWord_3370780).sum := by decide
  have hdescent : baseEnd_3370780 < baseStart_3370780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370814 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 1, 4, 2]
def baseStart_3370814 : Nat := 118140960795 + 3370814 * 2 ^ 59
def prefixEnd_3370814 : Nat := 4983230072969 + 3 ^ 40 * 3370814 * 2
def baseEnd_3370814 : Nat := 1730847778904679908422915

theorem tailTrace_3370814 : CollatzResearch.WordTrace tailWord_3370814 prefixEnd_3370814 1730847778904679908422915 := by
  unfold tailWord_3370814
  simp only [CollatzResearch.WordTrace]
  refine ⟨15367960851265505255418937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81962457873416028028900997 15367960851265505255418937)
  ·
    refine ⟨11525970638449128941564203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15367960851265505255418937 11525970638449128941564203)
    ·
      refine ⟨17288955957673693412346305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11525970638449128941564203 17288955957673693412346305)
      ·
        refine ⟨12966716968255270059259729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17288955957673693412346305 12966716968255270059259729)
        ·
          refine ⟨9725037726191452544444797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12966716968255270059259729 9725037726191452544444797)
          ·
            refine ⟨3646889147321794704166799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9725037726191452544444797 3646889147321794704166799)
            ·
              refine ⟨5470333720982692056250199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646889147321794704166799 5470333720982692056250199)
              ·
                refine ⟨8205500581474038084375299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5470333720982692056250199 8205500581474038084375299)
                ·
                  refine ⟨12308250872211057126562949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8205500581474038084375299 12308250872211057126562949)
                  ·
                    refine ⟨2307797038539573211230553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12308250872211057126562949 2307797038539573211230553)
                    ·
                      refine ⟨1730847778904679908422915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307797038539573211230553 1730847778904679908422915)
                      ·
                        rfl

theorem cell23_3370814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_3370814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370814 prefixEnd_3370814 := by exact prefixLift 3370814
  have htrace : WordTrace (prefixWord ++ tailWord_3370814) baseStart_3370814 baseEnd_3370814 := by
    simpa [prefixWord, tailWord_3370814, baseEnd_3370814] using wordTrace_append hprefix tailTrace_3370814
  have hstable : (prefixWord ++ tailWord_3370814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370814).length < 2 ^ (prefixWord ++ tailWord_3370814).sum := by decide
  have hdescent : baseEnd_3370814 < baseStart_3370814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370833 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 1, 7]
def baseStart_3370833 : Nat := 118140960795 + 3370833 * 2 ^ 59
def prefixEnd_3370833 : Nat := 4983230072969 + 3 ^ 40 * 3370833 * 2
def baseEnd_3370833 : Nat := 576952511679038444695109

theorem tailTrace_3370833 : CollatzResearch.WordTrace tailWord_3370833 prefixEnd_3370833 576952511679038444695109 := by
  unfold tailWord_3370833
  simp only [CollatzResearch.WordTrace]
  refine ⟨122944379797055208288293153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81962919864703472192195435 122944379797055208288293153)
  ·
    refine ⟨92208284847791406216219865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122944379797055208288293153 92208284847791406216219865)
    ·
      refine ⟨69156213635843554662164899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92208284847791406216219865 69156213635843554662164899)
      ·
        refine ⟨103734320453765331993247349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69156213635843554662164899 103734320453765331993247349)
        ·
          refine ⟨9725092542540499874366939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103734320453765331993247349 9725092542540499874366939)
          ·
            refine ⟨14587638813810749811550409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9725092542540499874366939 14587638813810749811550409)
            ·
              refine ⟨10940729110358062358662807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14587638813810749811550409 10940729110358062358662807)
              ·
                refine ⟨16411093665537093537994211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10940729110358062358662807 16411093665537093537994211)
                ·
                  refine ⟨24616640498305640306991317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16411093665537093537994211 24616640498305640306991317)
                  ·
                    refine ⟨576952511679038444695109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24616640498305640306991317 576952511679038444695109)
                    ·
                      rfl

theorem cell23_3370833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_3370833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370833 prefixEnd_3370833 := by exact prefixLift 3370833
  have htrace : WordTrace (prefixWord ++ tailWord_3370833) baseStart_3370833 baseEnd_3370833 := by
    simpa [prefixWord, tailWord_3370833, baseEnd_3370833] using wordTrace_append hprefix tailTrace_3370833
  have hstable : (prefixWord ++ tailWord_3370833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370833).length < 2 ^ (prefixWord ++ tailWord_3370833).sum := by decide
  have hdescent : baseEnd_3370833 < baseStart_3370833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370837 : List Nat := [1, 3, 2, 2, 2, 4, 1, 3, 5]
def baseStart_3370837 : Nat := 118140960795 + 3370837 * 2 ^ 59
def prefixEnd_3370837 : Nat := 4983230072969 + 3 ^ 40 * 3370837 * 2
def baseEnd_3370837 : Nat := 192317732106637035381701

theorem tailTrace_3370837 : CollatzResearch.WordTrace tailWord_3370837 prefixEnd_3370837 192317732106637035381701 := by
  unfold tailWord_3370837
  simp only [CollatzResearch.WordTrace]
  refine ⟨122944525689040716971438765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81963017126027144647625843 122944525689040716971438765)
  ·
    refine ⟨46104197133390268864289537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122944525689040716971438765 46104197133390268864289537)
    ·
      refine ⟨34578147850042701648217153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46104197133390268864289537 34578147850042701648217153)
      ·
        refine ⟨25933610887532026236162865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34578147850042701648217153 25933610887532026236162865)
        ·
          refine ⟨19450208165649019677122149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25933610887532026236162865 19450208165649019677122149)
          ·
            refine ⟨3646914031059191189460403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19450208165649019677122149 3646914031059191189460403)
            ·
              refine ⟨5470371046588786784190605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646914031059191189460403 5470371046588786784190605)
              ·
                refine ⟨2051389142470795044071477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5470371046588786784190605 2051389142470795044071477)
                ·
                  refine ⟨192317732106637035381701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2051389142470795044071477 192317732106637035381701)
                  ·
                    rfl

theorem cell23_3370837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_3370837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370837 prefixEnd_3370837 := by exact prefixLift 3370837
  have htrace : WordTrace (prefixWord ++ tailWord_3370837) baseStart_3370837 baseEnd_3370837 := by
    simpa [prefixWord, tailWord_3370837, baseEnd_3370837] using wordTrace_append hprefix tailTrace_3370837
  have hstable : (prefixWord ++ tailWord_3370837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370837).length < 2 ^ (prefixWord ++ tailWord_3370837).sum := by decide
  have hdescent : baseEnd_3370837 < baseStart_3370837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370850 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3370850 : Nat := 118140960795 + 3370850 * 2 ^ 59
def prefixEnd_3370850 : Nat := 4983230072969 + 3 ^ 40 * 3370850 * 2
def baseEnd_3370850 : Nat := 576955421402747255857583

theorem tailTrace_3370850 : CollatzResearch.WordTrace tailWord_3370850 prefixEnd_3370850 576955421402747255857583 := by
  unfold tailWord_3370850
  simp only [CollatzResearch.WordTrace]
  refine ⟨30736249959498405047915501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81963333225329080127774669 30736249959498405047915501)
  ·
    refine ⟨11526093734811901892968313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30736249959498405047915501 11526093734811901892968313)
    ·
      refine ⟨8644570301108926419726235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11526093734811901892968313 8644570301108926419726235)
      ·
        refine ⟨12966855451663389629589353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8644570301108926419726235 12966855451663389629589353)
        ·
          refine ⟨9725141588747542222192015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12966855451663389629589353 9725141588747542222192015)
          ·
            refine ⟨14587712383121313333288023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9725141588747542222192015 14587712383121313333288023)
            ·
              refine ⟨21881568574681969999932035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14587712383121313333288023 21881568574681969999932035)
              ·
                refine ⟨32822352862022954999898053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21881568574681969999932035 32822352862022954999898053)
                ·
                  refine ⟨6154191161629304062480885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32822352862022954999898053 6154191161629304062480885)
                  ·
                    refine ⟨576955421402747255857583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6154191161629304062480885 576955421402747255857583)
                    ·
                      rfl

theorem cell23_3370850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3370850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370850 prefixEnd_3370850 := by exact prefixLift 3370850
  have htrace : WordTrace (prefixWord ++ tailWord_3370850) baseStart_3370850 baseEnd_3370850 := by
    simpa [prefixWord, tailWord_3370850, baseEnd_3370850] using wordTrace_append hprefix tailTrace_3370850
  have hstable : (prefixWord ++ tailWord_3370850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370850).length < 2 ^ (prefixWord ++ tailWord_3370850).sum := by decide
  have hdescent : baseEnd_3370850 < baseStart_3370850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370887 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_3370887 : Nat := 118140960795 + 3370887 * 2 ^ 59
def prefixEnd_3370887 : Nat := 4983230072969 + 3 ^ 40 * 3370887 * 2
def baseEnd_3370887 : Nat := 1730885262992458122810079

theorem tailTrace_3370887 : CollatzResearch.WordTrace tailWord_3370887 prefixEnd_3370887 1730885262992458122810079 := by
  unfold tailWord_3370887
  simp only [CollatzResearch.WordTrace]
  refine ⟨122946349338859575510758915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81964232892573050340505943 122946349338859575510758915)
  ·
    refine ⟨184419524008289363266138373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122946349338859575510758915 184419524008289363266138373)
    ·
      refine ⟨34578660751554255612400945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184419524008289363266138373 34578660751554255612400945)
      ·
        refine ⟨25933995563665691709300709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34578660751554255612400945 25933995563665691709300709)
        ·
          refine ⟨4862624168187317195493883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25933995563665691709300709 4862624168187317195493883)
          ·
            refine ⟨7293936252280975793240825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4862624168187317195493883 7293936252280975793240825)
            ·
              refine ⟨5470452189210731844930619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7293936252280975793240825 5470452189210731844930619)
              ·
                refine ⟨8205678283816097767395929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5470452189210731844930619 8205678283816097767395929)
                ·
                  refine ⟨6154258712862073325546947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8205678283816097767395929 6154258712862073325546947)
                  ·
                    refine ⟨9231388069293109988320421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6154258712862073325546947 9231388069293109988320421)
                    ·
                      refine ⟨1730885262992458122810079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9231388069293109988320421 1730885262992458122810079)
                      ·
                        rfl

theorem cell23_3370887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_3370887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370887 prefixEnd_3370887 := by exact prefixLift 3370887
  have htrace : WordTrace (prefixWord ++ tailWord_3370887) baseStart_3370887 baseEnd_3370887 := by
    simpa [prefixWord, tailWord_3370887, baseEnd_3370887] using wordTrace_append hprefix tailTrace_3370887
  have hstable : (prefixWord ++ tailWord_3370887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370887).length < 2 ^ (prefixWord ++ tailWord_3370887).sum := by decide
  have hdescent : baseEnd_3370887 < baseStart_3370887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370937 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3370937 : Nat := 118140960795 + 3370937 * 2 ^ 59
def prefixEnd_3370937 : Nat := 4983230072969 + 3 ^ 40 * 3370937 * 2
def baseEnd_3370937 : Nat := 1730910937025182927184849

theorem tailTrace_3370937 : CollatzResearch.WordTrace tailWord_3370937 prefixEnd_3370937 1730910937025182927184849 := by
  unfold tailWord_3370937
  simp only [CollatzResearch.WordTrace]
  refine ⟨122948172988678434050079065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81965448659118956033386043 122948172988678434050079065)
  ·
    refine ⟨92211129741508825537559299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122948172988678434050079065 92211129741508825537559299)
    ·
      refine ⟨138316694612263238306338949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92211129741508825537559299 138316694612263238306338949)
      ·
        refine ⟨25934380239799357182438553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138316694612263238306338949 25934380239799357182438553)
        ·
          refine ⟨19450785179849517886828915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25934380239799357182438553 19450785179849517886828915)
          ·
            refine ⟨29176177769774276830243373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19450785179849517886828915 29176177769774276830243373)
            ·
              refine ⟨10941066663665353811341265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29176177769774276830243373 10941066663665353811341265)
              ·
                refine ⟨8205799997749015358505949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10941066663665353811341265 8205799997749015358505949)
                ·
                  refine ⟨3077174999155880759439731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8205799997749015358505949 3077174999155880759439731)
                  ·
                    refine ⟨4615762498733821139159597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3077174999155880759439731 4615762498733821139159597)
                    ·
                      refine ⟨1730910937025182927184849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4615762498733821139159597 1730910937025182927184849)
                      ·
                        rfl

theorem cell23_3370937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3370937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370937 prefixEnd_3370937 := by exact prefixLift 3370937
  have htrace : WordTrace (prefixWord ++ tailWord_3370937) baseStart_3370937 baseEnd_3370937 := by
    simpa [prefixWord, tailWord_3370937, baseEnd_3370937] using wordTrace_append hprefix tailTrace_3370937
  have hstable : (prefixWord ++ tailWord_3370937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370937).length < 2 ^ (prefixWord ++ tailWord_3370937).sum := by decide
  have hdescent : baseEnd_3370937 < baseStart_3370937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370954 : List Nat := [3, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3]
def baseStart_3370954 : Nat := 118140960795 + 3370954 * 2 ^ 59
def prefixEnd_3370954 : Nat := 4983230072969 + 3 ^ 40 * 3370954 * 2
def baseEnd_3370954 : Nat := 1730919666196309360672271

theorem tailTrace_3370954 : CollatzResearch.WordTrace tailWord_3370954 prefixEnd_3370954 1730919666196309360672271 := by
  unfold tailWord_3370954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30737198257404211488361979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81965862019744563968965277 30737198257404211488361979)
  ·
    refine ⟨46105797386106317232542969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30737198257404211488361979 46105797386106317232542969)
    ·
      refine ⟨34579348039579737924407227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46105797386106317232542969 34579348039579737924407227)
      ·
        refine ⟨51869022059369606886610841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34579348039579737924407227 51869022059369606886610841)
        ·
          refine ⟨38901766544527205164958131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51869022059369606886610841 38901766544527205164958131)
          ·
            refine ⟨58352649816790807747437197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38901766544527205164958131 58352649816790807747437197)
            ·
              refine ⟨21882243681296552905288949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58352649816790807747437197 21882243681296552905288949)
              ·
                refine ⟨2051460345121551834870839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21882243681296552905288949 2051460345121551834870839)
                ·
                  refine ⟨3077190517682327752306259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051460345121551834870839 3077190517682327752306259)
                  ·
                    refine ⟨4615785776523491628459389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3077190517682327752306259 4615785776523491628459389)
                    ·
                      refine ⟨1730919666196309360672271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4615785776523491628459389 1730919666196309360672271)
                      ·
                        rfl

theorem cell23_3370954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_3370954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370954 prefixEnd_3370954 := by exact prefixLift 3370954
  have htrace : WordTrace (prefixWord ++ tailWord_3370954) baseStart_3370954 baseEnd_3370954 := by
    simpa [prefixWord, tailWord_3370954, baseEnd_3370954] using wordTrace_append hprefix tailTrace_3370954
  have hstable : (prefixWord ++ tailWord_3370954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370954).length < 2 ^ (prefixWord ++ tailWord_3370954).sum := by decide
  have hdescent : baseEnd_3370954 < baseStart_3370954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370980 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_3370980 : Nat := 118140960795 + 3370980 * 2 ^ 59
def prefixEnd_3370980 : Nat := 4983230072969 + 3 ^ 40 * 3370980 * 2
def baseEnd_3370980 : Nat := 1730933016693326258947151

theorem tailTrace_3370980 : CollatzResearch.WordTrace tailWord_3370980 prefixEnd_3370980 1730933016693326258947151 := by
  unfold tailWord_3370980
  simp only [CollatzResearch.WordTrace]
  refine ⟨61474870663761326196947197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81966494218348434929262929 61474870663761326196947197)
  ·
    refine ⟨23053076498910497323855199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61474870663761326196947197 23053076498910497323855199)
    ·
      refine ⟨34579614748365745985782799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23053076498910497323855199 34579614748365745985782799)
      ·
        refine ⟨51869422122548618978674199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34579614748365745985782799 51869422122548618978674199)
        ·
          refine ⟨77804133183822928468011299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51869422122548618978674199 77804133183822928468011299)
          ·
            refine ⟨116706199775734392702016949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77804133183822928468011299 116706199775734392702016949)
            ·
              refine ⟨10941206228975099315814089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116706199775734392702016949 10941206228975099315814089)
              ·
                refine ⟨8205904671731324486860567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10941206228975099315814089 8205904671731324486860567)
                ·
                  refine ⟨12308857007596986730290851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8205904671731324486860567 12308857007596986730290851)
                  ·
                    refine ⟨18463285511395480095436277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12308857007596986730290851 18463285511395480095436277)
                    ·
                      refine ⟨1730933016693326258947151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18463285511395480095436277 1730933016693326258947151)
                      ·
                        rfl

theorem cell23_3370980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_3370980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370980 prefixEnd_3370980 := by exact prefixLift 3370980
  have htrace : WordTrace (prefixWord ++ tailWord_3370980) baseStart_3370980 baseEnd_3370980 := by
    simpa [prefixWord, tailWord_3370980, baseEnd_3370980] using wordTrace_append hprefix tailTrace_3370980
  have hstable : (prefixWord ++ tailWord_3370980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370980).length < 2 ^ (prefixWord ++ tailWord_3370980).sum := by decide
  have hdescent : baseEnd_3370980 < baseStart_3370980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371000 : List Nat := [2, 1, 2, 1, 1, 3, 6, 7]
def baseStart_3371000 : Nat := 118140960795 + 3371000 * 2 ^ 59
def prefixEnd_3371000 : Nat := 4983230072969 + 3 ^ 40 * 3371000 * 2
def baseEnd_3371000 : Nat := 64109010603941340025817

theorem tailTrace_3371000 : CollatzResearch.WordTrace tailWord_3371000 prefixEnd_3371000 64109010603941340025817 := by
  unfold tailWord_3371000
  simp only [CollatzResearch.WordTrace]
  refine ⟨61475235393725097904811227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81966980524966797206414969 61475235393725097904811227)
  ·
    refine ⟨92212853090587646857216841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61475235393725097904811227 92212853090587646857216841)
    ·
      refine ⟨69159639817940735142912631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92212853090587646857216841 69159639817940735142912631)
      ·
        refine ⟨103739459726911102714368947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69159639817940735142912631 103739459726911102714368947)
        ·
          refine ⟨155609189590366654071553421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103739459726911102714368947 155609189590366654071553421)
          ·
            refine ⟨58353446096387495276832533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155609189590366654071553421 58353446096387495276832533)
            ·
              refine ⟨2735317785768163841101525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58353446096387495276832533 2735317785768163841101525)
              ·
                refine ⟨64109010603941340025817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2735317785768163841101525 64109010603941340025817)
                ·
                  rfl

theorem cell23_3371000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6, 7].length) (baseStart_3371000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371000 prefixEnd_3371000 := by exact prefixLift 3371000
  have htrace : WordTrace (prefixWord ++ tailWord_3371000) baseStart_3371000 baseEnd_3371000 := by
    simpa [prefixWord, tailWord_3371000, baseEnd_3371000] using wordTrace_append hprefix tailTrace_3371000
  have hstable : (prefixWord ++ tailWord_3371000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371000).length < 2 ^ (prefixWord ++ tailWord_3371000).sum := by decide
  have hdescent : baseEnd_3371000 < baseStart_3371000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371023 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 7]
def baseStart_3371023 : Nat := 118140960795 + 3371023 * 2 ^ 59
def prefixEnd_3371023 : Nat := 4983230072969 + 3 ^ 40 * 3371023 * 2
def baseEnd_3371023 : Nat := 1730955096361469590709453

theorem tailTrace_3371023 : CollatzResearch.WordTrace tailWord_3371023 prefixEnd_3371023 1730955096361469590709453 := by
  unfold tailWord_3371023
  simp only [CollatzResearch.WordTrace]
  refine ⟨122951309666366870737709723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81967539777577913825139815 122951309666366870737709723)
  ·
    refine ⟨184426964499550306106564585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122951309666366870737709723 184426964499550306106564585)
    ·
      refine ⟨138320223374662729579923439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184426964499550306106564585 138320223374662729579923439)
      ·
        refine ⟨207480335061994094369885159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138320223374662729579923439 207480335061994094369885159)
        ·
          refine ⟨311220502592991141554827739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207480335061994094369885159 311220502592991141554827739)
          ·
            refine ⟨466830753889486712332241609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311220502592991141554827739 466830753889486712332241609)
            ·
              refine ⟨350123065417115034249181207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466830753889486712332241609 350123065417115034249181207)
              ·
                refine ⟨525184598125672551373771811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350123065417115034249181207 525184598125672551373771811)
                ·
                  refine ⟨787776897188508827060657717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 525184598125672551373771811 787776897188508827060657717)
                  ·
                    refine ⟨73854084111422702536936661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 787776897188508827060657717 73854084111422702536936661)
                    ·
                      refine ⟨1730955096361469590709453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73854084111422702536936661 1730955096361469590709453)
                      ·
                        rfl

theorem cell23_3371023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_3371023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371023 prefixEnd_3371023 := by exact prefixLift 3371023
  have htrace : WordTrace (prefixWord ++ tailWord_3371023) baseStart_3371023 baseEnd_3371023 := by
    simpa [prefixWord, tailWord_3371023, baseEnd_3371023] using wordTrace_append hprefix tailTrace_3371023
  have hstable : (prefixWord ++ tailWord_3371023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371023).length < 2 ^ (prefixWord ++ tailWord_3371023).sum := by decide
  have hdescent : baseEnd_3371023 < baseStart_3371023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371027 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 4, 1, 3]
def baseStart_3371027 : Nat := 118140960795 + 3371027 * 2 ^ 59
def prefixEnd_3371027 : Nat := 4983230072969 + 3 ^ 40 * 3371027 * 2
def baseEnd_3371027 : Nat := 1730957150284087575059435

theorem tailTrace_3371027 : CollatzResearch.WordTrace tailWord_3371027 prefixEnd_3371027 1730957150284087575059435 := by
  unfold tailWord_3371027
  simp only [CollatzResearch.WordTrace]
  refine ⟨122951455558352379420855335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81967637038901586280570223 122951455558352379420855335)
  ·
    refine ⟨184427183337528569131283003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122951455558352379420855335 184427183337528569131283003)
    ·
      refine ⟨276640775006292853696924505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184427183337528569131283003 276640775006292853696924505)
      ·
        refine ⟨207480581254719640272693379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276640775006292853696924505 207480581254719640272693379)
        ·
          refine ⟨311220871882079460409040069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207480581254719640272693379 311220871882079460409040069)
          ·
            refine ⟨58353913477889898826695013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311220871882079460409040069 58353913477889898826695013)
            ·
              refine ⟨10941358777104356030005315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58353913477889898826695013 10941358777104356030005315)
              ·
                refine ⟨16412038165656534045007973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10941358777104356030005315 16412038165656534045007973)
                ·
                  refine ⟨3077257156060600133438995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16412038165656534045007973 3077257156060600133438995)
                  ·
                    refine ⟨4615885734090900200158493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3077257156060600133438995 4615885734090900200158493)
                    ·
                      refine ⟨1730957150284087575059435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4615885734090900200158493 1730957150284087575059435)
                      ·
                        rfl

theorem cell23_3371027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 1, 3].length) (baseStart_3371027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371027 prefixEnd_3371027 := by exact prefixLift 3371027
  have htrace : WordTrace (prefixWord ++ tailWord_3371027) baseStart_3371027 baseEnd_3371027 := by
    simpa [prefixWord, tailWord_3371027, baseEnd_3371027] using wordTrace_append hprefix tailTrace_3371027
  have hstable : (prefixWord ++ tailWord_3371027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371027).length < 2 ^ (prefixWord ++ tailWord_3371027).sum := by decide
  have hdescent : baseEnd_3371027 < baseStart_3371027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371048 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3371048 : Nat := 118140960795 + 3371048 * 2 ^ 59
def prefixEnd_3371048 : Nat := 4983230072969 + 3 ^ 40 * 3371048 * 2
def baseEnd_3371048 : Nat := 1730967933377831992896839

theorem tailTrace_3371048 : CollatzResearch.WordTrace tailWord_3371048 prefixEnd_3371048 1730967933377831992896839 := by
  unfold tailWord_3371048
  simp only [CollatzResearch.WordTrace]
  refine ⟨61476110745638150003684899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81968147660850866671579865 61476110745638150003684899)
  ·
    refine ⟨92214166118457225005527349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61476110745638150003684899 92214166118457225005527349)
    ·
      refine ⟨8645078073605364844268189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92214166118457225005527349 8645078073605364844268189)
      ·
        refine ⟨3241904277602011816600571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8645078073605364844268189 3241904277602011816600571)
        ·
          refine ⟨4862856416403017724900857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3241904277602011816600571 4862856416403017724900857)
          ·
            refine ⟨3647142312302263293675643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4862856416403017724900857 3647142312302263293675643)
            ·
              refine ⟨5470713468453394940513465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3647142312302263293675643 5470713468453394940513465)
              ·
                refine ⟨4103035101340046205385099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5470713468453394940513465 4103035101340046205385099)
                ·
                  refine ⟨6154552652010069308077649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4103035101340046205385099 6154552652010069308077649)
                  ·
                    refine ⟨4615914489007551981058237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6154552652010069308077649 4615914489007551981058237)
                    ·
                      refine ⟨1730967933377831992896839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4615914489007551981058237 1730967933377831992896839)
                      ·
                        rfl

theorem cell23_3371048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3371048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371048 prefixEnd_3371048 := by exact prefixLift 3371048
  have htrace : WordTrace (prefixWord ++ tailWord_3371048) baseStart_3371048 baseEnd_3371048 := by
    simpa [prefixWord, tailWord_3371048, baseEnd_3371048] using wordTrace_append hprefix tailTrace_3371048
  have hstable : (prefixWord ++ tailWord_3371048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371048).length < 2 ^ (prefixWord ++ tailWord_3371048).sum := by decide
  have hdescent : baseEnd_3371048 < baseStart_3371048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371067 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 1, 4, 2]
def baseStart_3371067 : Nat := 118140960795 + 3371067 * 2 ^ 59
def prefixEnd_3371067 : Nat := 4983230072969 + 3 ^ 40 * 3371067 * 2
def baseEnd_3371067 : Nat := 1730977689510267418559251

theorem tailTrace_3371067 : CollatzResearch.WordTrace tailWord_3371067 prefixEnd_3371067 1730977689510267418559251 := by
  unfold tailWord_3371067
  simp only [CollatzResearch.WordTrace]
  refine ⟨122952914478207466252311455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81968609652138310834874303 122952914478207466252311455)
  ·
    refine ⟨184429371717311199378467183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122952914478207466252311455 184429371717311199378467183)
    ·
      refine ⟨276644057575966799067700775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184429371717311199378467183 276644057575966799067700775)
      ·
        refine ⟨414966086363950198601551163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276644057575966799067700775 414966086363950198601551163)
        ·
          refine ⟨622449129545925297902326745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414966086363950198601551163 622449129545925297902326745)
          ·
            refine ⟨466836847159443973426745059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622449129545925297902326745 466836847159443973426745059)
            ·
              refine ⟨700255270739165960140117589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466836847159443973426745059 700255270739165960140117589)
              ·
                refine ⟨8206116453974601095392003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 700255270739165960140117589 8206116453974601095392003)
                ·
                  refine ⟨12309174680961901643088005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8206116453974601095392003 12309174680961901643088005)
                  ·
                    refine ⟨2307970252680356558079001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12309174680961901643088005 2307970252680356558079001)
                    ·
                      refine ⟨1730977689510267418559251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307970252680356558079001 1730977689510267418559251)
                      ·
                        rfl

theorem cell23_3371067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 4, 2].length) (baseStart_3371067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371067 prefixEnd_3371067 := by exact prefixLift 3371067
  have htrace : WordTrace (prefixWord ++ tailWord_3371067) baseStart_3371067 baseEnd_3371067 := by
    simpa [prefixWord, tailWord_3371067, baseEnd_3371067] using wordTrace_append hprefix tailTrace_3371067
  have hstable : (prefixWord ++ tailWord_3371067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371067).length < 2 ^ (prefixWord ++ tailWord_3371067).sum := by decide
  have hdescent : baseEnd_3371067 < baseStart_3371067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371078 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3371078 : Nat := 118140960795 + 3371078 * 2 ^ 59
def prefixEnd_3371078 : Nat := 4983230072969 + 3 ^ 40 * 3371078 * 2
def baseEnd_3371078 : Nat := 1730983337797466875521701

theorem tailTrace_3371078 : CollatzResearch.WordTrace tailWord_3371078 prefixEnd_3371078 1730983337797466875521701 := by
  unfold tailWord_3371078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3842291115036487972842559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81968877120778410087307925 3842291115036487972842559)
  ·
    refine ⟨5763436672554731959263839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3842291115036487972842559 5763436672554731959263839)
    ·
      refine ⟨8645155008832097938895759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5763436672554731959263839 8645155008832097938895759)
      ·
        refine ⟨12967732513248146908343639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8645155008832097938895759 12967732513248146908343639)
        ·
          refine ⟨19451598769872220362515459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12967732513248146908343639 19451598769872220362515459)
          ·
            refine ⟨29177398154808330543773189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19451598769872220362515459 29177398154808330543773189)
            ·
              refine ⟨5470762154026561976957473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29177398154808330543773189 5470762154026561976957473)
              ·
                refine ⟨4103071615519921482718105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5470762154026561976957473 4103071615519921482718105)
                ·
                  refine ⟨3077303711639941112038579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4103071615519921482718105 3077303711639941112038579)
                  ·
                    refine ⟨4615955567459911668057869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3077303711639941112038579 4615955567459911668057869)
                    ·
                      refine ⟨1730983337797466875521701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4615955567459911668057869 1730983337797466875521701)
                      ·
                        rfl

theorem cell23_3371078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3371078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371078 prefixEnd_3371078 := by exact prefixLift 3371078
  have htrace : WordTrace (prefixWord ++ tailWord_3371078) baseStart_3371078 baseEnd_3371078 := by
    simpa [prefixWord, tailWord_3371078, baseEnd_3371078] using wordTrace_append hprefix tailTrace_3371078
  have hstable : (prefixWord ++ tailWord_3371078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371078).length < 2 ^ (prefixWord ++ tailWord_3371078).sum := by decide
  have hdescent : baseEnd_3371078 < baseStart_3371078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371084 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 4, 2, 2]
def baseStart_3371084 : Nat := 118140960795 + 3371084 * 2 ^ 59
def prefixEnd_3371084 : Nat := 4983230072969 + 3 ^ 40 * 3371084 * 2
def baseEnd_3371084 : Nat := 1730986418681393852046673

theorem tailTrace_3371084 : CollatzResearch.WordTrace tailWord_3371084 prefixEnd_3371084 1730986418681393852046673 := by
  unfold tailWord_3371084
  simp only [CollatzResearch.WordTrace]
  refine ⟨61476767259572939077840153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81969023012763918770453537 61476767259572939077840153)
  ·
    refine ⟨46107575444679704308380115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61476767259572939077840153 46107575444679704308380115)
    ·
      refine ⟨69161363167019556462570173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46107575444679704308380115 69161363167019556462570173)
      ·
        refine ⟨25935511187632333673463815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69161363167019556462570173 25935511187632333673463815)
        ·
          refine ⟨38903266781448500510195723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25935511187632333673463815 38903266781448500510195723)
          ·
            refine ⟨58354900172172750765293585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38903266781448500510195723 58354900172172750765293585)
            ·
              refine ⟨43766175129129563073970189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58354900172172750765293585 43766175129129563073970189)
              ·
                refine ⟨16412315673423586152738821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43766175129129563073970189 16412315673423586152738821)
                ·
                  refine ⟨3077309188766922403638529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16412315673423586152738821 3077309188766922403638529)
                  ·
                    refine ⟨2307981891575191802728897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3077309188766922403638529 2307981891575191802728897)
                    ·
                      refine ⟨1730986418681393852046673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307981891575191802728897 1730986418681393852046673)
                      ·
                        rfl

theorem cell23_3371084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_3371084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371084 prefixEnd_3371084 := by exact prefixLift 3371084
  have htrace : WordTrace (prefixWord ++ tailWord_3371084) baseStart_3371084 baseEnd_3371084 := by
    simpa [prefixWord, tailWord_3371084, baseEnd_3371084] using wordTrace_append hprefix tailTrace_3371084
  have hstable : (prefixWord ++ tailWord_3371084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371084).length < 2 ^ (prefixWord ++ tailWord_3371084).sum := by decide
  have hdescent : baseEnd_3371084 < baseStart_3371084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371094 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3371094 : Nat := 118140960795 + 3371094 * 2 ^ 59
def prefixEnd_3371094 : Nat := 4983230072969 + 3 ^ 40 * 3371094 * 2
def baseEnd_3371094 : Nat := 576997184495979604307209

theorem tailTrace_3371094 : CollatzResearch.WordTrace tailWord_3371094 prefixEnd_3371094 576997184495979604307209 := by
  unfold tailWord_3371094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7684618703069353116471521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81969266166073099909029557 7684618703069353116471521)
  ·
    refine ⟨5763464027302014837353641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7684618703069353116471521 5763464027302014837353641)
    ·
      refine ⟨4322598020476511128015231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5763464027302014837353641 4322598020476511128015231)
      ·
        refine ⟨6483897030714766692022847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4322598020476511128015231 6483897030714766692022847)
        ·
          refine ⟨9725845546072150038034271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6483897030714766692022847 9725845546072150038034271)
          ·
            refine ⟨14588768319108225057051407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9725845546072150038034271 14588768319108225057051407)
            ·
              refine ⟨21883152478662337585577111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14588768319108225057051407 21883152478662337585577111)
              ·
                refine ⟨32824728717993506378365667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21883152478662337585577111 32824728717993506378365667)
                ·
                  refine ⟨49237093076990259567548501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32824728717993506378365667 49237093076990259567548501)
                  ·
                    refine ⟨576997184495979604307209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49237093076990259567548501 576997184495979604307209)
                    ·
                      rfl

theorem cell23_3371094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3371094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371094 prefixEnd_3371094 := by exact prefixLift 3371094
  have htrace : WordTrace (prefixWord ++ tailWord_3371094) baseStart_3371094 baseEnd_3371094 := by
    simpa [prefixWord, tailWord_3371094, baseEnd_3371094] using wordTrace_append hprefix tailTrace_3371094
  have hstable : (prefixWord ++ tailWord_3371094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371094).length < 2 ^ (prefixWord ++ tailWord_3371094).sum := by decide
  have hdescent : baseEnd_3371094 < baseStart_3371094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371101 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3371101 : Nat := 118140960795 + 3371101 * 2 ^ 59
def prefixEnd_3371101 : Nat := 4983230072969 + 3 ^ 40 * 3371101 * 2
def baseEnd_3371101 : Nat := 1730995147852520285534095

theorem tailTrace_3371101 : CollatzResearch.WordTrace tailWord_3371101 prefixEnd_3371101 1730995147852520285534095 := by
  unfold tailWord_3371101
  simp only [CollatzResearch.WordTrace]
  refine ⟨122954154560084290059049157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81969436373389526706032771 122954154560084290059049157)
  ·
    refine ⟨23053903980015804386071717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122954154560084290059049157 23053903980015804386071717)
    ·
      refine ⟨4322606996252963322388447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23053903980015804386071717 4322606996252963322388447)
      ·
        refine ⟨6483910494379444983582671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4322606996252963322388447 6483910494379444983582671)
        ·
          refine ⟨9725865741569167475374007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6483910494379444983582671 9725865741569167475374007)
          ·
            refine ⟨14588798612353751213061011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9725865741569167475374007 14588798612353751213061011)
            ·
              refine ⟨21883197918530626819591517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14588798612353751213061011 21883197918530626819591517)
              ·
                refine ⟨8206199219448985057346819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21883197918530626819591517 8206199219448985057346819)
                ·
                  refine ⟨12309298829173477586020229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8206199219448985057346819 12309298829173477586020229)
                  ·
                    refine ⟨2307993530470027047378793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12309298829173477586020229 2307993530470027047378793)
                    ·
                      refine ⟨1730995147852520285534095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307993530470027047378793 1730995147852520285534095)
                      ·
                        rfl

theorem cell23_3371101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3371101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371101 prefixEnd_3371101 := by exact prefixLift 3371101
  have htrace : WordTrace (prefixWord ++ tailWord_3371101) baseStart_3371101 baseEnd_3371101 := by
    simpa [prefixWord, tailWord_3371101, baseEnd_3371101] using wordTrace_append hprefix tailTrace_3371101
  have hstable : (prefixWord ++ tailWord_3371101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371101).length < 2 ^ (prefixWord ++ tailWord_3371101).sum := by decide
  have hdescent : baseEnd_3371101 < baseStart_3371101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371117 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 1, 5, 3]
def baseStart_3371117 : Nat := 118140960795 + 3371117 * 2 ^ 59
def prefixEnd_3371117 : Nat := 4983230072969 + 3 ^ 40 * 3371117 * 2
def baseEnd_3371117 : Nat := 1731003363542992222934021

theorem tailTrace_3371117 : CollatzResearch.WordTrace tailWord_3371117 prefixEnd_3371117 1731003363542992222934021 := by
  unfold tailWord_3371117
  simp only [CollatzResearch.WordTrace]
  refine ⟨122954738128026324791631605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81969825418684216527754403 122954738128026324791631605)
  ·
    refine ⟨11527006699502467949215463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122954738128026324791631605 11527006699502467949215463)
    ·
      refine ⟨17290510049253701923823195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11527006699502467949215463 17290510049253701923823195)
      ·
        refine ⟨25935765073880552885734793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17290510049253701923823195 25935765073880552885734793)
        ·
          refine ⟨19451823805410414664301095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25935765073880552885734793 19451823805410414664301095)
          ·
            refine ⟨29177735708115621996451643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19451823805410414664301095 29177735708115621996451643)
            ·
              refine ⟨43766603562173432994677465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29177735708115621996451643 43766603562173432994677465)
              ·
                refine ⟨32824952671630074746008099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43766603562173432994677465 32824952671630074746008099)
                ·
                  refine ⟨49237429007445112119012149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32824952671630074746008099 49237429007445112119012149)
                  ·
                    refine ⟨4616008969447979261157389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49237429007445112119012149 4616008969447979261157389)
                    ·
                      refine ⟨1731003363542992222934021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4616008969447979261157389 1731003363542992222934021)
                      ·
                        rfl

theorem cell23_3371117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_3371117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371117 prefixEnd_3371117 := by exact prefixLift 3371117
  have htrace : WordTrace (prefixWord ++ tailWord_3371117) baseStart_3371117 baseEnd_3371117 := by
    simpa [prefixWord, tailWord_3371117, baseEnd_3371117] using wordTrace_append hprefix tailTrace_3371117
  have hstable : (prefixWord ++ tailWord_3371117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371117).length < 2 ^ (prefixWord ++ tailWord_3371117).sum := by decide
  have hdescent : baseEnd_3371117 < baseStart_3371117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371197 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 6]
def baseStart_3371197 : Nat := 118140960795 + 3371197 * 2 ^ 59
def prefixEnd_3371197 : Nat := 4983230072969 + 3 ^ 40 * 3371197 * 2
def baseEnd_3371197 : Nat := 192338271332816878881517

theorem tailTrace_3371197 : CollatzResearch.WordTrace tailWord_3371197 prefixEnd_3371197 192338271332816878881517 := by
  unfold tailWord_3371197
  simp only [CollatzResearch.WordTrace]
  refine ⟨122957655967736498454543845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81971770645157665636362563 122957655967736498454543845)
  ·
    refine ⟨23054560493950593460226971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122957655967736498454543845 23054560493950593460226971)
    ·
      refine ⟨34581840740925890190340457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23054560493950593460226971 34581840740925890190340457)
      ·
        refine ⟨25936380555694417642755343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34581840740925890190340457 25936380555694417642755343)
        ·
          refine ⟨38904570833541626464133015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25936380555694417642755343 38904570833541626464133015)
          ·
            refine ⟨58356856250312439696199523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38904570833541626464133015 58356856250312439696199523)
            ·
              refine ⟨87535284375468659544299285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58356856250312439696199523 87535284375468659544299285)
              ·
                refine ⟨4103216455100093416139029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87535284375468659544299285 4103216455100093416139029)
                ·
                  refine ⟨192338271332816878881517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4103216455100093416139029 192338271332816878881517)
                  ·
                    rfl

theorem cell23_3371197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_3371197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371197 prefixEnd_3371197 := by exact prefixLift 3371197
  have htrace : WordTrace (prefixWord ++ tailWord_3371197) baseStart_3371197 baseEnd_3371197 := by
    simpa [prefixWord, tailWord_3371197, baseEnd_3371197] using wordTrace_append hprefix tailTrace_3371197
  have hstable : (prefixWord ++ tailWord_3371197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371197).length < 2 ^ (prefixWord ++ tailWord_3371197).sum := by decide
  have hdescent : baseEnd_3371197 < baseStart_3371197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371214 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 6]
def baseStart_3371214 : Nat := 118140960795 + 3371214 * 2 ^ 59
def prefixEnd_3371214 : Nat := 4983230072969 + 3 ^ 40 * 3371214 * 2
def baseEnd_3371214 : Nat := 192339241240719815935675

theorem tailTrace_3371214 : CollatzResearch.WordTrace tailWord_3371214 prefixEnd_3371214 192339241240719815935675 := by
  unfold tailWord_3371214
  simp only [CollatzResearch.WordTrace]
  refine ⟨15369784501084363794739087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81972184005783273571941797 15369784501084363794739087)
  ·
    refine ⟨23054676751626545692108631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15369784501084363794739087 23054676751626545692108631)
    ·
      refine ⟨34582015127439818538162947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23054676751626545692108631 34582015127439818538162947)
      ·
        refine ⟨51873022691159727807244421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34582015127439818538162947 51873022691159727807244421)
        ·
          refine ⟨9726191754592448963858329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51873022691159727807244421 9726191754592448963858329)
          ·
            refine ⟨7294643815944336722893747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9726191754592448963858329 7294643815944336722893747)
            ·
              refine ⟨10941965723916505084340621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7294643815944336722893747 10941965723916505084340621)
              ·
                refine ⟨4103237146468689406627733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10941965723916505084340621 4103237146468689406627733)
                ·
                  refine ⟨192339241240719815935675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4103237146468689406627733 192339241240719815935675)
                  ·
                    rfl

theorem cell23_3371214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_3371214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371214 prefixEnd_3371214 := by exact prefixLift 3371214
  have htrace : WordTrace (prefixWord ++ tailWord_3371214) baseStart_3371214 baseEnd_3371214 := by
    simpa [prefixWord, tailWord_3371214, baseEnd_3371214] using wordTrace_append hprefix tailTrace_3371214
  have hstable : (prefixWord ++ tailWord_3371214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371214).length < 2 ^ (prefixWord ++ tailWord_3371214).sum := by decide
  have hdescent : baseEnd_3371214 < baseStart_3371214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371258 : List Nat := [3, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3]
def baseStart_3371258 : Nat := 118140960795 + 3371258 * 2 ^ 59
def prefixEnd_3371258 : Nat := 4983230072969 + 3 ^ 40 * 3371258 * 2
def baseEnd_3371258 : Nat := 1731075764315276171270873

theorem tailTrace_3371258 : CollatzResearch.WordTrace tailWord_3371258 prefixEnd_3371258 1731075764315276171270873 := by
  unfold tailWord_3371258
  simp only [CollatzResearch.WordTrace]
  refine ⟨30739970205128876468128607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81973253880343670581676285 30739970205128876468128607)
  ·
    refine ⟨46109955307693314702192911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30739970205128876468128607 46109955307693314702192911)
    ·
      refine ⟨69164932961539972053289367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46109955307693314702192911 69164932961539972053289367)
      ·
        refine ⟨103747399442309958079934051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69164932961539972053289367 103747399442309958079934051)
        ·
          refine ⟨155621099163464937119901077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103747399442309958079934051 155621099163464937119901077)
          ·
            refine ⟨7294739023287418927495363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155621099163464937119901077 7294739023287418927495363)
            ·
              refine ⟨10942108534931128391243045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7294739023287418927495363 10942108534931128391243045)
              ·
                refine ⟨2051645350299586573358071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10942108534931128391243045 2051645350299586573358071)
                ·
                  refine ⟨3077468025449379860037107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051645350299586573358071 3077468025449379860037107)
                  ·
                    refine ⟨4616202038174069790055661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3077468025449379860037107 4616202038174069790055661)
                    ·
                      refine ⟨1731075764315276171270873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4616202038174069790055661 1731075764315276171270873)
                      ·
                        rfl

theorem cell23_3371258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3].length) (baseStart_3371258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371258 prefixEnd_3371258 := by exact prefixLift 3371258
  have htrace : WordTrace (prefixWord ++ tailWord_3371258) baseStart_3371258 baseEnd_3371258 := by
    simpa [prefixWord, tailWord_3371258, baseEnd_3371258] using wordTrace_append hprefix tailTrace_3371258
  have hstable : (prefixWord ++ tailWord_3371258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371258).length < 2 ^ (prefixWord ++ tailWord_3371258).sum := by decide
  have hdescent : baseEnd_3371258 < baseStart_3371258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371267 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 5]
def baseStart_3371267 : Nat := 118140960795 + 3371267 * 2 ^ 59
def prefixEnd_3371267 : Nat := 4983230072969 + 3 ^ 40 * 3371267 * 2
def baseEnd_3371267 : Nat := 1731080385641166636058331

theorem tailTrace_3371267 : CollatzResearch.WordTrace tailWord_3371267 prefixEnd_3371267 1731080385641166636058331 := by
  unfold tailWord_3371267
  simp only [CollatzResearch.WordTrace]
  refine ⟨122960209077482900409592055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81973472718321933606394703 122960209077482900409592055)
  ·
    refine ⟨184440313616224350614388083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122960209077482900409592055 184440313616224350614388083)
    ·
      refine ⟨276660470424336525921582125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184440313616224350614388083 276660470424336525921582125)
      ·
        refine ⟨103747676409126197220593297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276660470424336525921582125 103747676409126197220593297)
        ·
          refine ⟨77810757306844647915444973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103747676409126197220593297 77810757306844647915444973)
          ·
            refine ⟨29179033990066742968291865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77810757306844647915444973 29179033990066742968291865)
            ·
              refine ⟨21884275492550057226218899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29179033990066742968291865 21884275492550057226218899)
              ·
                refine ⟨32826413238825085839328349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21884275492550057226218899 32826413238825085839328349)
                ·
                  refine ⟨12309904964559407189748131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32826413238825085839328349 12309904964559407189748131)
                  ·
                    refine ⟨18464857446839110784622197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12309904964559407189748131 18464857446839110784622197)
                    ·
                      refine ⟨1731080385641166636058331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18464857446839110784622197 1731080385641166636058331)
                      ·
                        rfl

theorem cell23_3371267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_3371267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371267 prefixEnd_3371267 := by exact prefixLift 3371267
  have htrace : WordTrace (prefixWord ++ tailWord_3371267) baseStart_3371267 baseEnd_3371267 := by
    simpa [prefixWord, tailWord_3371267, baseEnd_3371267] using wordTrace_append hprefix tailTrace_3371267
  have hstable : (prefixWord ++ tailWord_3371267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371267).length < 2 ^ (prefixWord ++ tailWord_3371267).sum := by decide
  have hdescent : baseEnd_3371267 < baseStart_3371267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371281 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 5, 2, 2]
def baseStart_3371281 : Nat := 118140960795 + 3371281 * 2 ^ 59
def prefixEnd_3371281 : Nat := 4983230072969 + 3 ^ 40 * 3371281 * 2
def baseEnd_3371281 : Nat := 1731087574370329581283267

theorem tailTrace_3371281 : CollatzResearch.WordTrace tailWord_3371281 prefixEnd_3371281 1731087574370329581283267 := by
  unfold tailWord_3371281
  simp only [CollatzResearch.WordTrace]
  refine ⟨122960719699432180800601697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81973813132954787200401131 122960719699432180800601697)
  ·
    refine ⟨92220539774574135600451273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122960719699432180800601697 92220539774574135600451273)
    ·
      refine ⟨69165404830930601700338455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92220539774574135600451273 69165404830930601700338455)
      ·
        refine ⟨103748107246395902550507683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69165404830930601700338455 103748107246395902550507683)
        ·
          refine ⟨155622160869593853825761525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103748107246395902550507683 155622160869593853825761525)
          ·
            refine ⟨14589577581524423796165143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155622160869593853825761525 14589577581524423796165143)
            ·
              refine ⟨21884366372286635694247715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14589577581524423796165143 21884366372286635694247715)
              ·
                refine ⟨32826549558429953541371573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21884366372286635694247715 32826549558429953541371573)
                ·
                  refine ⟨3077489021102808144503585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32826549558429953541371573 3077489021102808144503585)
                  ·
                    refine ⟨2308116765827106108377689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3077489021102808144503585 2308116765827106108377689)
                    ·
                      refine ⟨1731087574370329581283267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308116765827106108377689 1731087574370329581283267)
                      ·
                        rfl

theorem cell23_3371281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 2, 2].length) (baseStart_3371281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371281 prefixEnd_3371281 := by exact prefixLift 3371281
  have htrace : WordTrace (prefixWord ++ tailWord_3371281) baseStart_3371281 baseEnd_3371281 := by
    simpa [prefixWord, tailWord_3371281, baseEnd_3371281] using wordTrace_append hprefix tailTrace_3371281
  have hstable : (prefixWord ++ tailWord_3371281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371281).length < 2 ^ (prefixWord ++ tailWord_3371281).sum := by decide
  have hdescent : baseEnd_3371281 < baseStart_3371281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371298 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 1, 1, 4]
def baseStart_3371298 : Nat := 118140960795 + 3371298 * 2 ^ 59
def prefixEnd_3371298 : Nat := 4983230072969 + 3 ^ 40 * 3371298 * 2
def baseEnd_3371298 : Nat := 1731096303541456014770689

theorem tailTrace_3371298 : CollatzResearch.WordTrace tailWord_3371298 prefixEnd_3371298 1731096303541456014770689 := by
  unfold tailWord_3371298
  simp only [CollatzResearch.WordTrace]
  refine ⟨30740334935092648175992637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81974226493580395135980365 30740334935092648175992637)
  ·
    refine ⟨11527625600659743065997239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30740334935092648175992637 11527625600659743065997239)
    ·
      refine ⟨17291438400989614598995859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11527625600659743065997239 17291438400989614598995859)
      ·
        refine ⟨25937157601484421898493789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17291438400989614598995859 25937157601484421898493789)
        ·
          refine ⟨9726434100556658211935171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25937157601484421898493789 9726434100556658211935171)
          ·
            refine ⟨14589651150834987317902757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9726434100556658211935171 14589651150834987317902757)
            ·
              refine ⟨2735559590781560122106767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14589651150834987317902757 2735559590781560122106767)
              ·
                refine ⟨4103339386172340183160151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2735559590781560122106767 4103339386172340183160151)
                ·
                  refine ⟨6155009079258510274740227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4103339386172340183160151 6155009079258510274740227)
                  ·
                    refine ⟨9232513618887765412110341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6155009079258510274740227 9232513618887765412110341)
                    ·
                      refine ⟨1731096303541456014770689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9232513618887765412110341 1731096303541456014770689)
                      ·
                        rfl

theorem cell23_3371298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 1, 4].length) (baseStart_3371298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371298 prefixEnd_3371298 := by exact prefixLift 3371298
  have htrace : WordTrace (prefixWord ++ tailWord_3371298) baseStart_3371298 baseEnd_3371298 := by
    simpa [prefixWord, tailWord_3371298, baseEnd_3371298] using wordTrace_append hprefix tailTrace_3371298
  have hstable : (prefixWord ++ tailWord_3371298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371298).length < 2 ^ (prefixWord ++ tailWord_3371298).sum := by decide
  have hdescent : baseEnd_3371298 < baseStart_3371298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371304 : List Nat := [2, 1, 5, 1, 3, 1, 10]
def baseStart_3371304 : Nat := 118140960795 + 3371304 * 2 ^ 59
def prefixEnd_3371304 : Nat := 4983230072969 + 3 ^ 40 * 3371304 * 2
def baseEnd_3371304 : Nat := 21371597338584975201181

theorem tailTrace_3371304 : CollatzResearch.WordTrace tailWord_3371304 prefixEnd_3371304 21371597338584975201181 := by
  unfold tailWord_3371304
  simp only [CollatzResearch.WordTrace]
  refine ⟨61480779289174427864344483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81974372385565903819125977 61480779289174427864344483)
  ·
    refine ⟨92221168933761641796516725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61480779289174427864344483 92221168933761641796516725)
    ·
      refine ⟨8645734587540153918423443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92221168933761641796516725 8645734587540153918423443)
      ·
        refine ⟨12968601881310230877635165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8645734587540153918423443 12968601881310230877635165)
        ·
          refine ⟨4863225705491336579113187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12968601881310230877635165 4863225705491336579113187)
          ·
            refine ⟨7294838558237004868669781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4863225705491336579113187 7294838558237004868669781)
            ·
              refine ⟨21371597338584975201181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7294838558237004868669781 21371597338584975201181)
              ·
                rfl

theorem cell23_3371304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 10].length) (baseStart_3371304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371304 prefixEnd_3371304 := by exact prefixLift 3371304
  have htrace : WordTrace (prefixWord ++ tailWord_3371304) baseStart_3371304 baseEnd_3371304 := by
    simpa [prefixWord, tailWord_3371304, baseEnd_3371304] using wordTrace_append hprefix tailTrace_3371304
  have hstable : (prefixWord ++ tailWord_3371304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371304).length < 2 ^ (prefixWord ++ tailWord_3371304).sum := by decide
  have hdescent : baseEnd_3371304 < baseStart_3371304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371331 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 3]
def baseStart_3371331 : Nat := 118140960795 + 3371331 * 2 ^ 59
def prefixEnd_3371331 : Nat := 4983230072969 + 3 ^ 40 * 3371331 * 2
def baseEnd_3371331 : Nat := 1731113248403054385658037

theorem tailTrace_3371331 : CollatzResearch.WordTrace tailWord_3371331 prefixEnd_3371331 1731113248403054385658037 := by
  unfold tailWord_3371331
  simp only [CollatzResearch.WordTrace]
  refine ⟨122962543349251039339921847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81975028899500692893281231 122962543349251039339921847)
  ·
    refine ⟨184443815023876559009882771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122962543349251039339921847 184443815023876559009882771)
    ·
      refine ⟨276665722535814838514824157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184443815023876559009882771 276665722535814838514824157)
      ·
        refine ⟨103749645950930564443059059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276665722535814838514824157 103749645950930564443059059)
        ·
          refine ⟨155624468926395846664588589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103749645950930564443059059 155624468926395846664588589)
          ·
            refine ⟨58359175847398442499220721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155624468926395846664588589 58359175847398442499220721)
            ·
              refine ⟨43769381885548831874415541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58359175847398442499220721 43769381885548831874415541)
              ·
                refine ⟨4103379551770202988226457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43769381885548831874415541 4103379551770202988226457)
                ·
                  refine ⟨3077534663827652241169843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4103379551770202988226457 3077534663827652241169843)
                  ·
                    refine ⟨4616301995741478361754765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3077534663827652241169843 4616301995741478361754765)
                    ·
                      refine ⟨1731113248403054385658037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4616301995741478361754765 1731113248403054385658037)
                      ·
                        rfl

theorem cell23_3371331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_3371331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371331 prefixEnd_3371331 := by exact prefixLift 3371331
  have htrace : WordTrace (prefixWord ++ tailWord_3371331) baseStart_3371331 baseEnd_3371331 := by
    simpa [prefixWord, tailWord_3371331, baseEnd_3371331] using wordTrace_append hprefix tailTrace_3371331
  have hstable : (prefixWord ++ tailWord_3371331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371331).length < 2 ^ (prefixWord ++ tailWord_3371331).sum := by decide
  have hdescent : baseEnd_3371331 < baseStart_3371331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371347 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 4, 6]
def baseStart_3371347 : Nat := 118140960795 + 3371347 * 2 ^ 59
def prefixEnd_3371347 : Nat := 4983230072969 + 3 ^ 40 * 3371347 * 2
def baseEnd_3371347 : Nat := 577040488031175441019321

theorem tailTrace_3371347 : CollatzResearch.WordTrace tailWord_3371347 prefixEnd_3371347 577040488031175441019321 := by
  unfold tailWord_3371347
  simp only [CollatzResearch.WordTrace]
  refine ⟨122963126917193074072504295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81975417944795382715002863 122963126917193074072504295)
  ·
    refine ⟨184444690375789611108756443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122963126917193074072504295 184444690375789611108756443)
    ·
      refine ⟨276667035563684416663134665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184444690375789611108756443 276667035563684416663134665)
      ·
        refine ⟨207500276672763312497350999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276667035563684416663134665 207500276672763312497350999)
        ·
          refine ⟨311250415009144968746026499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207500276672763312497350999 311250415009144968746026499)
          ·
            refine ⟨466875622513717453119039749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311250415009144968746026499 466875622513717453119039749)
            ·
              refine ⟨87539179221322022459819953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 466875622513717453119039749 87539179221322022459819953)
              ·
                refine ⟨65654384415991516844864965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87539179221322022459819953 65654384415991516844864965)
                ·
                  refine ⟨12310197077998409408412181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65654384415991516844864965 12310197077998409408412181)
                  ·
                    refine ⟨577040488031175441019321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12310197077998409408412181 577040488031175441019321)
                    ·
                      rfl

theorem cell23_3371347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 6].length) (baseStart_3371347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371347 prefixEnd_3371347 := by exact prefixLift 3371347
  have htrace : WordTrace (prefixWord ++ tailWord_3371347) baseStart_3371347 baseEnd_3371347 := by
    simpa [prefixWord, tailWord_3371347, baseEnd_3371347] using wordTrace_append hprefix tailTrace_3371347
  have hstable : (prefixWord ++ tailWord_3371347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371347).length < 2 ^ (prefixWord ++ tailWord_3371347).sum := by decide
  have hdescent : baseEnd_3371347 < baseStart_3371347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371349 : List Nat := [1, 3, 2, 2, 5, 1, 1, 3, 1, 2, 2]
def baseStart_3371349 : Nat := 118140960795 + 3371349 * 2 ^ 59
def prefixEnd_3371349 : Nat := 4983230072969 + 3 ^ 40 * 3371349 * 2
def baseEnd_3371349 : Nat := 1731122491054835315232955

theorem tailTrace_3371349 : CollatzResearch.WordTrace tailWord_3371349 prefixEnd_3371349 1731122491054835315232955 := by
  unfold tailWord_3371349
  simp only [CollatzResearch.WordTrace]
  refine ⟨122963199863185828414077101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81975466575457218942718067 122963199863185828414077101)
  ·
    refine ⟨46111199948694685655278913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122963199863185828414077101 46111199948694685655278913)
    ·
      refine ⟨34583399961521014241459185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46111199948694685655278913 34583399961521014241459185)
      ·
        refine ⟨25937549971140760681094389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34583399961521014241459185 25937549971140760681094389)
        ·
          refine ⟨2431645309794446313852599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25937549971140760681094389 2431645309794446313852599)
          ·
            refine ⟨3647467964691669470778899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431645309794446313852599 3647467964691669470778899)
            ·
              refine ⟨5471201947037504206168349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3647467964691669470778899 5471201947037504206168349)
              ·
                refine ⟨2051700730139064077313131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5471201947037504206168349 2051700730139064077313131)
                ·
                  refine ⟨3077551095208596115969697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051700730139064077313131 3077551095208596115969697)
                  ·
                    refine ⟨2308163321406447086977273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3077551095208596115969697 2308163321406447086977273)
                    ·
                      refine ⟨1731122491054835315232955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308163321406447086977273 1731122491054835315232955)
                      ·
                        rfl

theorem cell23_3371349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_3371349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371349 prefixEnd_3371349 := by exact prefixLift 3371349
  have htrace : WordTrace (prefixWord ++ tailWord_3371349) baseStart_3371349 baseEnd_3371349 := by
    simpa [prefixWord, tailWord_3371349, baseEnd_3371349] using wordTrace_append hprefix tailTrace_3371349
  have hstable : (prefixWord ++ tailWord_3371349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371349).length < 2 ^ (prefixWord ++ tailWord_3371349).sum := by decide
  have hdescent : baseEnd_3371349 < baseStart_3371349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371382 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3371382 : Nat := 118140960795 + 3371382 * 2 ^ 59
def prefixEnd_3371382 : Nat := 4983230072969 + 3 ^ 40 * 3371382 * 2
def baseEnd_3371382 : Nat := 1731139435916433686120303

theorem tailTrace_3371382 : CollatzResearch.WordTrace tailWord_3371382 prefixEnd_3371382 1731139435916433686120303 := by
  unfold tailWord_3371382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685275217004142190626775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81976268981377516700018933 7685275217004142190626775)
  ·
    refine ⟨11527912825506213285940163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7685275217004142190626775 11527912825506213285940163)
    ·
      refine ⟨17291869238259319928910245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11527912825506213285940163 17291869238259319928910245)
      ·
        refine ⟨3242225482173622486670671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17291869238259319928910245 3242225482173622486670671)
        ·
          refine ⟨4863338223260433730006007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242225482173622486670671 4863338223260433730006007)
          ·
            refine ⟨7295007334890650595009011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4863338223260433730006007 7295007334890650595009011)
            ·
              refine ⟨10942511002335975892513517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7295007334890650595009011 10942511002335975892513517)
              ·
                refine ⟨4103441625875990959692569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10942511002335975892513517 4103441625875990959692569)
                ·
                  refine ⟨3077581219406993219769427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4103441625875990959692569 3077581219406993219769427)
                  ·
                    refine ⟨4616371829110489829654141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3077581219406993219769427 4616371829110489829654141)
                    ·
                      refine ⟨1731139435916433686120303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4616371829110489829654141 1731139435916433686120303)
                      ·
                        rfl

theorem cell23_3371382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3371382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371382 prefixEnd_3371382 := by exact prefixLift 3371382
  have htrace : WordTrace (prefixWord ++ tailWord_3371382) baseStart_3371382 baseEnd_3371382 := by
    simpa [prefixWord, tailWord_3371382, baseEnd_3371382] using wordTrace_append hprefix tailTrace_3371382
  have hstable : (prefixWord ++ tailWord_3371382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371382).length < 2 ^ (prefixWord ++ tailWord_3371382).sum := by decide
  have hdescent : baseEnd_3371382 < baseStart_3371382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371422 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_3371422 : Nat := 118140960795 + 3371422 * 2 ^ 59
def prefixEnd_3371422 : Nat := 4983230072969 + 3 ^ 40 * 3371422 * 2
def baseEnd_3371422 : Nat := 1731159975142613529620119

theorem tailTrace_3371422 : CollatzResearch.WordTrace tailWord_3371422 prefixEnd_3371422 1731159975142613529620119 := by
  unfold tailWord_3371422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15370732798990170235185565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81977241594614241254323013 15370732798990170235185565)
  ·
    refine ⟨5764024799621313838194587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15370732798990170235185565 5764024799621313838194587)
    ·
      refine ⟨8646037199431970757291881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5764024799621313838194587 8646037199431970757291881)
      ·
        refine ⟨6484527899573978067968911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8646037199431970757291881 6484527899573978067968911)
        ·
          refine ⟨9726791849360967101953367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6484527899573978067968911 9726791849360967101953367)
          ·
            refine ⟨14590187774041450652930051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9726791849360967101953367 14590187774041450652930051)
            ·
              refine ⟨21885281661062175979395077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14590187774041450652930051 21885281661062175979395077)
              ·
                refine ⟨4103490311449157996136577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21885281661062175979395077 4103490311449157996136577)
                ·
                  refine ⟨3077617733586868497102433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4103490311449157996136577 3077617733586868497102433)
                  ·
                    refine ⟨2308213300190151372826825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3077617733586868497102433 2308213300190151372826825)
                    ·
                      refine ⟨1731159975142613529620119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308213300190151372826825 1731159975142613529620119)
                      ·
                        rfl

theorem cell23_3371422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_3371422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371422 prefixEnd_3371422 := by exact prefixLift 3371422
  have htrace : WordTrace (prefixWord ++ tailWord_3371422) baseStart_3371422 baseEnd_3371422 := by
    simpa [prefixWord, tailWord_3371422, baseEnd_3371422] using wordTrace_append hprefix tailTrace_3371422
  have hstable : (prefixWord ++ tailWord_3371422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371422).length < 2 ^ (prefixWord ++ tailWord_3371422).sum := by decide
  have hdescent : baseEnd_3371422 < baseStart_3371422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371428 : List Nat := [2, 3, 1, 2, 1, 1, 6, 2, 5]
def baseStart_3371428 : Nat := 118140960795 + 3371428 * 2 ^ 59
def prefixEnd_3371428 : Nat := 4983230072969 + 3 ^ 40 * 3371428 * 2
def baseEnd_3371428 : Nat := 192351450669615611793899

theorem tailTrace_3371428 : CollatzResearch.WordTrace tailWord_3371428 prefixEnd_3371428 192351450669615611793899 := by
  unfold tailWord_3371428
  simp only [CollatzResearch.WordTrace]
  refine ⟨61483040614949812453101469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81977387486599749937468625 61483040614949812453101469)
  ·
    refine ⟨23056140230606179669913051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61483040614949812453101469 23056140230606179669913051)
    ·
      refine ⟨34584210345909269504869577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23056140230606179669913051 34584210345909269504869577)
      ·
        refine ⟨25938157759431952128652183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34584210345909269504869577 25938157759431952128652183)
        ·
          refine ⟨38907236639147928192978275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25938157759431952128652183 38907236639147928192978275)
          ·
            refine ⟨58360854958721892289467413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38907236639147928192978275 58360854958721892289467413)
            ·
              refine ⟨2735665076190088701068785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58360854958721892289467413 2735665076190088701068785)
              ·
                refine ⟨2051748807142566525801589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2735665076190088701068785 2051748807142566525801589)
                ·
                  refine ⟨192351450669615611793899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2051748807142566525801589 192351450669615611793899)
                  ·
                    rfl

theorem cell23_3371428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_3371428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371428 prefixEnd_3371428 := by exact prefixLift 3371428
  have htrace : WordTrace (prefixWord ++ tailWord_3371428) baseStart_3371428 baseEnd_3371428 := by
    simpa [prefixWord, tailWord_3371428, baseEnd_3371428] using wordTrace_append hprefix tailTrace_3371428
  have hstable : (prefixWord ++ tailWord_3371428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371428).length < 2 ^ (prefixWord ++ tailWord_3371428).sum := by decide
  have hdescent : baseEnd_3371428 < baseStart_3371428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371478 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3371478 : Nat := 118140960795 + 3371478 * 2 ^ 59
def prefixEnd_3371478 : Nat := 4983230072969 + 3 ^ 40 * 3371478 * 2
def baseEnd_3371478 : Nat := 1731188730059265310519861

theorem tailTrace_3371478 : CollatzResearch.WordTrace tailWord_3371478 prefixEnd_3371478 1731188730059265310519861 := by
  unfold tailWord_3371478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685494054982405215345193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81978603253145655630348725 7685494054982405215345193)
  ·
    refine ⟨5764120541236803911508895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7685494054982405215345193 5764120541236803911508895)
    ·
      refine ⟨8646180811855205867263343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5764120541236803911508895 8646180811855205867263343)
      ·
        refine ⟨12969271217782808800895015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8646180811855205867263343 12969271217782808800895015)
        ·
          refine ⟨19453906826674213201342523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12969271217782808800895015 19453906826674213201342523)
          ·
            refine ⟨29180860240011319802013785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19453906826674213201342523 29180860240011319802013785)
            ·
              refine ⟨21885645180008489851510339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29180860240011319802013785 21885645180008489851510339)
              ·
                refine ⟨32828467770012734777265509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21885645180008489851510339 32828467770012734777265509)
                ·
                  refine ⟨6155337706877387770737283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32828467770012734777265509 6155337706877387770737283)
                  ·
                    refine ⟨9233006560316081656105925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6155337706877387770737283 9233006560316081656105925)
                    ·
                      refine ⟨1731188730059265310519861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9233006560316081656105925 1731188730059265310519861)
                      ·
                        rfl

theorem cell23_3371478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3371478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371478 prefixEnd_3371478 := by exact prefixLift 3371478
  have htrace : WordTrace (prefixWord ++ tailWord_3371478) baseStart_3371478 baseEnd_3371478 := by
    simpa [prefixWord, tailWord_3371478, baseEnd_3371478] using wordTrace_append hprefix tailTrace_3371478
  have hstable : (prefixWord ++ tailWord_3371478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371478).length < 2 ^ (prefixWord ++ tailWord_3371478).sum := by decide
  have hdescent : baseEnd_3371478 < baseStart_3371478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371481 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 4, 2, 3]
def baseStart_3371481 : Nat := 118140960795 + 3371481 * 2 ^ 59
def prefixEnd_3371481 : Nat := 4983230072969 + 3 ^ 40 * 3371481 * 2
def baseEnd_3371481 : Nat := 1731190270501228798782347

theorem tailTrace_3371481 : CollatzResearch.WordTrace tailWord_3371481 prefixEnd_3371481 1731190270501228798782347 := by
  unfold tailWord_3371481
  simp only [CollatzResearch.WordTrace]
  refine ⟨122968014298707614957882297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81978676199138409971921531 122968014298707614957882297)
  ·
    refine ⟨92226010724030711218411723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122968014298707614957882297 92226010724030711218411723)
    ·
      refine ⟨138339016086046066827617585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92226010724030711218411723 138339016086046066827617585)
      ·
        refine ⟨103754262064534550120713189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138339016086046066827617585 103754262064534550120713189)
        ·
          refine ⟨19453924137100228147633723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103754262064534550120713189 19453924137100228147633723)
          ·
            refine ⟨29180886205650342221450585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19453924137100228147633723 29180886205650342221450585)
            ·
              refine ⟨21885664654237756666087939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29180886205650342221450585 21885664654237756666087939)
              ·
                refine ⟨32828496981356634999131909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21885664654237756666087939 32828496981356634999131909)
                ·
                  refine ⟨6155343184004369062337233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32828496981356634999131909 6155343184004369062337233)
                  ·
                    refine ⟨4616507388003276796752925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6155343184004369062337233 4616507388003276796752925)
                    ·
                      refine ⟨1731190270501228798782347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4616507388003276796752925 1731190270501228798782347)
                      ·
                        rfl

theorem cell23_3371481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_3371481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371481 prefixEnd_3371481 := by exact prefixLift 3371481
  have htrace : WordTrace (prefixWord ++ tailWord_3371481) baseStart_3371481 baseEnd_3371481 := by
    simpa [prefixWord, tailWord_3371481, baseEnd_3371481] using wordTrace_append hprefix tailTrace_3371481
  have hstable : (prefixWord ++ tailWord_3371481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371481).length < 2 ^ (prefixWord ++ tailWord_3371481).sum := by decide
  have hdescent : baseEnd_3371481 < baseStart_3371481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371488 : List Nat := [2, 1, 1, 3, 1, 1, 3, 6, 1, 4]
def baseStart_3371488 : Nat := 118140960795 + 3371488 * 2 ^ 59
def prefixEnd_3371488 : Nat := 4983230072969 + 3 ^ 40 * 3371488 * 2
def baseEnd_3371488 : Nat := 577064621621936757131605

theorem tailTrace_3371488 : CollatzResearch.WordTrace tailWord_3371488 prefixEnd_3371488 577064621621936757131605 := by
  unfold tailWord_3371488
  simp only [CollatzResearch.WordTrace]
  refine ⟨61484134804841127576693559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81978846406454836768924745 61484134804841127576693559)
  ·
    refine ⟨92226202207261691365040339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61484134804841127576693559 92226202207261691365040339)
    ·
      refine ⟨138339303310892537047560509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92226202207261691365040339 138339303310892537047560509)
      ·
        refine ⟨51877238741584701392835191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138339303310892537047560509 51877238741584701392835191)
        ·
          refine ⟨77815858112377052089252787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51877238741584701392835191 77815858112377052089252787)
          ·
            refine ⟨116723787168565578133879181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77815858112377052089252787 116723787168565578133879181)
            ·
              refine ⟨43771420188212091800204693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116723787168565578133879181 43771420188212091800204693)
              ·
                refine ⟨2051785321322441803134595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43771420188212091800204693 2051785321322441803134595)
                ·
                  refine ⟨3077677981983662704701893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051785321322441803134595 3077677981983662704701893)
                  ·
                    refine ⟨577064621621936757131605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3077677981983662704701893 577064621621936757131605)
                    ·
                      rfl

theorem cell23_3371488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 1, 4].length) (baseStart_3371488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371488 prefixEnd_3371488 := by exact prefixLift 3371488
  have htrace : WordTrace (prefixWord ++ tailWord_3371488) baseStart_3371488 baseEnd_3371488 := by
    simpa [prefixWord, tailWord_3371488, baseEnd_3371488] using wordTrace_append hprefix tailTrace_3371488
  have hstable : (prefixWord ++ tailWord_3371488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371488).length < 2 ^ (prefixWord ++ tailWord_3371488).sum := by decide
  have hdescent : baseEnd_3371488 < baseStart_3371488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371504 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_3371504 : Nat := 118140960795 + 3371504 * 2 ^ 59
def prefixEnd_3371504 : Nat := 4983230072969 + 3 ^ 40 * 3371504 * 2
def baseEnd_3371504 : Nat := 1731202080556282208794741

theorem tailTrace_3371504 : CollatzResearch.WordTrace tailWord_3371504 prefixEnd_3371504 1731202080556282208794741 := by
  unfold tailWord_3371504
  simp only [CollatzResearch.WordTrace]
  refine ⟨61484426588812144942984783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81979235451749526590646377 61484426588812144942984783)
  ·
    refine ⟨92226639883218217414477175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61484426588812144942984783 92226639883218217414477175)
    ·
      refine ⟨138339959824827326121715763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92226639883218217414477175 138339959824827326121715763)
      ·
        refine ⟨207509939737240989182573645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138339959824827326121715763 207509939737240989182573645)
        ·
          refine ⟨77816227401465370943465117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207509939737240989182573645 77816227401465370943465117)
          ·
            refine ⟨29181085275549514103799419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77816227401465370943465117 29181085275549514103799419)
            ·
              refine ⟨43771627913324271155699129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29181085275549514103799419 43771627913324271155699129)
              ·
                refine ⟨32828720934993203366774347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43771627913324271155699129 32828720934993203366774347)
                ·
                  refine ⟨49243081402489805050161521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32828720934993203366774347 49243081402489805050161521)
                  ·
                    refine ⟨36932311051867353787621141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49243081402489805050161521 36932311051867353787621141)
                    ·
                      refine ⟨1731202080556282208794741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36932311051867353787621141 1731202080556282208794741)
                      ·
                        rfl

theorem cell23_3371504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_3371504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371504 prefixEnd_3371504 := by exact prefixLift 3371504
  have htrace : WordTrace (prefixWord ++ tailWord_3371504) baseStart_3371504 baseEnd_3371504 := by
    simpa [prefixWord, tailWord_3371504, baseEnd_3371504] using wordTrace_append hprefix tailTrace_3371504
  have hstable : (prefixWord ++ tailWord_3371504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371504).length < 2 ^ (prefixWord ++ tailWord_3371504).sum := by decide
  have hdescent : baseEnd_3371504 < baseStart_3371504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371551 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 4]
def baseStart_3371551 : Nat := 118140960795 + 3371551 * 2 ^ 59
def prefixEnd_3371551 : Nat := 4983230072969 + 3 ^ 40 * 3371551 * 2
def baseEnd_3371551 : Nat := 1731226214147043524907025

theorem tailTrace_3371551 : CollatzResearch.WordTrace tailWord_3371551 prefixEnd_3371551 1731226214147043524907025 := by
  unfold tailWord_3371551
  simp only [CollatzResearch.WordTrace]
  refine ⟨122970567408454016912930507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81980378272302677941953671 122970567408454016912930507)
  ·
    refine ⟨184455851112681025369395761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122970567408454016912930507 184455851112681025369395761)
    ·
      refine ⟨138341888334510769027046821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184455851112681025369395761 138341888334510769027046821)
      ·
        refine ⟨25939104062720769192571279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138341888334510769027046821 25939104062720769192571279)
        ·
          refine ⟨38908656094081153788856919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25939104062720769192571279 38908656094081153788856919)
          ·
            refine ⟨58362984141121730683285379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38908656094081153788856919 58362984141121730683285379)
            ·
              refine ⟨87544476211682596024928069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58362984141121730683285379 87544476211682596024928069)
              ·
                refine ⟨16414589289690486754674013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87544476211682596024928069 16414589289690486754674013)
                ·
                  refine ⟨6155470983633932533002755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16414589289690486754674013 6155470983633932533002755)
                  ·
                    refine ⟨9233206475450898799504133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6155470983633932533002755 9233206475450898799504133)
                    ·
                      refine ⟨1731226214147043524907025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9233206475450898799504133 1731226214147043524907025)
                      ·
                        rfl

theorem cell23_3371551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_3371551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371551 prefixEnd_3371551 := by exact prefixLift 3371551
  have htrace : WordTrace (prefixWord ++ tailWord_3371551) baseStart_3371551 baseEnd_3371551 := by
    simpa [prefixWord, tailWord_3371551, baseEnd_3371551] using wordTrace_append hprefix tailTrace_3371551
  have hstable : (prefixWord ++ tailWord_3371551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371551).length < 2 ^ (prefixWord ++ tailWord_3371551).sum := by decide
  have hdescent : baseEnd_3371551 < baseStart_3371551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371552 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 6]
def baseStart_3371552 : Nat := 118140960795 + 3371552 * 2 ^ 59
def prefixEnd_3371552 : Nat := 4983230072969 + 3 ^ 40 * 3371552 * 2
def baseEnd_3371552 : Nat := 192358525291966446777169

theorem tailTrace_3371552 : CollatzResearch.WordTrace tailWord_3371552 prefixEnd_3371552 192358525291966446777169 := by
  unfold tailWord_3371552
  simp only [CollatzResearch.WordTrace]
  refine ⟨61485301940725197041858455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81980402587633596055811273 61485301940725197041858455)
  ·
    refine ⟨92227952911087795562787683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61485301940725197041858455 92227952911087795562787683)
    ·
      refine ⟨138341929366631693344181525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92227952911087795562787683 138341929366631693344181525)
      ·
        refine ⟨6484777939060860625508509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138341929366631693344181525 6484777939060860625508509)
        ·
          refine ⟨2431791727147822734565691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6484777939060860625508509 2431791727147822734565691)
          ·
            refine ⟨3647687590721734101848537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431791727147822734565691 3647687590721734101848537)
            ·
              refine ⟨2735765693041300576386403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3647687590721734101848537 2735765693041300576386403)
              ·
                refine ⟨4103648539561950864579605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2735765693041300576386403 4103648539561950864579605)
                ·
                  refine ⟨192358525291966446777169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4103648539561950864579605 192358525291966446777169)
                  ·
                    rfl

theorem cell23_3371552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 6].length) (baseStart_3371552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371552 prefixEnd_3371552 := by exact prefixLift 3371552
  have htrace : WordTrace (prefixWord ++ tailWord_3371552) baseStart_3371552 baseEnd_3371552 := by
    simpa [prefixWord, tailWord_3371552, baseEnd_3371552] using wordTrace_append hprefix tailTrace_3371552
  have hstable : (prefixWord ++ tailWord_3371552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371552).length < 2 ^ (prefixWord ++ tailWord_3371552).sum := by decide
  have hdescent : baseEnd_3371552 < baseStart_3371552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371568 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 4]
def baseStart_3371568 : Nat := 118140960795 + 3371568 * 2 ^ 59
def prefixEnd_3371568 : Nat := 4983230072969 + 3 ^ 40 * 3371568 * 2
def baseEnd_3371568 : Nat := 1731234943318169958394447

theorem tailTrace_3371568 : CollatzResearch.WordTrace tailWord_3371568 prefixEnd_3371568 1731234943318169958394447 := by
  unfold tailWord_3371568
  simp only [CollatzResearch.WordTrace]
  refine ⟨61485593724696214408149679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81980791632928285877532905 61485593724696214408149679)
  ·
    refine ⟨92228390587044321612224519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61485593724696214408149679 92228390587044321612224519)
    ·
      refine ⟨138342585880566482418336779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92228390587044321612224519 138342585880566482418336779)
      ·
        refine ⟨207513878820849723627505169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138342585880566482418336779 207513878820849723627505169)
        ·
          refine ⟨155635409115637292720628877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207513878820849723627505169 155635409115637292720628877)
          ·
            refine ⟨58363278418363984770235829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155635409115637292720628877 58363278418363984770235829)
            ·
              refine ⟨5471557351721623572209609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58363278418363984770235829 5471557351721623572209609)
              ·
                refine ⟨4103668013791217679157207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5471557351721623572209609 4103668013791217679157207)
                ·
                  refine ⟨6155502020686826518735811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4103668013791217679157207 6155502020686826518735811)
                  ·
                    refine ⟨9233253031030239778103717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6155502020686826518735811 9233253031030239778103717)
                    ·
                      refine ⟨1731234943318169958394447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9233253031030239778103717 1731234943318169958394447)
                      ·
                        rfl

theorem cell23_3371568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 4].length) (baseStart_3371568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371568 prefixEnd_3371568 := by exact prefixLift 3371568
  have htrace : WordTrace (prefixWord ++ tailWord_3371568) baseStart_3371568 baseEnd_3371568 := by
    simpa [prefixWord, tailWord_3371568, baseEnd_3371568] using wordTrace_append hprefix tailTrace_3371568
  have hstable : (prefixWord ++ tailWord_3371568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371568).length < 2 ^ (prefixWord ++ tailWord_3371568).sum := by decide
  have hdescent : baseEnd_3371568 < baseStart_3371568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371651 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 2, 6]
def baseStart_3371651 : Nat := 118140960795 + 3371651 * 2 ^ 59
def prefixEnd_3371651 : Nat := 4983230072969 + 3 ^ 40 * 3371651 * 2
def baseEnd_3371651 : Nat := 577092520737497711218855

theorem tailTrace_3371651 : CollatzResearch.WordTrace tailWord_3371651 prefixEnd_3371651 577092520737497711218855 := by
  unfold tailWord_3371651
  simp only [CollatzResearch.WordTrace]
  refine ⟨122974214708091733991570807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81982809805394489327713871 122974214708091733991570807)
  ·
    refine ⟨184461322062137600987356211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122974214708091733991570807 184461322062137600987356211)
    ·
      refine ⟨276691983093206401481034317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184461322062137600987356211 276691983093206401481034317)
      ·
        refine ⟨103759493659952400555387869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276691983093206401481034317 103759493659952400555387869)
        ·
          refine ⟨38909810122482150208270451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103759493659952400555387869 38909810122482150208270451)
          ·
            refine ⟨58364715183723225312405677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38909810122482150208270451 58364715183723225312405677)
            ·
              refine ⟨21886768193896209492152129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58364715183723225312405677 21886768193896209492152129)
              ·
                refine ⟨16415076145422157119114097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21886768193896209492152129 16415076145422157119114097)
                ·
                  refine ⟨12311307109066617839335573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16415076145422157119114097 12311307109066617839335573)
                  ·
                    refine ⟨577092520737497711218855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12311307109066617839335573 577092520737497711218855)
                    ·
                      rfl

theorem cell23_3371651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 6].length) (baseStart_3371651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371651 prefixEnd_3371651 := by exact prefixLift 3371651
  have htrace : WordTrace (prefixWord ++ tailWord_3371651) baseStart_3371651 baseEnd_3371651 := by
    simpa [prefixWord, tailWord_3371651, baseEnd_3371651] using wordTrace_append hprefix tailTrace_3371651
  have hstable : (prefixWord ++ tailWord_3371651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371651).length < 2 ^ (prefixWord ++ tailWord_3371651).sum := by decide
  have hdescent : baseEnd_3371651 < baseStart_3371651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371652 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_3371652 : Nat := 118140960795 + 3371652 * 2 ^ 59
def prefixEnd_3371652 : Nat := 4983230072969 + 3 ^ 40 * 3371652 * 2
def baseEnd_3371652 : Nat := 1731278075693147629744061

theorem tailTrace_3371652 : CollatzResearch.WordTrace tailWord_3371652 prefixEnd_3371652 1731278075693147629744061 := by
  unfold tailWord_3371652
  simp only [CollatzResearch.WordTrace]
  refine ⟨61487125590544055581178605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81982834120725407441571473 61487125590544055581178605)
  ·
    refine ⟨23057672096454020842941977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61487125590544055581178605 23057672096454020842941977)
    ·
      refine ⟨17293254072340515632206483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23057672096454020842941977 17293254072340515632206483)
      ·
        refine ⟨25939881108510773448309725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17293254072340515632206483 25939881108510773448309725)
        ·
          refine ⟨9727455415691540043116147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25939881108510773448309725 9727455415691540043116147)
          ·
            refine ⟨14591183123537310064674221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9727455415691540043116147 14591183123537310064674221)
            ·
              refine ⟨5471693671326491274252833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14591183123537310064674221 5471693671326491274252833)
              ·
                refine ⟨4103770253494868455689625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5471693671326491274252833 4103770253494868455689625)
                ·
                  refine ⟨3077827690121151341767219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4103770253494868455689625 3077827690121151341767219)
                  ·
                    refine ⟨4616741535181727012650829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3077827690121151341767219 4616741535181727012650829)
                    ·
                      refine ⟨1731278075693147629744061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4616741535181727012650829 1731278075693147629744061)
                      ·
                        rfl

theorem cell23_3371652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_3371652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371652 prefixEnd_3371652 := by exact prefixLift 3371652
  have htrace : WordTrace (prefixWord ++ tailWord_3371652) baseStart_3371652 baseEnd_3371652 := by
    simpa [prefixWord, tailWord_3371652, baseEnd_3371652] using wordTrace_append hprefix tailTrace_3371652
  have hstable : (prefixWord ++ tailWord_3371652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371652).length < 2 ^ (prefixWord ++ tailWord_3371652).sum := by decide
  have hdescent : baseEnd_3371652 < baseStart_3371652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371726 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2]
def baseStart_3371726 : Nat := 118140960795 + 3371726 * 2 ^ 59
def prefixEnd_3371726 : Nat := 4983230072969 + 3 ^ 40 * 3371726 * 2
def baseEnd_3371726 : Nat := 1731316073261580340218721

theorem tailTrace_3371726 : CollatzResearch.WordTrace tailWord_3371726 prefixEnd_3371726 1731316073261580340218721 := by
  unfold tailWord_3371726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15372118772852502725068879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81984633455213347867034021 15372118772852502725068879)
  ·
    refine ⟨23058178159278754087603319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15372118772852502725068879 23058178159278754087603319)
    ·
      refine ⟨34587267238918131131404979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23058178159278754087603319 34587267238918131131404979)
      ·
        refine ⟨51880900858377196697107469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34587267238918131131404979 51880900858377196697107469)
        ·
          refine ⟨19455337821891448761415301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51880900858377196697107469 19455337821891448761415301)
          ·
            refine ⟨3647875841604646642765369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19455337821891448761415301 3647875841604646642765369)
            ·
              refine ⟨2735906881203484982074027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3647875841604646642765369 2735906881203484982074027)
              ·
                refine ⟨4103860321805227473111041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2735906881203484982074027 4103860321805227473111041)
                ·
                  refine ⟨3077895241353920604833281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4103860321805227473111041 3077895241353920604833281)
                  ·
                    refine ⟨2308421431015440453624961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3077895241353920604833281 2308421431015440453624961)
                    ·
                      refine ⟨1731316073261580340218721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308421431015440453624961 1731316073261580340218721)
                      ·
                        rfl

theorem cell23_3371726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2].length) (baseStart_3371726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371726 prefixEnd_3371726 := by exact prefixLift 3371726
  have htrace : WordTrace (prefixWord ++ tailWord_3371726) baseStart_3371726 baseEnd_3371726 := by
    simpa [prefixWord, tailWord_3371726, baseEnd_3371726] using wordTrace_append hprefix tailTrace_3371726
  have hstable : (prefixWord ++ tailWord_3371726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371726).length < 2 ^ (prefixWord ++ tailWord_3371726).sum := by decide
  have hdescent : baseEnd_3371726 < baseStart_3371726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371745 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 2, 5]
def baseStart_3371745 : Nat := 118140960795 + 3371745 * 2 ^ 59
def prefixEnd_3371745 : Nat := 4983230072969 + 3 ^ 40 * 3371745 * 2
def baseEnd_3371745 : Nat := 577108609798005255293711

theorem tailTrace_3371745 : CollatzResearch.WordTrace tailWord_3371745 prefixEnd_3371745 577108609798005255293711 := by
  unfold tailWord_3371745
  simp only [CollatzResearch.WordTrace]
  refine ⟨122977643169751188045492689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81985095446500792030328459 122977643169751188045492689)
  ·
    refine ⟨92233232377313391034119517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122977643169751188045492689 92233232377313391034119517)
    ·
      refine ⟨34587462141492521637794819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92233232377313391034119517 34587462141492521637794819)
      ·
        refine ⟨51881193212238782456692229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34587462141492521637794819 51881193212238782456692229)
        ·
          refine ⟨9727723727294771710629793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51881193212238782456692229 9727723727294771710629793)
          ·
            refine ⟨7295792795471078782972345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9727723727294771710629793 7295792795471078782972345)
            ·
              refine ⟨5471844596603309087229259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7295792795471078782972345 5471844596603309087229259)
              ·
                refine ⟨8207766894904963630843889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471844596603309087229259 8207766894904963630843889)
                ·
                  refine ⟨6155825171178722723132917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8207766894904963630843889 6155825171178722723132917)
                  ·
                    refine ⟨577108609798005255293711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6155825171178722723132917 577108609798005255293711)
                    ·
                      rfl

theorem cell23_3371745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_3371745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371745 prefixEnd_3371745 := by exact prefixLift 3371745
  have htrace : WordTrace (prefixWord ++ tailWord_3371745) baseStart_3371745 baseEnd_3371745 := by
    simpa [prefixWord, tailWord_3371745, baseEnd_3371745] using wordTrace_append hprefix tailTrace_3371745
  have hstable : (prefixWord ++ tailWord_3371745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371745).length < 2 ^ (prefixWord ++ tailWord_3371745).sum := by decide
  have hdescent : baseEnd_3371745 < baseStart_3371745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371771 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 12]
def baseStart_3371771 : Nat := 118140960795 + 3371771 * 2 ^ 59
def prefixEnd_3371771 : Nat := 4983230072969 + 3 ^ 40 * 3371771 * 2
def baseEnd_3371771 : Nat := 192371019987892518239557

theorem tailTrace_3371771 : CollatzResearch.WordTrace tailWord_3371771 prefixEnd_3371771 192371019987892518239557 := by
  unfold tailWord_3371771
  simp only [CollatzResearch.WordTrace]
  refine ⟨122978591467656994485939167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81985727645104662990626111 122978591467656994485939167)
  ·
    refine ⟨184467887201485491728908751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122978591467656994485939167 184467887201485491728908751)
    ·
      refine ⟨276701830802228237593363127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184467887201485491728908751 276701830802228237593363127)
      ·
        refine ⟨415052746203342356390044691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276701830802228237593363127 415052746203342356390044691)
        ·
          refine ⟨622579119305013534585067037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415052746203342356390044691 622579119305013534585067037)
          ·
            refine ⟨233467169739380075469400139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 622579119305013534585067037 233467169739380075469400139)
            ·
              refine ⟨350200754609070113204100209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233467169739380075469400139 350200754609070113204100209)
              ·
                refine ⟨262650565956802584903075157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350200754609070113204100209 262650565956802584903075157)
                ·
                  refine ⟨192371019987892518239557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 262650565956802584903075157 192371019987892518239557)
                  ·
                    rfl

theorem cell23_3371771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 12].length) (baseStart_3371771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371771 prefixEnd_3371771 := by exact prefixLift 3371771
  have htrace : WordTrace (prefixWord ++ tailWord_3371771) baseStart_3371771 baseEnd_3371771 := by
    simpa [prefixWord, tailWord_3371771, baseEnd_3371771] using wordTrace_append hprefix tailTrace_3371771
  have hstable : (prefixWord ++ tailWord_3371771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371771).length < 2 ^ (prefixWord ++ tailWord_3371771).sum := by decide
  have hdescent : baseEnd_3371771 < baseStart_3371771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371799 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 2, 1, 4]
def baseStart_3371799 : Nat := 118140960795 + 3371799 * 2 ^ 59
def prefixEnd_3371799 : Nat := 4983230072969 + 3 ^ 40 * 3371799 * 2
def baseEnd_3371799 : Nat := 1731353557349358554605885

theorem tailTrace_3371799 : CollatzResearch.WordTrace tailWord_3371799 prefixEnd_3371799 1731353557349358554605885 := by
  unfold tailWord_3371799
  simp only [CollatzResearch.WordTrace]
  refine ⟨122979612711555555267958451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81986408474370370178638967 122979612711555555267958451)
  ·
    refine ⟨184469419067333332901937677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122979612711555555267958451 184469419067333332901937677)
    ·
      refine ⟨69176032150249999838226629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184469419067333332901937677 69176032150249999838226629)
      ·
        refine ⟨12970506028171874969667493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69176032150249999838226629 12970506028171874969667493)
        ·
          refine ⟨2431969880282226556812655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12970506028171874969667493 2431969880282226556812655)
          ·
            refine ⟨3647954820423339835218983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431969880282226556812655 3647954820423339835218983)
            ·
              refine ⟨5471932230635009752828475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3647954820423339835218983 5471932230635009752828475)
              ·
                refine ⟨8207898345952514629242713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471932230635009752828475 8207898345952514629242713)
                ·
                  refine ⟨6155923759464385971932035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8207898345952514629242713 6155923759464385971932035)
                  ·
                    refine ⟨9233885639196578957898053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6155923759464385971932035 9233885639196578957898053)
                    ·
                      refine ⟨1731353557349358554605885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9233885639196578957898053 1731353557349358554605885)
                      ·
                        rfl

theorem cell23_3371799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_3371799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371799 prefixEnd_3371799 := by exact prefixLift 3371799
  have htrace : WordTrace (prefixWord ++ tailWord_3371799) baseStart_3371799 baseEnd_3371799 := by
    simpa [prefixWord, tailWord_3371799, baseEnd_3371799] using wordTrace_append hprefix tailTrace_3371799
  have hstable : (prefixWord ++ tailWord_3371799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371799).length < 2 ^ (prefixWord ++ tailWord_3371799).sum := by decide
  have hdescent : baseEnd_3371799 < baseStart_3371799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371822 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_3371822 : Nat := 118140960795 + 3371822 * 2 ^ 59
def prefixEnd_3371822 : Nat := 4983230072969 + 3 ^ 40 * 3371822 * 2
def baseEnd_3371822 : Nat := 192373929711601329402031

theorem tailTrace_3371822 : CollatzResearch.WordTrace tailWord_3371822 prefixEnd_3371822 192373929711601329402031 := by
  unfold tailWord_3371822
  simp only [CollatzResearch.WordTrace]
  refine ⟨15372556448809028774505715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81986967726981486797363813 15372556448809028774505715)
  ·
    refine ⟨23058834673213543161758573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15372556448809028774505715 23058834673213543161758573)
    ·
      refine ⟨8647063002455078685659465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23058834673213543161758573 8647063002455078685659465)
      ·
        refine ⟨6485297251841309014244599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8647063002455078685659465 6485297251841309014244599)
        ·
          refine ⟨9727945877761963521366899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485297251841309014244599 9727945877761963521366899)
          ·
            refine ⟨14591918816642945282050349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9727945877761963521366899 14591918816642945282050349)
            ·
              refine ⟨5471969556241104480768881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14591918816642945282050349 5471969556241104480768881)
              ·
                refine ⟨4103977167180828360576661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5471969556241104480768881 4103977167180828360576661)
                ·
                  refine ⟨192373929711601329402031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4103977167180828360576661 192373929711601329402031)
                  ·
                    rfl

theorem cell23_3371822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_3371822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371822 prefixEnd_3371822 := by exact prefixLift 3371822
  have htrace : WordTrace (prefixWord ++ tailWord_3371822) baseStart_3371822 baseEnd_3371822 := by
    simpa [prefixWord, tailWord_3371822, baseEnd_3371822] using wordTrace_append hprefix tailTrace_3371822
  have hstable : (prefixWord ++ tailWord_3371822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371822).length < 2 ^ (prefixWord ++ tailWord_3371822).sum := by decide
  have hdescent : baseEnd_3371822 < baseStart_3371822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371832 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 3, 1, 3]
def baseStart_3371832 : Nat := 118140960795 + 3371832 * 2 ^ 59
def prefixEnd_3371832 : Nat := 4983230072969 + 3 ^ 40 * 3371832 * 2
def baseEnd_3371832 : Nat := 1731370502210956925493233

theorem tailTrace_3371832 : CollatzResearch.WordTrace tailWord_3371832 prefixEnd_3371832 1731370502210956925493233 := by
  unfold tailWord_3371832
  simp only [CollatzResearch.WordTrace]
  refine ⟨61490408160218000951954875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81987210880290667935939833 61490408160218000951954875)
  ·
    refine ⟨92235612240327001427932313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61490408160218000951954875 92235612240327001427932313)
    ·
      refine ⟨69176709180245251070949235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92235612240327001427932313 69176709180245251070949235)
      ·
        refine ⟨103765063770367876606423853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69176709180245251070949235 103765063770367876606423853)
        ·
          refine ⟨38911898913887953727408945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103765063770367876606423853 38911898913887953727408945)
          ·
            refine ⟨29183924185415965295556709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38911898913887953727408945 29183924185415965295556709)
            ·
              refine ⟨5471985784765493492916883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29183924185415965295556709 5471985784765493492916883)
              ·
                refine ⟨8207978677148240239375325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471985784765493492916883 8207978677148240239375325)
                ·
                  refine ⟨3077992003930590089765747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8207978677148240239375325 3077992003930590089765747)
                  ·
                    refine ⟨4616988005895885134648621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3077992003930590089765747 4616988005895885134648621)
                    ·
                      refine ⟨1731370502210956925493233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4616988005895885134648621 1731370502210956925493233)
                      ·
                        rfl

theorem cell23_3371832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_3371832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371832 prefixEnd_3371832 := by exact prefixLift 3371832
  have htrace : WordTrace (prefixWord ++ tailWord_3371832) baseStart_3371832 baseEnd_3371832 := by
    simpa [prefixWord, tailWord_3371832, baseEnd_3371832] using wordTrace_append hprefix tailTrace_3371832
  have hstable : (prefixWord ++ tailWord_3371832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371832).length < 2 ^ (prefixWord ++ tailWord_3371832).sum := by decide
  have hdescent : baseEnd_3371832 < baseStart_3371832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371852 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 1, 5]
def baseStart_3371852 : Nat := 118140960795 + 3371852 * 2 ^ 59
def prefixEnd_3371852 : Nat := 4983230072969 + 3 ^ 40 * 3371852 * 2
def baseEnd_3371852 : Nat := 577126923941348949081047

theorem tailTrace_3371852 : CollatzResearch.WordTrace tailWord_3371852 prefixEnd_3371852 577126923941348949081047 := by
  unfold tailWord_3371852
  simp only [CollatzResearch.WordTrace]
  refine ⟨61490772890181772659818905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81987697186909030213091873 61490772890181772659818905)
  ·
    refine ⟨46118079667636329494864179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61490772890181772659818905 46118079667636329494864179)
    ·
      refine ⟨69177119501454494242296269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46118079667636329494864179 69177119501454494242296269)
      ·
        refine ⟨25941419813045435340861101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69177119501454494242296269 25941419813045435340861101)
        ·
          refine ⟨9728032429892038252822913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25941419813045435340861101 9728032429892038252822913)
          ·
            refine ⟨7296024322419028689617185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9728032429892038252822913 7296024322419028689617185)
            ·
              refine ⟨5472018241814271517212889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7296024322419028689617185 5472018241814271517212889)
              ·
                refine ⟨4104013681360703637909667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5472018241814271517212889 4104013681360703637909667)
                ·
                  refine ⟨6156020522041055456864501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104013681360703637909667 6156020522041055456864501)
                  ·
                    refine ⟨577126923941348949081047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6156020522041055456864501 577126923941348949081047)
                    ·
                      rfl

theorem cell23_3371852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_3371852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371852 prefixEnd_3371852 := by exact prefixLift 3371852
  have htrace : WordTrace (prefixWord ++ tailWord_3371852) baseStart_3371852 baseEnd_3371852 := by
    simpa [prefixWord, tailWord_3371852, baseEnd_3371852] using wordTrace_append hprefix tailTrace_3371852
  have hstable : (prefixWord ++ tailWord_3371852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371852).length < 2 ^ (prefixWord ++ tailWord_3371852).sum := by decide
  have hdescent : baseEnd_3371852 < baseStart_3371852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371865 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 4, 4]
def baseStart_3371865 : Nat := 118140960795 + 3371865 * 2 ^ 59
def prefixEnd_3371865 : Nat := 4983230072969 + 3 ^ 40 * 3371865 * 2
def baseEnd_3371865 : Nat := 577129149024185098793527

theorem tailTrace_3371865 : CollatzResearch.WordTrace tailWord_3371865 prefixEnd_3371865 577129149024185098793527 := by
  unfold tailWord_3371865
  simp only [CollatzResearch.WordTrace]
  refine ⟨122982019929316448539861049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81988013286210965693240699 122982019929316448539861049)
  ·
    refine ⟨92236514946987336404895787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122982019929316448539861049 92236514946987336404895787)
    ·
      refine ⟨138354772420481004607343681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92236514946987336404895787 138354772420481004607343681)
      ·
        refine ⟨103766079315360753455507761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138354772420481004607343681 103766079315360753455507761)
        ·
          refine ⟨77824559486520565091630821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103766079315360753455507761 77824559486520565091630821)
          ·
            refine ⟨14592104903722605954680779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77824559486520565091630821 14592104903722605954680779)
            ·
              refine ⟨21888157355583908932021169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14592104903722605954680779 21888157355583908932021169)
              ·
                refine ⟨16416118016687931699015877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21888157355583908932021169 16416118016687931699015877)
                ·
                  refine ⟨3078022128128987193565477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16416118016687931699015877 3078022128128987193565477)
                  ·
                    refine ⟨577129149024185098793527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3078022128128987193565477 577129149024185098793527)
                    ·
                      rfl

theorem cell23_3371865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 4].length) (baseStart_3371865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371865 prefixEnd_3371865 := by exact prefixLift 3371865
  have htrace : WordTrace (prefixWord ++ tailWord_3371865) baseStart_3371865 baseEnd_3371865 := by
    simpa [prefixWord, tailWord_3371865, baseEnd_3371865] using wordTrace_append hprefix tailTrace_3371865
  have hstable : (prefixWord ++ tailWord_3371865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371865).length < 2 ^ (prefixWord ++ tailWord_3371865).sum := by decide
  have hdescent : baseEnd_3371865 < baseStart_3371865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371866 : List Nat := [3, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3]
def baseStart_3371866 : Nat := 118140960795 + 3371866 * 2 ^ 59
def prefixEnd_3371866 : Nat := 4983230072969 + 3 ^ 40 * 3371866 * 2
def baseEnd_3371866 : Nat := 1731387960553209792468077

theorem tailTrace_3371866 : CollatzResearch.WordTrace tailWord_3371866 prefixEnd_3371866 1731387960553209792468077 := by
  unfold tailWord_3371866
  simp only [CollatzResearch.WordTrace]
  refine ⟨30745514100578206427661863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81988037601541883807098301 30745514100578206427661863)
  ·
    refine ⟨46118271150867309641492795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30745514100578206427661863 46118271150867309641492795)
    ·
      refine ⟨69177406726300964462239193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46118271150867309641492795 69177406726300964462239193)
      ·
        refine ⟨51883055044725723346679395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69177406726300964462239193 51883055044725723346679395)
        ·
          refine ⟨77824582567088585020019093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51883055044725723346679395 77824582567088585020019093)
          ·
            refine ⟨3648027307832277422813395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77824582567088585020019093 3648027307832277422813395)
            ·
              refine ⟨5472040961748416134220093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648027307832277422813395 5472040961748416134220093)
              ·
                refine ⟨2052015360655656050332535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5472040961748416134220093 2052015360655656050332535)
                ·
                  refine ⟨3078023040983484075498803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052015360655656050332535 3078023040983484075498803)
                  ·
                    refine ⟨4617034561475226113248205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3078023040983484075498803 4617034561475226113248205)
                    ·
                      refine ⟨1731387960553209792468077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4617034561475226113248205 1731387960553209792468077)
                      ·
                        rfl

theorem cell23_3371866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_3371866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371866 prefixEnd_3371866 := by exact prefixLift 3371866
  have htrace : WordTrace (prefixWord ++ tailWord_3371866) baseStart_3371866 baseEnd_3371866 := by
    simpa [prefixWord, tailWord_3371866, baseEnd_3371866] using wordTrace_append hprefix tailTrace_3371866
  have hstable : (prefixWord ++ tailWord_3371866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371866).length < 2 ^ (prefixWord ++ tailWord_3371866).sum := by decide
  have hdescent : baseEnd_3371866 < baseStart_3371866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371875 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 5]
def baseStart_3371875 : Nat := 118140960795 + 3371875 * 2 ^ 59
def prefixEnd_3371875 : Nat := 4983230072969 + 3 ^ 40 * 3371875 * 2
def baseEnd_3371875 : Nat := 1731392581879100257255535

theorem tailTrace_3371875 : CollatzResearch.WordTrace tailWord_3371875 prefixEnd_3371875 1731392581879100257255535 := by
  unfold tailWord_3371875
  simp only [CollatzResearch.WordTrace]
  refine ⟨122982384659280220247725079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81988256439520146831816719 122982384659280220247725079)
  ·
    refine ⟨184473576988920330371587619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122982384659280220247725079 184473576988920330371587619)
    ·
      refine ⟨276710365483380495557381429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184473576988920330371587619 276710365483380495557381429)
      ·
        refine ⟨25941596764066921458504509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276710365483380495557381429 25941596764066921458504509)
        ·
          refine ⟨9728098786525095546939191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25941596764066921458504509 9728098786525095546939191)
          ·
            refine ⟨14592148179787643320408787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9728098786525095546939191 14592148179787643320408787)
            ·
              refine ⟨21888222269681464980613181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14592148179787643320408787 21888222269681464980613181)
              ·
                refine ⟨8208083351130549367729943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21888222269681464980613181 8208083351130549367729943)
                ·
                  refine ⟨12312125026695824051594915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8208083351130549367729943 12312125026695824051594915)
                  ·
                    refine ⟨18468187540043736077392373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12312125026695824051594915 18468187540043736077392373)
                    ·
                      refine ⟨1731392581879100257255535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18468187540043736077392373 1731392581879100257255535)
                      ·
                        rfl

theorem cell23_3371875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_3371875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371875 prefixEnd_3371875 := by exact prefixLift 3371875
  have htrace : WordTrace (prefixWord ++ tailWord_3371875) baseStart_3371875 baseEnd_3371875 := by
    simpa [prefixWord, tailWord_3371875, baseEnd_3371875] using wordTrace_append hprefix tailTrace_3371875
  have hstable : (prefixWord ++ tailWord_3371875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371875).length < 2 ^ (prefixWord ++ tailWord_3371875).sum := by decide
  have hdescent : baseEnd_3371875 < baseStart_3371875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371889 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 3, 2, 2]
def baseStart_3371889 : Nat := 118140960795 + 3371889 * 2 ^ 59
def prefixEnd_3371889 : Nat := 4983230072969 + 3 ^ 40 * 3371889 * 2
def baseEnd_3371889 : Nat := 1731399770608263202480471

theorem tailTrace_3371889 : CollatzResearch.WordTrace tailWord_3371889 prefixEnd_3371889 1731399770608263202480471 := by
  unfold tailWord_3371889
  simp only [CollatzResearch.WordTrace]
  refine ⟨122982895281229500638734721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81988596854153000425823147 122982895281229500638734721)
  ·
    refine ⟨92237171460922125479051041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122982895281229500638734721 92237171460922125479051041)
    ·
      refine ⟨69177878595691594109288281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92237171460922125479051041 69177878595691594109288281)
      ·
        refine ⟨51883408946768695581966211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69177878595691594109288281 51883408946768695581966211)
        ·
          refine ⟨77825113420153043372949317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51883408946768695581966211 77825113420153043372949317)
          ·
            refine ⟨14592208766278695632427997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77825113420153043372949317 14592208766278695632427997)
            ·
              refine ⟨5472078287354510862160499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14592208766278695632427997 5472078287354510862160499)
              ·
                refine ⟨8208117431031766293240749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5472078287354510862160499 8208117431031766293240749)
                ·
                  refine ⟨3078044036636912359965281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8208117431031766293240749 3078044036636912359965281)
                  ·
                    refine ⟨2308533027477684269973961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3078044036636912359965281 2308533027477684269973961)
                    ·
                      refine ⟨1731399770608263202480471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308533027477684269973961 1731399770608263202480471)
                      ·
                        rfl

theorem cell23_3371889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_3371889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371889 prefixEnd_3371889 := by exact prefixLift 3371889
  have htrace : WordTrace (prefixWord ++ tailWord_3371889) baseStart_3371889 baseEnd_3371889 := by
    simpa [prefixWord, tailWord_3371889, baseEnd_3371889] using wordTrace_append hprefix tailTrace_3371889
  have hstable : (prefixWord ++ tailWord_3371889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371889).length < 2 ^ (prefixWord ++ tailWord_3371889).sum := by decide
  have hdescent : baseEnd_3371889 < baseStart_3371889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371898 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_3371898 : Nat := 118140960795 + 3371898 * 2 ^ 59
def prefixEnd_3371898 : Nat := 4983230072969 + 3 ^ 40 * 3371898 * 2
def baseEnd_3371898 : Nat := 1731404391934153667267929

theorem tailTrace_3371898 : CollatzResearch.WordTrace tailWord_3371898 prefixEnd_3371898 1731404391934153667267929 := by
  unfold tailWord_3371898
  simp only [CollatzResearch.WordTrace]
  refine ⟨30745805884549223793953087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81988815692131263450541565 30745805884549223793953087)
  ·
    refine ⟨46118708826823835690929631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30745805884549223793953087 46118708826823835690929631)
    ·
      refine ⟨69178063240235753536394447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46118708826823835690929631 69178063240235753536394447)
      ·
        refine ⟨103767094860353630304591671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69178063240235753536394447 103767094860353630304591671)
        ·
          refine ⟨155650642290530445456887507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103767094860353630304591671 155650642290530445456887507)
          ·
            refine ⟨233475963435795668185331261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155650642290530445456887507 233475963435795668185331261)
            ·
              refine ⟨87553486288423375569499223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233475963435795668185331261 87553486288423375569499223)
              ·
                refine ⟨131330229432635063354248835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87553486288423375569499223 131330229432635063354248835)
                ·
                  refine ⟨196995344148952595031373253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131330229432635063354248835 196995344148952595031373253)
                  ·
                    refine ⟨36936627027928611568382485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 196995344148952595031373253 36936627027928611568382485)
                    ·
                      refine ⟨1731404391934153667267929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36936627027928611568382485 1731404391934153667267929)
                      ·
                        rfl

theorem cell23_3371898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_3371898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371898 prefixEnd_3371898 := by exact prefixLift 3371898
  have htrace : WordTrace (prefixWord ++ tailWord_3371898) baseStart_3371898 baseEnd_3371898 := by
    simpa [prefixWord, tailWord_3371898, baseEnd_3371898] using wordTrace_append hprefix tailTrace_3371898
  have hstable : (prefixWord ++ tailWord_3371898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371898).length < 2 ^ (prefixWord ++ tailWord_3371898).sum := by decide
  have hdescent : baseEnd_3371898 < baseStart_3371898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371906 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3371906 : Nat := 118140960795 + 3371906 * 2 ^ 59
def prefixEnd_3371906 : Nat := 4983230072969 + 3 ^ 40 * 3371906 * 2
def baseEnd_3371906 : Nat := 1731408499779389635967893

theorem tailTrace_3371906 : CollatzResearch.WordTrace tailWord_3371906 prefixEnd_3371906 1731408499779389635967893 := by
  unfold tailWord_3371906
  simp only [CollatzResearch.WordTrace]
  refine ⟨30745878830541978135525893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81989010214778608361402381 30745878830541978135525893)
  ·
    refine ⟨5764852280726620900411105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30745878830541978135525893 5764852280726620900411105)
    ·
      refine ⟨4323639210544965675308329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5764852280726620900411105 4323639210544965675308329)
      ·
        refine ⟨3242729407908724256481247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4323639210544965675308329 3242729407908724256481247)
        ·
          refine ⟨4864094111863086384721871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242729407908724256481247 4864094111863086384721871)
          ·
            refine ⟨7296141167794629577082807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4864094111863086384721871 7296141167794629577082807)
            ·
              refine ⟨10944211751691944365624211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7296141167794629577082807 10944211751691944365624211)
              ·
                refine ⟨16416317627537916548436317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10944211751691944365624211 16416317627537916548436317)
                ·
                  refine ⟨6156119110326718705663619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16416317627537916548436317 6156119110326718705663619)
                  ·
                    refine ⟨9234178665490078058495429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6156119110326718705663619 9234178665490078058495429)
                    ·
                      refine ⟨1731408499779389635967893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9234178665490078058495429 1731408499779389635967893)
                      ·
                        rfl

theorem cell23_3371906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3371906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371906 prefixEnd_3371906 := by exact prefixLift 3371906
  have htrace : WordTrace (prefixWord ++ tailWord_3371906) baseStart_3371906 baseEnd_3371906 := by
    simpa [prefixWord, tailWord_3371906, baseEnd_3371906] using wordTrace_append hprefix tailTrace_3371906
  have hstable : (prefixWord ++ tailWord_3371906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371906).length < 2 ^ (prefixWord ++ tailWord_3371906).sum := by decide
  have hdescent : baseEnd_3371906 < baseStart_3371906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371909 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 1, 2, 3]
def baseStart_3371909 : Nat := 118140960795 + 3371909 * 2 ^ 59
def prefixEnd_3371909 : Nat := 4983230072969 + 3 ^ 40 * 3371909 * 2
def baseEnd_3371909 : Nat := 1731410040221353124230379

theorem tailTrace_3371909 : CollatzResearch.WordTrace tailWord_3371909 prefixEnd_3371909 1731410040221353124230379 := by
  unfold tailWord_3371909
  simp only [CollatzResearch.WordTrace]
  refine ⟨122983624741157044054462781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81989083160771362702975187 122983624741157044054462781)
  ·
    refine ⟨46118859277933891520423543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122983624741157044054462781 46118859277933891520423543)
    ·
      refine ⟨69178288916900837280635315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46118859277933891520423543 69178288916900837280635315)
      ·
        refine ⟨103767433375351255920952973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69178288916900837280635315 103767433375351255920952973)
        ·
          refine ⟨38912787515756720970357365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103767433375351255920952973 38912787515756720970357365)
          ·
            refine ⟨3648073829602192590971003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38912787515756720970357365 3648073829602192590971003)
            ·
              refine ⟨5472110744403288886456505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648073829602192590971003 5472110744403288886456505)
              ·
                refine ⟨4104083058302466664842379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5472110744403288886456505 4104083058302466664842379)
                ·
                  refine ⟨6156124587453699997263569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104083058302466664842379 6156124587453699997263569)
                  ·
                    refine ⟨4617093440590274997947677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6156124587453699997263569 4617093440590274997947677)
                    ·
                      refine ⟨1731410040221353124230379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4617093440590274997947677 1731410040221353124230379)
                      ·
                        rfl

theorem cell23_3371909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 2, 3].length) (baseStart_3371909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371909 prefixEnd_3371909 := by exact prefixLift 3371909
  have htrace : WordTrace (prefixWord ++ tailWord_3371909) baseStart_3371909 baseEnd_3371909 := by
    simpa [prefixWord, tailWord_3371909, baseEnd_3371909] using wordTrace_append hprefix tailTrace_3371909
  have hstable : (prefixWord ++ tailWord_3371909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371909).length < 2 ^ (prefixWord ++ tailWord_3371909).sum := by decide
  have hdescent : baseEnd_3371909 < baseStart_3371909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371926 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3371926 : Nat := 118140960795 + 3371926 * 2 ^ 59
def prefixEnd_3371926 : Nat := 4983230072969 + 3 ^ 40 * 3371926 * 2
def baseEnd_3371926 : Nat := 1731418769392479557717801

theorem tailTrace_3371926 : CollatzResearch.WordTrace tailWord_3371926 prefixEnd_3371926 1731418769392479557717801 := by
  unfold tailWord_3371926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7686515298880965997364477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81989496521396970638554421 7686515298880965997364477)
  ·
    refine ⟨2882443237080362249011679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7686515298880965997364477 2882443237080362249011679)
    ·
      refine ⟨4323664855620543373517519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882443237080362249011679 4323664855620543373517519)
      ·
        refine ⟨6485497283430815060276279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323664855620543373517519 6485497283430815060276279)
        ·
          refine ⟨9728245925146222590414419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485497283430815060276279 9728245925146222590414419)
          ·
            refine ⟨14592368887719333885621629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9728245925146222590414419 14592368887719333885621629)
            ·
              refine ⟨5472138332894750207108111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14592368887719333885621629 5472138332894750207108111)
              ·
                refine ⟨8208207499342125310662167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5472138332894750207108111 8208207499342125310662167)
                ·
                  refine ⟨12312311249013187965993251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8208207499342125310662167 12312311249013187965993251)
                  ·
                    refine ⟨18468466873519781948989877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12312311249013187965993251 18468466873519781948989877)
                    ·
                      refine ⟨1731418769392479557717801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18468466873519781948989877 1731418769392479557717801)
                      ·
                        rfl

theorem cell23_3371926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3371926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371926 prefixEnd_3371926 := by exact prefixLift 3371926
  have htrace : WordTrace (prefixWord ++ tailWord_3371926) baseStart_3371926 baseEnd_3371926 := by
    simpa [prefixWord, tailWord_3371926, baseEnd_3371926] using wordTrace_append hprefix tailTrace_3371926
  have hstable : (prefixWord ++ tailWord_3371926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371926).length < 2 ^ (prefixWord ++ tailWord_3371926).sum := by decide
  have hdescent : baseEnd_3371926 < baseStart_3371926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371956 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3371956 : Nat := 118140960795 + 3371956 * 2 ^ 59
def prefixEnd_3371956 : Nat := 4983230072969 + 3 ^ 40 * 3371956 * 2
def baseEnd_3371956 : Nat := 1731434173812114440342663

theorem tailTrace_3371956 : CollatzResearch.WordTrace tailWord_3371956 prefixEnd_3371956 1731434173812114440342663 := by
  unfold tailWord_3371956
  simp only [CollatzResearch.WordTrace]
  refine ⟨61492669485993385540711861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81990225981324514054282481 61492669485993385540711861)
  ·
    refine ⟨5764937764311879894441737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61492669485993385540711861 5764937764311879894441737)
    ·
      refine ⟨4323703323233909920831303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5764937764311879894441737 4323703323233909920831303)
      ·
        refine ⟨6485554984850864881246955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323703323233909920831303 6485554984850864881246955)
        ·
          refine ⟨9728332477276297321870433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485554984850864881246955 9728332477276297321870433)
          ·
            refine ⟨7296249357957222991402825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9728332477276297321870433 7296249357957222991402825)
            ·
              refine ⟨5472187018467917243552119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7296249357957222991402825 5472187018467917243552119)
              ·
                refine ⟨8208280527701875865328179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5472187018467917243552119 8208280527701875865328179)
                ·
                  refine ⟨12312420791552813797992269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8208280527701875865328179 12312420791552813797992269)
                  ·
                    refine ⟨4617157796832305174247101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12312420791552813797992269 4617157796832305174247101)
                    ·
                      refine ⟨1731434173812114440342663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4617157796832305174247101 1731434173812114440342663)
                      ·
                        rfl

theorem cell23_3371956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3371956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371956 prefixEnd_3371956 := by exact prefixLift 3371956
  have htrace : WordTrace (prefixWord ++ tailWord_3371956) baseStart_3371956 baseEnd_3371956 := by
    simpa [prefixWord, tailWord_3371956, baseEnd_3371956] using wordTrace_append hprefix tailTrace_3371956
  have hstable : (prefixWord ++ tailWord_3371956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371956).length < 2 ^ (prefixWord ++ tailWord_3371956).sum := by decide
  have hdescent : baseEnd_3371956 < baseStart_3371956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3371974 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_3371974 : Nat := 118140960795 + 3371974 * 2 ^ 59
def prefixEnd_3371974 : Nat := 4983230072969 + 3 ^ 40 * 3371974 * 2
def baseEnd_3371974 : Nat := 1731443416463895369917581

theorem tailTrace_3371974 : CollatzResearch.WordTrace tailWord_3371974 prefixEnd_3371974 1731443416463895369917581 := by
  unfold tailWord_3371974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843312358935048754861843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81990663657281040103719317 3843312358935048754861843)
  ·
    refine ⟨5764968538402573132292765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3843312358935048754861843 5764968538402573132292765)
    ·
      refine ⟨2161863201900964924609787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5764968538402573132292765 2161863201900964924609787)
      ·
        refine ⟨3242794802851447386914681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2161863201900964924609787 3242794802851447386914681)
        ·
          refine ⟨2432096102138585540186011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3242794802851447386914681 2432096102138585540186011)
          ·
            refine ⟨3648144153207878310279017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432096102138585540186011 3648144153207878310279017)
            ·
              refine ⟨2736108114905908732709263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3648144153207878310279017 2736108114905908732709263)
              ·
                refine ⟨4104162172358863099063895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2736108114905908732709263 4104162172358863099063895)
                ·
                  refine ⟨6156243258538294648595843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104162172358863099063895 6156243258538294648595843)
                  ·
                    refine ⟨9234364887807441972893765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6156243258538294648595843 9234364887807441972893765)
                    ·
                      refine ⟨1731443416463895369917581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9234364887807441972893765 1731443416463895369917581)
                      ·
                        rfl

theorem cell23_3371974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_3371974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3371974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3371974 prefixEnd_3371974 := by exact prefixLift 3371974
  have htrace : WordTrace (prefixWord ++ tailWord_3371974) baseStart_3371974 baseEnd_3371974 := by
    simpa [prefixWord, tailWord_3371974, baseEnd_3371974] using wordTrace_append hprefix tailTrace_3371974
  have hstable : (prefixWord ++ tailWord_3371974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3371974).length < 2 ^ (prefixWord ++ tailWord_3371974).sum := by decide
  have hdescent : baseEnd_3371974 < baseStart_3371974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3371974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372015 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 1, 7]
def baseStart_3372015 : Nat := 118140960795 + 3372015 * 2 ^ 59
def prefixEnd_3372015 : Nat := 4983230072969 + 3 ^ 40 * 3372015 * 2
def baseEnd_3372015 : Nat := 577154823056909903168297

theorem tailTrace_3372015 : CollatzResearch.WordTrace tailWord_3372015 prefixEnd_3372015 577154823056909903168297 := by
  unfold tailWord_3372015
  simp only [CollatzResearch.WordTrace]
  refine ⟨122987490878773024157821499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81991660585848682771880999 122987490878773024157821499)
  ·
    refine ⟨184481236318159536236732249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122987490878773024157821499 184481236318159536236732249)
    ·
      refine ⟨138360927238619652177549187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184481236318159536236732249 138360927238619652177549187)
      ·
        refine ⟨207541390857929478266323781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138360927238619652177549187 207541390857929478266323781)
        ·
          refine ⟨38914010785861777174935709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207541390857929478266323781 38914010785861777174935709)
          ·
            refine ⟨14592754044698166440600891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38914010785861777174935709 14592754044698166440600891)
            ·
              refine ⟨21889131067047249660901337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14592754044698166440600891 21889131067047249660901337)
              ·
                refine ⟨16416848300285437245676003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21889131067047249660901337 16416848300285437245676003)
                ·
                  refine ⟨24625272450428155868514005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16416848300285437245676003 24625272450428155868514005)
                  ·
                    refine ⟨577154823056909903168297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24625272450428155868514005 577154823056909903168297)
                    ·
                      rfl

theorem cell23_3372015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_3372015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372015 prefixEnd_3372015 := by exact prefixLift 3372015
  have htrace : WordTrace (prefixWord ++ tailWord_3372015) baseStart_3372015 baseEnd_3372015 := by
    simpa [prefixWord, tailWord_3372015, baseEnd_3372015] using wordTrace_append hprefix tailTrace_3372015
  have hstable : (prefixWord ++ tailWord_3372015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372015).length < 2 ^ (prefixWord ++ tailWord_3372015).sum := by decide
  have hdescent : baseEnd_3372015 < baseStart_3372015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372086 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3372086 : Nat := 118140960795 + 3372086 * 2 ^ 59
def prefixEnd_3372086 : Nat := 4983230072969 + 3 ^ 40 * 3372086 * 2
def baseEnd_3372086 : Nat := 1731500926297198931717065

theorem tailTrace_3372086 : CollatzResearch.WordTrace tailWord_3372086 prefixEnd_3372086 1731500926297198931717065 := by
  unfold tailWord_3372086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7686880028844737705228507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81993386974343868855770741 7686880028844737705228507)
  ·
    refine ⟨11530320043267106557842761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7686880028844737705228507 11530320043267106557842761)
    ·
      refine ⟨8647740032450329918382071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11530320043267106557842761 8647740032450329918382071)
      ·
        refine ⟨12971610048675494877573107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8647740032450329918382071 12971610048675494877573107)
        ·
          refine ⟨19457415073013242316359661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12971610048675494877573107 19457415073013242316359661)
          ·
            refine ⟨7296530652379965868634873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19457415073013242316359661 7296530652379965868634873)
            ·
              refine ⟨5472397989284974401476155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7296530652379965868634873 5472397989284974401476155)
              ·
                refine ⟨8208596983927461602214233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5472397989284974401476155 8208596983927461602214233)
                ·
                  refine ⟨6156447737945596201660675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8208596983927461602214233 6156447737945596201660675)
                  ·
                    refine ⟨9234671606918394302491013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6156447737945596201660675 9234671606918394302491013)
                    ·
                      refine ⟨1731500926297198931717065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9234671606918394302491013 1731500926297198931717065)
                      ·
                        rfl

theorem cell23_3372086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3372086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372086 prefixEnd_3372086 := by exact prefixLift 3372086
  have htrace : WordTrace (prefixWord ++ tailWord_3372086) baseStart_3372086 baseEnd_3372086 := by
    simpa [prefixWord, tailWord_3372086, baseEnd_3372086] using wordTrace_append hprefix tailTrace_3372086
  have hstable : (prefixWord ++ tailWord_3372086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372086).length < 2 ^ (prefixWord ++ tailWord_3372086).sum := by decide
  have hdescent : baseEnd_3372086 < baseStart_3372086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372089 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3372089 : Nat := 118140960795 + 3372089 * 2 ^ 59
def prefixEnd_3372089 : Nat := 4983230072969 + 3 ^ 40 * 3372089 * 2
def baseEnd_3372089 : Nat := 1731502466739162419979551

theorem tailTrace_3372089 : CollatzResearch.WordTrace tailWord_3372089 prefixEnd_3372089 1731502466739162419979551 := by
  unfold tailWord_3372089
  simp only [CollatzResearch.WordTrace]
  refine ⟨122990189880504934796015321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81993459920336623197343547 122990189880504934796015321)
  ·
    refine ⟨92242642410378701097011491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122990189880504934796015321 92242642410378701097011491)
    ·
      refine ⟨138363963615568051645517237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92242642410378701097011491 138363963615568051645517237)
      ·
        refine ⟨12971621588959504841767241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138363963615568051645517237 12971621588959504841767241)
        ·
          refine ⟨9728716191719628631325431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12971621588959504841767241 9728716191719628631325431)
          ·
            refine ⟨14593074287579442946988147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9728716191719628631325431 14593074287579442946988147)
            ·
              refine ⟨21889611431369164420482221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14593074287579442946988147 21889611431369164420482221)
              ·
                refine ⟨8208604286763436657680833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21889611431369164420482221 8208604286763436657680833)
                ·
                  refine ⟨6156453215072577493260625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8208604286763436657680833 6156453215072577493260625)
                  ·
                    refine ⟨4617339911304433119945469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6156453215072577493260625 4617339911304433119945469)
                    ·
                      refine ⟨1731502466739162419979551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4617339911304433119945469 1731502466739162419979551)
                      ·
                        rfl

theorem cell23_3372089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3372089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372089 prefixEnd_3372089 := by exact prefixLift 3372089
  have htrace : WordTrace (prefixWord ++ tailWord_3372089) baseStart_3372089 baseEnd_3372089 := by
    simpa [prefixWord, tailWord_3372089, baseEnd_3372089] using wordTrace_append hprefix tailTrace_3372089
  have hstable : (prefixWord ++ tailWord_3372089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372089).length < 2 ^ (prefixWord ++ tailWord_3372089).sum := by decide
  have hdescent : baseEnd_3372089 < baseStart_3372089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372095 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_3372095 : Nat := 118140960795 + 3372095 * 2 ^ 59
def prefixEnd_3372095 : Nat := 4983230072969 + 3 ^ 40 * 3372095 * 2
def baseEnd_3372095 : Nat := 1731505547623089396504523

theorem tailTrace_3372095 : CollatzResearch.WordTrace tailWord_3372095 prefixEnd_3372095 1731505547623089396504523 := by
  unfold tailWord_3372095
  simp only [CollatzResearch.WordTrace]
  refine ⟨122990408718483197820733739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81993605812322131880489159 122990408718483197820733739)
  ·
    refine ⟨184485613077724796731100609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122990408718483197820733739 184485613077724796731100609)
    ·
      refine ⟨138364209808293597548325457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184485613077724796731100609 138364209808293597548325457)
      ·
        refine ⟨103773157356220198161244093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138364209808293597548325457 103773157356220198161244093)
        ·
          refine ⟨38914934008582574310466535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103773157356220198161244093 38914934008582574310466535)
          ·
            refine ⟨58372401012873861465699803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38914934008582574310466535 58372401012873861465699803)
            ·
              refine ⟨87558601519310792198549705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58372401012873861465699803 87558601519310792198549705)
              ·
                refine ⟨65668951139483094148912279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87558601519310792198549705 65668951139483094148912279)
                ·
                  refine ⟨98503426709224641223368419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65668951139483094148912279 98503426709224641223368419)
                  ·
                    refine ⟨147755140063836961835052629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98503426709224641223368419 147755140063836961835052629)
                    ·
                      refine ⟨1731505547623089396504523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 147755140063836961835052629 1731505547623089396504523)
                      ·
                        rfl

theorem cell23_3372095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_3372095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372095 prefixEnd_3372095 := by exact prefixLift 3372095
  have htrace : WordTrace (prefixWord ++ tailWord_3372095) baseStart_3372095 baseEnd_3372095 := by
    simpa [prefixWord, tailWord_3372095, baseEnd_3372095] using wordTrace_append hprefix tailTrace_3372095
  have hstable : (prefixWord ++ tailWord_3372095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372095).length < 2 ^ (prefixWord ++ tailWord_3372095).sum := by decide
  have hdescent : baseEnd_3372095 < baseStart_3372095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372109 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 6]
def baseStart_3372109 : Nat := 118140960795 + 3372109 * 2 ^ 59
def prefixEnd_3372109 : Nat := 4983230072969 + 3 ^ 40 * 3372109 * 2
def baseEnd_3372109 : Nat := 192390304039139149081051

theorem tailTrace_3372109 : CollatzResearch.WordTrace tailWord_3372109 prefixEnd_3372109 192390304039139149081051 := by
  unfold tailWord_3372109
  simp only [CollatzResearch.WordTrace]
  refine ⟨122990919340432478211743381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81993946226954985474495587 122990919340432478211743381)
  ·
    refine ⟨5765199344082772416175471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122990919340432478211743381 5765199344082772416175471)
    ·
      refine ⟨8647799016124158624263207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5765199344082772416175471 8647799016124158624263207)
      ·
        refine ⟨12971698524186237936394811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8647799016124158624263207 12971698524186237936394811)
        ·
          refine ⟨19457547786279356904592217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12971698524186237936394811 19457547786279356904592217)
          ·
            refine ⟨14593160839709517678444163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19457547786279356904592217 14593160839709517678444163)
            ·
              refine ⟨21889741259564276517666245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14593160839709517678444163 21889741259564276517666245)
              ·
                refine ⟨4104326486168301847062421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21889741259564276517666245 4104326486168301847062421)
                ·
                  refine ⟨192390304039139149081051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4104326486168301847062421 192390304039139149081051)
                  ·
                    rfl

theorem cell23_3372109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_3372109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372109 prefixEnd_3372109 := by exact prefixLift 3372109
  have htrace : WordTrace (prefixWord ++ tailWord_3372109) baseStart_3372109 baseEnd_3372109 := by
    simpa [prefixWord, tailWord_3372109, baseEnd_3372109] using wordTrace_append hprefix tailTrace_3372109
  have hstable : (prefixWord ++ tailWord_3372109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372109).length < 2 ^ (prefixWord ++ tailWord_3372109).sum := by decide
  have hdescent : baseEnd_3372109 < baseStart_3372109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372115 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 7]
def baseStart_3372115 : Nat := 118140960795 + 3372115 * 2 ^ 59
def prefixEnd_3372115 : Nat := 4983230072969 + 3 ^ 40 * 3372115 * 2
def baseEnd_3372115 : Nat := 1731515817236179318254431

theorem tailTrace_3372115 : CollatzResearch.WordTrace tailWord_3372115 prefixEnd_3372115 1731515817236179318254431 := by
  unfold tailWord_3372115
  simp only [CollatzResearch.WordTrace]
  refine ⟨122991138178410741236461799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81994092118940494157641199 122991138178410741236461799)
  ·
    refine ⟨184486707267616111854692699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122991138178410741236461799 184486707267616111854692699)
    ·
      refine ⟨276730060901424167782039049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184486707267616111854692699 276730060901424167782039049)
      ·
        refine ⟨207547545676068125836529287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276730060901424167782039049 207547545676068125836529287)
        ·
          refine ⟨311321318514102188754793931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207547545676068125836529287 311321318514102188754793931)
          ·
            refine ⟨466981977771153283132190897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311321318514102188754793931 466981977771153283132190897)
            ·
              refine ⟨350236483328364962349143173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466981977771153283132190897 350236483328364962349143173)
              ·
                refine ⟨65669340624068430440464345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350236483328364962349143173 65669340624068430440464345)
                ·
                  refine ⟨49252005468051322830348259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65669340624068430440464345 49252005468051322830348259)
                  ·
                    refine ⟨73878008202076984245522389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49252005468051322830348259 73878008202076984245522389)
                    ·
                      refine ⟨1731515817236179318254431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73878008202076984245522389 1731515817236179318254431)
                      ·
                        rfl

theorem cell23_3372115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_3372115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372115 prefixEnd_3372115 := by exact prefixLift 3372115
  have htrace : WordTrace (prefixWord ++ tailWord_3372115) baseStart_3372115 baseEnd_3372115 := by
    simpa [prefixWord, tailWord_3372115, baseEnd_3372115] using wordTrace_append hprefix tailTrace_3372115
  have hstable : (prefixWord ++ tailWord_3372115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372115).length < 2 ^ (prefixWord ++ tailWord_3372115).sum := by decide
  have hdescent : baseEnd_3372115 < baseStart_3372115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372119 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 3, 1, 3]
def baseStart_3372119 : Nat := 118140960795 + 3372119 * 2 ^ 59
def prefixEnd_3372119 : Nat := 4983230072969 + 3 ^ 40 * 3372119 * 2
def baseEnd_3372119 : Nat := 1731517871158797302604413

theorem tailTrace_3372119 : CollatzResearch.WordTrace tailWord_3372119 prefixEnd_3372119 1731517871158797302604413 := by
  unfold tailWord_3372119
  simp only [CollatzResearch.WordTrace]
  refine ⟨122991284070396249919607411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81994189380264166613071607 122991284070396249919607411)
  ·
    refine ⟨184486926105594374879411117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122991284070396249919607411 184486926105594374879411117)
    ·
      refine ⟨69182597289597890579779169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184486926105594374879411117 69182597289597890579779169)
      ·
        refine ⟨51886947967198417934834377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69182597289597890579779169 51886947967198417934834377)
        ·
          refine ⟨38915210975398813451125783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51886947967198417934834377 38915210975398813451125783)
          ·
            refine ⟨58372816463098220176688675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38915210975398813451125783 58372816463098220176688675)
            ·
              refine ⟨87559224694647330265033013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58372816463098220176688675 87559224694647330265033013)
              ·
                refine ⟨8208677315123187212346845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87559224694647330265033013 8208677315123187212346845)
                ·
                  refine ⟨3078253993171195204630067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8208677315123187212346845 3078253993171195204630067)
                  ·
                    refine ⟨4617380989756792806945101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3078253993171195204630067 4617380989756792806945101)
                    ·
                      refine ⟨1731517871158797302604413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4617380989756792806945101 1731517871158797302604413)
                      ·
                        rfl

theorem cell23_3372119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_3372119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372119 prefixEnd_3372119 := by exact prefixLift 3372119
  have htrace : WordTrace (prefixWord ++ tailWord_3372119) baseStart_3372119 baseEnd_3372119 := by
    simpa [prefixWord, tailWord_3372119, baseEnd_3372119] using wordTrace_append hprefix tailTrace_3372119
  have hstable : (prefixWord ++ tailWord_3372119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372119).length < 2 ^ (prefixWord ++ tailWord_3372119).sum := by decide
  have hdescent : baseEnd_3372119 < baseStart_3372119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372129 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 4, 3, 2]
def baseStart_3372129 : Nat := 118140960795 + 3372129 * 2 ^ 59
def prefixEnd_3372129 : Nat := 4983230072969 + 3 ^ 40 * 3372129 * 2
def baseEnd_3372129 : Nat := 1731523005965342263479367

theorem tailTrace_3372129 : CollatzResearch.WordTrace tailWord_3372129 prefixEnd_3372129 1731523005965342263479367 := by
  unfold tailWord_3372129
  simp only [CollatzResearch.WordTrace]
  refine ⟨122991648800360021627471441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81994432533573347751647627 122991648800360021627471441)
  ·
    refine ⟨92243736600270016220603581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122991648800360021627471441 92243736600270016220603581)
    ·
      refine ⟨34591401225101256082726343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92243736600270016220603581 34591401225101256082726343)
      ·
        refine ⟨51887101837651884124089515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34591401225101256082726343 51887101837651884124089515)
        ·
          refine ⟨77830652756477826186134273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51887101837651884124089515 77830652756477826186134273)
          ·
            refine ⟨58372989567358369639600705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77830652756477826186134273 58372989567358369639600705)
            ·
              refine ⟨43779742175518777229700529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58372989567358369639600705 43779742175518777229700529)
              ·
                refine ⟨32834806631639082922275397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43779742175518777229700529 32834806631639082922275397)
                ·
                  refine ⟨6156526243432328047926637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32834806631639082922275397 6156526243432328047926637)
                  ·
                    refine ⟨2308697341287123017972489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6156526243432328047926637 2308697341287123017972489)
                    ·
                      refine ⟨1731523005965342263479367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308697341287123017972489 1731523005965342263479367)
                      ·
                        rfl

theorem cell23_3372129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_3372129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372129 prefixEnd_3372129 := by exact prefixLift 3372129
  have htrace : WordTrace (prefixWord ++ tailWord_3372129) baseStart_3372129 baseEnd_3372129 := by
    simpa [prefixWord, tailWord_3372129, baseEnd_3372129] using wordTrace_append hprefix tailTrace_3372129
  have hstable : (prefixWord ++ tailWord_3372129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372129).length < 2 ^ (prefixWord ++ tailWord_3372129).sum := by decide
  have hdescent : baseEnd_3372129 < baseStart_3372129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372152 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 1, 6]
def baseStart_3372152 : Nat := 118140960795 + 3372152 * 2 ^ 59
def prefixEnd_3372152 : Nat := 4983230072969 + 3 ^ 40 * 3372152 * 2
def baseEnd_3372152 : Nat := 577178272006798557830587

theorem tailTrace_3372152 : CollatzResearch.WordTrace tailWord_3372152 prefixEnd_3372152 577178272006798557830587 := by
  unfold tailWord_3372152
  simp only [CollatzResearch.WordTrace]
  refine ⟨61496243839638348277779355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81994991786184464370372473 61496243839638348277779355)
  ·
    refine ⟨92244365759457522416669033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61496243839638348277779355 92244365759457522416669033)
    ·
      refine ⟨69183274319593141812501775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92244365759457522416669033 69183274319593141812501775)
      ·
        refine ⟨103774911479389712718752663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69183274319593141812501775 103774911479389712718752663)
        ·
          refine ⟨155662367219084569078128995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103774911479389712718752663 155662367219084569078128995)
          ·
            refine ⟨233493550828626853617193493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155662367219084569078128995 233493550828626853617193493)
            ·
              refine ⟨10945010195091883763305945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 233493550828626853617193493 10945010195091883763305945)
              ·
                refine ⟨8208757646318912822479459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10945010195091883763305945 8208757646318912822479459)
                ·
                  refine ⟨12313136469478369233719189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8208757646318912822479459 12313136469478369233719189)
                  ·
                    refine ⟨577178272006798557830587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12313136469478369233719189 577178272006798557830587)
                    ·
                      rfl

theorem cell23_3372152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_3372152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372152 prefixEnd_3372152 := by exact prefixLift 3372152
  have htrace : WordTrace (prefixWord ++ tailWord_3372152) baseStart_3372152 baseEnd_3372152 := by
    simpa [prefixWord, tailWord_3372152, baseEnd_3372152] using wordTrace_append hprefix tailTrace_3372152
  have hstable : (prefixWord ++ tailWord_3372152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372152).length < 2 ^ (prefixWord ++ tailWord_3372152).sum := by decide
  have hdescent : baseEnd_3372152 < baseStart_3372152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372169 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 4, 4]
def baseStart_3372169 : Nat := 118140960795 + 3372169 * 2 ^ 59
def prefixEnd_3372169 : Nat := 4983230072969 + 3 ^ 40 * 3372169 * 2
def baseEnd_3372169 : Nat := 577181181730507368993061

theorem tailTrace_3372169 : CollatzResearch.WordTrace tailWord_3372169 prefixEnd_3372169 577181181730507368993061 := by
  unfold tailWord_3372169
  simp only [CollatzResearch.WordTrace]
  refine ⟨122993107720215108458927561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81995405146810072305951707 122993107720215108458927561)
  ·
    refine ⟨92244830790161331344195671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122993107720215108458927561 92244830790161331344195671)
    ·
      refine ⟨138367246185241997016293507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92244830790161331344195671 138367246185241997016293507)
      ·
        refine ⟨207550869277862995524440261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138367246185241997016293507 207550869277862995524440261)
        ·
          refine ⟨38915787989599311660832549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207550869277862995524440261 38915787989599311660832549)
          ·
            refine ⟨7296710248049870936406103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38915787989599311660832549 7296710248049870936406103)
            ·
              refine ⟨10945065372074806404609155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7296710248049870936406103 10945065372074806404609155)
              ·
                refine ⟨16417598058112209606913733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10945065372074806404609155 16417598058112209606913733)
                ·
                  refine ⟨3078299635896039301296325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16417598058112209606913733 3078299635896039301296325)
                  ·
                    refine ⟨577181181730507368993061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3078299635896039301296325 577181181730507368993061)
                    ·
                      rfl

theorem cell23_3372169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 4].length) (baseStart_3372169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372169 prefixEnd_3372169 := by exact prefixLift 3372169
  have htrace : WordTrace (prefixWord ++ tailWord_3372169) baseStart_3372169 baseEnd_3372169 := by
    simpa [prefixWord, tailWord_3372169, baseEnd_3372169] using wordTrace_append hprefix tailTrace_3372169
  have hstable : (prefixWord ++ tailWord_3372169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372169).length < 2 ^ (prefixWord ++ tailWord_3372169).sum := by decide
  have hdescent : baseEnd_3372169 < baseStart_3372169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372172 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_3372172 : Nat := 118140960795 + 3372172 * 2 ^ 59
def prefixEnd_3372172 : Nat := 4983230072969 + 3 ^ 40 * 3372172 * 2
def baseEnd_3372172 : Nat := 1731545085633485595241669

theorem tailTrace_3372172 : CollatzResearch.WordTrace tailWord_3372172 prefixEnd_3372172 1731545085633485595241669 := by
  unfold tailWord_3372172
  simp only [CollatzResearch.WordTrace]
  refine ⟨61496608569602119985643385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81995478092802826647524513 61496608569602119985643385)
  ·
    refine ⟨46122456427201589989232539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61496608569602119985643385 46122456427201589989232539)
    ·
      refine ⟨69183684640802384983848809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46122456427201589989232539 69183684640802384983848809)
      ·
        refine ⟨51887763480601788737886607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69183684640802384983848809 51887763480601788737886607)
        ·
          refine ⟨77831645220902683106829911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51887763480601788737886607 77831645220902683106829911)
          ·
            refine ⟨116747467831354024660244867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77831645220902683106829911 116747467831354024660244867)
            ·
              refine ⟨175121201747031036990367301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116747467831354024660244867 175121201747031036990367301)
              ·
                refine ⟨32835225327568319435693869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175121201747031036990367301 32835225327568319435693869)
                ·
                  refine ⟨12313209497838119788385201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32835225327568319435693869 12313209497838119788385201)
                  ·
                    refine ⟨9234907123378589841288901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12313209497838119788385201 9234907123378589841288901)
                    ·
                      refine ⟨1731545085633485595241669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9234907123378589841288901 1731545085633485595241669)
                      ·
                        rfl

theorem cell23_3372172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_3372172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372172 prefixEnd_3372172 := by exact prefixLift 3372172
  have htrace : WordTrace (prefixWord ++ tailWord_3372172) baseStart_3372172 baseEnd_3372172 := by
    simpa [prefixWord, tailWord_3372172, baseEnd_3372172] using wordTrace_append hprefix tailTrace_3372172
  have hstable : (prefixWord ++ tailWord_3372172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372172).length < 2 ^ (prefixWord ++ tailWord_3372172).sum := by decide
  have hdescent : baseEnd_3372172 < baseStart_3372172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372186 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 1, 6]
def baseStart_3372186 : Nat := 118140960795 + 3372186 * 2 ^ 59
def prefixEnd_3372186 : Nat := 4983230072969 + 3 ^ 40 * 3372186 * 2
def baseEnd_3372186 : Nat := 577184091454216180155535

theorem tailTrace_3372186 : CollatzResearch.WordTrace tailWord_3372186 prefixEnd_3372186 577184091454216180155535 := by
  unfold tailWord_3372186
  simp only [CollatzResearch.WordTrace]
  refine ⟨30748431940288380090574103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81995818507435680241530941 30748431940288380090574103)
  ·
    refine ⟨46122647910432570135861155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30748431940288380090574103 46122647910432570135861155)
    ·
      refine ⟨69183971865648855203791733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46122647910432570135861155 69183971865648855203791733)
      ·
        refine ⟨6485997362404580175355475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69183971865648855203791733 6485997362404580175355475)
        ·
          refine ⟨9728996043606870263033213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485997362404580175355475 9728996043606870263033213)
          ·
            refine ⟨3648373516352576348637455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9728996043606870263033213 3648373516352576348637455)
            ·
              refine ⟨5472560274528864522956183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648373516352576348637455 5472560274528864522956183)
              ·
                refine ⟨8208840411793296784434275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5472560274528864522956183 8208840411793296784434275)
                ·
                  refine ⟨12313260617689945176651413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8208840411793296784434275 12313260617689945176651413)
                  ·
                    refine ⟨577184091454216180155535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12313260617689945176651413 577184091454216180155535)
                    ·
                      rfl

theorem cell23_3372186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_3372186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372186 prefixEnd_3372186 := by exact prefixLift 3372186
  have htrace : WordTrace (prefixWord ++ tailWord_3372186) baseStart_3372186 baseEnd_3372186 := by
    simpa [prefixWord, tailWord_3372186, baseEnd_3372186] using wordTrace_append hprefix tailTrace_3372186
  have hstable : (prefixWord ++ tailWord_3372186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372186).length < 2 ^ (prefixWord ++ tailWord_3372186).sum := by decide
  have hdescent : baseEnd_3372186 < baseStart_3372186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372196 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_3372196 : Nat := 118140960795 + 3372196 * 2 ^ 59
def prefixEnd_3372196 : Nat := 4983230072969 + 3 ^ 40 * 3372196 * 2
def baseEnd_3372196 : Nat := 1731557409169193501341559

theorem tailTrace_3372196 : CollatzResearch.WordTrace tailWord_3372196 prefixEnd_3372196 1731557409169193501341559 := by
  unfold tailWord_3372196
  simp only [CollatzResearch.WordTrace]
  refine ⟨61497046245558646035080221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81996061660744861380106961 61497046245558646035080221)
  ·
    refine ⟨23061392342084492263155083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61497046245558646035080221 23061392342084492263155083)
    ·
      refine ⟨34592088513126738394732625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23061392342084492263155083 34592088513126738394732625)
      ·
        refine ⟨25944066384845053796049469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34592088513126738394732625 25944066384845053796049469)
        ·
          refine ⟨9729024894316895173518551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25944066384845053796049469 9729024894316895173518551)
          ·
            refine ⟨14593537341475342760277827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9729024894316895173518551 14593537341475342760277827)
            ·
              refine ⟨21890306012213014140416741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14593537341475342760277827 21890306012213014140416741)
              ·
                refine ⟨4104432377289940151328139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21890306012213014140416741 4104432377289940151328139)
                ·
                  refine ⟨6156648565934910226992209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104432377289940151328139 6156648565934910226992209)
                  ·
                    refine ⟨4617486424451182670244157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6156648565934910226992209 4617486424451182670244157)
                    ·
                      refine ⟨1731557409169193501341559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4617486424451182670244157 1731557409169193501341559)
                      ·
                        rfl

theorem cell23_3372196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_3372196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372196 prefixEnd_3372196 := by exact prefixLift 3372196
  have htrace : WordTrace (prefixWord ++ tailWord_3372196) baseStart_3372196 baseEnd_3372196 := by
    simpa [prefixWord, tailWord_3372196, baseEnd_3372196] using wordTrace_append hprefix tailTrace_3372196
  have hstable : (prefixWord ++ tailWord_3372196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372196).length < 2 ^ (prefixWord ++ tailWord_3372196).sum := by decide
  have hdescent : baseEnd_3372196 < baseStart_3372196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372199 : List Nat := [1, 1, 6, 2, 1, 2, 1, 9]
def baseStart_3372199 : Nat := 118140960795 + 3372199 * 2 ^ 59
def prefixEnd_3372199 : Nat := 4983230072969 + 3 ^ 40 * 3372199 * 2
def baseEnd_3372199 : Nat := 64131812948561369985335

theorem tailTrace_3372199 : CollatzResearch.WordTrace tailWord_3372199 prefixEnd_3372199 64131812948561369985335 := by
  unfold tailWord_3372199
  simp only [CollatzResearch.WordTrace]
  refine ⟨122994201910106423582519651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81996134606737615721679767 122994201910106423582519651)
  ·
    refine ⟨184491302865159635373779477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122994201910106423582519651 184491302865159635373779477)
    ·
      refine ⟨8648029821804357908145913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184491302865159635373779477 8648029821804357908145913)
      ·
        refine ⟨6486022366353268431109435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8648029821804357908145913 6486022366353268431109435)
        ·
          refine ⟨9729033549529902646664153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6486022366353268431109435 9729033549529902646664153)
          ·
            refine ⟨7296775162147426984998115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9729033549529902646664153 7296775162147426984998115)
            ·
              refine ⟨10945162743221140477497173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7296775162147426984998115 10945162743221140477497173)
              ·
                refine ⟨64131812948561369985335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10945162743221140477497173 64131812948561369985335)
                ·
                  rfl

theorem cell23_3372199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 9].length) (baseStart_3372199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372199 prefixEnd_3372199 := by exact prefixLift 3372199
  have htrace : WordTrace (prefixWord ++ tailWord_3372199) baseStart_3372199 baseEnd_3372199 := by
    simpa [prefixWord, tailWord_3372199, baseEnd_3372199] using wordTrace_append hprefix tailTrace_3372199
  have hstable : (prefixWord ++ tailWord_3372199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372199).length < 2 ^ (prefixWord ++ tailWord_3372199).sum := by decide
  have hdescent : baseEnd_3372199 < baseStart_3372199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372210 : List Nat := [3, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2]
def baseStart_3372210 : Nat := 118140960795 + 3372210 * 2 ^ 59
def prefixEnd_3372210 : Nat := 4983230072969 + 3 ^ 40 * 3372210 * 2
def baseEnd_3372210 : Nat := 1731564597898356446566495

theorem tailTrace_3372210 : CollatzResearch.WordTrace tailWord_3372210 prefixEnd_3372210 1731564597898356446566495 := by
  unfold tailWord_3372210
  simp only [CollatzResearch.WordTrace]
  refine ⟨30748650778266643115292521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81996402075377714974113389 30748650778266643115292521)
  ·
    refine ⟨23061488083699982336469391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30748650778266643115292521 23061488083699982336469391)
    ·
      refine ⟨34592232125549973504704087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23061488083699982336469391 34592232125549973504704087)
      ·
        refine ⟨51888348188324960257056131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34592232125549973504704087 51888348188324960257056131)
        ·
          refine ⟨77832522282487440385584197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51888348188324960257056131 77832522282487440385584197)
          ·
            refine ⟨14593597927966395072297037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77832522282487440385584197 14593597927966395072297037)
            ·
              refine ⟨5472599222987398152111389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14593597927966395072297037 5472599222987398152111389)
              ·
                refine ⟨2052224708620274307041771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5472599222987398152111389 2052224708620274307041771)
                ·
                  refine ⟨3078337062930411460562657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052224708620274307041771 3078337062930411460562657)
                  ·
                    refine ⟨2308752797197808595421993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3078337062930411460562657 2308752797197808595421993)
                    ·
                      refine ⟨1731564597898356446566495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308752797197808595421993 1731564597898356446566495)
                      ·
                        rfl

theorem cell23_3372210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_3372210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372210 prefixEnd_3372210 := by exact prefixLift 3372210
  have htrace : WordTrace (prefixWord ++ tailWord_3372210) baseStart_3372210 baseEnd_3372210 := by
    simpa [prefixWord, tailWord_3372210, baseEnd_3372210] using wordTrace_append hprefix tailTrace_3372210
  have hstable : (prefixWord ++ tailWord_3372210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372210).length < 2 ^ (prefixWord ++ tailWord_3372210).sum := by decide
  have hdescent : baseEnd_3372210 < baseStart_3372210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372266 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2]
def baseStart_3372266 : Nat := 118140960795 + 3372266 * 2 ^ 59
def prefixEnd_3372266 : Nat := 4983230072969 + 3 ^ 40 * 3372266 * 2
def baseEnd_3372266 : Nat := 1731593352815008227466237

theorem tailTrace_3372266 : CollatzResearch.WordTrace tailWord_3372266 prefixEnd_3372266 1731593352815008227466237 := by
  unfold tailWord_3372266
  simp only [CollatzResearch.WordTrace]
  refine ⟨30749161400215923506302163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81997763733909129350139101 30749161400215923506302163)
  ·
    refine ⟨46123742100323885259453245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30749161400215923506302163 46123742100323885259453245)
    ·
      refine ⟨17296403287621456972294967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46123742100323885259453245 17296403287621456972294967)
      ·
        refine ⟨25944604931432185458442451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17296403287621456972294967 25944604931432185458442451)
        ·
          refine ⟨38916907397148278187663677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25944604931432185458442451 38916907397148278187663677)
          ·
            refine ⟨14593840273930604320373879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38916907397148278187663677 14593840273930604320373879)
            ·
              refine ⟨21890760410895906480560819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14593840273930604320373879 21890760410895906480560819)
              ·
                refine ⟨32836140616343859720841229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21890760410895906480560819 32836140616343859720841229)
                ·
                  refine ⟨12313552731128947395315461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32836140616343859720841229 12313552731128947395315461)
                  ·
                    refine ⟨2308791137086677636621649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12313552731128947395315461 2308791137086677636621649)
                    ·
                      refine ⟨1731593352815008227466237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308791137086677636621649 1731593352815008227466237)
                      ·
                        rfl

theorem cell23_3372266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_3372266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372266 prefixEnd_3372266 := by exact prefixLift 3372266
  have htrace : WordTrace (prefixWord ++ tailWord_3372266) baseStart_3372266 baseEnd_3372266 := by
    simpa [prefixWord, tailWord_3372266, baseEnd_3372266] using wordTrace_append hprefix tailTrace_3372266
  have hstable : (prefixWord ++ tailWord_3372266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372266).length < 2 ^ (prefixWord ++ tailWord_3372266).sum := by decide
  have hdescent : baseEnd_3372266 < baseStart_3372266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372286 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_3372286 : Nat := 118140960795 + 3372286 * 2 ^ 59
def prefixEnd_3372286 : Nat := 4983230072969 + 3 ^ 40 * 3372286 * 2
def baseEnd_3372286 : Nat := 1731603622428098149216145

theorem tailTrace_3372286 : CollatzResearch.WordTrace tailWord_3372286 prefixEnd_3372286 1731603622428098149216145 := by
  unfold tailWord_3372286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15374671882598904680117089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81998250040527491627291141 15374671882598904680117089)
  ·
    refine ⟨11531003911949178510087817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15374671882598904680117089 11531003911949178510087817)
    ·
      refine ⟨8648252933961883882565863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11531003911949178510087817 8648252933961883882565863)
      ·
        refine ⟨12972379400942825823848795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8648252933961883882565863 12972379400942825823848795)
        ·
          refine ⟨19458569101414238735773193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12972379400942825823848795 19458569101414238735773193)
          ·
            refine ⟨14593926826060679051829895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19458569101414238735773193 14593926826060679051829895)
            ·
              refine ⟨21890890239091018577744843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14593926826060679051829895 21890890239091018577744843)
              ·
                refine ⟨32836335358636527866617265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21890890239091018577744843 32836335358636527866617265)
                ·
                  refine ⟨24627251518977395899962949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32836335358636527866617265 24627251518977395899962949)
                  ·
                    refine ⟨4617609659808261731243053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24627251518977395899962949 4617609659808261731243053)
                    ·
                      refine ⟨1731603622428098149216145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4617609659808261731243053 1731603622428098149216145)
                      ·
                        rfl

theorem cell23_3372286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_3372286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372286 prefixEnd_3372286 := by exact prefixLift 3372286
  have htrace : WordTrace (prefixWord ++ tailWord_3372286) baseStart_3372286 baseEnd_3372286 := by
    simpa [prefixWord, tailWord_3372286, baseEnd_3372286] using wordTrace_append hprefix tailTrace_3372286
  have hstable : (prefixWord ++ tailWord_3372286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372286).length < 2 ^ (prefixWord ++ tailWord_3372286).sum := by decide
  have hdescent : baseEnd_3372286 < baseStart_3372286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372296 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_3372296 : Nat := 118140960795 + 3372296 * 2 ^ 59
def prefixEnd_3372296 : Nat := 4983230072969 + 3 ^ 40 * 3372296 * 2
def baseEnd_3372296 : Nat := 1731608757234643110091099

theorem tailTrace_3372296 : CollatzResearch.WordTrace tailWord_3372296 prefixEnd_3372296 1731608757234643110091099 := by
  unfold tailWord_3372296
  simp only [CollatzResearch.WordTrace]
  refine ⟨61498869895377504574400371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81998493193836672765867161 61498869895377504574400371)
  ·
    refine ⟨92248304843066256861600557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61498869895377504574400371 92248304843066256861600557)
    ·
      refine ⟨34593114316149846323100209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92248304843066256861600557 34593114316149846323100209)
      ·
        refine ⟨25944835737112384742325157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34593114316149846323100209 25944835737112384742325157)
        ·
          refine ⟨4864656700708572139185967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25944835737112384742325157 4864656700708572139185967)
          ·
            refine ⟨7296985051062858208778951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4864656700708572139185967 7296985051062858208778951)
            ·
              refine ⟨10945477576594287313168427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7296985051062858208778951 10945477576594287313168427)
              ·
                refine ⟨16418216364891430969752641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10945477576594287313168427 16418216364891430969752641)
                ·
                  refine ⟨12313662273668573227314481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16418216364891430969752641 12313662273668573227314481)
                  ·
                    refine ⟨9235246705251429920485861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12313662273668573227314481 9235246705251429920485861)
                    ·
                      refine ⟨1731608757234643110091099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9235246705251429920485861 1731608757234643110091099)
                      ·
                        rfl

theorem cell23_3372296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_3372296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372296 prefixEnd_3372296 := by exact prefixLift 3372296
  have htrace : WordTrace (prefixWord ++ tailWord_3372296) baseStart_3372296 baseEnd_3372296 := by
    simpa [prefixWord, tailWord_3372296, baseEnd_3372296] using wordTrace_append hprefix tailTrace_3372296
  have hstable : (prefixWord ++ tailWord_3372296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372296).length < 2 ^ (prefixWord ++ tailWord_3372296).sum := by decide
  have hdescent : baseEnd_3372296 < baseStart_3372296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372299 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 3]
def baseStart_3372299 : Nat := 118140960795 + 3372299 * 2 ^ 59
def prefixEnd_3372299 : Nat := 4983230072969 + 3 ^ 40 * 3372299 * 2
def baseEnd_3372299 : Nat := 1731610297676606598353585

theorem tailTrace_3372299 : CollatzResearch.WordTrace tailWord_3372299 prefixEnd_3372299 1731610297676606598353585 := by
  unfold tailWord_3372299
  simp only [CollatzResearch.WordTrace]
  refine ⟨122997849209744140661159951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81998566139829427107439967 122997849209744140661159951)
  ·
    refine ⟨184496773814616210991739927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122997849209744140661159951 184496773814616210991739927)
    ·
      refine ⟨276745160721924316487609891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184496773814616210991739927 276745160721924316487609891)
      ·
        refine ⟨415117741082886474731414837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276745160721924316487609891 415117741082886474731414837)
        ·
          refine ⟨38917288226520607006070141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 415117741082886474731414837 38917288226520607006070141)
          ·
            refine ⟨14593983084945227627276303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38917288226520607006070141 14593983084945227627276303)
            ·
              refine ⟨21890974627417841440914455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14593983084945227627276303 21890974627417841440914455)
              ·
                refine ⟨32836461941126762161371683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21890974627417841440914455 32836461941126762161371683)
                ·
                  refine ⟨49254692911690143242057525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32836461941126762161371683 49254692911690143242057525)
                  ·
                    refine ⟨4617627460470950928942893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49254692911690143242057525 4617627460470950928942893)
                    ·
                      refine ⟨1731610297676606598353585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4617627460470950928942893 1731610297676606598353585)
                      ·
                        rfl

theorem cell23_3372299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 3].length) (baseStart_3372299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372299 prefixEnd_3372299 := by exact prefixLift 3372299
  have htrace : WordTrace (prefixWord ++ tailWord_3372299) baseStart_3372299 baseEnd_3372299 := by
    simpa [prefixWord, tailWord_3372299, baseEnd_3372299] using wordTrace_append hprefix tailTrace_3372299
  have hstable : (prefixWord ++ tailWord_3372299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372299).length < 2 ^ (prefixWord ++ tailWord_3372299).sum := by decide
  have hdescent : baseEnd_3372299 < baseStart_3372299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372333 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_3372333 : Nat := 118140960795 + 3372333 * 2 ^ 59
def prefixEnd_3372333 : Nat := 4983230072969 + 3 ^ 40 * 3372333 * 2
def baseEnd_3372333 : Nat := 1731627756018859465328429

theorem tailTrace_3372333 : CollatzResearch.WordTrace tailWord_3372333 prefixEnd_3372333 1731627756018859465328429 := by
  unfold tailWord_3372333
  simp only [CollatzResearch.WordTrace]
  refine ⟨122999089291620964467897653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81999392861080642978598435 122999089291620964467897653)
  ·
    refine ⟨11531164621089465418865405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122999089291620964467897653 11531164621089465418865405)
    ·
      refine ⟨4324186732908549532074527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11531164621089465418865405 4324186732908549532074527)
      ·
        refine ⟨6486280099362824298111791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4324186732908549532074527 6486280099362824298111791)
        ·
          refine ⟨9729420149044236447167687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6486280099362824298111791 9729420149044236447167687)
          ·
            refine ⟨14594130223566354670751531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9729420149044236447167687 14594130223566354670751531)
            ·
              refine ⟨21891195335349532006127297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14594130223566354670751531 21891195335349532006127297)
              ·
                refine ⟨16418396501512149004595473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21891195335349532006127297 16418396501512149004595473)
                ·
                  refine ⟨12313797376134111753446605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16418396501512149004595473 12313797376134111753446605)
                  ·
                    refine ⟨4617674016050291907542477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12313797376134111753446605 4617674016050291907542477)
                    ·
                      refine ⟨1731627756018859465328429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4617674016050291907542477 1731627756018859465328429)
                      ·
                        rfl

theorem cell23_3372333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_3372333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372333 prefixEnd_3372333 := by exact prefixLift 3372333
  have htrace : WordTrace (prefixWord ++ tailWord_3372333) baseStart_3372333 baseEnd_3372333 := by
    simpa [prefixWord, tailWord_3372333, baseEnd_3372333] using wordTrace_append hprefix tailTrace_3372333
  have hstable : (prefixWord ++ tailWord_3372333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372333).length < 2 ^ (prefixWord ++ tailWord_3372333).sum := by decide
  have hdescent : baseEnd_3372333 < baseStart_3372333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372366 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_3372366 : Nat := 118140960795 + 3372366 * 2 ^ 59
def prefixEnd_3372366 : Nat := 4983230072969 + 3 ^ 40 * 3372366 * 2
def baseEnd_3372366 : Nat := 577214900293485945405259

theorem tailTrace_3372366 : CollatzResearch.WordTrace tailWord_3372366 prefixEnd_3372366 577214900293485945405259 := by
  unfold tailWord_3372366
  simp only [CollatzResearch.WordTrace]
  refine ⟨15375036612562676387981119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82000195267000940735899301 15375036612562676387981119)
  ·
    refine ⟨23062554918844014581971679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15375036612562676387981119 23062554918844014581971679)
    ·
      refine ⟨34593832378266021872957519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23062554918844014581971679 34593832378266021872957519)
      ·
        refine ⟨51890748567399032809436279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34593832378266021872957519 51890748567399032809436279)
        ·
          refine ⟨77836122851098549214154419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51890748567399032809436279 77836122851098549214154419)
          ·
            refine ⟨116754184276647823821231629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77836122851098549214154419 116754184276647823821231629)
            ·
              refine ⟨43782819103742933932961861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116754184276647823821231629 43782819103742933932961861)
              ·
                refine ⟨8209278581951800112430349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43782819103742933932961861 8209278581951800112430349)
                ·
                  refine ⟨3078479468231925042161381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8209278581951800112430349 3078479468231925042161381)
                  ·
                    refine ⟨577214900293485945405259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3078479468231925042161381 577214900293485945405259)
                    ·
                      rfl

theorem cell23_3372366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_3372366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372366 prefixEnd_3372366 := by exact prefixLift 3372366
  have htrace : WordTrace (prefixWord ++ tailWord_3372366) baseStart_3372366 baseEnd_3372366 := by
    simpa [prefixWord, tailWord_3372366, baseEnd_3372366] using wordTrace_append hprefix tailTrace_3372366
  have hstable : (prefixWord ++ tailWord_3372366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372366).length < 2 ^ (prefixWord ++ tailWord_3372366).sum := by decide
  have hdescent : baseEnd_3372366 < baseStart_3372366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372369 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_3372369 : Nat := 118140960795 + 3372369 * 2 ^ 59
def prefixEnd_3372369 : Nat := 4983230072969 + 3 ^ 40 * 3372369 * 2
def baseEnd_3372369 : Nat := 1731646241322421324478263

theorem tailTrace_3372369 : CollatzResearch.WordTrace tailWord_3372369 prefixEnd_3372369 1731646241322421324478263 := by
  unfold tailWord_3372369
  simp only [CollatzResearch.WordTrace]
  refine ⟨123000402319490542616208161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82000268212993695077472107 123000402319490542616208161)
  ·
    refine ⟨92250301739617906962156121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123000402319490542616208161 92250301739617906962156121)
    ·
      refine ⟨69187726304713430221617091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92250301739617906962156121 69187726304713430221617091)
      ·
        refine ⟨103781589457070145332425637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69187726304713430221617091 103781589457070145332425637)
        ·
          refine ⟨19459048023200652249829807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103781589457070145332425637 19459048023200652249829807)
          ·
            refine ⟨29188572034800978374744711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19459048023200652249829807 29188572034800978374744711)
            ·
              refine ⟨43782858052201467562117067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29188572034800978374744711 43782858052201467562117067)
              ·
                refine ⟨65674287078302201343175601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43782858052201467562117067 65674287078302201343175601)
                ·
                  refine ⟨49255715308726651007381701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65674287078302201343175601 49255715308726651007381701)
                  ·
                    refine ⟨9235446620386247063884069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49255715308726651007381701 9235446620386247063884069)
                    ·
                      refine ⟨1731646241322421324478263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9235446620386247063884069 1731646241322421324478263)
                      ·
                        rfl

theorem cell23_3372369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_3372369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372369 prefixEnd_3372369 := by exact prefixLift 3372369
  have htrace : WordTrace (prefixWord ++ tailWord_3372369) baseStart_3372369 baseEnd_3372369 := by
    simpa [prefixWord, tailWord_3372369, baseEnd_3372369] using wordTrace_append hprefix tailTrace_3372369
  have hstable : (prefixWord ++ tailWord_3372369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372369).length < 2 ^ (prefixWord ++ tailWord_3372369).sum := by decide
  have hdescent : baseEnd_3372369 < baseStart_3372369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372376 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 2, 2, 3]
def baseStart_3372376 : Nat := 118140960795 + 3372376 * 2 ^ 59
def prefixEnd_3372376 : Nat := 4983230072969 + 3 ^ 40 * 3372376 * 2
def baseEnd_3372376 : Nat := 1731649835687002797090731

theorem tailTrace_3372376 : CollatzResearch.WordTrace tailWord_3372376 prefixEnd_3372376 1731649835687002797090731 := by
  unfold tailWord_3372376
  simp only [CollatzResearch.WordTrace]
  refine ⟨61500328815232591405856491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82000438420310121874475321 61500328815232591405856491)
  ·
    refine ⟨92250493222848887108784737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61500328815232591405856491 92250493222848887108784737)
    ·
      refine ⟨69187869917136665331588553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92250493222848887108784737 69187869917136665331588553)
      ·
        refine ⟨51890902437852498998691415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69187869917136665331588553 51890902437852498998691415)
        ·
          refine ⟨77836353656778748498037123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51890902437852498998691415 77836353656778748498037123)
          ·
            refine ⟨116754530485168122747055685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77836353656778748498037123 116754530485168122747055685)
            ·
              refine ⟨21891474465969023015072941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116754530485168122747055685 21891474465969023015072941)
              ·
                refine ⟨8209302924738383630652353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21891474465969023015072941 8209302924738383630652353)
                ·
                  refine ⟨6156977193553787722989265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8209302924738383630652353 6156977193553787722989265)
                  ·
                    refine ⟨4617732895165340792241949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6156977193553787722989265 4617732895165340792241949)
                    ·
                      refine ⟨1731649835687002797090731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4617732895165340792241949 1731649835687002797090731)
                      ·
                        rfl

theorem cell23_3372376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_3372376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372376 prefixEnd_3372376 := by exact prefixLift 3372376
  have htrace : WordTrace (prefixWord ++ tailWord_3372376) baseStart_3372376 baseEnd_3372376 := by
    simpa [prefixWord, tailWord_3372376, baseEnd_3372376] using wordTrace_append hprefix tailTrace_3372376
  have hstable : (prefixWord ++ tailWord_3372376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372376).length < 2 ^ (prefixWord ++ tailWord_3372376).sum := by decide
  have hdescent : baseEnd_3372376 < baseStart_3372376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372400 : List Nat := [2, 1, 1, 1, 4, 2, 5, 2, 1, 4]
def baseStart_3372400 : Nat := 118140960795 + 3372400 * 2 ^ 59
def prefixEnd_3372400 : Nat := 4983230072969 + 3 ^ 40 * 3372400 * 2
def baseEnd_3372400 : Nat := 577220719740903567730207

theorem tailTrace_3372400 : CollatzResearch.WordTrace tailWord_3372400 prefixEnd_3372400 577220719740903567730207 := by
  unfold tailWord_3372400
  simp only [CollatzResearch.WordTrace]
  refine ⟨61500766491189117455293327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82001021988252156607057769 61500766491189117455293327)
  ·
    refine ⟨92251149736783676182939991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61500766491189117455293327 92251149736783676182939991)
    ·
      refine ⟨138376724605175514274409987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92251149736783676182939991 138376724605175514274409987)
      ·
        refine ⟨207565086907763271411614981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138376724605175514274409987 207565086907763271411614981)
        ·
          refine ⟨38918453795205613389677809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207565086907763271411614981 38918453795205613389677809)
          ·
            refine ⟨29188840346404210042258357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38918453795205613389677809 29188840346404210042258357)
            ·
              refine ⟨2736453782475394691461721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29188840346404210042258357 2736453782475394691461721)
              ·
                refine ⟨2052340336856546018596291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2736453782475394691461721 2052340336856546018596291)
                ·
                  refine ⟨3078510505284819027894437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052340336856546018596291 3078510505284819027894437)
                  ·
                    refine ⟨577220719740903567730207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3078510505284819027894437 577220719740903567730207)
                    ·
                      rfl

theorem cell23_3372400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 2, 1, 4].length) (baseStart_3372400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372400 prefixEnd_3372400 := by exact prefixLift 3372400
  have htrace : WordTrace (prefixWord ++ tailWord_3372400) baseStart_3372400 baseEnd_3372400 := by
    simpa [prefixWord, tailWord_3372400, baseEnd_3372400] using wordTrace_append hprefix tailTrace_3372400
  have hstable : (prefixWord ++ tailWord_3372400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372400).length < 2 ^ (prefixWord ++ tailWord_3372400).sum := by decide
  have hdescent : baseEnd_3372400 < baseStart_3372400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372416 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 3, 5, 2]
def baseStart_3372416 : Nat := 118140960795 + 3372416 * 2 ^ 59
def prefixEnd_3372416 : Nat := 4983230072969 + 3 ^ 40 * 3372416 * 2
def baseEnd_3372416 : Nat := 1731670374913182640590547

theorem tailTrace_3372416 : CollatzResearch.WordTrace tailWord_3372416 prefixEnd_3372416 1731670374913182640590547 := by
  unfold tailWord_3372416
  simp only [CollatzResearch.WordTrace]
  refine ⟨61501058275160134821584551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82001411033546846428779401 61501058275160134821584551)
  ·
    refine ⟨92251587412740202232376827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61501058275160134821584551 92251587412740202232376827)
    ·
      refine ⟨138377381119110303348565241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92251587412740202232376827 138377381119110303348565241)
      ·
        refine ⟨103783035839332727511423931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138377381119110303348565241 103783035839332727511423931)
        ·
          refine ⟨155674553758999091267135897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103783035839332727511423931 155674553758999091267135897)
          ·
            refine ⟨116755915319249318450351923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155674553758999091267135897 116755915319249318450351923)
            ·
              refine ⟨175133872978873977675527885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116755915319249318450351923 175133872978873977675527885)
              ·
                refine ⟨65675202367077741628322957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175133872978873977675527885 65675202367077741628322957)
                ·
                  refine ⟨24628200887654153110621109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65675202367077741628322957 24628200887654153110621109)
                  ·
                    refine ⟨2308893833217576854120729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24628200887654153110621109 2308893833217576854120729)
                    ·
                      refine ⟨1731670374913182640590547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308893833217576854120729 1731670374913182640590547)
                      ·
                        rfl

theorem cell23_3372416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 5, 2].length) (baseStart_3372416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372416 prefixEnd_3372416 := by exact prefixLift 3372416
  have htrace : WordTrace (prefixWord ++ tailWord_3372416) baseStart_3372416 baseEnd_3372416 := by
    simpa [prefixWord, tailWord_3372416, baseEnd_3372416] using wordTrace_append hprefix tailTrace_3372416
  have hstable : (prefixWord ++ tailWord_3372416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372416).length < 2 ^ (prefixWord ++ tailWord_3372416).sum := by decide
  have hdescent : baseEnd_3372416 < baseStart_3372416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372450 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 2, 3, 2]
def baseStart_3372450 : Nat := 118140960795 + 3372450 * 2 ^ 59
def prefixEnd_3372450 : Nat := 4983230072969 + 3 ^ 40 * 3372450 * 2
def baseEnd_3372450 : Nat := 1731687833255435507565391

theorem tailTrace_3372450 : CollatzResearch.WordTrace tailWord_3372450 prefixEnd_3372450 1731687833255435507565391 := by
  unfold tailWord_3372450
  simp only [CollatzResearch.WordTrace]
  refine ⟨30750839158049273362476701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82002237754798062299937869 30750839158049273362476701)
  ·
    refine ⟨11531564684268477510928763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30750839158049273362476701 11531564684268477510928763)
    ·
      refine ⟨17297347026402716266393145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11531564684268477510928763 17297347026402716266393145)
      ·
        refine ⟨12973010269802037199794859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17297347026402716266393145 12973010269802037199794859)
        ·
          refine ⟨19459515404703055799692289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12973010269802037199794859 19459515404703055799692289)
          ·
            refine ⟨14594636553527291849769217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19459515404703055799692289 14594636553527291849769217)
            ·
              refine ⟨10945977415145468887326913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14594636553527291849769217 10945977415145468887326913)
              ·
                refine ⟨8209483061359101665495185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10945977415145468887326913 8209483061359101665495185)
                ·
                  refine ⟨6157112296019326249121389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8209483061359101665495185 6157112296019326249121389)
                  ·
                    refine ⟨2308917111007247343420521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6157112296019326249121389 2308917111007247343420521)
                    ·
                      refine ⟨1731687833255435507565391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308917111007247343420521 1731687833255435507565391)
                      ·
                        rfl

theorem cell23_3372450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_3372450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372450 prefixEnd_3372450 := by exact prefixLift 3372450
  have htrace : WordTrace (prefixWord ++ tailWord_3372450) baseStart_3372450 baseEnd_3372450 := by
    simpa [prefixWord, tailWord_3372450, baseEnd_3372450] using wordTrace_append hprefix tailTrace_3372450
  have hstable : (prefixWord ++ tailWord_3372450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372450).length < 2 ^ (prefixWord ++ tailWord_3372450).sum := by decide
  have hdescent : baseEnd_3372450 < baseStart_3372450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372463 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 7, 2, 2]
def baseStart_3372463 : Nat := 118140960795 + 3372463 * 2 ^ 59
def prefixEnd_3372463 : Nat := 4983230072969 + 3 ^ 40 * 3372463 * 2
def baseEnd_3372463 : Nat := 1731694508503943956702831

theorem tailTrace_3372463 : CollatzResearch.WordTrace tailWord_3372463 prefixEnd_3372463 1731694508503943956702831 := by
  unfold tailWord_3372463
  simp only [CollatzResearch.WordTrace]
  refine ⟨123003830781149996670130043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82002553854099997780086695 123003830781149996670130043)
  ·
    refine ⟨184505746171724995005195065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123003830781149996670130043 184505746171724995005195065)
    ·
      refine ⟨138379309628793746253896299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184505746171724995005195065 138379309628793746253896299)
      ·
        refine ⟨207568964443190619380844449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138379309628793746253896299 207568964443190619380844449)
        ·
          refine ⟨155676723332392964535633337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207568964443190619380844449 155676723332392964535633337)
          ·
            refine ⟨116757542499294723401725003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155676723332392964535633337 116757542499294723401725003)
            ·
              refine ⟨175136313748942085102587505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116757542499294723401725003 175136313748942085102587505)
              ·
                refine ⟨131352235311706563826940629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175136313748942085102587505 131352235311706563826940629)
                ·
                  refine ⟨3078568015118122589693921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 131352235311706563826940629 3078568015118122589693921)
                  ·
                    refine ⟨2308926011338591942270441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3078568015118122589693921 2308926011338591942270441)
                    ·
                      refine ⟨1731694508503943956702831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308926011338591942270441 1731694508503943956702831)
                      ·
                        rfl

theorem cell23_3372463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 2, 2].length) (baseStart_3372463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372463 prefixEnd_3372463 := by exact prefixLift 3372463
  have htrace : WordTrace (prefixWord ++ tailWord_3372463) baseStart_3372463 baseEnd_3372463 := by
    simpa [prefixWord, tailWord_3372463, baseEnd_3372463] using wordTrace_append hprefix tailTrace_3372463
  have hstable : (prefixWord ++ tailWord_3372463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372463).length < 2 ^ (prefixWord ++ tailWord_3372463).sum := by decide
  have hdescent : baseEnd_3372463 < baseStart_3372463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372473 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 1, 6]
def baseStart_3372473 : Nat := 118140960795 + 3372473 * 2 ^ 59
def prefixEnd_3372473 : Nat := 4983230072969 + 3 ^ 40 * 3372473 * 2
def baseEnd_3372473 : Nat := 577233214436829639192595

theorem tailTrace_3372473 : CollatzResearch.WordTrace tailWord_3372473 prefixEnd_3372473 577233214436829639192595 := by
  unfold tailWord_3372473
  simp only [CollatzResearch.WordTrace]
  refine ⟨123004195511113768377994073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82002797007409178918662715 123004195511113768377994073)
  ·
    refine ⟨92253146633335326283495555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123004195511113768377994073 92253146633335326283495555)
    ·
      refine ⟨138379719950002989425243333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92253146633335326283495555 138379719950002989425243333)
      ·
        refine ⟨25946197490625560517233125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138379719950002989425243333 25946197490625560517233125)
        ·
          refine ⟨4864912029492292596981211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25946197490625560517233125 4864912029492292596981211)
          ·
            refine ⟨7297368044238438895471817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4864912029492292596981211 7297368044238438895471817)
            ·
              refine ⟨5473026033178829171603863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7297368044238438895471817 5473026033178829171603863)
              ·
                refine ⟨8209539049768243757405795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5473026033178829171603863 8209539049768243757405795)
                ·
                  refine ⟨12314308574652365636108693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8209539049768243757405795 12314308574652365636108693)
                  ·
                    refine ⟨577233214436829639192595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12314308574652365636108693 577233214436829639192595)
                    ·
                      rfl

theorem cell23_3372473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 6].length) (baseStart_3372473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372473 prefixEnd_3372473 := by exact prefixLift 3372473
  have htrace : WordTrace (prefixWord ++ tailWord_3372473) baseStart_3372473 baseEnd_3372473 := by
    simpa [prefixWord, tailWord_3372473, baseEnd_3372473] using wordTrace_append hprefix tailTrace_3372473
  have hstable : (prefixWord ++ tailWord_3372473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372473).length < 2 ^ (prefixWord ++ tailWord_3372473).sum := by decide
  have hdescent : baseEnd_3372473 < baseStart_3372473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372479 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_3372479 : Nat := 118140960795 + 3372479 * 2 ^ 59
def prefixEnd_3372479 : Nat := 4983230072969 + 3 ^ 40 * 3372479 * 2
def baseEnd_3372479 : Nat := 1731702724194415894102757

theorem tailTrace_3372479 : CollatzResearch.WordTrace tailWord_3372479 prefixEnd_3372479 1731702724194415894102757 := by
  unfold tailWord_3372479
  simp only [CollatzResearch.WordTrace]
  refine ⟨123004414349092031402712491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82002942899394687601808327 123004414349092031402712491)
  ·
    refine ⟨184506621523638047104068737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123004414349092031402712491 184506621523638047104068737)
    ·
      refine ⟨138379966142728535328051553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184506621523638047104068737 138379966142728535328051553)
      ·
        refine ⟨103784974607046401496038665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138379966142728535328051553 103784974607046401496038665)
        ·
          refine ⟨77838730955284801122028999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103784974607046401496038665 77838730955284801122028999)
          ·
            refine ⟨116758096432927201683043499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77838730955284801122028999 116758096432927201683043499)
            ·
              refine ⟨175137144649390802524565249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116758096432927201683043499 175137144649390802524565249)
              ·
                refine ⟨131352858487043101893423937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175137144649390802524565249 131352858487043101893423937)
                ·
                  refine ⟨98514643865282326420067953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131352858487043101893423937 98514643865282326420067953)
                  ·
                    refine ⟨73885982898961744815050965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98514643865282326420067953 73885982898961744815050965)
                    ·
                      refine ⟨1731702724194415894102757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73885982898961744815050965 1731702724194415894102757)
                      ·
                        rfl

theorem cell23_3372479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_3372479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372479 prefixEnd_3372479 := by exact prefixLift 3372479
  have htrace : WordTrace (prefixWord ++ tailWord_3372479) baseStart_3372479 baseEnd_3372479 := by
    simpa [prefixWord, tailWord_3372479, baseEnd_3372479] using wordTrace_append hprefix tailTrace_3372479
  have hstable : (prefixWord ++ tailWord_3372479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372479).length < 2 ^ (prefixWord ++ tailWord_3372479).sum := by decide
  have hdescent : baseEnd_3372479 < baseStart_3372479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372523 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 3, 3, 2]
def baseStart_3372523 : Nat := 118140960795 + 3372523 * 2 ^ 59
def prefixEnd_3372523 : Nat := 4983230072969 + 3 ^ 40 * 3372523 * 2
def baseEnd_3372523 : Nat := 1731725317343213721952555

theorem tailTrace_3372523 : CollatzResearch.WordTrace tailWord_3372523 prefixEnd_3372523 1731725317343213721952555 := by
  unfold tailWord_3372523
  simp only [CollatzResearch.WordTrace]
  refine ⟨123006019160932626917314223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82004012773955084611542815 123006019160932626917314223)
  ·
    refine ⟨184509028741398940375971335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123006019160932626917314223 184509028741398940375971335)
    ·
      refine ⟨276763543112098410563957003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184509028741398940375971335 276763543112098410563957003)
      ·
        refine ⟨415145314668147615845935505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276763543112098410563957003 415145314668147615845935505)
        ·
          refine ⟨311358986001110711884451629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415145314668147615845935505 311358986001110711884451629)
          ·
            refine ⟨116759619750416516956669361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311358986001110711884451629 116759619750416516956669361)
            ·
              refine ⟨87569714812812387717502021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116759619750416516956669361 87569714812812387717502021)
              ·
                refine ⟨16419321527402322697031629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87569714812812387717502021 16419321527402322697031629)
                ·
                  refine ⟨6157245572775871011386861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16419321527402322697031629 6157245572775871011386861)
                  ·
                    refine ⟨2308967089790951629270073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6157245572775871011386861 2308967089790951629270073)
                    ·
                      refine ⟨1731725317343213721952555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308967089790951629270073 1731725317343213721952555)
                      ·
                        rfl

theorem cell23_3372523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 3, 2].length) (baseStart_3372523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372523 prefixEnd_3372523 := by exact prefixLift 3372523
  have htrace : WordTrace (prefixWord ++ tailWord_3372523) baseStart_3372523 baseEnd_3372523 := by
    simpa [prefixWord, tailWord_3372523, baseEnd_3372523] using wordTrace_append hprefix tailTrace_3372523
  have hstable : (prefixWord ++ tailWord_3372523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372523).length < 2 ^ (prefixWord ++ tailWord_3372523).sum := by decide
  have hdescent : baseEnd_3372523 < baseStart_3372523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372530 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3372530 : Nat := 118140960795 + 3372530 * 2 ^ 59
def prefixEnd_3372530 : Nat := 4983230072969 + 3 ^ 40 * 3372530 * 2
def baseEnd_3372530 : Nat := 1731728911707795194565023

theorem tailTrace_3372530 : CollatzResearch.WordTrace tailWord_3372530 prefixEnd_3372530 1731728911707795194565023 := by
  unfold tailWord_3372530
  simp only [CollatzResearch.WordTrace]
  refine ⟨30751568617976816778204761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82004182981271511408546029 30751568617976816778204761)
  ·
    refine ⟨23063676463482612583653571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30751568617976816778204761 23063676463482612583653571)
    ·
      refine ⟨34595514695223918875480357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23063676463482612583653571 34595514695223918875480357)
      ·
        refine ⟨6486659005354484789152567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34595514695223918875480357 6486659005354484789152567)
        ·
          refine ⟨9729988508031727183728851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6486659005354484789152567 9729988508031727183728851)
          ·
            refine ⟨14594982762047590775593277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9729988508031727183728851 14594982762047590775593277)
            ·
              refine ⟨5473118535767846540847479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14594982762047590775593277 5473118535767846540847479)
              ·
                refine ⟨8209677803651769811271219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5473118535767846540847479 8209677803651769811271219)
                ·
                  refine ⟨12314516705477654716906829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8209677803651769811271219 12314516705477654716906829)
                  ·
                    refine ⟨4617943764554120518840061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12314516705477654716906829 4617943764554120518840061)
                    ·
                      refine ⟨1731728911707795194565023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4617943764554120518840061 1731728911707795194565023)
                      ·
                        rfl

theorem cell23_3372530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3372530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372530 prefixEnd_3372530 := by exact prefixLift 3372530
  have htrace : WordTrace (prefixWord ++ tailWord_3372530) baseStart_3372530 baseEnd_3372530 := by
    simpa [prefixWord, tailWord_3372530, baseEnd_3372530] using wordTrace_append hprefix tailTrace_3372530
  have hstable : (prefixWord ++ tailWord_3372530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372530).length < 2 ^ (prefixWord ++ tailWord_3372530).sum := by decide
  have hdescent : baseEnd_3372530 < baseStart_3372530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372540 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 1, 3, 2]
def baseStart_3372540 : Nat := 118140960795 + 3372540 * 2 ^ 59
def prefixEnd_3372540 : Nat := 4983230072969 + 3 ^ 40 * 3372540 * 2
def baseEnd_3372540 : Nat := 1731734046514340155439977

theorem tailTrace_3372540 : CollatzResearch.WordTrace tailWord_3372540 prefixEnd_3372540 1731734046514340155439977 := by
  unfold tailWord_3372540
  simp only [CollatzResearch.WordTrace]
  refine ⟨61503319600935519410341537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82004426134580692547122049 61503319600935519410341537)
  ·
    refine ⟨46127489700701639557756153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61503319600935519410341537 46127489700701639557756153)
    ·
      refine ⟨34595617275526229668317115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46127489700701639557756153 34595617275526229668317115)
      ·
        refine ⟨51893425913289344502475673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34595617275526229668317115 51893425913289344502475673)
        ·
          refine ⟨38920069434967008376856755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51893425913289344502475673 38920069434967008376856755)
          ·
            refine ⟨58380104152450512565285133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38920069434967008376856755 58380104152450512565285133)
            ·
              refine ⟨21892539057168942211981925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58380104152450512565285133 21892539057168942211981925)
              ·
                refine ⟨4104851073219176664746611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21892539057168942211981925 4104851073219176664746611)
                ·
                  refine ⟨6157276609828764997119917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104851073219176664746611 6157276609828764997119917)
                  ·
                    refine ⟨2308978728685786873919969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6157276609828764997119917 2308978728685786873919969)
                    ·
                      refine ⟨1731734046514340155439977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308978728685786873919969 1731734046514340155439977)
                      ·
                        rfl

theorem cell23_3372540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_3372540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372540 prefixEnd_3372540 := by exact prefixLift 3372540
  have htrace : WordTrace (prefixWord ++ tailWord_3372540) baseStart_3372540 baseEnd_3372540 := by
    simpa [prefixWord, tailWord_3372540, baseEnd_3372540] using wordTrace_append hprefix tailTrace_3372540
  have hstable : (prefixWord ++ tailWord_3372540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372540).length < 2 ^ (prefixWord ++ tailWord_3372540).sum := by decide
  have hdescent : baseEnd_3372540 < baseStart_3372540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372548 : List Nat := [2, 3, 2, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_3372548 : Nat := 118140960795 + 3372548 * 2 ^ 59
def prefixEnd_3372548 : Nat := 4983230072969 + 3 ^ 40 * 3372548 * 2
def baseEnd_3372548 : Nat := 1731738154359576124139941

theorem tailTrace_3372548 : CollatzResearch.WordTrace tailWord_3372548 prefixEnd_3372548 1731738154359576124139941 := by
  unfold tailWord_3372548
  simp only [CollatzResearch.WordTrace]
  refine ⟨61503465492921028093487149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82004620657228037457982865 61503465492921028093487149)
  ·
    refine ⟨23063799559845385535057681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61503465492921028093487149 23063799559845385535057681)
    ·
      refine ⟨17297849669884039151293261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23063799559845385535057681 17297849669884039151293261)
      ·
        refine ⟨6486693626206514681734973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17297849669884039151293261 6486693626206514681734973)
        ·
          refine ⟨2432510109827443005650615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6486693626206514681734973 2432510109827443005650615)
          ·
            refine ⟨3648765164741164508475923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432510109827443005650615 3648765164741164508475923)
            ·
              refine ⟨5473147747111746762713885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648765164741164508475923 5473147747111746762713885)
              ·
                refine ⟨2052430405166905036017707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5473147747111746762713885 2052430405166905036017707)
                ·
                  refine ⟨3078645607750357554026561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052430405166905036017707 3078645607750357554026561)
                  ·
                    refine ⟨2308984205812768165519921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3078645607750357554026561 2308984205812768165519921)
                    ·
                      refine ⟨1731738154359576124139941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308984205812768165519921 1731738154359576124139941)
                      ·
                        rfl

theorem cell23_3372548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_3372548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372548 prefixEnd_3372548 := by exact prefixLift 3372548
  have htrace : WordTrace (prefixWord ++ tailWord_3372548) baseStart_3372548 baseEnd_3372548 := by
    simpa [prefixWord, tailWord_3372548, baseEnd_3372548] using wordTrace_append hprefix tailTrace_3372548
  have hstable : (prefixWord ++ tailWord_3372548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372548).length < 2 ^ (prefixWord ++ tailWord_3372548).sum := by decide
  have hdescent : baseEnd_3372548 < baseStart_3372548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372553 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 3, 4, 2]
def baseStart_3372553 : Nat := 118140960795 + 3372553 * 2 ^ 59
def prefixEnd_3372553 : Nat := 4983230072969 + 3 ^ 40 * 3372553 * 2
def baseEnd_3372553 : Nat := 1731740721762848604577417

theorem tailTrace_3372553 : CollatzResearch.WordTrace tailWord_3372553 prefixEnd_3372553 1731740721762848604577417 := by
  unfold tailWord_3372553
  simp only [CollatzResearch.WordTrace]
  refine ⟨123007113350823942040906313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82004742233882628027270875 123007113350823942040906313)
  ·
    refine ⟨92255335013117956530679735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123007113350823942040906313 92255335013117956530679735)
    ·
      refine ⟨138383002519676934796019603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92255335013117956530679735 138383002519676934796019603)
      ·
        refine ⟨207574503779515402194029405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138383002519676934796019603 207574503779515402194029405)
        ·
          refine ⟨77840438917318275822761027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207574503779515402194029405 77840438917318275822761027)
          ·
            refine ⟨116760658375977413734141541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77840438917318275822761027 116760658375977413734141541)
            ·
              refine ⟨21892623445495765075151539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116760658375977413734141541 21892623445495765075151539)
              ·
                refine ⟨32838935168243647612727309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21892623445495765075151539 32838935168243647612727309)
                ·
                  refine ⟨12314600688091367854772741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32838935168243647612727309 12314600688091367854772741)
                  ·
                    refine ⟨2308987629017131472769889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12314600688091367854772741 2308987629017131472769889)
                    ·
                      refine ⟨1731740721762848604577417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2308987629017131472769889 1731740721762848604577417)
                      ·
                        rfl

theorem cell23_3372553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 4, 2].length) (baseStart_3372553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372553 prefixEnd_3372553 := by exact prefixLift 3372553
  have htrace : WordTrace (prefixWord ++ tailWord_3372553) baseStart_3372553 baseEnd_3372553 := by
    simpa [prefixWord, tailWord_3372553, baseEnd_3372553] using wordTrace_append hprefix tailTrace_3372553
  have hstable : (prefixWord ++ tailWord_3372553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372553).length < 2 ^ (prefixWord ++ tailWord_3372553).sum := by decide
  have hdescent : baseEnd_3372553 < baseStart_3372553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372573 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_3372573 : Nat := 118140960795 + 3372573 * 2 ^ 59
def prefixEnd_3372573 : Nat := 4983230072969 + 3 ^ 40 * 3372573 * 2
def baseEnd_3372573 : Nat := 1731750991375938526327325

theorem tailTrace_3372573 : CollatzResearch.WordTrace tailWord_3372573 prefixEnd_3372573 1731750991375938526327325 := by
  unfold tailWord_3372573
  simp only [CollatzResearch.WordTrace]
  refine ⟨123007842810751485456634373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82005228540500990304422915 123007842810751485456634373)
  ·
    refine ⟨23063970527015903523118945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123007842810751485456634373 23063970527015903523118945)
    ·
      refine ⟨17297977895261927642339209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23063970527015903523118945 17297977895261927642339209)
      ·
        refine ⟨12973483421446445731754407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17297977895261927642339209 12973483421446445731754407)
        ·
          refine ⟨19460225132169668597631611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12973483421446445731754407 19460225132169668597631611)
          ·
            refine ⟨29190337698254502896447417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19460225132169668597631611 29190337698254502896447417)
            ·
              refine ⟨21892753273690877172335563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29190337698254502896447417 21892753273690877172335563)
              ·
                refine ⟨32839129910536315758503345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21892753273690877172335563 32839129910536315758503345)
                ·
                  refine ⟨24629347432902236818877509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32839129910536315758503345 24629347432902236818877509)
                  ·
                    refine ⟨4618002643669169403539533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24629347432902236818877509 4618002643669169403539533)
                    ·
                      refine ⟨1731750991375938526327325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4618002643669169403539533 1731750991375938526327325)
                      ·
                        rfl

theorem cell23_3372573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_3372573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372573 prefixEnd_3372573 := by exact prefixLift 3372573
  have htrace : WordTrace (prefixWord ++ tailWord_3372573) baseStart_3372573 baseEnd_3372573 := by
    simpa [prefixWord, tailWord_3372573, baseEnd_3372573] using wordTrace_append hprefix tailTrace_3372573
  have hstable : (prefixWord ++ tailWord_3372573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372573).length < 2 ^ (prefixWord ++ tailWord_3372573).sum := by decide
  have hdescent : baseEnd_3372573 < baseStart_3372573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372621 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 2, 2, 2]
def baseStart_3372621 : Nat := 118140960795 + 3372621 * 2 ^ 59
def prefixEnd_3372621 : Nat := 4983230072969 + 3 ^ 40 * 3372621 * 2
def baseEnd_3372621 : Nat := 1731775638447354338527105

theorem tailTrace_3372621 : CollatzResearch.WordTrace tailWord_3372621 prefixEnd_3372621 1731775638447354338527105 := by
  unfold tailWord_3372621
  simp only [CollatzResearch.WordTrace]
  refine ⟨123009593514577589654381717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82006395676385059769587811 123009593514577589654381717)
  ·
    refine ⟨5766074695995824515049143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 123009593514577589654381717 5766074695995824515049143)
    ·
      refine ⟨8649112043993736772573715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5766074695995824515049143 8649112043993736772573715)
      ·
        refine ⟨12973668065990605158860573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8649112043993736772573715 12973668065990605158860573)
        ·
          refine ⟨4865125524746476934572715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12973668065990605158860573 4865125524746476934572715)
          ·
            refine ⟨7297688287119715401859073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865125524746476934572715 7297688287119715401859073)
            ·
              refine ⟨5473266215339786551394305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7297688287119715401859073 5473266215339786551394305)
              ·
                refine ⟨4104949661504839913545729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5473266215339786551394305 4104949661504839913545729)
                ·
                  refine ⟨3078712246128629935159297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4104949661504839913545729 3078712246128629935159297)
                  ·
                    refine ⟨2309034184596472451369473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3078712246128629935159297 2309034184596472451369473)
                    ·
                      refine ⟨1731775638447354338527105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2309034184596472451369473 1731775638447354338527105)
                      ·
                        rfl

theorem cell23_3372621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_3372621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372621 prefixEnd_3372621 := by exact prefixLift 3372621
  have htrace : WordTrace (prefixWord ++ tailWord_3372621) baseStart_3372621 baseEnd_3372621 := by
    simpa [prefixWord, tailWord_3372621, baseEnd_3372621] using wordTrace_append hprefix tailTrace_3372621
  have hstable : (prefixWord ++ tailWord_3372621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372621).length < 2 ^ (prefixWord ++ tailWord_3372621).sum := by decide
  have hdescent : baseEnd_3372621 < baseStart_3372621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372673 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3372673 : Nat := 118140960795 + 3372673 * 2 ^ 59
def prefixEnd_3372673 : Nat := 4983230072969 + 3 ^ 40 * 3372673 * 2
def baseEnd_3372673 : Nat := 1731802339441388135076865

theorem tailTrace_3372673 : CollatzResearch.WordTrace tailWord_3372673 prefixEnd_3372673 1731802339441388135076865 := by
  unfold tailWord_3372673
  simp only [CollatzResearch.WordTrace]
  refine ⟨123011490110389202535274673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82007660073592801690183115 123011490110389202535274673)
  ·
    refine ⟨92258617582791901901456005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123011490110389202535274673 92258617582791901901456005)
    ·
      refine ⟨17298490796773481606523001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92258617582791901901456005 17298490796773481606523001)
      ·
        refine ⟨12973868097580111204892251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17298490796773481606523001 12973868097580111204892251)
        ·
          refine ⟨19460802146370166807338377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12973868097580111204892251 19460802146370166807338377)
          ·
            refine ⟨14595601609777625105503783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19460802146370166807338377 14595601609777625105503783)
            ·
              refine ⟨21893402414666437658255675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14595601609777625105503783 21893402414666437658255675)
              ·
                refine ⟨32840103621999656487383513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21893402414666437658255675 32840103621999656487383513)
                ·
                  refine ⟨24630077716499742365537635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32840103621999656487383513 24630077716499742365537635)
                  ·
                    refine ⟨36945116574749613548306453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24630077716499742365537635 36945116574749613548306453)
                    ·
                      refine ⟨1731802339441388135076865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36945116574749613548306453 1731802339441388135076865)
                      ·
                        rfl

theorem cell23_3372673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3372673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372673 prefixEnd_3372673 := by exact prefixLift 3372673
  have htrace : WordTrace (prefixWord ++ tailWord_3372673) baseStart_3372673 baseEnd_3372673 := by
    simpa [prefixWord, tailWord_3372673, baseEnd_3372673] using wordTrace_append hprefix tailTrace_3372673
  have hstable : (prefixWord ++ tailWord_3372673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372673).length < 2 ^ (prefixWord ++ tailWord_3372673).sum := by decide
  have hdescent : baseEnd_3372673 < baseStart_3372673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372720 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 1, 5, 2]
def baseStart_3372720 : Nat := 118140960795 + 3372720 * 2 ^ 59
def prefixEnd_3372720 : Nat := 4983230072969 + 3 ^ 40 * 3372720 * 2
def baseEnd_3372720 : Nat := 1731826473032149451189149

theorem tailTrace_3372720 : CollatzResearch.WordTrace tailWord_3372720 prefixEnd_3372720 1731826473032149451189149 := by
  unfold tailWord_3372720
  simp only [CollatzResearch.WordTrace]
  refine ⟨61506602170609464781117807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82008802894145953041490409 61506602170609464781117807)
  ·
    refine ⟨92259903255914197171676711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61506602170609464781117807 92259903255914197171676711)
    ·
      refine ⟨138389854883871295757515067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92259903255914197171676711 138389854883871295757515067)
      ·
        refine ⟨207584782325806943636272601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138389854883871295757515067 207584782325806943636272601)
        ·
          refine ⟨155688586744355207727204451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207584782325806943636272601 155688586744355207727204451)
          ·
            refine ⟨233532880116532811590806677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155688586744355207727204451 233532880116532811590806677)
            ·
              refine ⟨10946853755462475543319063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 233532880116532811590806677 10946853755462475543319063)
              ·
                refine ⟨16420280633193713314978595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10946853755462475543319063 16420280633193713314978595)
                ·
                  refine ⟨24630420949790569972467893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16420280633193713314978595 24630420949790569972467893)
                  ·
                    refine ⟨2309101964042865934918865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24630420949790569972467893 2309101964042865934918865)
                    ·
                      refine ⟨1731826473032149451189149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2309101964042865934918865 1731826473032149451189149)
                      ·
                        rfl

theorem cell23_3372720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 5, 2].length) (baseStart_3372720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372720 prefixEnd_3372720 := by exact prefixLift 3372720
  have htrace : WordTrace (prefixWord ++ tailWord_3372720) baseStart_3372720 baseEnd_3372720 := by
    simpa [prefixWord, tailWord_3372720, baseEnd_3372720] using wordTrace_append hprefix tailTrace_3372720
  have hstable : (prefixWord ++ tailWord_3372720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372720).length < 2 ^ (prefixWord ++ tailWord_3372720).sum := by decide
  have hdescent : baseEnd_3372720 < baseStart_3372720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372730 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 1, 5]
def baseStart_3372730 : Nat := 118140960795 + 3372730 * 2 ^ 59
def prefixEnd_3372730 : Nat := 4983230072969 + 3 ^ 40 * 3372730 * 2
def baseEnd_3372730 : Nat := 577277202612898137354701

theorem tailTrace_3372730 : CollatzResearch.WordTrace tailWord_3372730 prefixEnd_3372730 577277202612898137354701 := by
  unfold tailWord_3372730
  simp only [CollatzResearch.WordTrace]
  refine ⟨30753392267795675317524911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82009046047455134180066429 30753392267795675317524911)
  ·
    refine ⟨46130088401693512976287367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30753392267795675317524911 46130088401693512976287367)
    ·
      refine ⟨69195132602540269464431051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46130088401693512976287367 69195132602540269464431051)
      ·
        refine ⟨103792698903810404196646577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69195132602540269464431051 103792698903810404196646577)
        ·
          refine ⟨77844524177857803147484933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103792698903810404196646577 77844524177857803147484933)
          ·
            refine ⟨14595848283348338090153425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77844524177857803147484933 14595848283348338090153425)
            ·
              refine ⟨10946886212511253567615069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14595848283348338090153425 10946886212511253567615069)
              ·
                refine ⟨4105082329691720087855651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10946886212511253567615069 4105082329691720087855651)
                ·
                  refine ⟨6157623494537580131783477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4105082329691720087855651 6157623494537580131783477)
                  ·
                    refine ⟨577277202612898137354701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6157623494537580131783477 577277202612898137354701)
                    ·
                      rfl

theorem cell23_3372730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_3372730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372730 prefixEnd_3372730 := by exact prefixLift 3372730
  have htrace : WordTrace (prefixWord ++ tailWord_3372730) baseStart_3372730 baseEnd_3372730 := by
    simpa [prefixWord, tailWord_3372730, baseEnd_3372730] using wordTrace_append hprefix tailTrace_3372730
  have hstable : (prefixWord ++ tailWord_3372730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372730).length < 2 ^ (prefixWord ++ tailWord_3372730).sum := by decide
  have hdescent : baseEnd_3372730 < baseStart_3372730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372738 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_3372738 : Nat := 118140960795 + 3372738 * 2 ^ 59
def prefixEnd_3372738 : Nat := 4983230072969 + 3 ^ 40 * 3372738 * 2
def baseEnd_3372738 : Nat := 577278571894643460254689

theorem tailTrace_3372738 : CollatzResearch.WordTrace tailWord_3372738 prefixEnd_3372738 577278571894643460254689 := by
  unfold tailWord_3372738
  simp only [CollatzResearch.WordTrace]
  refine ⟨30753465213788429659097717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82009240570102479090927245 30753465213788429659097717)
  ·
    refine ⟨2883137363792665280540411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30753465213788429659097717 2883137363792665280540411)
    ·
      refine ⟨4324706045688997920810617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2883137363792665280540411 4324706045688997920810617)
      ·
        refine ⟨3243529534266748440607963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4324706045688997920810617 3243529534266748440607963)
        ·
          refine ⟨4865294301400122660911945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243529534266748440607963 4865294301400122660911945)
          ·
            refine ⟨3648970726050091995683959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4865294301400122660911945 3648970726050091995683959)
            ·
              refine ⟨5473456089075137993525939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648970726050091995683959 5473456089075137993525939)
              ·
                refine ⟨8210184133612706990288909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5473456089075137993525939 8210184133612706990288909)
                ·
                  refine ⟨3078819050104765121358341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8210184133612706990288909 3078819050104765121358341)
                  ·
                    refine ⟨577278571894643460254689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3078819050104765121358341 577278571894643460254689)
                    ·
                      rfl

theorem cell23_3372738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_3372738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372738 prefixEnd_3372738 := by exact prefixLift 3372738
  have htrace : WordTrace (prefixWord ++ tailWord_3372738) baseStart_3372738 baseEnd_3372738 := by
    simpa [prefixWord, tailWord_3372738, baseEnd_3372738] using wordTrace_append hprefix tailTrace_3372738
  have hstable : (prefixWord ++ tailWord_3372738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372738).length < 2 ^ (prefixWord ++ tailWord_3372738).sum := by decide
  have hdescent : baseEnd_3372738 < baseStart_3372738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372750 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_3372750 : Nat := 118140960795 + 3372750 * 2 ^ 59
def prefixEnd_3372750 : Nat := 4983230072969 + 3 ^ 40 * 3372750 * 2
def baseEnd_3372750 : Nat := 1731841877451784333814011

theorem tailTrace_3372750 : CollatzResearch.WordTrace tailWord_3372750 prefixEnd_3372750 1731841877451784333814011 := by
  unfold tailWord_3372750
  simp only [CollatzResearch.WordTrace]
  refine ⟨15376787316388780585728463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82009532354073496457218469 15376787316388780585728463)
  ·
    refine ⟨23065180974583170878592695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15376787316388780585728463 23065180974583170878592695)
    ·
      refine ⟨34597771461874756317889043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23065180974583170878592695 34597771461874756317889043)
      ·
        refine ⟨51896657192812134476833565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34597771461874756317889043 51896657192812134476833565)
        ·
          refine ⟨19461246447304550428812587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51896657192812134476833565 19461246447304550428812587)
          ·
            refine ⟨29191869670956825643218881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19461246447304550428812587 29191869670956825643218881)
            ·
              refine ⟨21893902253217619232414161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29191869670956825643218881 21893902253217619232414161)
              ·
                refine ⟨16420426689913214424310621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21893902253217619232414161 16420426689913214424310621)
                ·
                  refine ⟨6157660008717455409116483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16420426689913214424310621 6157660008717455409116483)
                  ·
                    refine ⟨9236490013076183113674725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6157660008717455409116483 9236490013076183113674725)
                    ·
                      refine ⟨1731841877451784333814011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9236490013076183113674725 1731841877451784333814011)
                      ·
                        rfl

theorem cell23_3372750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_3372750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372750 prefixEnd_3372750 := by exact prefixLift 3372750
  have htrace : WordTrace (prefixWord ++ tailWord_3372750) baseStart_3372750 baseEnd_3372750 := by
    simpa [prefixWord, tailWord_3372750, baseEnd_3372750] using wordTrace_append hprefix tailTrace_3372750
  have hstable : (prefixWord ++ tailWord_3372750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372750).length < 2 ^ (prefixWord ++ tailWord_3372750).sum := by decide
  have hdescent : baseEnd_3372750 < baseStart_3372750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372767 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 5, 2, 2]
def baseStart_3372767 : Nat := 118140960795 + 3372767 * 2 ^ 59
def prefixEnd_3372767 : Nat := 4983230072969 + 3 ^ 40 * 3372767 * 2
def baseEnd_3372767 : Nat := 1731850606622910767301433

theorem tailTrace_3372767 : CollatzResearch.WordTrace tailWord_3372767 prefixEnd_3372767 1731850606622910767301433 := by
  unfold tailWord_3372767
  simp only [CollatzResearch.WordTrace]
  refine ⟨123014918572048656589196555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82009945714699104392797703 123014918572048656589196555)
  ·
    refine ⟨184522377858072984883794833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123014918572048656589196555 184522377858072984883794833)
    ·
      refine ⟨138391783393554738662846125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184522377858072984883794833 138391783393554738662846125)
      ·
        refine ⟨51896918772583026998567297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138391783393554738662846125 51896918772583026998567297)
        ·
          refine ⟨38922689079437270248925473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51896918772583026998567297 38922689079437270248925473)
          ·
            refine ⟨29192016809577952686694105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38922689079437270248925473 29192016809577952686694105)
            ·
              refine ⟨21894012607183464515020579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29192016809577952686694105 21894012607183464515020579)
              ·
                refine ⟨32841018910775196772530869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21894012607183464515020579 32841018910775196772530869)
                ·
                  refine ⟨3078845522885174697424769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32841018910775196772530869 3078845522885174697424769)
                  ·
                    refine ⟨2309134142163881023068577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3078845522885174697424769 2309134142163881023068577)
                    ·
                      refine ⟨1731850606622910767301433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2309134142163881023068577 1731850606622910767301433)
                      ·
                        rfl

theorem cell23_3372767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_3372767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372767 prefixEnd_3372767 := by exact prefixLift 3372767
  have htrace : WordTrace (prefixWord ++ tailWord_3372767) baseStart_3372767 baseEnd_3372767 := by
    simpa [prefixWord, tailWord_3372767, baseEnd_3372767] using wordTrace_append hprefix tailTrace_3372767
  have hstable : (prefixWord ++ tailWord_3372767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372767).length < 2 ^ (prefixWord ++ tailWord_3372767).sum := by decide
  have hdescent : baseEnd_3372767 < baseStart_3372767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372773 : List Nat := [1, 3, 1, 4, 1, 1, 1, 11]
def baseStart_3372773 : Nat := 118140960795 + 3372773 * 2 ^ 59
def prefixEnd_3372773 : Nat := 4983230072969 + 3 ^ 40 * 3372773 * 2
def baseEnd_3372773 : Nat := 64142729166919916438015

theorem tailTrace_3372773 : CollatzResearch.WordTrace tailWord_3372773 prefixEnd_3372773 64142729166919916438015 := by
  unfold tailWord_3372773
  simp only [CollatzResearch.WordTrace]
  refine ⟨123015137410026919613914973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82010091606684613075943315 123015137410026919613914973)
  ·
    refine ⟨46130676528760094855218115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123015137410026919613914973 46130676528760094855218115)
    ·
      refine ⟨69196014793140142282827173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46130676528760094855218115 69196014793140142282827173)
      ·
        refine ⟨12974252773713776678030095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69196014793140142282827173 12974252773713776678030095)
        ·
          refine ⟨19461379160570665017045143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12974252773713776678030095 19461379160570665017045143)
          ·
            refine ⟨29192068740855997525567715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19461379160570665017045143 29192068740855997525567715)
            ·
              refine ⟨43788103111283996288351573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29192068740855997525567715 43788103111283996288351573)
              ·
                refine ⟨64142729166919916438015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 43788103111283996288351573 64142729166919916438015)
                ·
                  rfl

theorem cell23_3372773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 11].length) (baseStart_3372773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372773 prefixEnd_3372773 := by exact prefixLift 3372773
  have htrace : WordTrace (prefixWord ++ tailWord_3372773) baseStart_3372773 baseEnd_3372773 := by
    simpa [prefixWord, tailWord_3372773, baseEnd_3372773] using wordTrace_append hprefix tailTrace_3372773
  have hstable : (prefixWord ++ tailWord_3372773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372773).length < 2 ^ (prefixWord ++ tailWord_3372773).sum := by decide
  have hdescent : baseEnd_3372773 < baseStart_3372773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372803 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 2, 7]
def baseStart_3372803 : Nat := 118140960795 + 3372803 * 2 ^ 59
def prefixEnd_3372803 : Nat := 4983230072969 + 3 ^ 40 * 3372803 * 2
def baseEnd_3372803 : Nat := 577289697308824208817089

theorem tailTrace_3372803 : CollatzResearch.WordTrace tailWord_3372803 prefixEnd_3372803 577289697308824208817089 := by
  unfold tailWord_3372803
  simp only [CollatzResearch.WordTrace]
  refine ⟨123016231599918234737507063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82010821066612156491671375 123016231599918234737507063)
  ·
    refine ⟨184524347399877352106260595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123016231599918234737507063 184524347399877352106260595)
    ·
      refine ⟨276786521099816028159390893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184524347399877352106260595 276786521099816028159390893)
      ·
        refine ⟨103794945412431010559771585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276786521099816028159390893 103794945412431010559771585)
        ·
          refine ⟨77846209059323257919828689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103794945412431010559771585 77846209059323257919828689)
          ·
            refine ⟨58384656794492443439871517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77846209059323257919828689 58384656794492443439871517)
            ·
              refine ⟨21894246297934666289951819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58384656794492443439871517 21894246297934666289951819)
              ·
                refine ⟨32841369446901999434927729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21894246297934666289951819 32841369446901999434927729)
                ·
                  refine ⟨24631027085176499576195797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32841369446901999434927729 24631027085176499576195797)
                  ·
                    refine ⟨577289697308824208817089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24631027085176499576195797 577289697308824208817089)
                    ·
                      rfl

theorem cell23_3372803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 7].length) (baseStart_3372803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372803 prefixEnd_3372803 := by exact prefixLift 3372803
  have htrace : WordTrace (prefixWord ++ tailWord_3372803) baseStart_3372803 baseEnd_3372803 := by
    simpa [prefixWord, tailWord_3372803, baseEnd_3372803] using wordTrace_append hprefix tailTrace_3372803
  have hstable : (prefixWord ++ tailWord_3372803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372803).length < 2 ^ (prefixWord ++ tailWord_3372803).sum := by decide
  have hdescent : baseEnd_3372803 < baseStart_3372803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372807 : List Nat := [1, 1, 4, 4, 2, 2, 1, 8]
def baseStart_3372807 : Nat := 118140960795 + 3372807 * 2 ^ 59
def prefixEnd_3372807 : Nat := 4983230072969 + 3 ^ 40 * 3372807 * 2
def baseEnd_3372807 : Nat := 64143375772188541140787

theorem tailTrace_3372807 : CollatzResearch.WordTrace tailWord_3372807 prefixEnd_3372807 64143375772188541140787 := by
  unfold tailWord_3372807
  simp only [CollatzResearch.WordTrace]
  refine ⟨123016377491903743420652675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82010918327935828947101783 123016377491903743420652675)
  ·
    refine ⟨184524566237855615130979013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123016377491903743420652675 184524566237855615130979013)
    ·
      refine ⟨34598356169597927837058565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184524566237855615130979013 34598356169597927837058565)
      ·
        refine ⟨6487191781799611469448481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34598356169597927837058565 6487191781799611469448481)
        ·
          refine ⟨4865393836349708602086361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6487191781799611469448481 4865393836349708602086361)
          ·
            refine ⟨3649045377262281451564771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4865393836349708602086361 3649045377262281451564771)
            ·
              refine ⟨5473568065893422177347157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649045377262281451564771 5473568065893422177347157)
              ·
                refine ⟨64143375772188541140787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5473568065893422177347157 64143375772188541140787)
                ·
                  rfl

theorem cell23_3372807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 8].length) (baseStart_3372807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372807 prefixEnd_3372807 := by exact prefixLift 3372807
  have htrace : WordTrace (prefixWord ++ tailWord_3372807) baseStart_3372807 baseEnd_3372807 := by
    simpa [prefixWord, tailWord_3372807, baseEnd_3372807] using wordTrace_append hprefix tailTrace_3372807
  have hstable : (prefixWord ++ tailWord_3372807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372807).length < 2 ^ (prefixWord ++ tailWord_3372807).sum := by decide
  have hdescent : baseEnd_3372807 < baseStart_3372807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372844 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 1, 3, 2]
def baseStart_3372844 : Nat := 118140960795 + 3372844 * 2 ^ 59
def prefixEnd_3372844 : Nat := 4983230072969 + 3 ^ 40 * 3372844 * 2
def baseEnd_3372844 : Nat := 1731890144633306966038579

theorem tailTrace_3372844 : CollatzResearch.WordTrace tailWord_3372844 prefixEnd_3372844 1731890144633306966038579 := by
  unfold tailWord_3372844
  simp only [CollatzResearch.WordTrace]
  refine ⟨61508863496384849369874793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82011817995179799159833057 61508863496384849369874793)
  ·
    refine ⟨46131647622288637027406095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61508863496384849369874793 46131647622288637027406095)
    ·
      refine ⟨69197471433432955541109143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46131647622288637027406095 69197471433432955541109143)
      ·
        refine ⟨103796207150149433311663715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69197471433432955541109143 103796207150149433311663715)
        ·
          refine ⟨155694310725224149967495573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103796207150149433311663715 155694310725224149967495573)
          ·
            refine ⟨7298170815244882029726355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155694310725224149967495573 7298170815244882029726355)
            ·
              refine ⟨10947256222867323044589533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7298170815244882029726355 10947256222867323044589533)
              ·
                refine ⟨4105221083575246141721075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10947256222867323044589533 4105221083575246141721075)
                ·
                  refine ⟨6157831625362869212581613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4105221083575246141721075 6157831625362869212581613)
                  ·
                    refine ⟨2309186859511075954718105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6157831625362869212581613 2309186859511075954718105)
                    ·
                      refine ⟨1731890144633306966038579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2309186859511075954718105 1731890144633306966038579)
                      ·
                        rfl

theorem cell23_3372844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 3, 2].length) (baseStart_3372844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372844 prefixEnd_3372844 := by exact prefixLift 3372844
  have htrace : WordTrace (prefixWord ++ tailWord_3372844) baseStart_3372844 baseEnd_3372844 := by
    simpa [prefixWord, tailWord_3372844, baseEnd_3372844] using wordTrace_append hprefix tailTrace_3372844
  have hstable : (prefixWord ++ tailWord_3372844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372844).length < 2 ^ (prefixWord ++ tailWord_3372844).sum := by decide
  have hdescent : baseEnd_3372844 < baseStart_3372844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372850 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 2, 6]
def baseStart_3372850 : Nat := 118140960795 + 3372850 * 2 ^ 59
def prefixEnd_3372850 : Nat := 4983230072969 + 3 ^ 40 * 3372850 * 2
def baseEnd_3372850 : Nat := 577297741839077980854517

theorem tailTrace_3372850 : CollatzResearch.WordTrace tailWord_3372850 prefixEnd_3372850 577297741839077980854517 := by
  unfold tailWord_3372850
  simp only [CollatzResearch.WordTrace]
  refine ⟨30754486457686990441117001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82011963887165307842978669 30754486457686990441117001)
  ·
    refine ⟨23065864843265242830837751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30754486457686990441117001 23065864843265242830837751)
    ·
      refine ⟨34598797264897864246256627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23065864843265242830837751 34598797264897864246256627)
      ·
        refine ⟨51898195897346796369384941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34598797264897864246256627 51898195897346796369384941)
        ·
          refine ⟨19461823461505048638519353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51898195897346796369384941 19461823461505048638519353)
          ·
            refine ⟨14596367596128786478889515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19461823461505048638519353 14596367596128786478889515)
            ·
              refine ⟨21894551394193179718334273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14596367596128786478889515 21894551394193179718334273)
              ·
                refine ⟨16420913545644884788750705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21894551394193179718334273 16420913545644884788750705)
                ·
                  refine ⟨12315685159233663591563029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16420913545644884788750705 12315685159233663591563029)
                  ·
                    refine ⟨577297741839077980854517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12315685159233663591563029 577297741839077980854517)
                    ·
                      rfl

theorem cell23_3372850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_3372850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372850 prefixEnd_3372850 := by exact prefixLift 3372850
  have htrace : WordTrace (prefixWord ++ tailWord_3372850) baseStart_3372850 baseEnd_3372850 := by
    simpa [prefixWord, tailWord_3372850, baseEnd_3372850] using wordTrace_append hprefix tailTrace_3372850
  have hstable : (prefixWord ++ tailWord_3372850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372850).length < 2 ^ (prefixWord ++ tailWord_3372850).sum := by decide
  have hdescent : baseEnd_3372850 < baseStart_3372850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372851 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 2, 1, 3]
def baseStart_3372851 : Nat := 118140960795 + 3372851 * 2 ^ 59
def prefixEnd_3372851 : Nat := 4983230072969 + 3 ^ 40 * 3372851 * 2
def baseEnd_3372851 : Nat := 1731893738997888438651047

theorem tailTrace_3372851 : CollatzResearch.WordTrace tailWord_3372851 prefixEnd_3372851 1731893738997888438651047 := by
  unfold tailWord_3372851
  simp only [CollatzResearch.WordTrace]
  refine ⟨123017982303744338935254407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82011988202496225956836271 123017982303744338935254407)
  ·
    refine ⟨184526973455616508402881611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123017982303744338935254407 184526973455616508402881611)
    ·
      refine ⟨276790460183424762604322417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184526973455616508402881611 276790460183424762604322417)
      ·
        refine ⟨207592845137568571953241813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276790460183424762604322417 207592845137568571953241813)
        ·
          refine ⟨4865457307911763405154105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 207592845137568571953241813 4865457307911763405154105)
          ·
            refine ⟨3649092980933822553865579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4865457307911763405154105 3649092980933822553865579)
            ·
              refine ⟨5473639471400733830798369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649092980933822553865579 5473639471400733830798369)
              ·
                refine ⟨4105229603550550373098777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5473639471400733830798369 4105229603550550373098777)
                ·
                  refine ⟨3078922202662912779824083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4105229603550550373098777 3078922202662912779824083)
                  ·
                    refine ⟨4618383303994369169736125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3078922202662912779824083 4618383303994369169736125)
                    ·
                      refine ⟨1731893738997888438651047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4618383303994369169736125 1731893738997888438651047)
                      ·
                        rfl

theorem cell23_3372851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 1, 3].length) (baseStart_3372851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372851 prefixEnd_3372851 := by exact prefixLift 3372851
  have htrace : WordTrace (prefixWord ++ tailWord_3372851) baseStart_3372851 baseEnd_3372851 := by
    simpa [prefixWord, tailWord_3372851, baseEnd_3372851] using wordTrace_append hprefix tailTrace_3372851
  have hstable : (prefixWord ++ tailWord_3372851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372851).length < 2 ^ (prefixWord ++ tailWord_3372851).sum := by decide
  have hdescent : baseEnd_3372851 < baseStart_3372851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372860 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_3372860 : Nat := 118140960795 + 3372860 * 2 ^ 59
def prefixEnd_3372860 : Nat := 4983230072969 + 3 ^ 40 * 3372860 * 2
def baseEnd_3372860 : Nat := 1731898360323778903438505

theorem tailTrace_3372860 : CollatzResearch.WordTrace tailWord_3372860 prefixEnd_3372860 1731898360323778903438505 := by
  unfold tailWord_3372860
  simp only [CollatzResearch.WordTrace]
  refine ⟨61509155280355866736166017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82012207040474488981554689 61509155280355866736166017)
  ·
    refine ⟨46131866460266900052124513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61509155280355866736166017 46131866460266900052124513)
    ·
      refine ⟨34598899845200175039093385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46131866460266900052124513 34598899845200175039093385)
      ·
        refine ⟨25949174883900131279320039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34598899845200175039093385 25949174883900131279320039)
        ·
          refine ⟨38923762325850196918980059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25949174883900131279320039 38923762325850196918980059)
          ·
            refine ⟨58385643488775295378470089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38923762325850196918980059 58385643488775295378470089)
            ·
              refine ⟨43789232616581471533852567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58385643488775295378470089 43789232616581471533852567)
              ·
                refine ⟨65683848924872207300778851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43789232616581471533852567 65683848924872207300778851)
                ·
                  refine ⟨98525773387308310951168277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65683848924872207300778851 98525773387308310951168277)
                  ·
                    refine ⟨4618395627530077075836013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98525773387308310951168277 4618395627530077075836013)
                    ·
                      refine ⟨1731898360323778903438505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4618395627530077075836013 1731898360323778903438505)
                      ·
                        rfl

theorem cell23_3372860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_3372860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372860 prefixEnd_3372860 := by exact prefixLift 3372860
  have htrace : WordTrace (prefixWord ++ tailWord_3372860) baseStart_3372860 baseEnd_3372860 := by
    simpa [prefixWord, tailWord_3372860, baseEnd_3372860] using wordTrace_append hprefix tailTrace_3372860
  have hstable : (prefixWord ++ tailWord_3372860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372860).length < 2 ^ (prefixWord ++ tailWord_3372860).sum := by decide
  have hdescent : baseEnd_3372860 < baseStart_3372860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3372960 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_3372960 : Nat := 118140960795 + 3372960 * 2 ^ 59
def prefixEnd_3372960 : Nat := 4983230072969 + 3 ^ 40 * 3372960 * 2
def baseEnd_3372960 : Nat := 1731949708389228512188045

theorem tailTrace_3372960 : CollatzResearch.WordTrace tailWord_3372960 prefixEnd_3372960 1731949708389228512188045 := by
  unfold tailWord_3372960
  simp only [CollatzResearch.WordTrace]
  refine ⟨61510978930174725275486167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82014638573566300367314889 61510978930174725275486167)
  ·
    refine ⟨92266468395262087913229251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61510978930174725275486167 92266468395262087913229251)
    ·
      refine ⟨138399702592893131869843877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92266468395262087913229251 138399702592893131869843877)
      ·
        refine ⟨25949944236167462225595727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138399702592893131869843877 25949944236167462225595727)
        ·
          refine ⟨38924916354251193338393591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25949944236167462225595727 38924916354251193338393591)
          ·
            refine ⟨58387374531376790007590387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38924916354251193338393591 58387374531376790007590387)
            ·
              refine ⟨87581061797065185011385581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58387374531376790007590387 87581061797065185011385581)
              ·
                refine ⟨32842898173899444379269593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87581061797065185011385581 32842898173899444379269593)
                ·
                  refine ⟨24632173630424583284452195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32842898173899444379269593 24632173630424583284452195)
                  ·
                    refine ⟨36948260445636874926678293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24632173630424583284452195 36948260445636874926678293)
                    ·
                      refine ⟨1731949708389228512188045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36948260445636874926678293 1731949708389228512188045)
                      ·
                        rfl

theorem cell23_3372960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_3372960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3372960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3372960 prefixEnd_3372960 := by exact prefixLift 3372960
  have htrace : WordTrace (prefixWord ++ tailWord_3372960) baseStart_3372960 baseEnd_3372960 := by
    simpa [prefixWord, tailWord_3372960, baseEnd_3372960] using wordTrace_append hprefix tailTrace_3372960
  have hstable : (prefixWord ++ tailWord_3372960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3372960).length < 2 ^ (prefixWord ++ tailWord_3372960).sum := by decide
  have hdescent : baseEnd_3372960 < baseStart_3372960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3372960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373021 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 6]
def baseStart_3373021 : Nat := 118140960795 + 3373021 * 2 ^ 59
def prefixEnd_3373021 : Nat := 4983230072969 + 3 ^ 40 * 3373021 * 2
def baseEnd_3373021 : Nat := 192442336745461419280585

theorem tailTrace_3373021 : CollatzResearch.WordTrace tailWord_3373021 prefixEnd_3373021 192442336745461419280585 := by
  unfold tailWord_3373021
  simp only [CollatzResearch.WordTrace]
  refine ⟨123024182713128457968942917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82016121808752305312628611 123024182713128457968942917)
  ·
    refine ⟨23067034258711585869176797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123024182713128457968942917 23067034258711585869176797)
    ·
      refine ⟨8650137847016844700941299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23067034258711585869176797 8650137847016844700941299)
      ·
        refine ⟨12975206770525267051411949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8650137847016844700941299 12975206770525267051411949)
        ·
          refine ⟨4865702538946975144279481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12975206770525267051411949 4865702538946975144279481)
          ·
            refine ⟨3649276904210231358209611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4865702538946975144279481 3649276904210231358209611)
            ·
              refine ⟨5473915356315347037314417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649276904210231358209611 5473915356315347037314417)
              ·
                refine ⟨4105436517236510277985813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5473915356315347037314417 4105436517236510277985813)
                ·
                  refine ⟨192442336745461419280585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4105436517236510277985813 192442336745461419280585)
                  ·
                    rfl

theorem cell23_3373021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_3373021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373021 prefixEnd_3373021 := by exact prefixLift 3373021
  have htrace : WordTrace (prefixWord ++ tailWord_3373021) baseStart_3373021 baseEnd_3373021 := by
    simpa [prefixWord, tailWord_3373021, baseEnd_3373021] using wordTrace_append hprefix tailTrace_3373021
  have hstable : (prefixWord ++ tailWord_3373021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373021).length < 2 ^ (prefixWord ++ tailWord_3373021).sum := by decide
  have hdescent : baseEnd_3373021 < baseStart_3373021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373024 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 2, 3, 2]
def baseStart_3373024 : Nat := 118140960795 + 3373024 * 2 ^ 59
def prefixEnd_3373024 : Nat := 4983230072969 + 3 ^ 40 * 3373024 * 2
def baseEnd_3373024 : Nat := 1731982571151116261787751

theorem tailTrace_3373024 : CollatzResearch.WordTrace tailWord_3373024 prefixEnd_3373024 1731982571151116261787751 := by
  unfold tailWord_3373024
  simp only [CollatzResearch.WordTrace]
  refine ⟨61512146066058794740651063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82016194754745059654201417 61512146066058794740651063)
  ·
    refine ⟨92268219099088192110976595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61512146066058794740651063 92268219099088192110976595)
    ·
      refine ⟨138402328648632288166464893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92268219099088192110976595 138402328648632288166464893)
      ·
        refine ⟨51900873243237108062424335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138402328648632288166464893 51900873243237108062424335)
        ·
          refine ⟨77851309864855662093636503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51900873243237108062424335 77851309864855662093636503)
          ·
            refine ⟨116776964797283493140454755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77851309864855662093636503 116776964797283493140454755)
            ·
              refine ⟨175165447195925239710682133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116776964797283493140454755 175165447195925239710682133)
              ·
                refine ⟨8210880337308995611438225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 175165447195925239710682133 8210880337308995611438225)
                ·
                  refine ⟨6158160252981746708578669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8210880337308995611438225 6158160252981746708578669)
                  ·
                    refine ⟨2309310094868155015717001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6158160252981746708578669 2309310094868155015717001)
                    ·
                      refine ⟨1731982571151116261787751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2309310094868155015717001 1731982571151116261787751)
                      ·
                        rfl

theorem cell23_3373024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_3373024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373024 prefixEnd_3373024 := by exact prefixLift 3373024
  have htrace : WordTrace (prefixWord ++ tailWord_3373024) baseStart_3373024 baseEnd_3373024 := by
    simpa [prefixWord, tailWord_3373024, baseEnd_3373024] using wordTrace_append hprefix tailTrace_3373024
  have hstable : (prefixWord ++ tailWord_3373024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373024).length < 2 ^ (prefixWord ++ tailWord_3373024).sum := by decide
  have hdescent : baseEnd_3373024 < baseStart_3373024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373057 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_3373057 : Nat := 118140960795 + 3373057 * 2 ^ 59
def prefixEnd_3373057 : Nat := 4983230072969 + 3 ^ 40 * 3373057 * 2
def baseEnd_3373057 : Nat := 1731999516012714632675099

theorem tailTrace_3373057 : CollatzResearch.WordTrace tailWord_3373057 prefixEnd_3373057 1731999516012714632675099 := by
  unfold tailWord_3373057
  simp only [CollatzResearch.WordTrace]
  refine ⟨123025495740998036117253425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82016997160665357411502283 123025495740998036117253425)
  ·
    refine ⟨92269121805748527087940069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123025495740998036117253425 92269121805748527087940069)
    ·
      refine ⟨17300460338577848828988763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92269121805748527087940069 17300460338577848828988763)
      ·
        refine ⟨25950690507866773243483145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17300460338577848828988763 25950690507866773243483145)
        ·
          refine ⟨19463017880900079932612359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25950690507866773243483145 19463017880900079932612359)
          ·
            refine ⟨29194526821350119898918539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19463017880900079932612359 29194526821350119898918539)
            ·
              refine ⟨43791790232025179848377809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29194526821350119898918539 43791790232025179848377809)
              ·
                refine ⟨32843842674018884886283357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43791790232025179848377809 32843842674018884886283357)
                ·
                  refine ⟨12316441002757081832356259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32843842674018884886283357 12316441002757081832356259)
                  ·
                    refine ⟨18474661504135622748534389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12316441002757081832356259 18474661504135622748534389)
                    ·
                      refine ⟨1731999516012714632675099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18474661504135622748534389 1731999516012714632675099)
                      ·
                        rfl

theorem cell23_3373057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_3373057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373057 prefixEnd_3373057 := by exact prefixLift 3373057
  have htrace : WordTrace (prefixWord ++ tailWord_3373057) baseStart_3373057 baseEnd_3373057 := by
    simpa [prefixWord, tailWord_3373057, baseEnd_3373057] using wordTrace_append hprefix tailTrace_3373057
  have hstable : (prefixWord ++ tailWord_3373057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373057).length < 2 ^ (prefixWord ++ tailWord_3373057).sum := by decide
  have hdescent : baseEnd_3373057 < baseStart_3373057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373067 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 4]
def baseStart_3373067 : Nat := 118140960795 + 3373067 * 2 ^ 59
def prefixEnd_3373067 : Nat := 4983230072969 + 3 ^ 40 * 3373067 * 2
def baseEnd_3373067 : Nat := 1732004650819259593550053

theorem tailTrace_3373067 : CollatzResearch.WordTrace tailWord_3373067 prefixEnd_3373067 1732004650819259593550053 := by
  unfold tailWord_3373067
  simp only [CollatzResearch.WordTrace]
  refine ⟨123025860470961807825117455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82017240313974538550078303 123025860470961807825117455)
  ·
    refine ⟨184538790706442711737676183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123025860470961807825117455 184538790706442711737676183)
    ·
      refine ⟨276808186059664067606514275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184538790706442711737676183 276808186059664067606514275)
      ·
        refine ⟨415212279089496101409771413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276808186059664067606514275 415212279089496101409771413)
        ·
          refine ⟨19463075582320129753583035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 415212279089496101409771413 19463075582320129753583035)
          ·
            refine ⟨29194613373480194630374553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19463075582320129753583035 29194613373480194630374553)
            ·
              refine ⟨21895960030110145972780915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29194613373480194630374553 21895960030110145972780915)
              ·
                refine ⟨32843940045165218959171373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21895960030110145972780915 32843940045165218959171373)
                ·
                  refine ⟨12316477516936957109689265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32843940045165218959171373 12316477516936957109689265)
                  ·
                    refine ⟨9237358137702717832266949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12316477516936957109689265 9237358137702717832266949)
                    ·
                      refine ⟨1732004650819259593550053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9237358137702717832266949 1732004650819259593550053)
                      ·
                        rfl

theorem cell23_3373067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 4].length) (baseStart_3373067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373067 prefixEnd_3373067 := by exact prefixLift 3373067
  have htrace : WordTrace (prefixWord ++ tailWord_3373067) baseStart_3373067 baseEnd_3373067 := by
    simpa [prefixWord, tailWord_3373067, baseEnd_3373067] using wordTrace_append hprefix tailTrace_3373067
  have hstable : (prefixWord ++ tailWord_3373067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373067).length < 2 ^ (prefixWord ++ tailWord_3373067).sum := by decide
  have hdescent : baseEnd_3373067 < baseStart_3373067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373098 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 2, 4]
def baseStart_3373098 : Nat := 118140960795 + 3373098 * 2 ^ 59
def prefixEnd_3373098 : Nat := 4983230072969 + 3 ^ 40 * 3373098 * 2
def baseEnd_3373098 : Nat := 577340189573182990754137

theorem tailTrace_3373098 : CollatzResearch.WordTrace tailWord_3373098 prefixEnd_3373098 577340189573182990754137 := by
  unfold tailWord_3373098
  simp only [CollatzResearch.WordTrace]
  refine ⟨30756747783462375029873987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82017994089233000079663965 30756747783462375029873987)
  ·
    refine ⟨46135121675193562544810981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30756747783462375029873987 46135121675193562544810981)
    ·
      refine ⟨8650335314098792977152059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46135121675193562544810981 8650335314098792977152059)
      ·
        refine ⟨12975502971148189465728089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8650335314098792977152059 12975502971148189465728089)
        ·
          refine ⟨9731627228361142099296067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12975502971148189465728089 9731627228361142099296067)
          ·
            refine ⟨14597440842541713148944101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9731627228361142099296067 14597440842541713148944101)
            ·
              refine ⟨2737020157976571215427019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14597440842541713148944101 2737020157976571215427019)
              ·
                refine ⟨4105530236964856823140529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737020157976571215427019 4105530236964856823140529)
                ·
                  refine ⟨3079147677723642617355397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4105530236964856823140529 3079147677723642617355397)
                  ·
                    refine ⟨577340189573182990754137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3079147677723642617355397 577340189573182990754137)
                    ·
                      rfl

theorem cell23_3373098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_3373098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373098 prefixEnd_3373098 := by exact prefixLift 3373098
  have htrace : WordTrace (prefixWord ++ tailWord_3373098) baseStart_3373098 baseEnd_3373098 := by
    simpa [prefixWord, tailWord_3373098, baseEnd_3373098] using wordTrace_append hprefix tailTrace_3373098
  have hstable : (prefixWord ++ tailWord_3373098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373098).length < 2 ^ (prefixWord ++ tailWord_3373098).sum := by decide
  have hdescent : baseEnd_3373098 < baseStart_3373098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373108 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3373108 : Nat := 118140960795 + 3373108 * 2 ^ 59
def prefixEnd_3373108 : Nat := 4983230072969 + 3 ^ 40 * 3373108 * 2
def baseEnd_3373108 : Nat := 1732025703526093933137365

theorem tailTrace_3373108 : CollatzResearch.WordTrace tailWord_3373108 prefixEnd_3373108 1732025703526093933137365 := by
  unfold tailWord_3373108
  simp only [CollatzResearch.WordTrace]
  refine ⟨61513677931906635913679989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82018237242542181218239985 61513677931906635913679989)
  ·
    refine ⟨5766907306116247116907499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61513677931906635913679989 5766907306116247116907499)
    ·
      refine ⟨8650360959174370675361249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5766907306116247116907499 8650360959174370675361249)
      ·
        refine ⟨6487770719380778006520937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8650360959174370675361249 6487770719380778006520937)
        ·
          refine ⟨4865828039535583504890703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6487770719380778006520937 4865828039535583504890703)
          ·
            refine ⟨7298742059303375257336055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865828039535583504890703 7298742059303375257336055)
            ·
              refine ⟨10948113088955062886004083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7298742059303375257336055 10948113088955062886004083)
              ·
                refine ⟨16422169633432594329006125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10948113088955062886004083 16422169633432594329006125)
                ·
                  refine ⟨6158313612537222873377297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16422169633432594329006125 6158313612537222873377297)
                  ·
                    refine ⟨4618735209402917155032973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6158313612537222873377297 4618735209402917155032973)
                    ·
                      refine ⟨1732025703526093933137365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4618735209402917155032973 1732025703526093933137365)
                      ·
                        rfl

theorem cell23_3373108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3373108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373108 prefixEnd_3373108 := by exact prefixLift 3373108
  have htrace : WordTrace (prefixWord ++ tailWord_3373108) baseStart_3373108 baseEnd_3373108 := by
    simpa [prefixWord, tailWord_3373108, baseEnd_3373108] using wordTrace_append hprefix tailTrace_3373108
  have hstable : (prefixWord ++ tailWord_3373108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373108).length < 2 ^ (prefixWord ++ tailWord_3373108).sum := by decide
  have hdescent : baseEnd_3373108 < baseStart_3373108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373121 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3373121 : Nat := 118140960795 + 3373121 * 2 ^ 59
def prefixEnd_3373121 : Nat := 4983230072969 + 3 ^ 40 * 3373121 * 2
def baseEnd_3373121 : Nat := 1732032378774602382274805

theorem tailTrace_3373121 : CollatzResearch.WordTrace tailWord_3373121 prefixEnd_3373121 1732032378774602382274805 := by
  unfold tailWord_3373121
  simp only [CollatzResearch.WordTrace]
  refine ⟨123027830012766175047583217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82018553341844116698388811 123027830012766175047583217)
  ·
    refine ⟨92270872509574631285687413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123027830012766175047583217 92270872509574631285687413)
    ·
      refine ⟨8650394297772621683033195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92270872509574631285687413 8650394297772621683033195)
      ·
        refine ⟨12975591446658932524549793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8650394297772621683033195 12975591446658932524549793)
        ·
          refine ⟨9731693584994199393412345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12975591446658932524549793 9731693584994199393412345)
          ·
            refine ⟨7298770188745649545059259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9731693584994199393412345 7298770188745649545059259)
            ·
              refine ⟨10948155283118474317588889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7298770188745649545059259 10948155283118474317588889)
              ·
                refine ⟨8211116462338855738191667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10948155283118474317588889 8211116462338855738191667)
                ·
                  refine ⟨12316674693508283607287501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8211116462338855738191667 12316674693508283607287501)
                  ·
                    refine ⟨4618753010065606352732813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12316674693508283607287501 4618753010065606352732813)
                    ·
                      refine ⟨1732032378774602382274805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4618753010065606352732813 1732032378774602382274805)
                      ·
                        rfl

theorem cell23_3373121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3373121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373121 prefixEnd_3373121 := by exact prefixLift 3373121
  have htrace : WordTrace (prefixWord ++ tailWord_3373121) baseStart_3373121 baseEnd_3373121 := by
    simpa [prefixWord, tailWord_3373121, baseEnd_3373121] using wordTrace_append hprefix tailTrace_3373121
  have hstable : (prefixWord ++ tailWord_3373121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373121).length < 2 ^ (prefixWord ++ tailWord_3373121).sum := by decide
  have hdescent : baseEnd_3373121 < baseStart_3373121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373137 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 2, 6]
def baseStart_3373137 : Nat := 118140960795 + 3373137 * 2 ^ 59
def prefixEnd_3373137 : Nat := 4983230072969 + 3 ^ 40 * 3373137 * 2
def baseEnd_3373137 : Nat := 577346864821691439891577

theorem tailTrace_3373137 : CollatzResearch.WordTrace tailWord_3373137 prefixEnd_3373137 577346864821691439891577 := by
  unfold tailWord_3373137
  simp only [CollatzResearch.WordTrace]
  refine ⟨123028413580708209780165665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82018942387138806520110443 123028413580708209780165665)
  ·
    refine ⟨92271310185531157335124249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123028413580708209780165665 92271310185531157335124249)
    ·
      refine ⟨69203482639148368001343187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92271310185531157335124249 69203482639148368001343187)
      ·
        refine ⟨103805223958722552002014781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69203482639148368001343187 103805223958722552002014781)
        ·
          refine ⟨38926958984520957000755543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103805223958722552002014781 38926958984520957000755543)
          ·
            refine ⟨58390438476781435501133315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38926958984520957000755543 58390438476781435501133315)
            ·
              refine ⟨87585657715172153251699973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58390438476781435501133315 87585657715172153251699973)
              ·
                refine ⟨16422310821594778734693745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87585657715172153251699973 16422310821594778734693745)
                ·
                  refine ⟨12316733116196084051020309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16422310821594778734693745 12316733116196084051020309)
                  ·
                    refine ⟨577346864821691439891577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12316733116196084051020309 577346864821691439891577)
                    ·
                      rfl

theorem cell23_3373137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_3373137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373137 prefixEnd_3373137 := by exact prefixLift 3373137
  have htrace : WordTrace (prefixWord ++ tailWord_3373137) baseStart_3373137 baseEnd_3373137 := by
    simpa [prefixWord, tailWord_3373137, baseEnd_3373137] using wordTrace_append hprefix tailTrace_3373137
  have hstable : (prefixWord ++ tailWord_3373137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373137).length < 2 ^ (prefixWord ++ tailWord_3373137).sum := by decide
  have hdescent : baseEnd_3373137 < baseStart_3373137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373161 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 1, 4, 2]
def baseStart_3373161 : Nat := 118140960795 + 3373161 * 2 ^ 59
def prefixEnd_3373161 : Nat := 4983230072969 + 3 ^ 40 * 3373161 * 2
def baseEnd_3373161 : Nat := 1732052918000782225774621

theorem tailTrace_3373161 : CollatzResearch.WordTrace tailWord_3373161 prefixEnd_3373161 1732052918000782225774621 := by
  unfold tailWord_3373161
  simp only [CollatzResearch.WordTrace]
  refine ⟨123029288932621261879039337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82019525955080841252692891 123029288932621261879039337)
  ·
    refine ⟨92271966699465946409279503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123029288932621261879039337 92271966699465946409279503)
    ·
      refine ⟨138407950049198919613919255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92271966699465946409279503 138407950049198919613919255)
      ·
        refine ⟨207611925073798379420878883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138407950049198919613919255 207611925073798379420878883)
        ·
          refine ⟨311417887610697569131318325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207611925073798379420878883 311417887610697569131318325)
          ·
            refine ⟨29195426963502897106061093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 311417887610697569131318325 29195426963502897106061093)
            ·
              refine ⟨5474142555656793207386455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29195426963502897106061093 5474142555656793207386455)
              ·
                refine ⟨8211213833485189811079683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474142555656793207386455 8211213833485189811079683)
                ·
                  refine ⟨12316820750227784716619525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8211213833485189811079683 12316820750227784716619525)
                  ·
                    refine ⟨2309403890667709634366161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12316820750227784716619525 2309403890667709634366161)
                    ·
                      refine ⟨1732052918000782225774621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2309403890667709634366161 1732052918000782225774621)
                      ·
                        rfl

theorem cell23_3373161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 4, 2].length) (baseStart_3373161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373161 prefixEnd_3373161 := by exact prefixLift 3373161
  have htrace : WordTrace (prefixWord ++ tailWord_3373161) baseStart_3373161 baseEnd_3373161 := by
    simpa [prefixWord, tailWord_3373161, baseEnd_3373161] using wordTrace_append hprefix tailTrace_3373161
  have hstable : (prefixWord ++ tailWord_3373161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373161).length < 2 ^ (prefixWord ++ tailWord_3373161).sum := by decide
  have hdescent : baseEnd_3373161 < baseStart_3373161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373167 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 9]
def baseStart_3373167 : Nat := 118140960795 + 3373167 * 2 ^ 59
def prefixEnd_3373167 : Nat := 4983230072969 + 3 ^ 40 * 3373167 * 2
def baseEnd_3373167 : Nat := 192450666542745466922177

theorem tailTrace_3373167 : CollatzResearch.WordTrace tailWord_3373167 prefixEnd_3373167 192450666542745466922177 := by
  unfold tailWord_3373167
  simp only [CollatzResearch.WordTrace]
  refine ⟨123029507770599524903757755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82019671847066349935838503 123029507770599524903757755)
  ·
    refine ⟨184544261655899287355636633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123029507770599524903757755 184544261655899287355636633)
    ·
      refine ⟨138408196241924465516727475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184544261655899287355636633 138408196241924465516727475)
      ·
        refine ⟨207612294362886698275091213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138408196241924465516727475 207612294362886698275091213)
        ·
          refine ⟨77854610386082511853159205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207612294362886698275091213 77854610386082511853159205)
          ·
            refine ⟨14597739447390470972467351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77854610386082511853159205 14597739447390470972467351)
            ·
              refine ⟨21896609171085706458701027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14597739447390470972467351 21896609171085706458701027)
              ·
                refine ⟨32844913756628559688051541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21896609171085706458701027 32844913756628559688051541)
                ·
                  refine ⟨192450666542745466922177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32844913756628559688051541 192450666542745466922177)
                  ·
                    rfl

theorem cell23_3373167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 9].length) (baseStart_3373167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373167 prefixEnd_3373167 := by exact prefixLift 3373167
  have htrace : WordTrace (prefixWord ++ tailWord_3373167) baseStart_3373167 baseEnd_3373167 := by
    simpa [prefixWord, tailWord_3373167, baseEnd_3373167] using wordTrace_append hprefix tailTrace_3373167
  have hstable : (prefixWord ++ tailWord_3373167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373167).length < 2 ^ (prefixWord ++ tailWord_3373167).sum := by decide
  have hdescent : baseEnd_3373167 < baseStart_3373167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373206 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_3373206 : Nat := 118140960795 + 3373206 * 2 ^ 59
def prefixEnd_3373206 : Nat := 4983230072969 + 3 ^ 40 * 3373206 * 2
def baseEnd_3373206 : Nat := 1732076024630234549711915

theorem tailTrace_3373206 : CollatzResearch.WordTrace tailWord_3373206 prefixEnd_3373206 1732076024630234549711915 := by
  unfold tailWord_3373206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7689433138591139660276717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82020620144972156376284981 7689433138591139660276717)
  ·
    refine ⟨2883537426971677372603769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7689433138591139660276717 2883537426971677372603769)
    ·
      refine ⟨2162653070228758029452827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2883537426971677372603769 2162653070228758029452827)
      ·
        refine ⟨3243979605343137044179241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162653070228758029452827 3243979605343137044179241)
        ·
          refine ⟨2432984704007352783134431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3243979605343137044179241 2432984704007352783134431)
          ·
            refine ⟨3649477056011029174701647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432984704007352783134431 3649477056011029174701647)
            ·
              refine ⟨5474215584016543762052471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649477056011029174701647 5474215584016543762052471)
              ·
                refine ⟨8211323376024815643078707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474215584016543762052471 8211323376024815643078707)
                ·
                  refine ⟨12316985064037223464618061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8211323376024815643078707 12316985064037223464618061)
                  ·
                    refine ⟨4618869399013958799231773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12316985064037223464618061 4618869399013958799231773)
                    ·
                      refine ⟨1732076024630234549711915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4618869399013958799231773 1732076024630234549711915)
                      ·
                        rfl

theorem cell23_3373206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_3373206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373206 prefixEnd_3373206 := by exact prefixLift 3373206
  have htrace : WordTrace (prefixWord ++ tailWord_3373206) baseStart_3373206 baseEnd_3373206 := by
    simpa [prefixWord, tailWord_3373206, baseEnd_3373206] using wordTrace_append hprefix tailTrace_3373206
  have hstable : (prefixWord ++ tailWord_3373206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373206).length < 2 ^ (prefixWord ++ tailWord_3373206).sum := by decide
  have hdescent : baseEnd_3373206 < baseStart_3373206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373234 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_3373234 : Nat := 118140960795 + 3373234 * 2 ^ 59
def prefixEnd_3373234 : Nat := 4983230072969 + 3 ^ 40 * 3373234 * 2
def baseEnd_3373234 : Nat := 1732090402088560440161785

theorem tailTrace_3373234 : CollatzResearch.WordTrace tailWord_3373234 prefixEnd_3373234 1732090402088560440161785 := by
  unfold tailWord_3373234
  simp only [CollatzResearch.WordTrace]
  refine ⟨30757987865339198836611689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82021300974237863564297837 30757987865339198836611689)
  ·
    refine ⟨23068490899004399127458767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30757987865339198836611689 23068490899004399127458767)
    ·
      refine ⟨34602736348506598691188151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23068490899004399127458767 34602736348506598691188151)
      ·
        refine ⟨51904104522759898036782227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34602736348506598691188151 51904104522759898036782227)
        ·
          refine ⟨77856156784139847055173341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51904104522759898036782227 77856156784139847055173341)
          ·
            refine ⟨29196058794052442645690003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77856156784139847055173341 29196058794052442645690003)
            ·
              refine ⟨43794088191078663968535005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29196058794052442645690003 43794088191078663968535005)
              ·
                refine ⟨16422783071654498988200627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43794088191078663968535005 16422783071654498988200627)
                ·
                  refine ⟨24634174607481748482300941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16422783071654498988200627 24634174607481748482300941)
                  ·
                    refine ⟨9237815477805655680862853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24634174607481748482300941 9237815477805655680862853)
                    ·
                      refine ⟨1732090402088560440161785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9237815477805655680862853 1732090402088560440161785)
                      ·
                        rfl

theorem cell23_3373234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_3373234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373234 prefixEnd_3373234 := by exact prefixLift 3373234
  have htrace : WordTrace (prefixWord ++ tailWord_3373234) baseStart_3373234 baseEnd_3373234 := by
    simpa [prefixWord, tailWord_3373234, baseEnd_3373234] using wordTrace_append hprefix tailTrace_3373234
  have hstable : (prefixWord ++ tailWord_3373234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373234).length < 2 ^ (prefixWord ++ tailWord_3373234).sum := by decide
  have hdescent : baseEnd_3373234 < baseStart_3373234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373282 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3373282 : Nat := 118140960795 + 3373282 * 2 ^ 59
def prefixEnd_3373282 : Nat := 4983230072969 + 3 ^ 40 * 3373282 * 2
def baseEnd_3373282 : Nat := 577371683053325417453855

theorem tailTrace_3373282 : CollatzResearch.WordTrace tailWord_3373282 prefixEnd_3373282 577371683053325417453855 := by
  unfold tailWord_3373282
  simp only [CollatzResearch.WordTrace]
  refine ⟨30758425541295724886048525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82022468110121933029462733 30758425541295724886048525)
  ·
    refine ⟨11534409577985896832268197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30758425541295724886048525 11534409577985896832268197)
    ·
      refine ⟨2162701795872355656050287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11534409577985896832268197 2162701795872355656050287)
      ·
        refine ⟨3244052693808533484075431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162701795872355656050287 3244052693808533484075431)
        ·
          refine ⟨4866079040712800226113147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244052693808533484075431 4866079040712800226113147)
          ·
            refine ⟨7299118561069200339169721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866079040712800226113147 7299118561069200339169721)
            ·
              refine ⟨5474338920801900254377291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7299118561069200339169721 5474338920801900254377291)
              ·
                refine ⟨8211508381202850381565937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474338920801900254377291 8211508381202850381565937)
                ·
                  refine ⟨6158631285902137786174453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8211508381202850381565937 6158631285902137786174453)
                  ·
                    refine ⟨577371683053325417453855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6158631285902137786174453 577371683053325417453855)
                    ·
                      rfl

theorem cell23_3373282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3373282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373282 prefixEnd_3373282 := by exact prefixLift 3373282
  have htrace : WordTrace (prefixWord ++ tailWord_3373282) baseStart_3373282 baseEnd_3373282 := by
    simpa [prefixWord, tailWord_3373282, baseEnd_3373282] using wordTrace_append hprefix tailTrace_3373282
  have hstable : (prefixWord ++ tailWord_3373282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373282).length < 2 ^ (prefixWord ++ tailWord_3373282).sum := by decide
  have hdescent : baseEnd_3373282 < baseStart_3373282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373288 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_3373288 : Nat := 118140960795 + 3373288 * 2 ^ 59
def prefixEnd_3373288 : Nat := 4983230072969 + 3 ^ 40 * 3373288 * 2
def baseEnd_3373288 : Nat := 1732118130043903228886537

theorem tailTrace_3373288 : CollatzResearch.WordTrace tailWord_3373288 prefixEnd_3373288 1732118130043903228886537 := by
  unfold tailWord_3373288
  simp only [CollatzResearch.WordTrace]
  refine ⟨61516960501580581284456259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82022614002107441712608345 61516960501580581284456259)
  ·
    refine ⟨92275440752370871926684389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61516960501580581284456259 92275440752370871926684389)
    ·
      refine ⟨17301645141069538486253323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92275440752370871926684389 17301645141069538486253323)
      ·
        refine ⟨25952467711604307729379985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17301645141069538486253323 25952467711604307729379985)
        ·
          refine ⟨19464350783703230797034989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25952467711604307729379985 19464350783703230797034989)
          ·
            refine ⟨7299131543888711548888121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19464350783703230797034989 7299131543888711548888121)
            ·
              refine ⟨5474348657916533661666091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7299131543888711548888121 5474348657916533661666091)
              ·
                refine ⟨8211522986874800492499137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474348657916533661666091 8211522986874800492499137)
                ·
                  refine ⟨6158642240156100369374353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8211522986874800492499137 6158642240156100369374353)
                  ·
                    refine ⟨4618981680117075277030765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6158642240156100369374353 4618981680117075277030765)
                    ·
                      refine ⟨1732118130043903228886537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4618981680117075277030765 1732118130043903228886537)
                      ·
                        rfl

theorem cell23_3373288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_3373288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373288 prefixEnd_3373288 := by exact prefixLift 3373288
  have htrace : WordTrace (prefixWord ++ tailWord_3373288) baseStart_3373288 baseEnd_3373288 := by
    simpa [prefixWord, tailWord_3373288, baseEnd_3373288] using wordTrace_append hprefix tailTrace_3373288
  have hstable : (prefixWord ++ tailWord_3373288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373288).length < 2 ^ (prefixWord ++ tailWord_3373288).sum := by decide
  have hdescent : baseEnd_3373288 < baseStart_3373288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373294 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_3373294 : Nat := 118140960795 + 3373294 * 2 ^ 59
def prefixEnd_3373294 : Nat := 4983230072969 + 3 ^ 40 * 3373294 * 2
def baseEnd_3373294 : Nat := 1732121210927830205411509

theorem tailTrace_3373294 : CollatzResearch.WordTrace tailWord_3373294 prefixEnd_3373294 1732121210927830205411509 := by
  unfold tailWord_3373294
  simp only [CollatzResearch.WordTrace]
  refine ⟨15379267480142428199203867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82022759894092950395753957 15379267480142428199203867)
  ·
    refine ⟨23068901220213642298805801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15379267480142428199203867 23068901220213642298805801)
    ·
      refine ⟨17301675915160231724104351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23068901220213642298805801 17301675915160231724104351)
      ·
        refine ⟨25952513872740347586156527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17301675915160231724104351 25952513872740347586156527)
        ·
          refine ⟨38928770809110521379234791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25952513872740347586156527 38928770809110521379234791)
          ·
            refine ⟨58393156213665782068852187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38928770809110521379234791 58393156213665782068852187)
            ·
              refine ⟨87589734320498673103278281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58393156213665782068852187 87589734320498673103278281)
              ·
                refine ⟨65692300740374004827458711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87589734320498673103278281 65692300740374004827458711)
                ·
                  refine ⟨98538451110561007241188067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65692300740374004827458711 98538451110561007241188067)
                  ·
                    refine ⟨147807676665841510861782101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98538451110561007241188067 147807676665841510861782101)
                    ·
                      refine ⟨1732121210927830205411509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 147807676665841510861782101 1732121210927830205411509)
                      ·
                        rfl

theorem cell23_3373294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_3373294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373294 prefixEnd_3373294 := by exact prefixLift 3373294
  have htrace : WordTrace (prefixWord ++ tailWord_3373294) baseStart_3373294 baseEnd_3373294 := by
    simpa [prefixWord, tailWord_3373294, baseEnd_3373294] using wordTrace_append hprefix tailTrace_3373294
  have hstable : (prefixWord ++ tailWord_3373294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373294).length < 2 ^ (prefixWord ++ tailWord_3373294).sum := by decide
  have hdescent : baseEnd_3373294 < baseStart_3373294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373368 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 2, 4]
def baseStart_3373368 : Nat := 118140960795 + 3373368 * 2 ^ 59
def prefixEnd_3373368 : Nat := 4983230072969 + 3 ^ 40 * 3373368 * 2
def baseEnd_3373368 : Nat := 577386402832087638628723

theorem tailTrace_3373368 : CollatzResearch.WordTrace tailWord_3373368 prefixEnd_3373368 577386402832087638628723 := by
  unfold tailWord_3373368
  simp only [CollatzResearch.WordTrace]
  refine ⟨61518419421435668115912379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82024559228580890821216505 61518419421435668115912379)
  ·
    refine ⟨92277629132153502173868569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61518419421435668115912379 92277629132153502173868569)
    ·
      refine ⟨69208221849115126630401427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92277629132153502173868569 69208221849115126630401427)
      ·
        refine ⟨103812332773672689945602141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69208221849115126630401427 103812332773672689945602141)
        ·
          refine ⟨38929624790127258729600803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103812332773672689945602141 38929624790127258729600803)
          ·
            refine ⟨58394437185190888094401205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38929624790127258729600803 58394437185190888094401205)
            ·
              refine ⟨5474478486111645758850113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58394437185190888094401205 5474478486111645758850113)
              ·
                refine ⟨4105858864583734319137585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5474478486111645758850113 4105858864583734319137585)
                ·
                  refine ⟨3079394148437800739353189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4105858864583734319137585 3079394148437800739353189)
                  ·
                    refine ⟨577386402832087638628723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3079394148437800739353189 577386402832087638628723)
                    ·
                      rfl

theorem cell23_3373368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_3373368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373368 prefixEnd_3373368 := by exact prefixLift 3373368
  have htrace : WordTrace (prefixWord ++ tailWord_3373368) baseStart_3373368 baseEnd_3373368 := by
    simpa [prefixWord, tailWord_3373368, baseEnd_3373368] using wordTrace_append hprefix tailTrace_3373368
  have hstable : (prefixWord ++ tailWord_3373368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373368).length < 2 ^ (prefixWord ++ tailWord_3373368).sum := by decide
  have hdescent : baseEnd_3373368 < baseStart_3373368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373375 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 3, 2, 2]
def baseStart_3373375 : Nat := 118140960795 + 3373375 * 2 ^ 59
def prefixEnd_3373375 : Nat := 4983230072969 + 3 ^ 40 * 3373375 * 2
def baseEnd_3373375 : Nat := 1732162802860844388498637

theorem tailTrace_3373375 : CollatzResearch.WordTrace tailWord_3373375 prefixEnd_3373375 1732162802860844388498637 := by
  unfold tailWord_3373375
  simp only [CollatzResearch.WordTrace]
  refine ⟨123037094153845976427329579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82024729435897317618219719 123037094153845976427329579)
  ·
    refine ⟨184555641230768964640994369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123037094153845976427329579 184555641230768964640994369)
    ·
      refine ⟨138416730923076723480745777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184555641230768964640994369 138416730923076723480745777)
      ·
        refine ⟨103812548192307542610559333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138416730923076723480745777 103812548192307542610559333)
        ·
          refine ⟨19464852786057664239479875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103812548192307542610559333 19464852786057664239479875)
          ·
            refine ⟨29197279179086496359219813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19464852786057664239479875 29197279179086496359219813)
            ·
              refine ⟨5474489846078718067353715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29197279179086496359219813 5474489846078718067353715)
              ·
                refine ⟨8211734769118077101030573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474489846078718067353715 8211734769118077101030573)
                ·
                  refine ⟨3079400538419278912886465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8211734769118077101030573 3079400538419278912886465)
                  ·
                    refine ⟨2309550403814459184664849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3079400538419278912886465 2309550403814459184664849)
                    ·
                      refine ⟨1732162802860844388498637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2309550403814459184664849 1732162802860844388498637)
                      ·
                        rfl

theorem cell23_3373375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 2, 2].length) (baseStart_3373375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373375 prefixEnd_3373375 := by exact prefixLift 3373375
  have htrace : WordTrace (prefixWord ++ tailWord_3373375) baseStart_3373375 baseEnd_3373375 := by
    simpa [prefixWord, tailWord_3373375, baseEnd_3373375] using wordTrace_append hprefix tailTrace_3373375
  have hstable : (prefixWord ++ tailWord_3373375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373375).length < 2 ^ (prefixWord ++ tailWord_3373375).sum := by decide
  have hdescent : baseEnd_3373375 < baseStart_3373375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373391 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 3]
def baseStart_3373391 : Nat := 118140960795 + 3373391 * 2 ^ 59
def prefixEnd_3373391 : Nat := 4983230072969 + 3 ^ 40 * 3373391 * 2
def baseEnd_3373391 : Nat := 1732171018551316325898563

theorem tailTrace_3373391 : CollatzResearch.WordTrace tailWord_3373391 prefixEnd_3373391 1732171018551316325898563 := by
  unfold tailWord_3373391
  simp only [CollatzResearch.WordTrace]
  refine ⟨123037677721788011159912027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82025118481192007439941351 123037677721788011159912027)
  ·
    refine ⟨184556516582682016739868041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123037677721788011159912027 184556516582682016739868041)
    ·
      refine ⟨138417387437011512554901031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184556516582682016739868041 138417387437011512554901031)
      ·
        refine ⟨207626081155517268832351547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138417387437011512554901031 207626081155517268832351547)
        ·
          refine ⟨311439121733275903248527321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207626081155517268832351547 311439121733275903248527321)
          ·
            refine ⟨233579341299956927436395491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311439121733275903248527321 233579341299956927436395491)
            ·
              refine ⟨350369011949935391154593237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233579341299956927436395491 350369011949935391154593237)
              ·
                refine ⟨8211773717576610730185779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 350369011949935391154593237 8211773717576610730185779)
                ·
                  refine ⟨12317660576364916095278669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8211773717576610730185779 12317660576364916095278669)
                  ·
                    refine ⟨4619122716136843535729501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12317660576364916095278669 4619122716136843535729501)
                    ·
                      refine ⟨1732171018551316325898563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4619122716136843535729501 1732171018551316325898563)
                      ·
                        rfl

theorem cell23_3373391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 3].length) (baseStart_3373391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373391 prefixEnd_3373391 := by exact prefixLift 3373391
  have htrace : WordTrace (prefixWord ++ tailWord_3373391) baseStart_3373391 baseEnd_3373391 := by
    simpa [prefixWord, tailWord_3373391, baseEnd_3373391] using wordTrace_append hprefix tailTrace_3373391
  have hstable : (prefixWord ++ tailWord_3373391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373391).length < 2 ^ (prefixWord ++ tailWord_3373391).sum := by decide
  have hdescent : baseEnd_3373391 < baseStart_3373391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373421 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3373421 : Nat := 118140960795 + 3373421 * 2 ^ 59
def prefixEnd_3373421 : Nat := 4983230072969 + 3 ^ 40 * 3373421 * 2
def baseEnd_3373421 : Nat := 1732186422970951208523425

theorem tailTrace_3373421 : CollatzResearch.WordTrace tailWord_3373421 prefixEnd_3373421 1732186422970951208523425 := by
  unfold tailWord_3373421
  simp only [CollatzResearch.WordTrace]
  refine ⟨123038771911679326283504117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82025847941119550855669411 123038771911679326283504117)
  ·
    refine ⟨11534884866719936839078511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123038771911679326283504117 11534884866719936839078511)
    ·
      refine ⟨17302327300079905258617767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11534884866719936839078511 17302327300079905258617767)
      ·
        refine ⟨25953490950119857887926651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17302327300079905258617767 25953490950119857887926651)
        ·
          refine ⟨38930236425179786831889977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25953490950119857887926651 38930236425179786831889977)
          ·
            refine ⟨29197677318884840123917483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38930236425179786831889977 29197677318884840123917483)
            ·
              refine ⟨43796515978327260185876225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29197677318884840123917483 43796515978327260185876225)
              ·
                refine ⟨32847386983745445139407169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43796515978327260185876225 32847386983745445139407169)
                ·
                  refine ⟨24635540237809083854555377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32847386983745445139407169 24635540237809083854555377)
                  ·
                    refine ⟨18476655178356812890916533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24635540237809083854555377 18476655178356812890916533)
                    ·
                      refine ⟨1732186422970951208523425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18476655178356812890916533 1732186422970951208523425)
                      ·
                        rfl

theorem cell23_3373421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3373421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373421 prefixEnd_3373421 := by exact prefixLift 3373421
  have htrace : WordTrace (prefixWord ++ tailWord_3373421) baseStart_3373421 baseEnd_3373421 := by
    simpa [prefixWord, tailWord_3373421, baseEnd_3373421] using wordTrace_append hprefix tailTrace_3373421
  have hstable : (prefixWord ++ tailWord_3373421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373421).length < 2 ^ (prefixWord ++ tailWord_3373421).sum := by decide
  have hdescent : baseEnd_3373421 < baseStart_3373421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373451 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 5]
def baseStart_3373451 : Nat := 118140960795 + 3373451 * 2 ^ 59
def prefixEnd_3373451 : Nat := 4983230072969 + 3 ^ 40 * 3373451 * 2
def baseEnd_3373451 : Nat := 1732201827390586091148287

theorem tailTrace_3373451 : CollatzResearch.WordTrace tailWord_3373451 prefixEnd_3373451 1732201827390586091148287 := by
  unfold tailWord_3373451
  simp only [CollatzResearch.WordTrace]
  refine ⟨123039866101570641407096207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82026577401047094271397471 123039866101570641407096207)
  ·
    refine ⟨184559799152355962110644311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123039866101570641407096207 184559799152355962110644311)
    ·
      refine ⟨276839698728533943165966467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184559799152355962110644311 276839698728533943165966467)
      ·
        refine ⟨415259548092800914748949701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276839698728533943165966467 415259548092800914748949701)
        ·
          refine ⟨77861165267400171515428069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415259548092800914748949701 77861165267400171515428069)
          ·
            refine ⟨14598968487637532159142763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77861165267400171515428069 14598968487637532159142763)
            ·
              refine ⟨21898452731456298238714145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14598968487637532159142763 21898452731456298238714145)
              ·
                refine ⟨16423839548592223679035609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21898452731456298238714145 16423839548592223679035609)
                ·
                  refine ⟨12317879661444167759276707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16423839548592223679035609 12317879661444167759276707)
                  ·
                    refine ⟨18476819492166251638915061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12317879661444167759276707 18476819492166251638915061)
                    ·
                      refine ⟨1732201827390586091148287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18476819492166251638915061 1732201827390586091148287)
                      ·
                        rfl

theorem cell23_3373451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 5].length) (baseStart_3373451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373451 prefixEnd_3373451 := by exact prefixLift 3373451
  have htrace : WordTrace (prefixWord ++ tailWord_3373451) baseStart_3373451 baseEnd_3373451 := by
    simpa [prefixWord, tailWord_3373451, baseEnd_3373451] using wordTrace_append hprefix tailTrace_3373451
  have hstable : (prefixWord ++ tailWord_3373451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373451).length < 2 ^ (prefixWord ++ tailWord_3373451).sum := by decide
  have hdescent : baseEnd_3373451 < baseStart_3373451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373452 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 1, 3, 2]
def baseStart_3373452 : Nat := 118140960795 + 3373452 * 2 ^ 59
def prefixEnd_3373452 : Nat := 4983230072969 + 3 ^ 40 * 3373452 * 2
def baseEnd_3373452 : Nat := 1732202340871240587235783

theorem tailTrace_3373452 : CollatzResearch.WordTrace tailWord_3373452 prefixEnd_3373452 1732202340871240587235783 := by
  unfold tailWord_3373452
  simp only [CollatzResearch.WordTrace]
  refine ⟨61519951287283509288941305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82026601716378012385255073 61519951287283509288941305)
  ·
    refine ⟨46139963465462631966705979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61519951287283509288941305 46139963465462631966705979)
    ·
      refine ⟨69209945198193947950058969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46139963465462631966705979 69209945198193947950058969)
      ·
        refine ⟨51907458898645460962544227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69209945198193947950058969 51907458898645460962544227)
        ·
          refine ⟨77861188347968191443816341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51907458898645460962544227 77861188347968191443816341)
          ·
            refine ⟨3649743203811008973928891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77861188347968191443816341 3649743203811008973928891)
            ·
              refine ⟨5474614805716513460893337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649743203811008973928891 5474614805716513460893337)
              ·
                refine ⟨4105961104287385095670003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5474614805716513460893337 4105961104287385095670003)
                ·
                  refine ⟨6158941656431077643505005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4105961104287385095670003 6158941656431077643505005)
                  ·
                    refine ⟨2309603121161654116314377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6158941656431077643505005 2309603121161654116314377)
                    ·
                      refine ⟨1732202340871240587235783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2309603121161654116314377 1732202340871240587235783)
                      ·
                        rfl

theorem cell23_3373452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_3373452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373452 prefixEnd_3373452 := by exact prefixLift 3373452
  have htrace : WordTrace (prefixWord ++ tailWord_3373452) baseStart_3373452 baseEnd_3373452 := by
    simpa [prefixWord, tailWord_3373452, baseEnd_3373452] using wordTrace_append hprefix tailTrace_3373452
  have hstable : (prefixWord ++ tailWord_3373452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373452).length < 2 ^ (prefixWord ++ tailWord_3373452).sum := by decide
  have hdescent : baseEnd_3373452 < baseStart_3373452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373461 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_3373461 : Nat := 118140960795 + 3373461 * 2 ^ 59
def prefixEnd_3373461 : Nat := 4983230072969 + 3 ^ 40 * 3373461 * 2
def baseEnd_3373461 : Nat := 1732206962197131052023241

theorem tailTrace_3373461 : CollatzResearch.WordTrace tailWord_3373461 prefixEnd_3373461 1732206962197131052023241 := by
  unfold tailWord_3373461
  simp only [CollatzResearch.WordTrace]
  refine ⟨123040230831534413114960237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82026820554356275409973491 123040230831534413114960237)
  ·
    refine ⟨46140086561825404918110089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123040230831534413114960237 46140086561825404918110089)
    ·
      refine ⟨34605064921369053688582567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46140086561825404918110089 34605064921369053688582567)
      ·
        refine ⟨51907597382053580532873851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34605064921369053688582567 51907597382053580532873851)
        ·
          refine ⟨77861396073080370799310777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51907597382053580532873851 77861396073080370799310777)
          ·
            refine ⟨58396047054810278099483083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77861396073080370799310777 58396047054810278099483083)
            ·
              refine ⟨87594070582215417149224625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58396047054810278099483083 87594070582215417149224625)
              ·
                refine ⟨65695552936661562861918469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87594070582215417149224625 65695552936661562861918469)
                ·
                  refine ⟨12317916175624043036609713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65695552936661562861918469 12317916175624043036609713)
                  ·
                    refine ⟨9238437131718032277457285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12317916175624043036609713 9238437131718032277457285)
                    ·
                      refine ⟨1732206962197131052023241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9238437131718032277457285 1732206962197131052023241)
                      ·
                        rfl

theorem cell23_3373461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_3373461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373461 prefixEnd_3373461 := by exact prefixLift 3373461
  have htrace : WordTrace (prefixWord ++ tailWord_3373461) baseStart_3373461 baseEnd_3373461 := by
    simpa [prefixWord, tailWord_3373461, baseEnd_3373461] using wordTrace_append hprefix tailTrace_3373461
  have hstable : (prefixWord ++ tailWord_3373461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373461).length < 2 ^ (prefixWord ++ tailWord_3373461).sum := by decide
  have hdescent : baseEnd_3373461 < baseStart_3373461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373469 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_3373469 : Nat := 118140960795 + 3373469 * 2 ^ 59
def prefixEnd_3373469 : Nat := 4983230072969 + 3 ^ 40 * 3373469 * 2
def baseEnd_3373469 : Nat := 1732211070042367020723205

theorem tailTrace_3373469 : CollatzResearch.WordTrace tailWord_3373469 prefixEnd_3373469 1732211070042367020723205 := by
  unfold tailWord_3373469
  simp only [CollatzResearch.WordTrace]
  refine ⟨123040522615505430481251461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82027015077003620320834307 123040522615505430481251461)
  ·
    refine ⟨23070097990407268215234649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123040522615505430481251461 23070097990407268215234649)
    ·
      refine ⟨17302573492805451161425987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23070097990407268215234649 17302573492805451161425987)
      ·
        refine ⟨25953860239208176742138981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17302573492805451161425987 25953860239208176742138981)
        ·
          refine ⟨4866348794851533139151059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25953860239208176742138981 4866348794851533139151059)
          ·
            refine ⟨7299523192277299708726589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866348794851533139151059 7299523192277299708726589)
            ·
              refine ⟨2737321197103987390772471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7299523192277299708726589 2737321197103987390772471)
              ·
                refine ⟨4105981795655981086158707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737321197103987390772471 4105981795655981086158707)
                ·
                  refine ⟨6158972693483971629238061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4105981795655981086158707 6158972693483971629238061)
                  ·
                    refine ⟨2309614760056489360964273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6158972693483971629238061 2309614760056489360964273)
                    ·
                      refine ⟨1732211070042367020723205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2309614760056489360964273 1732211070042367020723205)
                      ·
                        rfl

theorem cell23_3373469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_3373469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373469 prefixEnd_3373469 := by exact prefixLift 3373469
  have htrace : WordTrace (prefixWord ++ tailWord_3373469) baseStart_3373469 baseEnd_3373469 := by
    simpa [prefixWord, tailWord_3373469, baseEnd_3373469] using wordTrace_append hprefix tailTrace_3373469
  have hstable : (prefixWord ++ tailWord_3373469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373469).length < 2 ^ (prefixWord ++ tailWord_3373469).sum := by decide
  have hdescent : baseEnd_3373469 < baseStart_3373469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373481 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 3, 5, 3]
def baseStart_3373481 : Nat := 118140960795 + 3373481 * 2 ^ 59
def prefixEnd_3373481 : Nat := 4983230072969 + 3 ^ 40 * 3373481 * 2
def baseEnd_3373481 : Nat := 1732217231810220973773149

theorem tailTrace_3373481 : CollatzResearch.WordTrace tailWord_3373481 prefixEnd_3373481 1732217231810220973773149 := by
  unfold tailWord_3373481
  simp only [CollatzResearch.WordTrace]
  refine ⟨123040960291461956530688297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82027306860974637687125531 123040960291461956530688297)
  ·
    refine ⟨92280720218596467398016223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123040960291461956530688297 92280720218596467398016223)
    ·
      refine ⟨138421080327894701097024335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92280720218596467398016223 138421080327894701097024335)
      ·
        refine ⟨207631620491842051645536503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138421080327894701097024335 207631620491842051645536503)
        ·
          refine ⟨311447430737763077468304755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207631620491842051645536503 311447430737763077468304755)
          ·
            refine ⟨467171146106644616202457133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311447430737763077468304755 467171146106644616202457133)
            ·
              refine ⟨175189179789991731075921425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 467171146106644616202457133 175189179789991731075921425)
              ·
                refine ⟨131391884842493798306941069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175189179789991731075921425 131391884842493798306941069)
                ·
                  refine ⟨49271956815935174365102901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131391884842493798306941069 49271956815935174365102901)
                  ·
                    refine ⟨4619245951493922596728397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49271956815935174365102901 4619245951493922596728397)
                    ·
                      refine ⟨1732217231810220973773149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4619245951493922596728397 1732217231810220973773149)
                      ·
                        rfl

theorem cell23_3373481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 5, 3].length) (baseStart_3373481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373481 prefixEnd_3373481 := by exact prefixLift 3373481
  have htrace : WordTrace (prefixWord ++ tailWord_3373481) baseStart_3373481 baseEnd_3373481 := by
    simpa [prefixWord, tailWord_3373481, baseEnd_3373481] using wordTrace_append hprefix tailTrace_3373481
  have hstable : (prefixWord ++ tailWord_3373481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373481).length < 2 ^ (prefixWord ++ tailWord_3373481).sum := by decide
  have hdescent : baseEnd_3373481 < baseStart_3373481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373492 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3373492 : Nat := 118140960795 + 3373492 * 2 ^ 59
def prefixEnd_3373492 : Nat := 4983230072969 + 3 ^ 40 * 3373492 * 2
def baseEnd_3373492 : Nat := 577407626699140143578533

theorem tailTrace_3373492 : CollatzResearch.WordTrace tailWord_3373492 prefixEnd_3373492 577407626699140143578533 := by
  unfold tailWord_3373492
  simp only [CollatzResearch.WordTrace]
  refine ⟨61520680747211052704669365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82027574329614736939559153 61520680747211052704669365)
  ·
    refine ⟨5767563820051036191062753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61520680747211052704669365 5767563820051036191062753)
    ·
      refine ⟨4325672865038277143297065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5767563820051036191062753 4325672865038277143297065)
      ·
        refine ⟨3244254648778707857472799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4325672865038277143297065 3244254648778707857472799)
        ·
          refine ⟨4866381973168061786209199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244254648778707857472799 4866381973168061786209199)
          ·
            refine ⟨7299572959752092679313799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866381973168061786209199 7299572959752092679313799)
            ·
              refine ⟨10949359439628139018970699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7299572959752092679313799 10949359439628139018970699)
              ·
                refine ⟨16424039159442208528456049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10949359439628139018970699 16424039159442208528456049)
                ·
                  refine ⟨12318029369581656396342037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16424039159442208528456049 12318029369581656396342037)
                  ·
                    refine ⟨577407626699140143578533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12318029369581656396342037 577407626699140143578533)
                    ·
                      rfl

theorem cell23_3373492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3373492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373492 prefixEnd_3373492 := by exact prefixLift 3373492
  have htrace : WordTrace (prefixWord ++ tailWord_3373492) baseStart_3373492 baseEnd_3373492 := by
    simpa [prefixWord, tailWord_3373492, baseEnd_3373492] using wordTrace_append hprefix tailTrace_3373492
  have hstable : (prefixWord ++ tailWord_3373492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373492).length < 2 ^ (prefixWord ++ tailWord_3373492).sum := by decide
  have hdescent : baseEnd_3373492 < baseStart_3373492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373551 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_3373551 : Nat := 118140960795 + 3373551 * 2 ^ 59
def prefixEnd_3373551 : Nat := 4983230072969 + 3 ^ 40 * 3373551 * 2
def baseEnd_3373551 : Nat := 1732253175456035699897827

theorem tailTrace_3373551 : CollatzResearch.WordTrace tailWord_3373551 prefixEnd_3373551 1732253175456035699897827 := by
  unfold tailWord_3373551
  simp only [CollatzResearch.WordTrace]
  refine ⟨123043513401208358485736507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82029008934138905657157671 123043513401208358485736507)
  ·
    refine ⟨184565270101812537728604761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123043513401208358485736507 184565270101812537728604761)
    ·
      refine ⟨138423952576359403296453571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184565270101812537728604761 138423952576359403296453571)
      ·
        refine ⟨207635928864539104944680357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138423952576359403296453571 207635928864539104944680357)
        ·
          refine ⟨38931736662101082177127567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207635928864539104944680357 38931736662101082177127567)
          ·
            refine ⟨58397604993151623265691351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38931736662101082177127567 58397604993151623265691351)
            ·
              refine ⟨87596407489727434898537027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58397604993151623265691351 87596407489727434898537027)
              ·
                refine ⟨131394611234591152347805541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87596407489727434898537027 131394611234591152347805541)
                ·
                  refine ⟨24636489606485841065213539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131394611234591152347805541 24636489606485841065213539)
                  ·
                    refine ⟨36954734409728761597820309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24636489606485841065213539 36954734409728761597820309)
                    ·
                      refine ⟨1732253175456035699897827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36954734409728761597820309 1732253175456035699897827)
                      ·
                        rfl

theorem cell23_3373551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_3373551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373551 prefixEnd_3373551 := by exact prefixLift 3373551
  have htrace : WordTrace (prefixWord ++ tailWord_3373551) baseStart_3373551 baseEnd_3373551 := by
    simpa [prefixWord, tailWord_3373551, baseEnd_3373551] using wordTrace_append hprefix tailTrace_3373551
  have hstable : (prefixWord ++ tailWord_3373551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373551).length < 2 ^ (prefixWord ++ tailWord_3373551).sum := by decide
  have hdescent : baseEnd_3373551 < baseStart_3373551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373642 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 1, 5]
def baseStart_3373642 : Nat := 118140960795 + 3373642 * 2 ^ 59
def prefixEnd_3373642 : Nat := 4983230072969 + 3 ^ 40 * 3373642 * 2
def baseEnd_3373642 : Nat := 577433300731864947953303

theorem tailTrace_3373642 : CollatzResearch.WordTrace tailWord_3373642 prefixEnd_3373642 577433300731864947953303 := by
  unfold tailWord_3373642
  simp only [CollatzResearch.WordTrace]
  refine ⟨30761708110969670256824795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82031221629252454018199453 30761708110969670256824795)
  ·
    refine ⟨46142562166454505385237193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30761708110969670256824795 46142562166454505385237193)
    ·
      refine ⟨34606921624840879038927895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46142562166454505385237193 34606921624840879038927895)
      ·
        refine ⟨51910382437261318558391843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34606921624840879038927895 51910382437261318558391843)
        ·
          refine ⟨77865573655891977837587765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51910382437261318558391843 77865573655891977837587765)
          ·
            refine ⟨7299897530239872922273853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77865573655891977837587765 7299897530239872922273853)
            ·
              refine ⟨2737461573839952345852695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7299897530239872922273853 2737461573839952345852695)
              ·
                refine ⟨4106192360759928518779043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737461573839952345852695 4106192360759928518779043)
                ·
                  refine ⟨6159288541139892778168565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106192360759928518779043 6159288541139892778168565)
                  ·
                    refine ⟨577433300731864947953303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6159288541139892778168565 577433300731864947953303)
                    ·
                      rfl

theorem cell23_3373642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_3373642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373642 prefixEnd_3373642 := by exact prefixLift 3373642
  have htrace : WordTrace (prefixWord ++ tailWord_3373642) baseStart_3373642 baseEnd_3373642 := by
    simpa [prefixWord, tailWord_3373642, baseEnd_3373642] using wordTrace_append hprefix tailTrace_3373642
  have hstable : (prefixWord ++ tailWord_3373642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373642).length < 2 ^ (prefixWord ++ tailWord_3373642).sum := by decide
  have hdescent : baseEnd_3373642 < baseStart_3373642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373648 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 5]
def baseStart_3373648 : Nat := 118140960795 + 3373648 * 2 ^ 59
def prefixEnd_3373648 : Nat := 4983230072969 + 3 ^ 40 * 3373648 * 2
def baseEnd_3373648 : Nat := 1732302983079521820384881

theorem tailTrace_3373648 : CollatzResearch.WordTrace tailWord_3373648 prefixEnd_3373648 1732302983079521820384881 := by
  unfold tailWord_3373648
  simp only [CollatzResearch.WordTrace]
  refine ⟨61523525640928472026008799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82031367521237962701345065 61523525640928472026008799)
  ·
    refine ⟨92285288461392708039013199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61523525640928472026008799 92285288461392708039013199)
    ·
      refine ⟨138427932692089062058519799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92285288461392708039013199 138427932692089062058519799)
      ·
        refine ⟨207641899038133593087779699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138427932692089062058519799 207641899038133593087779699)
        ·
          refine ⟨311462848557200389631669549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207641899038133593087779699 311462848557200389631669549)
          ·
            refine ⟨116798568208950146111876081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 311462848557200389631669549 116798568208950146111876081)
            ·
              refine ⟨87598926156712609583907061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116798568208950146111876081 87598926156712609583907061)
              ·
                refine ⟨8212399327191807148491287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87598926156712609583907061 8212399327191807148491287)
                ·
                  refine ⟨12318598990787710722736931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8212399327191807148491287 12318598990787710722736931)
                  ·
                    refine ⟨18477898486181566084105397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12318598990787710722736931 18477898486181566084105397)
                    ·
                      refine ⟨1732302983079521820384881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18477898486181566084105397 1732302983079521820384881)
                      ·
                        rfl

theorem cell23_3373648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_3373648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373648 prefixEnd_3373648 := by exact prefixLift 3373648
  have htrace : WordTrace (prefixWord ++ tailWord_3373648) baseStart_3373648 baseEnd_3373648 := by
    simpa [prefixWord, tailWord_3373648, baseEnd_3373648] using wordTrace_append hprefix tailTrace_3373648
  have hstable : (prefixWord ++ tailWord_3373648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373648).length < 2 ^ (prefixWord ++ tailWord_3373648).sum := by decide
  have hdescent : baseEnd_3373648 < baseStart_3373648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373665 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 3, 2, 3]
def baseStart_3373665 : Nat := 118140960795 + 3373665 * 2 ^ 59
def prefixEnd_3373665 : Nat := 4983230072969 + 3 ^ 40 * 3373665 * 2
def baseEnd_3373665 : Nat := 1732311712250648253872303

theorem tailTrace_3373665 : CollatzResearch.WordTrace tailWord_3373665 prefixEnd_3373665 1732311712250648253872303 := by
  unfold tailWord_3373665
  simp only [CollatzResearch.WordTrace]
  refine ⟨123047671322795355955386449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82031780881863570636924299 123047671322795355955386449)
  ·
    refine ⟨92285753492096516966539837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123047671322795355955386449 92285753492096516966539837)
    ·
      refine ⟨34607157559536193862452439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92285753492096516966539837 34607157559536193862452439)
      ·
        refine ⟨51910736339304290793678659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34607157559536193862452439 51910736339304290793678659)
        ·
          refine ⟨77866104508956436190517989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51910736339304290793678659 77866104508956436190517989)
          ·
            refine ⟨14599894595429331785722123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77866104508956436190517989 14599894595429331785722123)
            ·
              refine ⟨21899841893143997678583185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14599894595429331785722123 21899841893143997678583185)
              ·
                refine ⟨16424881419857998258937389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21899841893143997678583185 16424881419857998258937389)
                ·
                  refine ⟨6159330532446749347101521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16424881419857998258937389 6159330532446749347101521)
                  ·
                    refine ⟨4619497899335062010326141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6159330532446749347101521 4619497899335062010326141)
                    ·
                      refine ⟨1732311712250648253872303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4619497899335062010326141 1732311712250648253872303)
                      ·
                        rfl

theorem cell23_3373665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_3373665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373665 prefixEnd_3373665 := by exact prefixLift 3373665
  have htrace : WordTrace (prefixWord ++ tailWord_3373665) baseStart_3373665 baseEnd_3373665 := by
    simpa [prefixWord, tailWord_3373665, baseEnd_3373665] using wordTrace_append hprefix tailTrace_3373665
  have hstable : (prefixWord ++ tailWord_3373665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373665).length < 2 ^ (prefixWord ++ tailWord_3373665).sum := by decide
  have hdescent : baseEnd_3373665 < baseStart_3373665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373672 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 1, 6]
def baseStart_3373672 : Nat := 118140960795 + 3373672 * 2 ^ 59
def prefixEnd_3373672 : Nat := 4983230072969 + 3 ^ 40 * 3373672 * 2
def baseEnd_3373672 : Nat := 577438435538409908828257

theorem tailTrace_3373672 : CollatzResearch.WordTrace tailWord_3373672 prefixEnd_3373672 577438435538409908828257 := by
  unfold tailWord_3373672
  simp only [CollatzResearch.WordTrace]
  refine ⟨61523963316884998075445635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82031951089179997433927513 61523963316884998075445635)
  ·
    refine ⟨92285944975327497113168453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61523963316884998075445635 92285944975327497113168453)
    ·
      refine ⟨17303614682873905708719085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92285944975327497113168453 17303614682873905708719085)
      ·
        refine ⟨6488855506077714640769657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17303614682873905708719085 6488855506077714640769657)
        ·
          refine ⟨4866641629558285980577243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6488855506077714640769657 4866641629558285980577243)
          ·
            refine ⟨7299962444337428970865865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866641629558285980577243 7299962444337428970865865)
            ·
              refine ⟨5474971833253071728149399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7299962444337428970865865 5474971833253071728149399)
              ·
                refine ⟨8212457749879607592224099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474971833253071728149399 8212457749879607592224099)
                ·
                  refine ⟨12318686624819411388336149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8212457749879607592224099 12318686624819411388336149)
                  ·
                    refine ⟨577438435538409908828257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12318686624819411388336149 577438435538409908828257)
                    ·
                      rfl

theorem cell23_3373672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_3373672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373672 prefixEnd_3373672 := by exact prefixLift 3373672
  have htrace : WordTrace (prefixWord ++ tailWord_3373672) baseStart_3373672 baseEnd_3373672 := by
    simpa [prefixWord, tailWord_3373672, baseEnd_3373672] using wordTrace_append hprefix tailTrace_3373672
  have hstable : (prefixWord ++ tailWord_3373672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373672).length < 2 ^ (prefixWord ++ tailWord_3373672).sum := by decide
  have hdescent : baseEnd_3373672 < baseStart_3373672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373696 : List Nat := [2, 1, 1, 2, 1, 6, 2, 3, 1, 2, 2]
def baseStart_3373696 : Nat := 118140960795 + 3373696 * 2 ^ 59
def prefixEnd_3373696 : Nat := 4983230072969 + 3 ^ 40 * 3373696 * 2
def baseEnd_3373696 : Nat := 1732327630150937632584661

theorem tailTrace_3373696 : CollatzResearch.WordTrace tailWord_3373696 prefixEnd_3373696 1732327630150937632584661 := by
  unfold tailWord_3373696
  simp only [CollatzResearch.WordTrace]
  refine ⟨61524400992841524124882471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82032534657122032166509961 61524400992841524124882471)
  ·
    refine ⟨92286601489262286187323707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61524400992841524124882471 92286601489262286187323707)
    ·
      refine ⟨138429902233893429280985561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92286601489262286187323707 138429902233893429280985561)
      ·
        refine ⟨103822426675420071960739171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138429902233893429280985561 103822426675420071960739171)
        ·
          refine ⟨155733640013130107941108757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103822426675420071960739171 155733640013130107941108757)
          ·
            refine ⟨7300014375615473809739473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155733640013130107941108757 7300014375615473809739473)
            ·
              refine ⟨5475010781711605357304605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7300014375615473809739473 5475010781711605357304605)
              ·
                refine ⟨2053129043141852008989227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5475010781711605357304605 2053129043141852008989227)
                ·
                  refine ⟨3079693564712778013483841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2053129043141852008989227 3079693564712778013483841)
                  ·
                    refine ⟨2309770173534583510112881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3079693564712778013483841 2309770173534583510112881)
                    ·
                      refine ⟨1732327630150937632584661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2309770173534583510112881 1732327630150937632584661)
                      ·
                        rfl

theorem cell23_3373696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 1, 2, 2].length) (baseStart_3373696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373696 prefixEnd_3373696 := by exact prefixLift 3373696
  have htrace : WordTrace (prefixWord ++ tailWord_3373696) baseStart_3373696 baseEnd_3373696 := by
    simpa [prefixWord, tailWord_3373696, baseEnd_3373696] using wordTrace_append hprefix tailTrace_3373696
  have hstable : (prefixWord ++ tailWord_3373696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373696).length < 2 ^ (prefixWord ++ tailWord_3373696).sum := by decide
  have hdescent : baseEnd_3373696 < baseStart_3373696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373706 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 2, 4]
def baseStart_3373706 : Nat := 118140960795 + 3373706 * 2 ^ 59
def prefixEnd_3373706 : Nat := 4983230072969 + 3 ^ 40 * 3373706 * 2
def baseEnd_3373706 : Nat := 577444254985827531153205

theorem tailTrace_3373706 : CollatzResearch.WordTrace tailWord_3373706 prefixEnd_3373706 577444254985827531153205 := by
  unfold tailWord_3373706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30762291678911704989407243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82032777810431213305085981 30762291678911704989407243)
  ·
    refine ⟨46143437518367557484110865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30762291678911704989407243 46143437518367557484110865)
    ·
      refine ⟨34607578138775668113083149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46143437518367557484110865 34607578138775668113083149)
      ·
        refine ⟨12977841802040875542406181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34607578138775668113083149 12977841802040875542406181)
        ·
          refine ⟨2433345337882664164201159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12977841802040875542406181 2433345337882664164201159)
          ·
            refine ⟨3650018006823996246301739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433345337882664164201159 3650018006823996246301739)
            ·
              refine ⟨5475027010235994369452609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650018006823996246301739 5475027010235994369452609)
              ·
                refine ⟨4106270257676995777089457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5475027010235994369452609 4106270257676995777089457)
                ·
                  refine ⟨3079702693257746832817093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4106270257676995777089457 3079702693257746832817093)
                  ·
                    refine ⟨577444254985827531153205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3079702693257746832817093 577444254985827531153205)
                    ·
                      rfl

theorem cell23_3373706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_3373706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373706 prefixEnd_3373706 := by exact prefixLift 3373706
  have htrace : WordTrace (prefixWord ++ tailWord_3373706) baseStart_3373706 baseEnd_3373706 := by
    simpa [prefixWord, tailWord_3373706, baseEnd_3373706] using wordTrace_append hprefix tailTrace_3373706
  have hstable : (prefixWord ++ tailWord_3373706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373706).length < 2 ^ (prefixWord ++ tailWord_3373706).sum := by decide
  have hdescent : baseEnd_3373706 < baseStart_3373706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373708 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_3373708 : Nat := 118140960795 + 3373708 * 2 ^ 59
def prefixEnd_3373708 : Nat := 4983230072969 + 3 ^ 40 * 3373708 * 2
def baseEnd_3373708 : Nat := 1732333791918791585634605

theorem tailTrace_3373708 : CollatzResearch.WordTrace tailWord_3373708 prefixEnd_3373708 1732333791918791585634605 := by
  unfold tailWord_3373708
  simp only [CollatzResearch.WordTrace]
  refine ⟨61524619830819787149600889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82032826441093049532801185 61524619830819787149600889)
  ·
    refine ⟨46143464873114840362200667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61524619830819787149600889 46143464873114840362200667)
    ·
      refine ⟨69215197309672260543301001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46143464873114840362200667 69215197309672260543301001)
      ·
        refine ⟨51911397982254195407475751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69215197309672260543301001 51911397982254195407475751)
        ·
          refine ⟨77867096973381293111213627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51911397982254195407475751 77867096973381293111213627)
          ·
            refine ⟨116800645460071939666820441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77867096973381293111213627 116800645460071939666820441)
            ·
              refine ⟨87600484095053954750115331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116800645460071939666820441 87600484095053954750115331)
              ·
                refine ⟨131400726142580932125172997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87600484095053954750115331 131400726142580932125172997)
                ·
                  refine ⟨24637636151733924773469937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131400726142580932125172997 24637636151733924773469937)
                  ·
                    refine ⟨18478227113800443580102453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24637636151733924773469937 18478227113800443580102453)
                    ·
                      refine ⟨1732333791918791585634605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18478227113800443580102453 1732333791918791585634605)
                      ·
                        rfl

theorem cell23_3373708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_3373708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373708 prefixEnd_3373708 := by exact prefixLift 3373708
  have htrace : WordTrace (prefixWord ++ tailWord_3373708) baseStart_3373708 baseEnd_3373708 := by
    simpa [prefixWord, tailWord_3373708, baseEnd_3373708] using wordTrace_append hprefix tailTrace_3373708
  have hstable : (prefixWord ++ tailWord_3373708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373708).length < 2 ^ (prefixWord ++ tailWord_3373708).sum := by decide
  have hdescent : baseEnd_3373708 < baseStart_3373708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373729 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 1, 3, 3]
def baseStart_3373729 : Nat := 118140960795 + 3373729 * 2 ^ 59
def prefixEnd_3373729 : Nat := 4983230072969 + 3 ^ 40 * 3373729 * 2
def baseEnd_3373729 : Nat := 1732344575012536003472009

theorem tailTrace_3373729 : CollatzResearch.WordTrace tailWord_3373729 prefixEnd_3373729 1732344575012536003472009 := by
  unfold tailWord_3373729
  simp only [CollatzResearch.WordTrace]
  refine ⟨123050005594563494885716241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82033337063042329923810827 123050005594563494885716241)
  ·
    refine ⟨92287504195922621164287181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123050005594563494885716241 92287504195922621164287181)
    ·
      refine ⟨34607814073470982936607693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92287504195922621164287181 34607814073470982936607693)
      ·
        refine ⟨12977930277551618601227885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34607814073470982936607693 12977930277551618601227885)
        ·
          refine ⟨4866723854081856975460457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12977930277551618601227885 4866723854081856975460457)
          ·
            refine ⟨3650042890561392731595343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4866723854081856975460457 3650042890561392731595343)
            ·
              refine ⟨5475064335842089097393015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650042890561392731595343 5475064335842089097393015)
              ·
                refine ⟨8212596503763133646089523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475064335842089097393015 8212596503763133646089523)
                ·
                  refine ⟨12318894755644700469134285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8212596503763133646089523 12318894755644700469134285)
                  ·
                    refine ⟨4619585533366762675925357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12318894755644700469134285 4619585533366762675925357)
                    ·
                      refine ⟨1732344575012536003472009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4619585533366762675925357 1732344575012536003472009)
                      ·
                        rfl

theorem cell23_3373729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_3373729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373729 prefixEnd_3373729 := by exact prefixLift 3373729
  have htrace : WordTrace (prefixWord ++ tailWord_3373729) baseStart_3373729 baseEnd_3373729 := by
    simpa [prefixWord, tailWord_3373729, baseEnd_3373729] using wordTrace_append hprefix tailTrace_3373729
  have hstable : (prefixWord ++ tailWord_3373729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373729).length < 2 ^ (prefixWord ++ tailWord_3373729).sum := by decide
  have hdescent : baseEnd_3373729 < baseStart_3373729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373742 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3373742 : Nat := 118140960795 + 3373742 * 2 ^ 59
def prefixEnd_3373742 : Nat := 4983230072969 + 3 ^ 40 * 3373742 * 2
def baseEnd_3373742 : Nat := 1732351250261044452609449

theorem tailTrace_3373742 : CollatzResearch.WordTrace tailWord_3373742 prefixEnd_3373742 1732351250261044452609449 := by
  unfold tailWord_3373742
  simp only [CollatzResearch.WordTrace]
  refine ⟨15381309967939549763242435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82033653162344265403959653 15381309967939549763242435)
  ·
    refine ⟨23071964951909324644863653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15381309967939549763242435 23071964951909324644863653)
    ·
      refine ⟨4325993428482998370911935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23071964951909324644863653 4325993428482998370911935)
      ·
        refine ⟨6488990142724497556367903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4325993428482998370911935 6488990142724497556367903)
        ·
          refine ⟨9733485214086746334551855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6488990142724497556367903 9733485214086746334551855)
          ·
            refine ⟨14600227821130119501827783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9733485214086746334551855 14600227821130119501827783)
            ·
              refine ⟨21900341731695179252741675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14600227821130119501827783 21900341731695179252741675)
              ·
                refine ⟨32850512597542768879112513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21900341731695179252741675 32850512597542768879112513)
                ·
                  refine ⟨24637884448157076659334385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32850512597542768879112513 24637884448157076659334385)
                  ·
                    refine ⟨18478413336117807494500789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24637884448157076659334385 18478413336117807494500789)
                    ·
                      refine ⟨1732351250261044452609449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18478413336117807494500789 1732351250261044452609449)
                      ·
                        rfl

theorem cell23_3373742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3373742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373742 prefixEnd_3373742 := by exact prefixLift 3373742
  have htrace : WordTrace (prefixWord ++ tailWord_3373742) baseStart_3373742 baseEnd_3373742 := by
    simpa [prefixWord, tailWord_3373742, baseEnd_3373742] using wordTrace_append hprefix tailTrace_3373742
  have hstable : (prefixWord ++ tailWord_3373742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373742).length < 2 ^ (prefixWord ++ tailWord_3373742).sum := by decide
  have hdescent : baseEnd_3373742 < baseStart_3373742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373780 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_3373780 : Nat := 118140960795 + 3373780 * 2 ^ 59
def prefixEnd_3373780 : Nat := 4983230072969 + 3 ^ 40 * 3373780 * 2
def baseEnd_3373780 : Nat := 1732370762525915303934275

theorem tailTrace_3373780 : CollatzResearch.WordTrace tailWord_3373780 prefixEnd_3373780 1732370762525915303934275 := by
  unfold tailWord_3373780
  simp only [CollatzResearch.WordTrace]
  refine ⟨61525932858689365297911397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82034577144919153730548529 61525932858689365297911397)
  ·
    refine ⟨11536112411004255993358387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61525932858689365297911397 11536112411004255993358387)
    ·
      refine ⟨17304168616506383990037581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11536112411004255993358387 17304168616506383990037581)
      ·
        refine ⟨6489063231189893996264093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17304168616506383990037581 6489063231189893996264093)
        ·
          refine ⟨2433398711696210248599035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6489063231189893996264093 2433398711696210248599035)
          ·
            refine ⟨3650098067544315372898553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433398711696210248599035 3650098067544315372898553)
            ·
              refine ⟨2737573550658236529673915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3650098067544315372898553 2737573550658236529673915)
              ·
                refine ⟨4106360325987354794510873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737573550658236529673915 4106360325987354794510873)
                ·
                  refine ⟨3079770244490516095883155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4106360325987354794510873 3079770244490516095883155)
                  ·
                    refine ⟨4619655366735774143824733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3079770244490516095883155 4619655366735774143824733)
                    ·
                      refine ⟨1732370762525915303934275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4619655366735774143824733 1732370762525915303934275)
                      ·
                        rfl

theorem cell23_3373780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_3373780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373780 prefixEnd_3373780 := by exact prefixLift 3373780
  have htrace : WordTrace (prefixWord ++ tailWord_3373780) baseStart_3373780 baseEnd_3373780 := by
    simpa [prefixWord, tailWord_3373780, baseEnd_3373780] using wordTrace_append hprefix tailTrace_3373780
  have hstable : (prefixWord ++ tailWord_3373780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373780).length < 2 ^ (prefixWord ++ tailWord_3373780).sum := by decide
  have hdescent : baseEnd_3373780 < baseStart_3373780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373785 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 1, 5, 3]
def baseStart_3373785 : Nat := 118140960795 + 3373785 * 2 ^ 59
def prefixEnd_3373785 : Nat := 4983230072969 + 3 ^ 40 * 3373785 * 2
def baseEnd_3373785 : Nat := 1732373329929187784371751

theorem tailTrace_3373785 : CollatzResearch.WordTrace tailWord_3373785 prefixEnd_3373785 1732373329929187784371751 := by
  unfold tailWord_3373785
  simp only [CollatzResearch.WordTrace]
  refine ⟨123052048082360616449754809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82034698721573744299836539 123052048082360616449754809)
  ·
    refine ⟨92289036061770462337316107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123052048082360616449754809 92289036061770462337316107)
    ·
      refine ⟨138433554092655693505974161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92289036061770462337316107 138433554092655693505974161)
      ·
        refine ⟨103825165569491770129480621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138433554092655693505974161 103825165569491770129480621)
        ·
          refine ⟨38934437088559413798555233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103825165569491770129480621 38934437088559413798555233)
          ·
            refine ⟨29200827816419560348916425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38934437088559413798555233 29200827816419560348916425)
            ·
              refine ⟨21900620862314670261687319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29200827816419560348916425 21900620862314670261687319)
              ·
                refine ⟨32850931293472005392530979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21900620862314670261687319 32850931293472005392530979)
                ·
                  refine ⟨49276396940208008088796469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32850931293472005392530979 49276396940208008088796469)
                  ·
                    refine ⟨4619662213144500758324669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49276396940208008088796469 4619662213144500758324669)
                    ·
                      refine ⟨1732373329929187784371751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4619662213144500758324669 1732373329929187784371751)
                      ·
                        rfl

theorem cell23_3373785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_3373785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373785 prefixEnd_3373785 := by exact prefixLift 3373785
  have htrace : WordTrace (prefixWord ++ tailWord_3373785) baseStart_3373785 baseEnd_3373785 := by
    simpa [prefixWord, tailWord_3373785, baseEnd_3373785] using wordTrace_append hprefix tailTrace_3373785
  have hstable : (prefixWord ++ tailWord_3373785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373785).length < 2 ^ (prefixWord ++ tailWord_3373785).sum := by decide
  have hdescent : baseEnd_3373785 < baseStart_3373785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373825 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_3373825 : Nat := 118140960795 + 3373825 * 2 ^ 59
def prefixEnd_3373825 : Nat := 4983230072969 + 3 ^ 40 * 3373825 * 2
def baseEnd_3373825 : Nat := 1732393869155367627871567

theorem tailTrace_3373825 : CollatzResearch.WordTrace tailWord_3373825 prefixEnd_3373825 1732393869155367627871567 := by
  unfold tailWord_3373825
  simp only [CollatzResearch.WordTrace]
  refine ⟨123053507002215703281210929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82035671334810468854140619 123053507002215703281210929)
  ·
    refine ⟨92290130251661777460908197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123053507002215703281210929 92290130251661777460908197)
    ·
      refine ⟨17304399422186583273920287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92290130251661777460908197 17304399422186583273920287)
      ·
        refine ⟨25956599133279874910880431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17304399422186583273920287 25956599133279874910880431)
        ·
          refine ⟨38934898699919812366320647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25956599133279874910880431 38934898699919812366320647)
          ·
            refine ⟨58402348049879718549480971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38934898699919812366320647 58402348049879718549480971)
            ·
              refine ⟨87603522074819577824221457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58402348049879718549480971 87603522074819577824221457)
              ·
                refine ⟨65702641556114683368166093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87603522074819577824221457 65702641556114683368166093)
                ·
                  refine ⟨24638490583543006263062285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65702641556114683368166093 24638490583543006263062285)
                  ·
                    refine ⟨9239433968828627348648357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24638490583543006263062285 9239433968828627348648357)
                    ·
                      refine ⟨1732393869155367627871567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9239433968828627348648357 1732393869155367627871567)
                      ·
                        rfl

theorem cell23_3373825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_3373825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373825 prefixEnd_3373825 := by exact prefixLift 3373825
  have htrace : WordTrace (prefixWord ++ tailWord_3373825) baseStart_3373825 baseEnd_3373825 := by
    simpa [prefixWord, tailWord_3373825, baseEnd_3373825] using wordTrace_append hprefix tailTrace_3373825
  have hstable : (prefixWord ++ tailWord_3373825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373825).length < 2 ^ (prefixWord ++ tailWord_3373825).sum := by decide
  have hdescent : baseEnd_3373825 < baseStart_3373825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373826 : List Nat := [3, 4, 1, 1, 1, 2, 4, 2, 5]
def baseStart_3373826 : Nat := 118140960795 + 3373826 * 2 ^ 59
def prefixEnd_3373826 : Nat := 4983230072969 + 3 ^ 40 * 3373826 * 2
def baseEnd_3373826 : Nat := 192488264737335791551007

theorem tailTrace_3373826 : CollatzResearch.WordTrace tailWord_3373826 prefixEnd_3373826 192488264737335791551007 := by
  unfold tailWord_3373826
  simp only [CollatzResearch.WordTrace]
  refine ⟨30763385868803020112999333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82035695650141386967998221 30763385868803020112999333)
  ·
    refine ⟨5768134850400566271187375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30763385868803020112999333 5768134850400566271187375)
    ·
      refine ⟨8652202275600849406781063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5768134850400566271187375 8652202275600849406781063)
      ·
        refine ⟨12978303413401274110171595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8652202275600849406781063 12978303413401274110171595)
        ·
          refine ⟨19467455120101911165257393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12978303413401274110171595 19467455120101911165257393)
          ·
            refine ⟨14600591340076433373943045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19467455120101911165257393 14600591340076433373943045)
            ·
              refine ⟨2737610876264331257614321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14600591340076433373943045 2737610876264331257614321)
              ·
                refine ⟨2053208157198248443210741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2737610876264331257614321 2053208157198248443210741)
                ·
                  refine ⟨192488264737335791551007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2053208157198248443210741 192488264737335791551007)
                  ·
                    rfl

theorem cell23_3373826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_3373826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373826 prefixEnd_3373826 := by exact prefixLift 3373826
  have htrace : WordTrace (prefixWord ++ tailWord_3373826) baseStart_3373826 baseEnd_3373826 := by
    simpa [prefixWord, tailWord_3373826, baseEnd_3373826] using wordTrace_append hprefix tailTrace_3373826
  have hstable : (prefixWord ++ tailWord_3373826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373826).length < 2 ^ (prefixWord ++ tailWord_3373826).sum := by decide
  have hdescent : baseEnd_3373826 < baseStart_3373826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373852 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 5, 4]
def baseStart_3373852 : Nat := 118140960795 + 3373852 * 2 ^ 59
def prefixEnd_3373852 : Nat := 4983230072969 + 3 ^ 40 * 3373852 * 2
def baseEnd_3373852 : Nat := 577469244377679674077981

theorem tailTrace_3373852 : CollatzResearch.WordTrace tailWord_3373852 prefixEnd_3373852 577469244377679674077981 := by
  unfold tailWord_3373852
  simp only [CollatzResearch.WordTrace]
  refine ⟨61527245886558943446221905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82036327848745257928295873 61527245886558943446221905)
  ·
    refine ⟨46145434414919207584666429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61527245886558943446221905 46145434414919207584666429)
    ·
      refine ⟨17304537905594702844249911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46145434414919207584666429 17304537905594702844249911)
      ·
        refine ⟨25956806858392054266374867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17304537905594702844249911 25956806858392054266374867)
        ·
          refine ⟨38935210287588081399562301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25956806858392054266374867 38935210287588081399562301)
          ·
            refine ⟨14600703857845530524835863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38935210287588081399562301 14600703857845530524835863)
            ·
              refine ⟨21901055786768295787253795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14600703857845530524835863 21901055786768295787253795)
              ·
                refine ⟨32851583680152443680880693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21901055786768295787253795 32851583680152443680880693)
                ·
                  refine ⟨3079835970014291595082565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32851583680152443680880693 3079835970014291595082565)
                  ·
                    refine ⟨577469244377679674077981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3079835970014291595082565 577469244377679674077981)
                    ·
                      rfl

theorem cell23_3373852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_3373852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373852 prefixEnd_3373852 := by exact prefixLift 3373852
  have htrace : WordTrace (prefixWord ++ tailWord_3373852) baseStart_3373852 baseEnd_3373852 := by
    simpa [prefixWord, tailWord_3373852, baseEnd_3373852] using wordTrace_append hprefix tailTrace_3373852
  have hstable : (prefixWord ++ tailWord_3373852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373852).length < 2 ^ (prefixWord ++ tailWord_3373852).sum := by decide
  have hdescent : baseEnd_3373852 < baseStart_3373852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373882 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 8]
def baseStart_3373882 : Nat := 118140960795 + 3373882 * 2 ^ 59
def prefixEnd_3373882 : Nat := 4983230072969 + 3 ^ 40 * 3373882 * 2
def baseEnd_3373882 : Nat := 192491459728074878317645

theorem tailTrace_3373882 : CollatzResearch.WordTrace tailWord_3373882 prefixEnd_3373882 192491459728074878317645 := by
  unfold tailWord_3373882
  simp only [CollatzResearch.WordTrace]
  refine ⟨30763896490752300504008975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82037057308672801344023933 30763896490752300504008975)
  ·
    refine ⟨46145844736128450756013463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30763896490752300504008975 46145844736128450756013463)
    ·
      refine ⟨69218767104192676134020195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46145844736128450756013463 69218767104192676134020195)
      ·
        refine ⟨103828150656289014201030293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69218767104192676134020195 103828150656289014201030293)
        ·
          refine ⟨4866944562013547540673295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103828150656289014201030293 4866944562013547540673295)
          ·
            refine ⟨7300416843020321311009943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866944562013547540673295 7300416843020321311009943)
            ·
              refine ⟨10950625264530481966514915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7300416843020321311009943 10950625264530481966514915)
              ·
                refine ⟨16425937896795722949772373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10950625264530481966514915 16425937896795722949772373)
                ·
                  refine ⟨192491459728074878317645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16425937896795722949772373 192491459728074878317645)
                  ·
                    rfl

theorem cell23_3373882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_3373882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373882 prefixEnd_3373882 := by exact prefixLift 3373882
  have htrace : WordTrace (prefixWord ++ tailWord_3373882) baseStart_3373882 baseEnd_3373882 := by
    simpa [prefixWord, tailWord_3373882, baseEnd_3373882] using wordTrace_append hprefix tailTrace_3373882
  have hstable : (prefixWord ++ tailWord_3373882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373882).length < 2 ^ (prefixWord ++ tailWord_3373882).sum := by decide
  have hdescent : baseEnd_3373882 < baseStart_3373882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373886 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_3373886 : Nat := 118140960795 + 3373886 * 2 ^ 59
def prefixEnd_3373886 : Nat := 4983230072969 + 3 ^ 40 * 3373886 * 2
def baseEnd_3373886 : Nat := 577475063825097296402929

theorem tailTrace_3373886 : CollatzResearch.WordTrace tailWord_3373886 prefixEnd_3373886 577475063825097296402929 := by
  unfold tailWord_3373886
  simp only [CollatzResearch.WordTrace]
  refine ⟨15381966481874338837397689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82037154569996473799454341 15381966481874338837397689)
  ·
    refine ⟨11536474861405754128048267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15381966481874338837397689 11536474861405754128048267)
    ·
      refine ⟨17304712292108631192072401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11536474861405754128048267 17304712292108631192072401)
      ·
        refine ⟨12978534219081473394054301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17304712292108631192072401 12978534219081473394054301)
        ·
          refine ⟨4866950332155552522770363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12978534219081473394054301 4866950332155552522770363)
          ·
            refine ⟨7300425498233328784155545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866950332155552522770363 7300425498233328784155545)
            ·
              refine ⟨5475319123674996588116659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7300425498233328784155545 5475319123674996588116659)
              ·
                refine ⟨8212978685512494882174989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475319123674996588116659 8212978685512494882174989)
                ·
                  refine ⟨3079867007067185580815621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8212978685512494882174989 3079867007067185580815621)
                  ·
                    refine ⟨577475063825097296402929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3079867007067185580815621 577475063825097296402929)
                    ·
                      rfl

theorem cell23_3373886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_3373886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373886 prefixEnd_3373886 := by exact prefixLift 3373886
  have htrace : WordTrace (prefixWord ++ tailWord_3373886) baseStart_3373886 baseEnd_3373886 := by
    simpa [prefixWord, tailWord_3373886, baseEnd_3373886] using wordTrace_append hprefix tailTrace_3373886
  have hstable : (prefixWord ++ tailWord_3373886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373886).length < 2 ^ (prefixWord ++ tailWord_3373886).sum := by decide
  have hdescent : baseEnd_3373886 < baseStart_3373886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373909 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_3373909 : Nat := 118140960795 + 3373909 * 2 ^ 59
def prefixEnd_3373909 : Nat := 4983230072969 + 3 ^ 40 * 3373909 * 2
def baseEnd_3373909 : Nat := 1732437001530345299221181

theorem tailTrace_3373909 : CollatzResearch.WordTrace tailWord_3373909 prefixEnd_3373909 1732437001530345299221181 := by
  unfold tailWord_3373909
  simp only [CollatzResearch.WordTrace]
  refine ⟨123056570733911385627268781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82037713822607590418179187 123056570733911385627268781)
  ·
    refine ⟨46146214025216769610225793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123056570733911385627268781 46146214025216769610225793)
    ·
      refine ⟨34609660518912577207669345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46146214025216769610225793 34609660518912577207669345)
      ·
        refine ⟨25957245389184432905752009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34609660518912577207669345 25957245389184432905752009)
        ·
          refine ⟨19467934041888324679314007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25957245389184432905752009 19467934041888324679314007)
          ·
            refine ⟨29201901062832487018971011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19467934041888324679314007 29201901062832487018971011)
            ·
              refine ⟨43802851594248730528456517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29201901062832487018971011 43802851594248730528456517)
              ·
                refine ⟨8213034673921636974085597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43802851594248730528456517 8213034673921636974085597)
                ·
                  refine ⟨3079888002720613865282099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8213034673921636974085597 3079888002720613865282099)
                  ·
                    refine ⟨4619832004080920797923149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3079888002720613865282099 4619832004080920797923149)
                    ·
                      refine ⟨1732437001530345299221181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4619832004080920797923149 1732437001530345299221181)
                      ·
                        rfl

theorem cell23_3373909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_3373909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373909 prefixEnd_3373909 := by exact prefixLift 3373909
  have htrace : WordTrace (prefixWord ++ tailWord_3373909) baseStart_3373909 baseEnd_3373909 := by
    simpa [prefixWord, tailWord_3373909, baseEnd_3373909] using wordTrace_append hprefix tailTrace_3373909
  have hstable : (prefixWord ++ tailWord_3373909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373909).length < 2 ^ (prefixWord ++ tailWord_3373909).sum := by decide
  have hdescent : baseEnd_3373909 < baseStart_3373909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373919 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 2, 3, 2]
def baseStart_3373919 : Nat := 118140960795 + 3373919 * 2 ^ 59
def prefixEnd_3373919 : Nat := 4983230072969 + 3 ^ 40 * 3373919 * 2
def baseEnd_3373919 : Nat := 1732442136336890260096135

theorem tailTrace_3373919 : CollatzResearch.WordTrace tailWord_3373919 prefixEnd_3373919 1732442136336890260096135 := by
  unfold tailWord_3373919
  simp only [CollatzResearch.WordTrace]
  refine ⟨123056935463875157335132811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82037956975916771556755207 123056935463875157335132811)
  ·
    refine ⟨184585403195812736002699217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123056935463875157335132811 184585403195812736002699217)
    ·
      refine ⟨138439052396859552002024413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184585403195812736002699217 138439052396859552002024413)
      ·
        refine ⟨51914644648822332000759155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138439052396859552002024413 51914644648822332000759155)
        ·
          refine ⟨77871966973233498001138733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51914644648822332000759155 77871966973233498001138733)
          ·
            refine ⟨29201987614962561750427025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77871966973233498001138733 29201987614962561750427025)
            ·
              refine ⟨21901490711221921312820269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29201987614962561750427025 21901490711221921312820269)
              ·
                refine ⟨8213059016708220492307601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21901490711221921312820269 8213059016708220492307601)
                ·
                  refine ⟨6159794262531165369230701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8213059016708220492307601 6159794262531165369230701)
                  ·
                    refine ⟨2309922848449187013461513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6159794262531165369230701 2309922848449187013461513)
                    ·
                      refine ⟨1732442136336890260096135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2309922848449187013461513 1732442136336890260096135)
                      ·
                        rfl

theorem cell23_3373919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_3373919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373919 prefixEnd_3373919 := by exact prefixLift 3373919
  have htrace : WordTrace (prefixWord ++ tailWord_3373919) baseStart_3373919 baseEnd_3373919 := by
    simpa [prefixWord, tailWord_3373919, baseEnd_3373919] using wordTrace_append hprefix tailTrace_3373919
  have hstable : (prefixWord ++ tailWord_3373919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373919).length < 2 ^ (prefixWord ++ tailWord_3373919).sum := by decide
  have hdescent : baseEnd_3373919 < baseStart_3373919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373950 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 6]
def baseStart_3373950 : Nat := 118140960795 + 3373950 * 2 ^ 59
def prefixEnd_3373950 : Nat := 4983230072969 + 3 ^ 40 * 3373950 * 2
def baseEnd_3373950 : Nat := 192495339359686626534277

theorem tailTrace_3373950 : CollatzResearch.WordTrace tailWord_3373950 prefixEnd_3373950 192495339359686626534277 := by
  unfold tailWord_3373950
  simp only [CollatzResearch.WordTrace]
  refine ⟨15382258265845356203688913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82038710751175233086340869 15382258265845356203688913)
  ·
    refine ⟨11536693699384017152766685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15382258265845356203688913 11536693699384017152766685)
    ·
      refine ⟨4326260137269006432287507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11536693699384017152766685 4326260137269006432287507)
      ·
        refine ⟨6489390205903509648431261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326260137269006432287507 6489390205903509648431261)
        ·
          refine ⟨2433521327213816118161723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6489390205903509648431261 2433521327213816118161723)
          ·
            refine ⟨3650281990820724177242585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433521327213816118161723 3650281990820724177242585)
            ·
              refine ⟨2737711493115543132931939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3650281990820724177242585 2737711493115543132931939)
              ·
                refine ⟨4106567239673314699397909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737711493115543132931939 4106567239673314699397909)
                ·
                  refine ⟨192495339359686626534277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4106567239673314699397909 192495339359686626534277)
                  ·
                    rfl

theorem cell23_3373950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_3373950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373950 prefixEnd_3373950 := by exact prefixLift 3373950
  have htrace : WordTrace (prefixWord ++ tailWord_3373950) baseStart_3373950 baseEnd_3373950 := by
    simpa [prefixWord, tailWord_3373950, baseEnd_3373950] using wordTrace_append hprefix tailTrace_3373950
  have hstable : (prefixWord ++ tailWord_3373950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373950).length < 2 ^ (prefixWord ++ tailWord_3373950).sum := by decide
  have hdescent : baseEnd_3373950 < baseStart_3373950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373972 : List Nat := [2, 4, 2, 1, 1, 1, 1, 11]
def baseStart_3373972 : Nat := 118140960795 + 3373972 * 2 ^ 59
def prefixEnd_3373972 : Nat := 4983230072969 + 3 ^ 40 * 3373972 * 2
def baseEnd_3373972 : Nat := 64165531511539946397533

theorem tailTrace_3373972 : CollatzResearch.WordTrace tailWord_3373972 prefixEnd_3373972 64165531511539946397533 := by
  unfold tailWord_3373972
  simp only [CollatzResearch.WordTrace]
  refine ⟨61529434266341573693406085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82039245688455431591208113 61529434266341573693406085)
  ·
    refine ⟨11536768924939045067513641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61529434266341573693406085 11536768924939045067513641)
    ·
      refine ⟨8652576693704283800635231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11536768924939045067513641 8652576693704283800635231)
      ·
        refine ⟨12978865040556425700952847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8652576693704283800635231 12978865040556425700952847)
        ·
          refine ⟨19468297560834638551429271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12978865040556425700952847 19468297560834638551429271)
          ·
            refine ⟨29202446341251957827143907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19468297560834638551429271 29202446341251957827143907)
            ·
              refine ⟨43803669511877936740715861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29202446341251957827143907 43803669511877936740715861)
              ·
                refine ⟨64165531511539946397533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 43803669511877936740715861 64165531511539946397533)
                ·
                  rfl

theorem cell23_3373972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 11].length) (baseStart_3373972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373972 prefixEnd_3373972 := by exact prefixLift 3373972
  have htrace : WordTrace (prefixWord ++ tailWord_3373972) baseStart_3373972 baseEnd_3373972 := by
    simpa [prefixWord, tailWord_3373972, baseEnd_3373972] using wordTrace_append hprefix tailTrace_3373972
  have hstable : (prefixWord ++ tailWord_3373972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373972).length < 2 ^ (prefixWord ++ tailWord_3373972).sum := by decide
  have hdescent : baseEnd_3373972 < baseStart_3373972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3373986 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 1, 1, 5]
def baseStart_3373986 : Nat := 118140960795 + 3373986 * 2 ^ 59
def prefixEnd_3373986 : Nat := 4983230072969 + 3 ^ 40 * 3373986 * 2
def baseEnd_3373986 : Nat := 1732476539540741497958327

theorem tailTrace_3373986 : CollatzResearch.WordTrace tailWord_3373986 prefixEnd_3373986 1732476539540741497958327 := by
  unfold tailWord_3373986
  simp only [CollatzResearch.WordTrace]
  refine ⟨30764844788658106944455453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82039586103088285185214541 30764844788658106944455453)
  ·
    refine ⟨11536816795746790104170795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30764844788658106944455453 11536816795746790104170795)
    ·
      refine ⟨17305225193620185156256193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11536816795746790104170795 17305225193620185156256193)
      ·
        refine ⟨12978918895215138867192145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17305225193620185156256193 12978918895215138867192145)
        ·
          refine ⟨9734189171411354150394109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12978918895215138867192145 9734189171411354150394109)
          ·
            refine ⟨3650320939279257806397791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9734189171411354150394109 3650320939279257806397791)
            ·
              refine ⟨5475481408918886709596687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650320939279257806397791 5475481408918886709596687)
              ·
                refine ⟨8213222113378330064395031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475481408918886709596687 8213222113378330064395031)
                ·
                  refine ⟨12319833170067495096592547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8213222113378330064395031 12319833170067495096592547)
                  ·
                    refine ⟨18479749755101242644888821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12319833170067495096592547 18479749755101242644888821)
                    ·
                      refine ⟨1732476539540741497958327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18479749755101242644888821 1732476539540741497958327)
                      ·
                        rfl

theorem cell23_3373986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_3373986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3373986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3373986 prefixEnd_3373986 := by exact prefixLift 3373986
  have htrace : WordTrace (prefixWord ++ tailWord_3373986) baseStart_3373986 baseEnd_3373986 := by
    simpa [prefixWord, tailWord_3373986, baseEnd_3373986] using wordTrace_append hprefix tailTrace_3373986
  have hstable : (prefixWord ++ tailWord_3373986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3373986).length < 2 ^ (prefixWord ++ tailWord_3373986).sum := by decide
  have hdescent : baseEnd_3373986 < baseStart_3373986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3373986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374016 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 2, 1, 3]
def baseStart_3374016 : Nat := 118140960795 + 3374016 * 2 ^ 59
def prefixEnd_3374016 : Nat := 4983230072969 + 3 ^ 40 * 3374016 * 2
def baseEnd_3374016 : Nat := 1732491943960376380583189

theorem tailTrace_3374016 : CollatzResearch.WordTrace tailWord_3374016 prefixEnd_3374016 1732491943960376380583189 := by
  unfold tailWord_3374016
  simp only [CollatzResearch.WordTrace]
  refine ⟨61530236672261871450706951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82040315563015828600942601 61530236672261871450706951)
  ·
    refine ⟨92295355008392807176060427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61530236672261871450706951 92295355008392807176060427)
    ·
      refine ⟨138443032512589210764090641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92295355008392807176060427 138443032512589210764090641)
      ·
        refine ⟨103832274384441908073067981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138443032512589210764090641 103832274384441908073067981)
        ·
          refine ⟨38937102894165715527400493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103832274384441908073067981 38937102894165715527400493)
          ·
            refine ⟨14601413585312143322775185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38937102894165715527400493 14601413585312143322775185)
            ·
              refine ⟨10951060188984107492081389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14601413585312143322775185 10951060188984107492081389)
              ·
                refine ⟨4106647570869040309530521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10951060188984107492081389 4106647570869040309530521)
                ·
                  refine ⟨3079985678151780232147891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4106647570869040309530521 3079985678151780232147891)
                  ·
                    refine ⟨4619978517227670348221837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3079985678151780232147891 4619978517227670348221837)
                    ·
                      refine ⟨1732491943960376380583189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4619978517227670348221837 1732491943960376380583189)
                      ·
                        rfl

theorem cell23_3374016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_3374016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374016 prefixEnd_3374016 := by exact prefixLift 3374016
  have htrace : WordTrace (prefixWord ++ tailWord_3374016) baseStart_3374016 baseEnd_3374016 := by
    simpa [prefixWord, tailWord_3374016, baseEnd_3374016] using wordTrace_append hprefix tailTrace_3374016
  have hstable : (prefixWord ++ tailWord_3374016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374016).length < 2 ^ (prefixWord ++ tailWord_3374016).sum := by decide
  have hdescent : baseEnd_3374016 < baseStart_3374016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374026 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2]
def baseStart_3374026 : Nat := 118140960795 + 3374026 * 2 ^ 59
def prefixEnd_3374026 : Nat := 4983230072969 + 3 ^ 40 * 3374026 * 2
def baseEnd_3374026 : Nat := 1732497078766921341458143

theorem tailTrace_3374026 : CollatzResearch.WordTrace tailWord_3374026 prefixEnd_3374026 1732497078766921341458143 := by
  unfold tailWord_3374026
  simp only [CollatzResearch.WordTrace]
  refine ⟨30765209518621878652319483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82040558716325009739518621 30765209518621878652319483)
  ·
    refine ⟨46147814277932817978479225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30765209518621878652319483 46147814277932817978479225)
    ·
      refine ⟨34610860708449613483859419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46147814277932817978479225 34610860708449613483859419)
      ·
        refine ⟨51916291062674420225789129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34610860708449613483859419 51916291062674420225789129)
        ·
          refine ⟨38937218297005815169341847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51916291062674420225789129 38937218297005815169341847)
          ·
            refine ⟨58405827445508722754012771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38937218297005815169341847 58405827445508722754012771)
            ·
              refine ⟨87608741168263084131019157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58405827445508722754012771 87608741168263084131019157)
              ·
                refine ⟨4106659742262332068641523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87608741168263084131019157 4106659742262332068641523)
                ·
                  refine ⟨6159989613393498102962285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106659742262332068641523 6159989613393498102962285)
                  ·
                    refine ⟨2309996105022561788610857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6159989613393498102962285 2309996105022561788610857)
                    ·
                      refine ⟨1732497078766921341458143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2309996105022561788610857 1732497078766921341458143)
                      ·
                        rfl

theorem cell23_3374026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_3374026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374026 prefixEnd_3374026 := by exact prefixLift 3374026
  have htrace : WordTrace (prefixWord ++ tailWord_3374026) baseStart_3374026 baseEnd_3374026 := by
    simpa [prefixWord, tailWord_3374026, baseEnd_3374026] using wordTrace_append hprefix tailTrace_3374026
  have hstable : (prefixWord ++ tailWord_3374026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374026).length < 2 ^ (prefixWord ++ tailWord_3374026).sum := by decide
  have hdescent : baseEnd_3374026 < baseStart_3374026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374039 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 3, 4, 2]
def baseStart_3374039 : Nat := 118140960795 + 3374039 * 2 ^ 59
def prefixEnd_3374039 : Nat := 4983230072969 + 3 ^ 40 * 3374039 * 2
def baseEnd_3374039 : Nat := 1732503754015429790595583

theorem tailTrace_3374039 : CollatzResearch.WordTrace tailWord_3374039 prefixEnd_3374039 1732503754015429790595583 := by
  unfold tailWord_3374039
  simp only [CollatzResearch.WordTrace]
  refine ⟨123061312223440417829501171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82040874815626945219667447 123061312223440417829501171)
  ·
    refine ⟨184591968335160626744251757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123061312223440417829501171 184591968335160626744251757)
    ·
      refine ⟨69221988125685235029094409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184591968335160626744251757 69221988125685235029094409)
      ·
        refine ⟨51916491094263926271820807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69221988125685235029094409 51916491094263926271820807)
        ·
          refine ⟨77874736641395889407731211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51916491094263926271820807 77874736641395889407731211)
          ·
            refine ⟨116812104962093834111596817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77874736641395889407731211 116812104962093834111596817)
            ·
              refine ⟨87609078721570375583697613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116812104962093834111596817 87609078721570375583697613)
              ·
                refine ⟨32853404520588890843886605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87609078721570375583697613 32853404520588890843886605)
                ·
                  refine ⟨12320026695220834066457477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32853404520588890843886605 12320026695220834066457477)
                  ·
                    refine ⟨2310005005353906387460777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12320026695220834066457477 2310005005353906387460777)
                    ·
                      refine ⟨1732503754015429790595583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310005005353906387460777 1732503754015429790595583)
                      ·
                        rfl

theorem cell23_3374039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_3374039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374039 prefixEnd_3374039 := by exact prefixLift 3374039
  have htrace : WordTrace (prefixWord ++ tailWord_3374039) baseStart_3374039 baseEnd_3374039 := by
    simpa [prefixWord, tailWord_3374039, baseEnd_3374039] using wordTrace_append hprefix tailTrace_3374039
  have hstable : (prefixWord ++ tailWord_3374039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374039).length < 2 ^ (prefixWord ++ tailWord_3374039).sum := by decide
  have hdescent : baseEnd_3374039 < baseStart_3374039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374050 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 2, 1, 3]
def baseStart_3374050 : Nat := 118140960795 + 3374050 * 2 ^ 59
def prefixEnd_3374050 : Nat := 4983230072969 + 3 ^ 40 * 3374050 * 2
def baseEnd_3374050 : Nat := 1732509402302629247558033

theorem tailTrace_3374050 : CollatzResearch.WordTrace tailWord_3374050 prefixEnd_3374050 1732509402302629247558033 := by
  unfold tailWord_3374050
  simp only [CollatzResearch.WordTrace]
  refine ⟨30765428356600141677037901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82041142284267044472101069 30765428356600141677037901)
  ·
    refine ⟨11537035633725053128889213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30765428356600141677037901 11537035633725053128889213)
    ·
      refine ⟨4326388362646894923333455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11537035633725053128889213 4326388362646894923333455)
      ·
        refine ⟨6489582543970342385000183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326388362646894923333455 6489582543970342385000183)
        ·
          refine ⟨9734373815955513577500275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6489582543970342385000183 9734373815955513577500275)
          ·
            refine ⟨14601560723933270366250413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734373815955513577500275 14601560723933270366250413)
            ·
              refine ⟨5475585271474976387343905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14601560723933270366250413 5475585271474976387343905)
              ·
                refine ⟨4106688953606232290507929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5475585271474976387343905 4106688953606232290507929)
                ·
                  refine ⟨3080016715204674217880947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4106688953606232290507929 3080016715204674217880947)
                  ·
                    refine ⟨4620025072807011326821421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3080016715204674217880947 4620025072807011326821421)
                    ·
                      refine ⟨1732509402302629247558033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4620025072807011326821421 1732509402302629247558033)
                      ·
                        rfl

theorem cell23_3374050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_3374050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374050 prefixEnd_3374050 := by exact prefixLift 3374050
  have htrace : WordTrace (prefixWord ++ tailWord_3374050) baseStart_3374050 baseEnd_3374050 := by
    simpa [prefixWord, tailWord_3374050, baseEnd_3374050] using wordTrace_append hprefix tailTrace_3374050
  have hstable : (prefixWord ++ tailWord_3374050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374050).length < 2 ^ (prefixWord ++ tailWord_3374050).sum := by decide
  have hdescent : baseEnd_3374050 < baseStart_3374050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374099 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 1, 7, 2]
def baseStart_3374099 : Nat := 118140960795 + 3374099 * 2 ^ 59
def prefixEnd_3374099 : Nat := 4983230072969 + 3 ^ 40 * 3374099 * 2
def baseEnd_3374099 : Nat := 1732534562854699555845307

theorem tailTrace_3374099 : CollatzResearch.WordTrace tailWord_3374099 prefixEnd_3374099 1732534562854699555845307 := by
  unfold tailWord_3374099
  simp only [CollatzResearch.WordTrace]
  refine ⟨123063500603223048076685351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82042333735482032051123567 123063500603223048076685351)
  ·
    refine ⟨184595250904834572115028027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123063500603223048076685351 184595250904834572115028027)
    ·
      refine ⟨276892876357251858172542041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184595250904834572115028027 276892876357251858172542041)
      ·
        refine ⟨207669657267938893629406531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276892876357251858172542041 207669657267938893629406531)
        ·
          refine ⟨311504485901908340444109797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207669657267938893629406531 311504485901908340444109797)
          ·
            refine ⟨58407091106607813833270587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311504485901908340444109797 58407091106607813833270587)
            ·
              refine ⟨87610636659911720749905881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58407091106607813833270587 87610636659911720749905881)
              ·
                refine ⟨65707977494933790562429411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87610636659911720749905881 65707977494933790562429411)
                ·
                  refine ⟨98561966242400685843644117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65707977494933790562429411 98561966242400685843644117)
                  ·
                    refine ⟨2310046083806266074460409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 98561966242400685843644117 2310046083806266074460409)
                    ·
                      refine ⟨1732534562854699555845307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310046083806266074460409 1732534562854699555845307)
                      ·
                        rfl

theorem cell23_3374099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 7, 2].length) (baseStart_3374099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374099 prefixEnd_3374099 := by exact prefixLift 3374099
  have htrace : WordTrace (prefixWord ++ tailWord_3374099) baseStart_3374099 baseEnd_3374099 := by
    simpa [prefixWord, tailWord_3374099, baseEnd_3374099] using wordTrace_append hprefix tailTrace_3374099
  have hstable : (prefixWord ++ tailWord_3374099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374099).length < 2 ^ (prefixWord ++ tailWord_3374099).sum := by decide
  have hdescent : baseEnd_3374099 < baseStart_3374099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374113 : List Nat := [1, 2, 3, 2, 3, 2, 3, 2, 5]
def baseStart_3374113 : Nat := 118140960795 + 3374113 * 2 ^ 59
def prefixEnd_3374113 : Nat := 4983230072969 + 3 ^ 40 * 3374113 * 2
def baseEnd_3374113 : Nat := 192504639064873611230027

theorem tailTrace_3374113 : CollatzResearch.WordTrace tailWord_3374113 prefixEnd_3374113 192504639064873611230027 := by
  unfold tailWord_3374113
  simp only [CollatzResearch.WordTrace]
  refine ⟨123064011225172328467694993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82042674150114885645129995 123064011225172328467694993)
  ·
    refine ⟨92298008418879246350771245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123064011225172328467694993 92298008418879246350771245)
    ·
      refine ⟨34611753157079717381539217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92298008418879246350771245 34611753157079717381539217)
      ·
        refine ⟨25958814867809788036154413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34611753157079717381539217 25958814867809788036154413)
        ·
          refine ⟨9734555575428670513557905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25958814867809788036154413 9734555575428670513557905)
          ·
            refine ⟨7300916681571502885168429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9734555575428670513557905 7300916681571502885168429)
            ·
              refine ⟨2737843755589313581938161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7300916681571502885168429 2737843755589313581938161)
              ·
                refine ⟨2053382816691985186453621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2737843755589313581938161 2053382816691985186453621)
                ·
                  refine ⟨192504639064873611230027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2053382816691985186453621 192504639064873611230027)
                  ·
                    rfl

theorem cell23_3374113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 5].length) (baseStart_3374113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374113 prefixEnd_3374113 := by exact prefixLift 3374113
  have htrace : WordTrace (prefixWord ++ tailWord_3374113) baseStart_3374113 baseEnd_3374113 := by
    simpa [prefixWord, tailWord_3374113, baseEnd_3374113] using wordTrace_append hprefix tailTrace_3374113
  have hstable : (prefixWord ++ tailWord_3374113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374113).length < 2 ^ (prefixWord ++ tailWord_3374113).sum := by decide
  have hdescent : baseEnd_3374113 < baseStart_3374113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374129 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3374129 : Nat := 118140960795 + 3374129 * 2 ^ 59
def prefixEnd_3374129 : Nat := 4983230072969 + 3 ^ 40 * 3374129 * 2
def baseEnd_3374129 : Nat := 1732549967274334438470169

theorem tailTrace_3374129 : CollatzResearch.WordTrace tailWord_3374129 prefixEnd_3374129 1732549967274334438470169 := by
  unfold tailWord_3374129
  simp only [CollatzResearch.WordTrace]
  refine ⟨123064594793114363200277441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82043063195409575466851627 123064594793114363200277441)
  ·
    refine ⟨92298446094835772400208081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123064594793114363200277441 92298446094835772400208081)
    ·
      refine ⟨69223834571126829300156061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92298446094835772400208081 69223834571126829300156061)
      ·
        refine ⟨25958937964172560987558523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69223834571126829300156061 25958937964172560987558523)
        ·
          refine ⟨38938406946258841481337785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25958937964172560987558523 38938406946258841481337785)
          ·
            refine ⟨29203805209694131111003339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38938406946258841481337785 29203805209694131111003339)
            ·
              refine ⟨43805707814541196666505009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29203805209694131111003339 43805707814541196666505009)
              ·
                refine ⟨32854280860905897499878757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43805707814541196666505009 32854280860905897499878757)
                ·
                  refine ⟨6160177661419855781227267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32854280860905897499878757 6160177661419855781227267)
                  ·
                    refine ⟨9240266492129783671840901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6160177661419855781227267 9240266492129783671840901)
                    ·
                      refine ⟨1732549967274334438470169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9240266492129783671840901 1732549967274334438470169)
                      ·
                        rfl

theorem cell23_3374129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3374129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374129 prefixEnd_3374129 := by exact prefixLift 3374129
  have htrace : WordTrace (prefixWord ++ tailWord_3374129) baseStart_3374129 baseEnd_3374129 := by
    simpa [prefixWord, tailWord_3374129, baseEnd_3374129] using wordTrace_append hprefix tailTrace_3374129
  have hstable : (prefixWord ++ tailWord_3374129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374129).length < 2 ^ (prefixWord ++ tailWord_3374129).sum := by decide
  have hdescent : baseEnd_3374129 < baseStart_3374129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374149 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 1, 4, 3]
def baseStart_3374149 : Nat := 118140960795 + 3374149 * 2 ^ 59
def prefixEnd_3374149 : Nat := 4983230072969 + 3 ^ 40 * 3374149 * 2
def baseEnd_3374149 : Nat := 1732560236887424360220077

theorem tailTrace_3374149 : CollatzResearch.WordTrace tailWord_3374149 prefixEnd_3374149 1732560236887424360220077 := by
  unfold tailWord_3374149
  simp only [CollatzResearch.WordTrace]
  refine ⟨123065324253041906616005501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82043549502027937744003667 123065324253041906616005501)
  ·
    refine ⟨46149496594890714981002063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123065324253041906616005501 46149496594890714981002063)
    ·
      refine ⟨69224244892336072471503095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46149496594890714981002063 69224244892336072471503095)
      ·
        refine ⟨103836367338504108707254643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69224244892336072471503095 103836367338504108707254643)
        ·
          refine ⟨155754551007756163060881965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103836367338504108707254643 155754551007756163060881965)
          ·
            refine ⟨58407956627908561147830737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155754551007756163060881965 58407956627908561147830737)
            ·
              refine ⟨43805967470931420860873053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58407956627908561147830737 43805967470931420860873053)
              ·
                refine ⟨16427237801599282822827395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43805967470931420860873053 16427237801599282822827395)
                ·
                  refine ⟨24640856702398924234241093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16427237801599282822827395 24640856702398924234241093)
                  ·
                    refine ⟨4620160631699798293920205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24640856702398924234241093 4620160631699798293920205)
                    ·
                      refine ⟨1732560236887424360220077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4620160631699798293920205 1732560236887424360220077)
                      ·
                        rfl

theorem cell23_3374149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_3374149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374149 prefixEnd_3374149 := by exact prefixLift 3374149
  have htrace : WordTrace (prefixWord ++ tailWord_3374149) baseStart_3374149 baseEnd_3374149 := by
    simpa [prefixWord, tailWord_3374149, baseEnd_3374149] using wordTrace_append hprefix tailTrace_3374149
  have hstable : (prefixWord ++ tailWord_3374149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374149).length < 2 ^ (prefixWord ++ tailWord_3374149).sum := by decide
  have hdescent : baseEnd_3374149 < baseStart_3374149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374179 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 3]
def baseStart_3374179 : Nat := 118140960795 + 3374179 * 2 ^ 59
def prefixEnd_3374179 : Nat := 4983230072969 + 3 ^ 40 * 3374179 * 2
def baseEnd_3374179 : Nat := 1732575641307059242844939

theorem tailTrace_3374179 : CollatzResearch.WordTrace tailWord_3374179 prefixEnd_3374179 1732575641307059242844939 := by
  unfold tailWord_3374179
  simp only [CollatzResearch.WordTrace]
  refine ⟨123066418442933221739597591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82044278961955481159731727 123066418442933221739597591)
  ·
    refine ⟨184599627664399832609396387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123066418442933221739597591 184599627664399832609396387)
    ·
      refine ⟨276899441496599748914094581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184599627664399832609396387 276899441496599748914094581)
      ·
        refine ⟨25959322640306226460696367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276899441496599748914094581 25959322640306226460696367)
        ·
          refine ⟨38938983960459339691044551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25959322640306226460696367 38938983960459339691044551)
          ·
            refine ⟨58408475940689009536566827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38938983960459339691044551 58408475940689009536566827)
            ·
              refine ⟨87612713911033514304850241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58408475940689009536566827 87612713911033514304850241)
              ·
                refine ⟨65709535433275135728637681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87612713911033514304850241 65709535433275135728637681)
                ·
                  refine ⟨49282151574956351796478261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65709535433275135728637681 49282151574956351796478261)
                  ·
                    refine ⟨4620201710152157980919837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49282151574956351796478261 4620201710152157980919837)
                    ·
                      refine ⟨1732575641307059242844939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4620201710152157980919837 1732575641307059242844939)
                      ·
                        rfl

theorem cell23_3374179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_3374179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374179 prefixEnd_3374179 := by exact prefixLift 3374179
  have htrace : WordTrace (prefixWord ++ tailWord_3374179) baseStart_3374179 baseEnd_3374179 := by
    simpa [prefixWord, tailWord_3374179, baseEnd_3374179] using wordTrace_append hprefix tailTrace_3374179
  have hstable : (prefixWord ++ tailWord_3374179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374179).length < 2 ^ (prefixWord ++ tailWord_3374179).sum := by decide
  have hdescent : baseEnd_3374179 < baseStart_3374179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374186 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 6]
def baseStart_3374186 : Nat := 118140960795 + 3374186 * 2 ^ 59
def prefixEnd_3374186 : Nat := 4983230072969 + 3 ^ 40 * 3374186 * 2
def baseEnd_3374186 : Nat := 192508803963515635050823

theorem tailTrace_3374186 : CollatzResearch.WordTrace tailWord_3374186 prefixEnd_3374186 192508803963515635050823 := by
  unfold tailWord_3374186
  simp only [CollatzResearch.WordTrace]
  refine ⟨30766668438476965483775603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82044449169271907956734941 30766668438476965483775603)
  ·
    refine ⟨46150002657715448225663405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30766668438476965483775603 46150002657715448225663405)
    ·
      refine ⟨17306250996643293084623777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46150002657715448225663405 17306250996643293084623777)
      ·
        refine ⟨12979688247482469813467833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17306250996643293084623777 12979688247482469813467833)
        ·
          refine ⟨9734766185611852360100875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12979688247482469813467833 9734766185611852360100875)
          ·
            refine ⟨14602149278417778540151313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9734766185611852360100875 14602149278417778540151313)
            ·
              refine ⟨10951611958813333905113485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14602149278417778540151313 10951611958813333905113485)
              ·
                refine ⟨4106854484555000214417557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10951611958813333905113485 4106854484555000214417557)
                ·
                  refine ⟨192508803963515635050823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4106854484555000214417557 192508803963515635050823)
                  ·
                    rfl

theorem cell23_3374186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_3374186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374186 prefixEnd_3374186 := by exact prefixLift 3374186
  have htrace : WordTrace (prefixWord ++ tailWord_3374186) baseStart_3374186 baseEnd_3374186 := by
    simpa [prefixWord, tailWord_3374186, baseEnd_3374186] using wordTrace_append hprefix tailTrace_3374186
  have hstable : (prefixWord ++ tailWord_3374186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374186).length < 2 ^ (prefixWord ++ tailWord_3374186).sum := by decide
  have hdescent : baseEnd_3374186 < baseStart_3374186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374197 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3374197 : Nat := 118140960795 + 3374197 * 2 ^ 59
def prefixEnd_3374197 : Nat := 4983230072969 + 3 ^ 40 * 3374197 * 2
def baseEnd_3374197 : Nat := 1732584883958840172419857

theorem tailTrace_3374197 : CollatzResearch.WordTrace tailWord_3374197 prefixEnd_3374197 1732584883958840172419857 := by
  unfold tailWord_3374197
  simp only [CollatzResearch.WordTrace]
  refine ⟨123067074956868010813752845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82044716637912007209168563 123067074956868010813752845)
  ·
    refine ⟨46150153108825504055157317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123067074956868010813752845 46150153108825504055157317)
    ·
      refine ⟨8653153707904782010341997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46150153108825504055157317 8653153707904782010341997)
      ·
        refine ⟨3244932640464293253878249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8653153707904782010341997 3244932640464293253878249)
        ·
          refine ⟨2433699480348219940408687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3244932640464293253878249 2433699480348219940408687)
          ·
            refine ⟨3650549220522329910613031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433699480348219940408687 3650549220522329910613031)
            ·
              refine ⟨5475823830783494865919547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650549220522329910613031 5475823830783494865919547)
              ·
                refine ⟨8213735746175242298879321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475823830783494865919547 8213735746175242298879321)
                ·
                  refine ⟨6160301809631431724159491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8213735746175242298879321 6160301809631431724159491)
                  ·
                    refine ⟨9240452714447147586239237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6160301809631431724159491 9240452714447147586239237)
                    ·
                      refine ⟨1732584883958840172419857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9240452714447147586239237 1732584883958840172419857)
                      ·
                        rfl

theorem cell23_3374197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3374197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374197 prefixEnd_3374197 := by exact prefixLift 3374197
  have htrace : WordTrace (prefixWord ++ tailWord_3374197) baseStart_3374197 baseEnd_3374197 := by
    simpa [prefixWord, tailWord_3374197, baseEnd_3374197] using wordTrace_append hprefix tailTrace_3374197
  have hstable : (prefixWord ++ tailWord_3374197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374197).length < 2 ^ (prefixWord ++ tailWord_3374197).sum := by decide
  have hdescent : baseEnd_3374197 < baseStart_3374197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374199 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 3, 5]
def baseStart_3374199 : Nat := 118140960795 + 3374199 * 2 ^ 59
def prefixEnd_3374199 : Nat := 4983230072969 + 3 ^ 40 * 3374199 * 2
def baseEnd_3374199 : Nat := 577528636973383054864949

theorem tailTrace_3374199 : CollatzResearch.WordTrace tailWord_3374199 prefixEnd_3374199 577528636973383054864949 := by
  unfold tailWord_3374199
  simp only [CollatzResearch.WordTrace]
  refine ⟨123067147902860765155325651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82044765268573843436883767 123067147902860765155325651)
  ·
    refine ⟨184600721854291147732988477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123067147902860765155325651 184600721854291147732988477)
    ·
      refine ⟨69225270695359180399870679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184600721854291147732988477 69225270695359180399870679)
      ·
        refine ⟨103837906043038770599806019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69225270695359180399870679 103837906043038770599806019)
        ·
          refine ⟨155756859064558155899709029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103837906043038770599806019 155756859064558155899709029)
          ·
            refine ⟨29204411074604654231195443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155756859064558155899709029 29204411074604654231195443)
            ·
              refine ⟨43806616611906981346793165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29204411074604654231195443 43806616611906981346793165)
              ·
                refine ⟨16427481229465118005047437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43806616611906981346793165 16427481229465118005047437)
                ·
                  refine ⟨6160305461049419251892789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16427481229465118005047437 6160305461049419251892789)
                  ·
                    refine ⟨577528636973383054864949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6160305461049419251892789 577528636973383054864949)
                    ·
                      rfl

theorem cell23_3374199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_3374199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374199 prefixEnd_3374199 := by exact prefixLift 3374199
  have htrace : WordTrace (prefixWord ++ tailWord_3374199) baseStart_3374199 baseEnd_3374199 := by
    simpa [prefixWord, tailWord_3374199, baseEnd_3374199] using wordTrace_append hprefix tailTrace_3374199
  have hstable : (prefixWord ++ tailWord_3374199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374199).length < 2 ^ (prefixWord ++ tailWord_3374199).sum := by decide
  have hdescent : baseEnd_3374199 < baseStart_3374199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374249 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 4]
def baseStart_3374249 : Nat := 118140960795 + 3374249 * 2 ^ 59
def prefixEnd_3374249 : Nat := 4983230072969 + 3 ^ 40 * 3374249 * 2
def baseEnd_3374249 : Nat := 1732611584952873968969617

theorem tailTrace_3374249 : CollatzResearch.WordTrace tailWord_3374249 prefixEnd_3374249 1732611584952873968969617 := by
  unfold tailWord_3374249
  simp only [CollatzResearch.WordTrace]
  refine ⟨123068971552679623694645801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82045981035119749129763867 123068971552679623694645801)
  ·
    refine ⟨92301728664509717770984351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123068971552679623694645801 92301728664509717770984351)
    ·
      refine ⟨138452592996764576656476527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92301728664509717770984351 138452592996764576656476527)
      ·
        refine ⟨207678889495146864984714791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138452592996764576656476527 207678889495146864984714791)
        ·
          refine ⟨311518334242720297477072187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207678889495146864984714791 311518334242720297477072187)
          ·
            refine ⟨467277501364080446215608281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311518334242720297477072187 467277501364080446215608281)
            ·
              refine ⟨350458126023060334661706211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467277501364080446215608281 350458126023060334661706211)
              ·
                refine ⟨525687189034590501992559317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350458126023060334661706211 525687189034590501992559317)
                ·
                  refine ⟨12320793492998214890450609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 525687189034590501992559317 12320793492998214890450609)
                  ·
                    refine ⟨9240595119748661167837957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12320793492998214890450609 9240595119748661167837957)
                    ·
                      refine ⟨1732611584952873968969617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9240595119748661167837957 1732611584952873968969617)
                      ·
                        rfl

theorem cell23_3374249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_3374249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374249 prefixEnd_3374249 := by exact prefixLift 3374249
  have htrace : WordTrace (prefixWord ++ tailWord_3374249) baseStart_3374249 baseEnd_3374249 := by
    simpa [prefixWord, tailWord_3374249, baseEnd_3374249] using wordTrace_append hprefix tailTrace_3374249
  have hstable : (prefixWord ++ tailWord_3374249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374249).length < 2 ^ (prefixWord ++ tailWord_3374249).sum := by decide
  have hdescent : baseEnd_3374249 < baseStart_3374249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374250 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 1, 5]
def baseStart_3374250 : Nat := 118140960795 + 3374250 * 2 ^ 59
def prefixEnd_3374250 : Nat := 4983230072969 + 3 ^ 40 * 3374250 * 2
def baseEnd_3374250 : Nat := 577537366144509488352371

theorem tailTrace_3374250 : CollatzResearch.WordTrace tailWord_3374250 prefixEnd_3374250 577537366144509488352371 := by
  unfold tailWord_3374250
  simp only [CollatzResearch.WordTrace]
  refine ⟨30767252006419000216358051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82046005350450667243621469 30767252006419000216358051)
  ·
    refine ⟨46150878009628500324537077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30767252006419000216358051 46150878009628500324537077)
    ·
      refine ⟨4326644813402671905425351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46150878009628500324537077 4326644813402671905425351)
      ·
        refine ⟨6489967220104007858138027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326644813402671905425351 6489967220104007858138027)
        ·
          refine ⟨9734950830156011787207041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6489967220104007858138027 9734950830156011787207041)
          ·
            refine ⟨7301213122617008840405281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9734950830156011787207041 7301213122617008840405281)
            ·
              refine ⟨5475909841962756630303961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7301213122617008840405281 5475909841962756630303961)
              ·
                refine ⟨4106932381472067472727971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5475909841962756630303961 4106932381472067472727971)
                ·
                  refine ⟨6160398572208101209091957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106932381472067472727971 6160398572208101209091957)
                  ·
                    refine ⟨577537366144509488352371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6160398572208101209091957 577537366144509488352371)
                    ·
                      rfl

theorem cell23_3374250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_3374250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374250 prefixEnd_3374250 := by exact prefixLift 3374250
  have htrace : WordTrace (prefixWord ++ tailWord_3374250) baseStart_3374250 baseEnd_3374250 := by
    simpa [prefixWord, tailWord_3374250, baseEnd_3374250] using wordTrace_append hprefix tailTrace_3374250
  have hstable : (prefixWord ++ tailWord_3374250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374250).length < 2 ^ (prefixWord ++ tailWord_3374250).sum := by decide
  have hdescent : baseEnd_3374250 < baseStart_3374250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374273 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3374273 : Nat := 118140960795 + 3374273 * 2 ^ 59
def prefixEnd_3374273 : Nat := 4983230072969 + 3 ^ 40 * 3374273 * 2
def baseEnd_3374273 : Nat := 1732623908488581875069507

theorem tailTrace_3374273 : CollatzResearch.WordTrace tailWord_3374273 prefixEnd_3374273 1732623908488581875069507 := by
  unfold tailWord_3374273
  simp only [CollatzResearch.WordTrace]
  refine ⟨123069846904592675793519473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82046564603061783862346315 123069846904592675793519473)
  ·
    refine ⟨92302385178444506845139605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123069846904592675793519473 92302385178444506845139605)
    ·
      refine ⟨4326674305239586258365919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92302385178444506845139605 4326674305239586258365919)
      ·
        refine ⟨6490011457859379387548879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326674305239586258365919 6490011457859379387548879)
        ·
          refine ⟨9735017186789069081323319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6490011457859379387548879 9735017186789069081323319)
          ·
            refine ⟨14602525780183603621984979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9735017186789069081323319 14602525780183603621984979)
            ·
              refine ⟨21903788670275405432977469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14602525780183603621984979 21903788670275405432977469)
              ·
                refine ⟨8213920751353277037366551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21903788670275405432977469 8213920751353277037366551)
                ·
                  refine ⟨12320881127029915556049827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8213920751353277037366551 12320881127029915556049827)
                  ·
                    refine ⟨18481321690544873334074741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12320881127029915556049827 18481321690544873334074741)
                    ·
                      refine ⟨1732623908488581875069507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18481321690544873334074741 1732623908488581875069507)
                      ·
                        rfl

theorem cell23_3374273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3374273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374273 prefixEnd_3374273 := by exact prefixLift 3374273
  have htrace : WordTrace (prefixWord ++ tailWord_3374273) baseStart_3374273 baseEnd_3374273 := by
    simpa [prefixWord, tailWord_3374273, baseEnd_3374273] using wordTrace_append hprefix tailTrace_3374273
  have hstable : (prefixWord ++ tailWord_3374273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374273).length < 2 ^ (prefixWord ++ tailWord_3374273).sum := by decide
  have hdescent : baseEnd_3374273 < baseStart_3374273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374274 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_3374274 : Nat := 118140960795 + 3374274 * 2 ^ 59
def prefixEnd_3374274 : Nat := 4983230072969 + 3 ^ 40 * 3374274 * 2
def baseEnd_3374274 : Nat := 1732624421969236371157003

theorem tailTrace_3374274 : CollatzResearch.WordTrace tailWord_3374274 prefixEnd_3374274 1732624421969236371157003 := by
  unfold tailWord_3374274
  simp only [CollatzResearch.WordTrace]
  refine ⟨30767470844397263241076469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82046588918392701976203917 30767470844397263241076469)
  ·
    refine ⟨2884450391662243428850919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30767470844397263241076469 2884450391662243428850919)
    ·
      refine ⟨4326675587493365143276379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2884450391662243428850919 4326675587493365143276379)
      ·
        refine ⟨6490013381240047714914569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326675587493365143276379 6490013381240047714914569)
        ·
          refine ⟨4867510035930035786185927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6490013381240047714914569 4867510035930035786185927)
          ·
            refine ⟨7301265053895053679278891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4867510035930035786185927 7301265053895053679278891)
            ·
              refine ⟨10951897580842580518918337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7301265053895053679278891 10951897580842580518918337)
              ·
                refine ⟨8213923185631935389188753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10951897580842580518918337 8213923185631935389188753)
                ·
                  refine ⟨6160442389223951541891565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8213923185631935389188753 6160442389223951541891565)
                  ·
                    refine ⟨2310165895958981828209337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6160442389223951541891565 2310165895958981828209337)
                    ·
                      refine ⟨1732624421969236371157003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310165895958981828209337 1732624421969236371157003)
                      ·
                        rfl

theorem cell23_3374274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_3374274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374274 prefixEnd_3374274 := by exact prefixLift 3374274
  have htrace : WordTrace (prefixWord ++ tailWord_3374274) baseStart_3374274 baseEnd_3374274 := by
    simpa [prefixWord, tailWord_3374274, baseEnd_3374274] using wordTrace_append hprefix tailTrace_3374274
  have hstable : (prefixWord ++ tailWord_3374274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374274).length < 2 ^ (prefixWord ++ tailWord_3374274).sum := by decide
  have hdescent : baseEnd_3374274 < baseStart_3374274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374289 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 2, 7]
def baseStart_3374289 : Nat := 118140960795 + 3374289 * 2 ^ 59
def prefixEnd_3374289 : Nat := 4983230072969 + 3 ^ 40 * 3374289 * 2
def baseEnd_3374289 : Nat := 577544041393017937489811

theorem tailTrace_3374289 : CollatzResearch.WordTrace tailWord_3374289 prefixEnd_3374289 577544041393017937489811 := by
  unfold tailWord_3374289
  simp only [CollatzResearch.WordTrace]
  refine ⟨123070430472534710526101921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82046953648356473684067947 123070430472534710526101921)
  ·
    refine ⟨92302822854401032894576441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123070430472534710526101921 92302822854401032894576441)
    ·
      refine ⟨69227117140800774670932331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92302822854401032894576441 69227117140800774670932331)
      ·
        refine ⟨103840675711201162006398497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69227117140800774670932331 103840675711201162006398497)
        ·
          refine ⟨77880506783400871504798873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103840675711201162006398497 77880506783400871504798873)
          ·
            refine ⟨58410380087550653628599155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77880506783400871504798873 58410380087550653628599155)
            ·
              refine ⟨87615570131325980442898733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58410380087550653628599155 87615570131325980442898733)
              ·
                refine ⟨32855838799247242666087025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87615570131325980442898733 32855838799247242666087025)
                ·
                  refine ⟨24641879099435431999565269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32855838799247242666087025 24641879099435431999565269)
                  ·
                    refine ⟨577544041393017937489811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24641879099435431999565269 577544041393017937489811)
                    ·
                      rfl

theorem cell23_3374289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_3374289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374289 prefixEnd_3374289 := by exact prefixLift 3374289
  have htrace : WordTrace (prefixWord ++ tailWord_3374289) baseStart_3374289 baseEnd_3374289 := by
    simpa [prefixWord, tailWord_3374289, baseEnd_3374289] using wordTrace_append hprefix tailTrace_3374289
  have hstable : (prefixWord ++ tailWord_3374289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374289).length < 2 ^ (prefixWord ++ tailWord_3374289).sum := by decide
  have hdescent : baseEnd_3374289 < baseStart_3374289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374324 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3374324 : Nat := 118140960795 + 3374324 * 2 ^ 59
def prefixEnd_3374324 : Nat := 4983230072969 + 3 ^ 40 * 3374324 * 2
def baseEnd_3374324 : Nat := 1732650096001961175531773

theorem tailTrace_3374324 : CollatzResearch.WordTrace tailWord_3374324 prefixEnd_3374324 1732650096001961175531773 := by
  unfold tailWord_3374324
  simp only [CollatzResearch.WordTrace]
  refine ⟨61535853513703955751813013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82047804684938607669084017 61535853513703955751813013)
  ·
    refine ⟨2884493133454872925866235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61535853513703955751813013 2884493133454872925866235)
    ·
      refine ⟨4326739700182309388799353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2884493133454872925866235 4326739700182309388799353)
      ·
        refine ⟨3245054775136732041599515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4326739700182309388799353 3245054775136732041599515)
        ·
          refine ⟨4867582162705098062399273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3245054775136732041599515 4867582162705098062399273)
          ·
            refine ⟨3650686622028823546799455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4867582162705098062399273 3650686622028823546799455)
            ·
              refine ⟨5476029933043235320199183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650686622028823546799455 5476029933043235320199183)
              ·
                refine ⟨8214044899564852980298775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5476029933043235320199183 8214044899564852980298775)
                ·
                  refine ⟨12321067349347279470448163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8214044899564852980298775 12321067349347279470448163)
                  ·
                    refine ⟨18481601024020919205672245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12321067349347279470448163 18481601024020919205672245)
                    ·
                      refine ⟨1732650096001961175531773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18481601024020919205672245 1732650096001961175531773)
                      ·
                        rfl

theorem cell23_3374324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3374324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374324 prefixEnd_3374324 := by exact prefixLift 3374324
  have htrace : WordTrace (prefixWord ++ tailWord_3374324) baseStart_3374324 baseEnd_3374324 := by
    simpa [prefixWord, tailWord_3374324, baseEnd_3374324] using wordTrace_append hprefix tailTrace_3374324
  have hstable : (prefixWord ++ tailWord_3374324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374324).length < 2 ^ (prefixWord ++ tailWord_3374324).sum := by decide
  have hdescent : baseEnd_3374324 < baseStart_3374324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374338 : List Nat := [3, 4, 1, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_3374338 : Nat := 118140960795 + 3374338 * 2 ^ 59
def prefixEnd_3374338 : Nat := 4983230072969 + 3 ^ 40 * 3374338 * 2
def baseEnd_3374338 : Nat := 1732657284731124120756709

theorem tailTrace_3374338 : CollatzResearch.WordTrace tailWord_3374338 prefixEnd_3374338 1732657284731124120756709 := by
  unfold tailWord_3374338
  simp only [CollatzResearch.WordTrace]
  refine ⟨30768054412339297973658917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82048145099571461263090445 30768054412339297973658917)
  ·
    refine ⟨5769010202313618370061047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30768054412339297973658917 5769010202313618370061047)
    ·
      refine ⟨8653515303470427555091571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5769010202313618370061047 8653515303470427555091571)
      ·
        refine ⟨12980272955205641332637357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8653515303470427555091571 12980272955205641332637357)
        ·
          refine ⟨4867602358202115499739009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12980272955205641332637357 4867602358202115499739009)
          ·
            refine ⟨3650701768651586624804257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4867602358202115499739009 3650701768651586624804257)
            ·
              refine ⟨2738026326488689968603193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3650701768651586624804257 2738026326488689968603193)
              ·
                refine ⟨2053519744866517476452395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2738026326488689968603193 2053519744866517476452395)
                ·
                  refine ⟨3080279617299776214678593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2053519744866517476452395 3080279617299776214678593)
                  ·
                    refine ⟨2310209712974832161008945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3080279617299776214678593 2310209712974832161008945)
                    ·
                      refine ⟨1732657284731124120756709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310209712974832161008945 1732657284731124120756709)
                      ·
                        rfl

theorem cell23_3374338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_3374338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374338 prefixEnd_3374338 := by exact prefixLift 3374338
  have htrace : WordTrace (prefixWord ++ tailWord_3374338) baseStart_3374338 baseEnd_3374338 := by
    simpa [prefixWord, tailWord_3374338, baseEnd_3374338] using wordTrace_append hprefix tailTrace_3374338
  have hstable : (prefixWord ++ tailWord_3374338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374338).length < 2 ^ (prefixWord ++ tailWord_3374338).sum := by decide
  have hdescent : baseEnd_3374338 < baseStart_3374338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374360 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 1, 4, 2]
def baseStart_3374360 : Nat := 118140960795 + 3374360 * 2 ^ 59
def prefixEnd_3374360 : Nat := 4983230072969 + 3 ^ 40 * 3374360 * 2
def baseEnd_3374360 : Nat := 1732668581305523034681607

theorem tailTrace_3374360 : CollatzResearch.WordTrace tailWord_3374360 prefixEnd_3374360 1732668581305523034681607 := by
  unfold tailWord_3374360
  simp only [CollatzResearch.WordTrace]
  refine ⟨61536510027638744825968267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82048680036851659767957689 61536510027638744825968267)
  ·
    refine ⟨92304765041458117238952401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61536510027638744825968267 92304765041458117238952401)
    ·
      refine ⟨69228573781093587929214301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92304765041458117238952401 69228573781093587929214301)
      ·
        refine ⟨25960715167910095473455363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69228573781093587929214301 25960715167910095473455363)
        ·
          refine ⟨38941072751865143210183045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25960715167910095473455363 38941072751865143210183045)
          ·
            refine ⟨7301451140974714351909321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38941072751865143210183045 7301451140974714351909321)
            ·
              refine ⟨5476088355731035763931991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7301451140974714351909321 5476088355731035763931991)
              ·
                refine ⟨8214132533596553645897987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5476088355731035763931991 8214132533596553645897987)
                ·
                  refine ⟨12321198800394830468846981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8214132533596553645897987 12321198800394830468846981)
                  ·
                    refine ⟨2310224775074030712908809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12321198800394830468846981 2310224775074030712908809)
                    ·
                      refine ⟨1732668581305523034681607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310224775074030712908809 1732668581305523034681607)
                      ·
                        rfl

theorem cell23_3374360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_3374360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374360 prefixEnd_3374360 := by exact prefixLift 3374360
  have htrace : WordTrace (prefixWord ++ tailWord_3374360) baseStart_3374360 baseEnd_3374360 := by
    simpa [prefixWord, tailWord_3374360, baseEnd_3374360] using wordTrace_append hprefix tailTrace_3374360
  have hstable : (prefixWord ++ tailWord_3374360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374360).length < 2 ^ (prefixWord ++ tailWord_3374360).sum := by decide
  have hdescent : baseEnd_3374360 < baseStart_3374360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374381 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_3374381 : Nat := 118140960795 + 3374381 * 2 ^ 59
def prefixEnd_3374381 : Nat := 4983230072969 + 3 ^ 40 * 3374381 * 2
def baseEnd_3374381 : Nat := 1732679364399267452519011

theorem tailTrace_3374381 : CollatzResearch.WordTrace tailWord_3374381 prefixEnd_3374381 1732679364399267452519011 := by
  unfold tailWord_3374381
  simp only [CollatzResearch.WordTrace]
  refine ⟨123073785988201410238450997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82049190658800940158967331 123073785988201410238450997)
  ·
    refine ⟨11538167436393882209854781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123073785988201410238450997 11538167436393882209854781)
    ·
      refine ⟨4326812788647705828695543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11538167436393882209854781 4326812788647705828695543)
      ·
        refine ⟨6490219182971558743043315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326812788647705828695543 6490219182971558743043315)
        ·
          refine ⟨9735328774457338114564973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6490219182971558743043315 9735328774457338114564973)
          ·
            refine ⟨3650748290421501792961865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9735328774457338114564973 3650748290421501792961865)
            ·
              refine ⟨2738061217816126344721399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3650748290421501792961865 2738061217816126344721399)
              ·
                refine ⟨4107091826724189517082099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2738061217816126344721399 4107091826724189517082099)
                ·
                  refine ⟨6160637740086284275623149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107091826724189517082099 6160637740086284275623149)
                  ·
                    refine ⟨2310239152532356603358681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6160637740086284275623149 2310239152532356603358681)
                    ·
                      refine ⟨1732679364399267452519011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310239152532356603358681 1732679364399267452519011)
                      ·
                        rfl

theorem cell23_3374381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_3374381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374381 prefixEnd_3374381 := by exact prefixLift 3374381
  have htrace : WordTrace (prefixWord ++ tailWord_3374381) baseStart_3374381 baseEnd_3374381 := by
    simpa [prefixWord, tailWord_3374381, baseEnd_3374381] using wordTrace_append hprefix tailTrace_3374381
  have hstable : (prefixWord ++ tailWord_3374381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374381).length < 2 ^ (prefixWord ++ tailWord_3374381).sum := by decide
  have hdescent : baseEnd_3374381 < baseStart_3374381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374416 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 4]
def baseStart_3374416 : Nat := 118140960795 + 3374416 * 2 ^ 59
def prefixEnd_3374416 : Nat := 4983230072969 + 3 ^ 40 * 3374416 * 2
def baseEnd_3374416 : Nat := 1732697336222174815581349

theorem tailTrace_3374416 : CollatzResearch.WordTrace tailWord_3374416 prefixEnd_3374416 1732697336222174815581349 := by
  unfold tailWord_3374416
  simp only [CollatzResearch.WordTrace]
  refine ⟨61537531271537305607987551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82050041695383074143983401 61537531271537305607987551)
  ·
    refine ⟨92306296907305958411981327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61537531271537305607987551 92306296907305958411981327)
    ·
      refine ⟨138459445360958937617971991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92306296907305958411981327 138459445360958937617971991)
      ·
        refine ⟨207689168041438406426957987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138459445360958937617971991 207689168041438406426957987)
        ·
          refine ⟨311533752062157609640436981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207689168041438406426957987 311533752062157609640436981)
          ·
            refine ⟨29206289255827275903790967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 311533752062157609640436981 29206289255827275903790967)
            ·
              refine ⟨43809433883740913855686451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29206289255827275903790967 43809433883740913855686451)
              ·
                refine ⟨65714150825611370783529677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43809433883740913855686451 65714150825611370783529677)
                ·
                  refine ⟨24642806559604264043823629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65714150825611370783529677 24642806559604264043823629)
                  ·
                    refine ⟨9241052459851599016433861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24642806559604264043823629 9241052459851599016433861)
                    ·
                      refine ⟨1732697336222174815581349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9241052459851599016433861 1732697336222174815581349)
                      ·
                        rfl

theorem cell23_3374416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_3374416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374416 prefixEnd_3374416 := by exact prefixLift 3374416
  have htrace : WordTrace (prefixWord ++ tailWord_3374416) baseStart_3374416 baseEnd_3374416 := by
    simpa [prefixWord, tailWord_3374416, baseEnd_3374416] using wordTrace_append hprefix tailTrace_3374416
  have hstable : (prefixWord ++ tailWord_3374416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374416).length < 2 ^ (prefixWord ++ tailWord_3374416).sum := by decide
  have hdescent : baseEnd_3374416 < baseStart_3374416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374433 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 1, 6, 2]
def baseStart_3374433 : Nat := 118140960795 + 3374433 * 2 ^ 59
def prefixEnd_3374433 : Nat := 4983230072969 + 3 ^ 40 * 3374433 * 2
def baseEnd_3374433 : Nat := 1732706065393301249068771

theorem tailTrace_3374433 : CollatzResearch.WordTrace tailWord_3374433 prefixEnd_3374433 1732706065393301249068771 := by
  unfold tailWord_3374433
  simp only [CollatzResearch.WordTrace]
  refine ⟨123075682584013023119343953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82050455056008682079562635 123075682584013023119343953)
  ·
    refine ⟨92306761938009767339507965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123075682584013023119343953 92306761938009767339507965)
    ·
      refine ⟨34615035726753662752315487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92306761938009767339507965 34615035726753662752315487)
      ·
        refine ⟨51922553590130494128473231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34615035726753662752315487 51922553590130494128473231)
        ·
          refine ⟨77883830385195741192709847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51922553590130494128473231 77883830385195741192709847)
          ·
            refine ⟨116825745577793611789064771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77883830385195741192709847 116825745577793611789064771)
            ·
              refine ⟨175238618366690417683597157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116825745577793611789064771 175238618366690417683597157)
              ·
                refine ⟨32857240943754453315674467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175238618366690417683597157 32857240943754453315674467)
                ·
                  refine ⟨49285861415631679973511701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32857240943754453315674467 49285861415631679973511701)
                  ·
                    refine ⟨2310274753857734998758361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49285861415631679973511701 2310274753857734998758361)
                    ·
                      refine ⟨1732706065393301249068771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310274753857734998758361 1732706065393301249068771)
                      ·
                        rfl

theorem cell23_3374433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_3374433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374433 prefixEnd_3374433 := by exact prefixLift 3374433
  have htrace : WordTrace (prefixWord ++ tailWord_3374433) baseStart_3374433 baseEnd_3374433 := by
    simpa [prefixWord, tailWord_3374433, baseEnd_3374433] using wordTrace_append hprefix tailTrace_3374433
  have hstable : (prefixWord ++ tailWord_3374433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374433).length < 2 ^ (prefixWord ++ tailWord_3374433).sum := by decide
  have hdescent : baseEnd_3374433 < baseStart_3374433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374540 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3374540 : Nat := 118140960795 + 3374540 * 2 ^ 59
def prefixEnd_3374540 : Nat := 4983230072969 + 3 ^ 40 * 3374540 * 2
def baseEnd_3374540 : Nat := 1732761007823332330430779

theorem tailTrace_3374540 : CollatzResearch.WordTrace tailWord_3374540 prefixEnd_3374540 1732761007823332330430779 := by
  unfold tailWord_3374540
  simp only [CollatzResearch.WordTrace]
  refine ⟨61539792597312690196744537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82053056796416920262326049 61539792597312690196744537)
  ·
    refine ⟨46154844447984517647558403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61539792597312690196744537 46154844447984517647558403)
    ·
      refine ⟨69232266671976776471337605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46154844447984517647558403 69232266671976776471337605)
      ·
        refine ⟨12981050000995645588375801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69232266671976776471337605 12981050000995645588375801)
        ·
          refine ⟨9735787500746734191281851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12981050000995645588375801 9735787500746734191281851)
          ·
            refine ⟨14603681251120101286922777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9735787500746734191281851 14603681251120101286922777)
            ·
              refine ⟨10952760938340075965192083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14603681251120101286922777 10952760938340075965192083)
              ·
                refine ⟨16429141407510113947788125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10952760938340075965192083 16429141407510113947788125)
                ·
                  refine ⟨6160928027816292730420547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16429141407510113947788125 6160928027816292730420547)
                  ·
                    refine ⟨9241392041724439095630821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6160928027816292730420547 9241392041724439095630821)
                    ·
                      refine ⟨1732761007823332330430779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9241392041724439095630821 1732761007823332330430779)
                      ·
                        rfl

theorem cell23_3374540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3374540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374540 prefixEnd_3374540 := by exact prefixLift 3374540
  have htrace : WordTrace (prefixWord ++ tailWord_3374540) baseStart_3374540 baseEnd_3374540 := by
    simpa [prefixWord, tailWord_3374540, baseEnd_3374540] using wordTrace_append hprefix tailTrace_3374540
  have hstable : (prefixWord ++ tailWord_3374540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374540).length < 2 ^ (prefixWord ++ tailWord_3374540).sum := by decide
  have hdescent : baseEnd_3374540 < baseStart_3374540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374557 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_3374557 : Nat := 118140960795 + 3374557 * 2 ^ 59
def prefixEnd_3374557 : Nat := 4983230072969 + 3 ^ 40 * 3374557 * 2
def baseEnd_3374557 : Nat := 1732769736994458763918201

theorem tailTrace_3374557 : CollatzResearch.WordTrace tailWord_3374557 prefixEnd_3374557 1732769736994458763918201 := by
  unfold tailWord_3374557
  simp only [CollatzResearch.WordTrace]
  refine ⟨123080205235563792296857925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82053470157042528197905283 123080205235563792296857925)
  ·
    refine ⟨23077538481668211055660861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123080205235563792296857925 23077538481668211055660861)
    ·
      refine ⟨8654076930625579145872823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23077538481668211055660861 8654076930625579145872823)
      ·
        refine ⟨12981115395938368718809235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8654076930625579145872823 12981115395938368718809235)
        ·
          refine ⟨19471673093907553078213853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12981115395938368718809235 19471673093907553078213853)
          ·
            refine ⟨7301877410215332404330195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19471673093907553078213853 7301877410215332404330195)
            ·
              refine ⟨10952816115322998606495293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7301877410215332404330195 10952816115322998606495293)
              ·
                refine ⟨4107306043246124477435735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10952816115322998606495293 4107306043246124477435735)
                ·
                  refine ⟨6160959064869186716153603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107306043246124477435735 6160959064869186716153603)
                  ·
                    refine ⟨9241438597303780074230405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6160959064869186716153603 9241438597303780074230405)
                    ·
                      refine ⟨1732769736994458763918201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9241438597303780074230405 1732769736994458763918201)
                      ·
                        rfl

theorem cell23_3374557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_3374557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374557 prefixEnd_3374557 := by exact prefixLift 3374557
  have htrace : WordTrace (prefixWord ++ tailWord_3374557) baseStart_3374557 baseEnd_3374557 := by
    simpa [prefixWord, tailWord_3374557, baseEnd_3374557] using wordTrace_append hprefix tailTrace_3374557
  have hstable : (prefixWord ++ tailWord_3374557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374557).length < 2 ^ (prefixWord ++ tailWord_3374557).sum := by decide
  have hdescent : baseEnd_3374557 < baseStart_3374557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374563 : List Nat := [1, 1, 1, 6, 2, 2, 10]
def baseStart_3374563 : Nat := 118140960795 + 3374563 * 2 ^ 59
def prefixEnd_3374563 : Nat := 4983230072969 + 3 ^ 40 * 3374563 * 2
def baseEnd_3374563 : Nat := 21392257010844268400533

theorem tailTrace_3374563 : CollatzResearch.WordTrace tailWord_3374563 prefixEnd_3374563 21392257010844268400533 := by
  unfold tailWord_3374563
  simp only [CollatzResearch.WordTrace]
  refine ⟨123080424073542055321576343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82053616049028036881050895 123080424073542055321576343)
  ·
    refine ⟨184620636110313082982364515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123080424073542055321576343 184620636110313082982364515)
    ·
      refine ⟨276930954165469624473546773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184620636110313082982364515 276930954165469624473546773)
      ·
        refine ⟨12981138476506388647197505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 276930954165469624473546773 12981138476506388647197505)
        ·
          refine ⟨9735853857379791485398129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12981138476506388647197505 9735853857379791485398129)
          ·
            refine ⟨7301890393034843614048597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9735853857379791485398129 7301890393034843614048597)
            ·
              refine ⟨21392257010844268400533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7301890393034843614048597 21392257010844268400533)
              ·
                rfl

theorem cell23_3374563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 10].length) (baseStart_3374563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374563 prefixEnd_3374563 := by exact prefixLift 3374563
  have htrace : WordTrace (prefixWord ++ tailWord_3374563) baseStart_3374563 baseEnd_3374563 := by
    simpa [prefixWord, tailWord_3374563, baseEnd_3374563] using wordTrace_append hprefix tailTrace_3374563
  have hstable : (prefixWord ++ tailWord_3374563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374563).length < 2 ^ (prefixWord ++ tailWord_3374563).sum := by decide
  have hdescent : baseEnd_3374563 < baseStart_3374563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374567 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 2, 4]
def baseStart_3374567 : Nat := 118140960795 + 3374567 * 2 ^ 59
def prefixEnd_3374567 : Nat := 4983230072969 + 3 ^ 40 * 3374567 * 2
def baseEnd_3374567 : Nat := 577591623933667908264385

theorem tailTrace_3374567 : CollatzResearch.WordTrace tailWord_3374567 prefixEnd_3374567 577591623933667908264385 := by
  unfold tailWord_3374567
  simp only [CollatzResearch.WordTrace]
  refine ⟨123080569965527564004721955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82053713310351709336481303 123080569965527564004721955)
  ·
    refine ⟨184620854948291346007082933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123080569965527564004721955 184620854948291346007082933)
    ·
      refine ⟨17308205151402313688164025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184620854948291346007082933 17308205151402313688164025)
      ·
        refine ⟨12981153863551735266123019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17308205151402313688164025 12981153863551735266123019)
        ·
          refine ⟨19471730795327602899184529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12981153863551735266123019 19471730795327602899184529)
          ·
            refine ⟨14603798096495702174388397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19471730795327602899184529 14603798096495702174388397)
            ·
              refine ⟨5476424286185888315395649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14603798096495702174388397 5476424286185888315395649)
              ·
                refine ⟨4107318214639416236546737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5476424286185888315395649 4107318214639416236546737)
                ·
                  refine ⟨3080488660979562177410053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4107318214639416236546737 3080488660979562177410053)
                  ·
                    refine ⟨577591623933667908264385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3080488660979562177410053 577591623933667908264385)
                    ·
                      rfl

theorem cell23_3374567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_3374567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374567 prefixEnd_3374567 := by exact prefixLift 3374567
  have htrace : WordTrace (prefixWord ++ tailWord_3374567) baseStart_3374567 baseEnd_3374567 := by
    simpa [prefixWord, tailWord_3374567, baseEnd_3374567] using wordTrace_append hprefix tailTrace_3374567
  have hstable : (prefixWord ++ tailWord_3374567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374567).length < 2 ^ (prefixWord ++ tailWord_3374567).sum := by decide
  have hdescent : baseEnd_3374567 < baseStart_3374567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374574 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2]
def baseStart_3374574 : Nat := 118140960795 + 3374574 * 2 ^ 59
def prefixEnd_3374574 : Nat := 4983230072969 + 3 ^ 40 * 3374574 * 2
def baseEnd_3374574 : Nat := 1732778466165585197405623

theorem tailTrace_3374574 : CollatzResearch.WordTrace tailWord_3374574 prefixEnd_3374574 1732778466165585197405623 := by
  unfold tailWord_3374574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15385103159562775525028347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82053883517668136133484517 15385103159562775525028347)
  ·
    refine ⟨23077654739344163287542521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15385103159562775525028347 23077654739344163287542521)
    ·
      refine ⟨17308241054508122465656891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23077654739344163287542521 17308241054508122465656891)
      ·
        refine ⟨25962361581762183698485337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17308241054508122465656891 25962361581762183698485337)
        ·
          refine ⟨19471771186321637773864003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25962361581762183698485337 19471771186321637773864003)
          ·
            refine ⟨29207656779482456660796005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19471771186321637773864003 29207656779482456660796005)
            ·
              refine ⟨5476435646152960623899251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29207656779482456660796005 5476435646152960623899251)
              ·
                refine ⟨8214653469229440935848877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5476435646152960623899251 8214653469229440935848877)
                ·
                  refine ⟨3080495050961040350943329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8214653469229440935848877 3080495050961040350943329)
                  ·
                    refine ⟨2310371288220780263207497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3080495050961040350943329 2310371288220780263207497)
                    ·
                      refine ⟨1732778466165585197405623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310371288220780263207497 1732778466165585197405623)
                      ·
                        rfl

theorem cell23_3374574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_3374574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374574 prefixEnd_3374574 := by exact prefixLift 3374574
  have htrace : WordTrace (prefixWord ++ tailWord_3374574) baseStart_3374574 baseEnd_3374574 := by
    simpa [prefixWord, tailWord_3374574, baseEnd_3374574] using wordTrace_append hprefix tailTrace_3374574
  have hstable : (prefixWord ++ tailWord_3374574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374574).length < 2 ^ (prefixWord ++ tailWord_3374574).sum := by decide
  have hdescent : baseEnd_3374574 < baseStart_3374574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374594 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_3374594 : Nat := 118140960795 + 3374594 * 2 ^ 59
def prefixEnd_3374594 : Nat := 4983230072969 + 3 ^ 40 * 3374594 * 2
def baseEnd_3374594 : Nat := 1732788735778675119155531

theorem tailTrace_3374594 : CollatzResearch.WordTrace tailWord_3374594 prefixEnd_3374594 1732788735778675119155531 := by
  unfold tailWord_3374594
  simp only [CollatzResearch.WordTrace]
  refine ⟨30770388684107436903988709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82054369824286498410636557 30770388684107436903988709)
  ·
    refine ⟨5769447878270144419497883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30770388684107436903988709 5769447878270144419497883)
    ·
      refine ⟨8654171817405216629246825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5769447878270144419497883 8654171817405216629246825)
      ·
        refine ⟨6490628863053912471935119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8654171817405216629246825 6490628863053912471935119)
        ·
          refine ⟨9735943294580868707902679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6490628863053912471935119 9735943294580868707902679)
          ·
            refine ⟨14603914941871303061854019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9735943294580868707902679 14603914941871303061854019)
            ·
              refine ⟨21905872412806954592781029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14603914941871303061854019 21905872412806954592781029)
              ·
                refine ⟨4107351077401303986146443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21905872412806954592781029 4107351077401303986146443)
                ·
                  refine ⟨6161026616101955979219665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107351077401303986146443 6161026616101955979219665)
                  ·
                    refine ⟨4620769962076466984414749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6161026616101955979219665 4620769962076466984414749)
                    ·
                      refine ⟨1732788735778675119155531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4620769962076466984414749 1732788735778675119155531)
                      ·
                        rfl

theorem cell23_3374594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_3374594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374594 prefixEnd_3374594 := by exact prefixLift 3374594
  have htrace : WordTrace (prefixWord ++ tailWord_3374594) baseStart_3374594 baseEnd_3374594 := by
    simpa [prefixWord, tailWord_3374594, baseEnd_3374594] using wordTrace_append hprefix tailTrace_3374594
  have hstable : (prefixWord ++ tailWord_3374594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374594).length < 2 ^ (prefixWord ++ tailWord_3374594).sum := by decide
  have hdescent : baseEnd_3374594 < baseStart_3374594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374623 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 4, 6]
def baseStart_3374623 : Nat := 118140960795 + 3374623 * 2 ^ 59
def prefixEnd_3374623 : Nat := 4983230072969 + 3 ^ 40 * 3374623 * 2
def baseEnd_3374623 : Nat := 577601208905885168564299

theorem tailTrace_3374623 : CollatzResearch.WordTrace tailWord_3374623 prefixEnd_3374623 577601208905885168564299 := by
  unfold tailWord_3374623
  simp only [CollatzResearch.WordTrace]
  refine ⟨123082612453324685568760523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82055074968883123712507015 123082612453324685568760523)
  ·
    refine ⟨184623918679987028353140785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123082612453324685568760523 184623918679987028353140785)
    ·
      refine ⟨138467939009990271264855589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184623918679987028353140785 138467939009990271264855589)
      ·
        refine ⟨25962738564373175862160423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138467939009990271264855589 25962738564373175862160423)
        ·
          refine ⟨38944107846559763793240635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25962738564373175862160423 38944107846559763793240635)
          ·
            refine ⟨58416161769839645689860953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38944107846559763793240635 58416161769839645689860953)
            ·
              refine ⟨43812121327379734267395715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58416161769839645689860953 43812121327379734267395715)
              ·
                refine ⟨65718181991069601401093573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43812121327379734267395715 65718181991069601401093573)
                ·
                  refine ⟨12322159123325550262705045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65718181991069601401093573 12322159123325550262705045)
                  ·
                    refine ⟨577601208905885168564299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12322159123325550262705045 577601208905885168564299)
                    ·
                      rfl

theorem cell23_3374623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_3374623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374623 prefixEnd_3374623 := by exact prefixLift 3374623
  have htrace : WordTrace (prefixWord ++ tailWord_3374623) baseStart_3374623 baseEnd_3374623 := by
    simpa [prefixWord, tailWord_3374623, baseEnd_3374623] using wordTrace_append hprefix tailTrace_3374623
  have hstable : (prefixWord ++ tailWord_3374623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374623).length < 2 ^ (prefixWord ++ tailWord_3374623).sum := by decide
  have hdescent : baseEnd_3374623 < baseStart_3374623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374680 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 2, 3, 3]
def baseStart_3374680 : Nat := 118140960795 + 3374680 * 2 ^ 59
def prefixEnd_3374680 : Nat := 4983230072969 + 3 ^ 40 * 3374680 * 2
def baseEnd_3374680 : Nat := 1732832895114961782680135

theorem tailTrace_3374680 : CollatzResearch.WordTrace tailWord_3374680 prefixEnd_3374680 1732832895114961782680135 := by
  unfold tailWord_3374680
  simp only [CollatzResearch.WordTrace]
  refine ⟨61542345707059092151792747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82056460942745456202390329 61542345707059092151792747)
  ·
    refine ⟨92313518560588638227689121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61542345707059092151792747 92313518560588638227689121)
    ·
      refine ⟨69235138920441478670766841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92313518560588638227689121 69235138920441478670766841)
      ·
        refine ⟨51926354190331109003075131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69235138920441478670766841 51926354190331109003075131)
        ·
          refine ⟨77889531285496663504612697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51926354190331109003075131 77889531285496663504612697)
          ·
            refine ⟨58417148464122497628459523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77889531285496663504612697 58417148464122497628459523)
            ·
              refine ⟨87625722696183746442689285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58417148464122497628459523 87625722696183746442689285)
              ·
                refine ⟨16429823005534452458004241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87625722696183746442689285 16429823005534452458004241)
                ·
                  refine ⟨12322367254150839343503181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16429823005534452458004241 12322367254150839343503181)
                  ·
                    refine ⟨4620887720306564753813693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12322367254150839343503181 4620887720306564753813693)
                    ·
                      refine ⟨1732832895114961782680135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4620887720306564753813693 1732832895114961782680135)
                      ·
                        rfl

theorem cell23_3374680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_3374680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374680 prefixEnd_3374680 := by exact prefixLift 3374680
  have htrace : WordTrace (prefixWord ++ tailWord_3374680) baseStart_3374680 baseEnd_3374680 := by
    simpa [prefixWord, tailWord_3374680, baseEnd_3374680] using wordTrace_append hprefix tailTrace_3374680
  have hstable : (prefixWord ++ tailWord_3374680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374680).length < 2 ^ (prefixWord ++ tailWord_3374680).sum := by decide
  have hdescent : baseEnd_3374680 < baseStart_3374680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374717 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_3374717 : Nat := 118140960795 + 3374717 * 2 ^ 59
def prefixEnd_3374717 : Nat := 4983230072969 + 3 ^ 40 * 3374717 * 2
def baseEnd_3374717 : Nat := 577617297966392712639155

theorem tailTrace_3374717 : CollatzResearch.WordTrace tailWord_3374717 prefixEnd_3374717 577617297966392712639155 := by
  unfold tailWord_3374717
  simp only [CollatzResearch.WordTrace]
  refine ⟨123086040914984139622682405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82057360609989426415121603 123086040914984139622682405)
  ·
    refine ⟨23078632671559526179252951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123086040914984139622682405 23078632671559526179252951)
    ·
      refine ⟨34617949007339289268879427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23078632671559526179252951 34617949007339289268879427)
      ·
        refine ⟨51926923511008933903319141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34617949007339289268879427 51926923511008933903319141)
        ·
          refine ⟨9736298158314175106872339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51926923511008933903319141 9736298158314175106872339)
          ·
            refine ⟨14604447237471262660308509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9736298158314175106872339 14604447237471262660308509)
            ·
              refine ⟨5476667714051723497615691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14604447237471262660308509 5476667714051723497615691)
              ·
                refine ⟨8215001571077585246423537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5476667714051723497615691 8215001571077585246423537)
                ·
                  refine ⟨6161251178308188934817653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8215001571077585246423537 6161251178308188934817653)
                  ·
                    refine ⟨577617297966392712639155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6161251178308188934817653 577617297966392712639155)
                    ·
                      rfl

theorem cell23_3374717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_3374717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374717 prefixEnd_3374717 := by exact prefixLift 3374717
  have htrace : WordTrace (prefixWord ++ tailWord_3374717) baseStart_3374717 baseEnd_3374717 := by
    simpa [prefixWord, tailWord_3374717, baseEnd_3374717] using wordTrace_append hprefix tailTrace_3374717
  have hstable : (prefixWord ++ tailWord_3374717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374717).length < 2 ^ (prefixWord ++ tailWord_3374717).sum := by decide
  have hdescent : baseEnd_3374717 < baseStart_3374717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374720 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 4]
def baseStart_3374720 : Nat := 118140960795 + 3374720 * 2 ^ 59
def prefixEnd_3374720 : Nat := 4983230072969 + 3 ^ 40 * 3374720 * 2
def baseEnd_3374720 : Nat := 1732853434341141626179951

theorem tailTrace_3374720 : CollatzResearch.WordTrace tailWord_3374720 prefixEnd_3374720 1732853434341141626179951 := by
  unfold tailWord_3374720
  simp only [CollatzResearch.WordTrace]
  refine ⟨61543075166986635567520807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82057433555982180756694409 61543075166986635567520807)
  ·
    refine ⟨92314612750479953351281211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61543075166986635567520807 92314612750479953351281211)
    ·
      refine ⟨138471919125719930026921817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92314612750479953351281211 138471919125719930026921817)
      ·
        refine ⟨103853939344289947520191363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138471919125719930026921817 103853939344289947520191363)
        ·
          refine ⟨155780909016434921280287045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103853939344289947520191363 155780909016434921280287045)
          ·
            refine ⟨29208920440581547740053821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155780909016434921280287045 29208920440581547740053821)
            ·
              refine ⟨10953345165218080402520183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29208920440581547740053821 10953345165218080402520183)
              ·
                refine ⟨16430017747827120603780275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10953345165218080402520183 16430017747827120603780275)
                ·
                  refine ⟨24645026621740680905670413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16430017747827120603780275 24645026621740680905670413)
                  ·
                    refine ⟨9241884983152755339626405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24645026621740680905670413 9241884983152755339626405)
                    ·
                      refine ⟨1732853434341141626179951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9241884983152755339626405 1732853434341141626179951)
                      ·
                        rfl

theorem cell23_3374720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_3374720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374720 prefixEnd_3374720 := by exact prefixLift 3374720
  have htrace : WordTrace (prefixWord ++ tailWord_3374720) baseStart_3374720 baseEnd_3374720 := by
    simpa [prefixWord, tailWord_3374720, baseEnd_3374720] using wordTrace_append hprefix tailTrace_3374720
  have hstable : (prefixWord ++ tailWord_3374720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374720).length < 2 ^ (prefixWord ++ tailWord_3374720).sum := by decide
  have hdescent : baseEnd_3374720 < baseStart_3374720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374824 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 1, 5]
def baseStart_3374824 : Nat := 118140960795 + 3374824 * 2 ^ 59
def prefixEnd_3374824 : Nat := 4983230072969 + 3 ^ 40 * 3374824 * 2
def baseEnd_3374824 : Nat := 577635612109736406426491

theorem tailTrace_3374824 : CollatzResearch.WordTrace tailWord_3374824 prefixEnd_3374824 577635612109736406426491 := by
  unfold tailWord_3374824
  simp only [CollatzResearch.WordTrace]
  refine ⟨61544971762798248448413763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82059962350397664597885017 61544971762798248448413763)
  ·
    refine ⟨92317457644197372672620645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61544971762798248448413763 92317457644197372672620645)
    ·
      refine ⟨17309523308287007376116371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92317457644197372672620645 17309523308287007376116371)
      ·
        refine ⟨25964284962430511064174557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17309523308287007376116371 25964284962430511064174557)
        ·
          refine ⟨9736606860911441649065459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25964284962430511064174557 9736606860911441649065459)
          ·
            refine ⟨14604910291367162473598189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9736606860911441649065459 14604910291367162473598189)
            ·
              refine ⟨5476841359262685927599321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14604910291367162473598189 5476841359262685927599321)
              ·
                refine ⟨4107631019447014445699491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5476841359262685927599321 4107631019447014445699491)
                ·
                  refine ⟨6161446529170521668549237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107631019447014445699491 6161446529170521668549237)
                  ·
                    refine ⟨577635612109736406426491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6161446529170521668549237 577635612109736406426491)
                    ·
                      rfl

theorem cell23_3374824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_3374824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374824 prefixEnd_3374824 := by exact prefixLift 3374824
  have htrace : WordTrace (prefixWord ++ tailWord_3374824) baseStart_3374824 baseEnd_3374824 := by
    simpa [prefixWord, tailWord_3374824, baseEnd_3374824] using wordTrace_append hprefix tailTrace_3374824
  have hstable : (prefixWord ++ tailWord_3374824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374824).length < 2 ^ (prefixWord ++ tailWord_3374824).sum := by decide
  have hdescent : baseEnd_3374824 < baseStart_3374824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374827 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 2, 6, 2]
def baseStart_3374827 : Nat := 118140960795 + 3374827 * 2 ^ 59
def prefixEnd_3374827 : Nat := 4983230072969 + 3 ^ 40 * 3374827 * 2
def baseEnd_3374827 : Nat := 1732908376771172707541959

theorem tailTrace_3374827 : CollatzResearch.WordTrace tailWord_3374827 prefixEnd_3374827 1732908376771172707541959 := by
  unfold tailWord_3374827
  simp only [CollatzResearch.WordTrace]
  refine ⟨123090052944585628409186735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82060035296390418939457823 123090052944585628409186735)
  ·
    refine ⟨184635079416878442613780103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123090052944585628409186735 184635079416878442613780103)
    ·
      refine ⟨276952619125317663920670155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184635079416878442613780103 276952619125317663920670155)
      ·
        refine ⟨415428928687976495881005233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276952619125317663920670155 415428928687976495881005233)
        ·
          refine ⟨311571696515982371910753925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415428928687976495881005233 311571696515982371910753925)
          ·
            refine ⟨58419693096746694733266361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311571696515982371910753925 58419693096746694733266361)
            ·
              refine ⟨43814769822560021049949771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58419693096746694733266361 43814769822560021049949771)
              ·
                refine ⟨65722154733840031574924657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43814769822560021049949771 65722154733840031574924657)
                ·
                  refine ⟨49291616050380023681193493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65722154733840031574924657 49291616050380023681193493)
                  ·
                    refine ⟨2310544502361563610055945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49291616050380023681193493 2310544502361563610055945)
                    ·
                      refine ⟨1732908376771172707541959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310544502361563610055945 1732908376771172707541959)
                      ·
                        rfl

theorem cell23_3374827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 6, 2].length) (baseStart_3374827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374827 prefixEnd_3374827 := by exact prefixLift 3374827
  have htrace : WordTrace (prefixWord ++ tailWord_3374827) baseStart_3374827 baseEnd_3374827 := by
    simpa [prefixWord, tailWord_3374827, baseEnd_3374827] using wordTrace_append hprefix tailTrace_3374827
  have hstable : (prefixWord ++ tailWord_3374827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374827).length < 2 ^ (prefixWord ++ tailWord_3374827).sum := by decide
  have hdescent : baseEnd_3374827 < baseStart_3374827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374840 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_3374840 : Nat := 118140960795 + 3374840 * 2 ^ 59
def prefixEnd_3374840 : Nat := 4983230072969 + 3 ^ 40 * 3374840 * 2
def baseEnd_3374840 : Nat := 1732915052019681156679399

theorem tailTrace_3374840 : CollatzResearch.WordTrace tailWord_3374840 prefixEnd_3374840 1732915052019681156679399 := by
  unfold tailWord_3374840
  simp only [CollatzResearch.WordTrace]
  refine ⟨61545263546769265814704987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82060351395692354419606649 61545263546769265814704987)
  ·
    refine ⟨92317895320153898722057481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61545263546769265814704987 92317895320153898722057481)
    ·
      refine ⟨69238421490115424041543111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92317895320153898722057481 69238421490115424041543111)
      ·
        refine ⟨103857632235173136062314667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69238421490115424041543111 103857632235173136062314667)
        ·
          refine ⟨155786448352759704093472001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103857632235173136062314667 155786448352759704093472001)
          ·
            refine ⟨116839836264569778070104001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155786448352759704093472001 116839836264569778070104001)
            ·
              refine ⟨87629877198427333552578001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116839836264569778070104001 87629877198427333552578001)
              ·
                refine ⟨65722407898820500164433501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87629877198427333552578001 65722407898820500164433501)
                ·
                  refine ⟨24645902962057687561662563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65722407898820500164433501 24645902962057687561662563)
                  ·
                    refine ⟨36968854443086531342493845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24645902962057687561662563 36968854443086531342493845)
                    ·
                      refine ⟨1732915052019681156679399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36968854443086531342493845 1732915052019681156679399)
                      ·
                        rfl

theorem cell23_3374840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_3374840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374840 prefixEnd_3374840 := by exact prefixLift 3374840
  have htrace : WordTrace (prefixWord ++ tailWord_3374840) baseStart_3374840 baseEnd_3374840 := by
    simpa [prefixWord, tailWord_3374840, baseEnd_3374840] using wordTrace_append hprefix tailTrace_3374840
  have hstable : (prefixWord ++ tailWord_3374840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374840).length < 2 ^ (prefixWord ++ tailWord_3374840).sum := by decide
  have hdescent : baseEnd_3374840 < baseStart_3374840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374847 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 5]
def baseStart_3374847 : Nat := 118140960795 + 3374847 * 2 ^ 59
def prefixEnd_3374847 : Nat := 4983230072969 + 3 ^ 40 * 3374847 * 2
def baseEnd_3374847 : Nat := 1732918646384262629291867

theorem tailTrace_3374847 : CollatzResearch.WordTrace tailWord_3374847 prefixEnd_3374847 1732918646384262629291867 := by
  unfold tailWord_3374847
  simp only [CollatzResearch.WordTrace]
  refine ⟨123090782404513171824914795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82060521603008781216609863 123090782404513171824914795)
  ·
    refine ⟨184636173606769757737372193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123090782404513171824914795 184636173606769757737372193)
    ·
      refine ⟨138477130205077318303029145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184636173606769757737372193 138477130205077318303029145)
      ·
        refine ⟨103857847653807988727271859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138477130205077318303029145 103857847653807988727271859)
        ·
          refine ⟨155786771480711983090907789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103857847653807988727271859 155786771480711983090907789)
          ·
            refine ⟨58420039305266993659090421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155786771480711983090907789 58420039305266993659090421)
            ·
              refine ⟨5476878684868780655539727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58420039305266993659090421 5476878684868780655539727)
              ·
                refine ⟨8215318027303170983309591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5476878684868780655539727 8215318027303170983309591)
                ·
                  refine ⟨12322977040954756474964387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8215318027303170983309591 12322977040954756474964387)
                  ·
                    refine ⟨18484465561432134712446581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12322977040954756474964387 18484465561432134712446581)
                    ·
                      refine ⟨1732918646384262629291867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18484465561432134712446581 1732918646384262629291867)
                      ·
                        rfl

theorem cell23_3374847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_3374847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374847 prefixEnd_3374847 := by exact prefixLift 3374847
  have htrace : WordTrace (prefixWord ++ tailWord_3374847) baseStart_3374847 baseEnd_3374847 := by
    simpa [prefixWord, tailWord_3374847, baseEnd_3374847] using wordTrace_append hprefix tailTrace_3374847
  have hstable : (prefixWord ++ tailWord_3374847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374847).length < 2 ^ (prefixWord ++ tailWord_3374847).sum := by decide
  have hdescent : baseEnd_3374847 < baseStart_3374847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374874 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4]
def baseStart_3374874 : Nat := 118140960795 + 3374874 * 2 ^ 59
def prefixEnd_3374874 : Nat := 4983230072969 + 3 ^ 40 * 3374874 * 2
def baseEnd_3374874 : Nat := 1732932510361934023654243

theorem tailTrace_3374874 : CollatzResearch.WordTrace tailWord_3374874 prefixEnd_3374874 1732932510361934023654243 := by
  unfold tailWord_3374874
  simp only [CollatzResearch.WordTrace]
  refine ⟨30772941793853838859036919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82061178116943570290765117 30772941793853838859036919)
  ·
    refine ⟨46159412690780758288555379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30772941793853838859036919 46159412690780758288555379)
    ·
      refine ⟨69239119036171137432833069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46159412690780758288555379 69239119036171137432833069)
      ·
        refine ⟨25964669638564176537312401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69239119036171137432833069 25964669638564176537312401)
        ·
          refine ⟨19473502228923132402984301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25964669638564176537312401 19473502228923132402984301)
          ·
            refine ⟨7302563335846174651119113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19473502228923132402984301 7302563335846174651119113)
            ·
              refine ⟨5476922501884630988339335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7302563335846174651119113 5476922501884630988339335)
              ·
                refine ⟨8215383752826946482509003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5476922501884630988339335 8215383752826946482509003)
                ·
                  refine ⟨12323075629240419723763505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8215383752826946482509003 12323075629240419723763505)
                  ·
                    refine ⟨9242306721930314792822629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12323075629240419723763505 9242306721930314792822629)
                    ·
                      refine ⟨1732932510361934023654243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9242306721930314792822629 1732932510361934023654243)
                      ·
                        rfl

theorem cell23_3374874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_3374874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374874 prefixEnd_3374874 := by exact prefixLift 3374874
  have htrace : WordTrace (prefixWord ++ tailWord_3374874) baseStart_3374874 baseEnd_3374874 := by
    simpa [prefixWord, tailWord_3374874, baseEnd_3374874] using wordTrace_append hprefix tailTrace_3374874
  have hstable : (prefixWord ++ tailWord_3374874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374874).length < 2 ^ (prefixWord ++ tailWord_3374874).sum := by decide
  have hdescent : baseEnd_3374874 < baseStart_3374874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374884 : List Nat := [2, 3, 1, 3, 2, 2, 3, 7]
def baseStart_3374884 : Nat := 118140960795 + 3374884 * 2 ^ 59
def prefixEnd_3374884 : Nat := 4983230072969 + 3 ^ 40 * 3374884 * 2
def baseEnd_3374884 : Nat := 64182875746980703130711

theorem tailTrace_3374884 : CollatzResearch.WordTrace tailWord_3374884 prefixEnd_3374884 64182875746980703130711 := by
  unfold tailWord_3374884
  simp only [CollatzResearch.WordTrace]
  refine ⟨61546065952689563572005853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82061421270252751429341137 61546065952689563572005853)
  ·
    refine ⟨23079774732258586339502195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61546065952689563572005853 23079774732258586339502195)
    ·
      refine ⟨34619662098387879509253293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23079774732258586339502195 34619662098387879509253293)
      ·
        refine ⟨12982373286895454815969985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34619662098387879509253293 12982373286895454815969985)
        ·
          refine ⟨9736779965171591111977489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12982373286895454815969985 9736779965171591111977489)
          ·
            refine ⟨7302584973878693333983117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9736779965171591111977489 7302584973878693333983117)
            ·
              refine ⟨2738469365204510000243669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7302584973878693333983117 2738469365204510000243669)
              ·
                refine ⟨64182875746980703130711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2738469365204510000243669 64182875746980703130711)
                ·
                  rfl

theorem cell23_3374884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 7].length) (baseStart_3374884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374884 prefixEnd_3374884 := by exact prefixLift 3374884
  have htrace : WordTrace (prefixWord ++ tailWord_3374884) baseStart_3374884 baseEnd_3374884 := by
    simpa [prefixWord, tailWord_3374884, baseEnd_3374884] using wordTrace_append hprefix tailTrace_3374884
  have hstable : (prefixWord ++ tailWord_3374884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374884).length < 2 ^ (prefixWord ++ tailWord_3374884).sum := by decide
  have hdescent : baseEnd_3374884 < baseStart_3374884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374898 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3]
def baseStart_3374898 : Nat := 118140960795 + 3374898 * 2 ^ 59
def prefixEnd_3374898 : Nat := 4983230072969 + 3 ^ 40 * 3374898 * 2
def baseEnd_3374898 : Nat := 1732944833897641929754133

theorem tailTrace_3374898 : CollatzResearch.WordTrace tailWord_3374898 prefixEnd_3374898 1732944833897641929754133 := by
  unfold tailWord_3374898
  simp only [CollatzResearch.WordTrace]
  refine ⟨30773160631832101883755337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82061761684885605023347565 30773160631832101883755337)
  ·
    refine ⟨23079870473874076412816503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30773160631832101883755337 23079870473874076412816503)
    ·
      refine ⟨34619805710811114619224755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23079870473874076412816503 34619805710811114619224755)
      ·
        refine ⟨51929708566216671928837133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34619805710811114619224755 51929708566216671928837133)
        ·
          refine ⟨19473640712331251973313925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51929708566216671928837133 19473640712331251973313925)
          ·
            refine ⟨3651307633562109744996361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19473640712331251973313925 3651307633562109744996361)
            ·
              refine ⟨2738480725171582308747271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3651307633562109744996361 2738480725171582308747271)
              ·
                refine ⟨4107721087757373463120907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2738480725171582308747271 4107721087757373463120907)
                ·
                  refine ⟨6161581631636060194681361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107721087757373463120907 6161581631636060194681361)
                  ·
                    refine ⟨4621186223727045146011021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6161581631636060194681361 4621186223727045146011021)
                    ·
                      refine ⟨1732944833897641929754133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4621186223727045146011021 1732944833897641929754133)
                      ·
                        rfl

theorem cell23_3374898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3].length) (baseStart_3374898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374898 prefixEnd_3374898 := by exact prefixLift 3374898
  have htrace : WordTrace (prefixWord ++ tailWord_3374898) baseStart_3374898 baseEnd_3374898 := by
    simpa [prefixWord, tailWord_3374898, baseEnd_3374898] using wordTrace_append hprefix tailTrace_3374898
  have hstable : (prefixWord ++ tailWord_3374898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374898).length < 2 ^ (prefixWord ++ tailWord_3374898).sum := by decide
  have hdescent : baseEnd_3374898 < baseStart_3374898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374905 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 2, 4]
def baseStart_3374905 : Nat := 118140960795 + 3374905 * 2 ^ 59
def prefixEnd_3374905 : Nat := 4983230072969 + 3 ^ 40 * 3374905 * 2
def baseEnd_3374905 : Nat := 577649476087407800788867

theorem tailTrace_3374905 : CollatzResearch.WordTrace tailWord_3374905 prefixEnd_3374905 577649476087407800788867 := by
  unfold tailWord_3374905
  simp only [CollatzResearch.WordTrace]
  refine ⟨123092897838303047730526169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82061931892202031820350779 123092897838303047730526169)
  ·
    refine ⟨92319673378727285797894627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123092897838303047730526169 92319673378727285797894627)
    ·
      refine ⟨138479510068090928696841941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92319673378727285797894627 138479510068090928696841941)
      ·
        refine ⟨3245613517220881141332233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 138479510068090928696841941 3245613517220881141332233)
        ·
          refine ⟨2434210137915660855999175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3245613517220881141332233 2434210137915660855999175)
          ·
            refine ⟨3651315206873491283998763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2434210137915660855999175 3651315206873491283998763)
            ·
              refine ⟨5476972810310236925998145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3651315206873491283998763 5476972810310236925998145)
              ·
                refine ⟨4107729607732677694498609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5476972810310236925998145 4107729607732677694498609)
                ·
                  refine ⟨3080797205799508270873957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4107729607732677694498609 3080797205799508270873957)
                  ·
                    refine ⟨577649476087407800788867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3080797205799508270873957 577649476087407800788867)
                    ·
                      rfl

theorem cell23_3374905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 2, 4].length) (baseStart_3374905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374905 prefixEnd_3374905 := by exact prefixLift 3374905
  have htrace : WordTrace (prefixWord ++ tailWord_3374905) baseStart_3374905 baseEnd_3374905 := by
    simpa [prefixWord, tailWord_3374905, baseEnd_3374905] using wordTrace_append hprefix tailTrace_3374905
  have hstable : (prefixWord ++ tailWord_3374905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374905).length < 2 ^ (prefixWord ++ tailWord_3374905).sum := by decide
  have hdescent : baseEnd_3374905 < baseStart_3374905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374911 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 4, 1, 3]
def baseStart_3374911 : Nat := 118140960795 + 3374911 * 2 ^ 59
def prefixEnd_3374911 : Nat := 4983230072969 + 3 ^ 40 * 3374911 * 2
def baseEnd_3374911 : Nat := 1732951509146150378891573

theorem tailTrace_3374911 : CollatzResearch.WordTrace tailWord_3374911 prefixEnd_3374911 1732951509146150378891573 := by
  unfold tailWord_3374911
  simp only [CollatzResearch.WordTrace]
  refine ⟨123093116676281310755244587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82062077784187540503496391 123093116676281310755244587)
  ·
    refine ⟨184639675014421966132866881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123093116676281310755244587 184639675014421966132866881)
    ·
      refine ⟨138479756260816474599650161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184639675014421966132866881 138479756260816474599650161)
      ·
        refine ⟨103859817195612355949737621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138479756260816474599650161 103859817195612355949737621)
        ·
          refine ⟨4868428931044329185143951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103859817195612355949737621 4868428931044329185143951)
          ·
            refine ⟨7302643396566493777715927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4868428931044329185143951 7302643396566493777715927)
            ·
              refine ⟨10953965094849740666573891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7302643396566493777715927 10953965094849740666573891)
              ·
                refine ⟨16430947642274610999860837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10953965094849740666573891 16430947642274610999860837)
                ·
                  refine ⟨3080802682926489562473907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16430947642274610999860837 3080802682926489562473907)
                  ·
                    refine ⟨4621204024389734343710861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3080802682926489562473907 4621204024389734343710861)
                    ·
                      refine ⟨1732951509146150378891573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4621204024389734343710861 1732951509146150378891573)
                      ·
                        rfl

theorem cell23_3374911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_3374911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374911 prefixEnd_3374911 := by exact prefixLift 3374911
  have htrace : WordTrace (prefixWord ++ tailWord_3374911) baseStart_3374911 baseEnd_3374911 := by
    simpa [prefixWord, tailWord_3374911, baseEnd_3374911] using wordTrace_append hprefix tailTrace_3374911
  have hstable : (prefixWord ++ tailWord_3374911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374911).length < 2 ^ (prefixWord ++ tailWord_3374911).sum := by decide
  have hdescent : baseEnd_3374911 < baseStart_3374911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374937 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 5]
def baseStart_3374937 : Nat := 118140960795 + 3374937 * 2 ^ 59
def prefixEnd_3374937 : Nat := 4983230072969 + 3 ^ 40 * 3374937 * 2
def baseEnd_3374937 : Nat := 1732964859643167277166453

theorem tailTrace_3374937 : CollatzResearch.WordTrace tailWord_3374937 prefixEnd_3374937 1732964859643167277166453 := by
  unfold tailWord_3374937
  simp only [CollatzResearch.WordTrace]
  refine ⟨123094064974187117195691065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82062709982791411463794043 123094064974187117195691065)
  ·
    refine ⟨92320548730640337896768299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123094064974187117195691065 92320548730640337896768299)
    ·
      refine ⟨138480823095960506845152449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92320548730640337896768299 138480823095960506845152449)
      ·
        refine ⟨103860617321970380133864337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138480823095960506845152449 103860617321970380133864337)
        ·
          refine ⟨77895462991477785100398253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103860617321970380133864337 77895462991477785100398253)
          ·
            refine ⟨29210798621804169412649345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77895462991477785100398253 29210798621804169412649345)
            ·
              refine ⟨21908098966353127059487009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29210798621804169412649345 21908098966353127059487009)
              ·
                refine ⟨16431074224764845294615257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21908098966353127059487009 16431074224764845294615257)
                ·
                  refine ⟨12323305668573633970961443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16431074224764845294615257 12323305668573633970961443)
                  ·
                    refine ⟨18484958502860450956442165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12323305668573633970961443 18484958502860450956442165)
                    ·
                      refine ⟨1732964859643167277166453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18484958502860450956442165 1732964859643167277166453)
                      ·
                        rfl

theorem cell23_3374937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_3374937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374937 prefixEnd_3374937 := by exact prefixLift 3374937
  have htrace : WordTrace (prefixWord ++ tailWord_3374937) baseStart_3374937 baseEnd_3374937 := by
    simpa [prefixWord, tailWord_3374937, baseEnd_3374937] using wordTrace_append hprefix tailTrace_3374937
  have hstable : (prefixWord ++ tailWord_3374937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374937).length < 2 ^ (prefixWord ++ tailWord_3374937).sum := by decide
  have hdescent : baseEnd_3374937 < baseStart_3374937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374951 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_3374951 : Nat := 118140960795 + 3374951 * 2 ^ 59
def prefixEnd_3374951 : Nat := 4983230072969 + 3 ^ 40 * 3374951 * 2
def baseEnd_3374951 : Nat := 1732972048372330222391389

theorem tailTrace_3374951 : CollatzResearch.WordTrace tailWord_3374951 prefixEnd_3374951 1732972048372330222391389 := by
  unfold tailWord_3374951
  simp only [CollatzResearch.WordTrace]
  refine ⟨123094575596136397586700707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82063050397424265057800471 123094575596136397586700707)
  ·
    refine ⟨184641863394204596380051061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123094575596136397586700707 184641863394204596380051061)
    ·
      refine ⟨17310174693206680910629787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184641863394204596380051061 17310174693206680910629787)
      ·
        refine ⟨25965262039810021365944681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17310174693206680910629787 25965262039810021365944681)
        ·
          refine ⟨19473946529857516024458511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25965262039810021365944681 19473946529857516024458511)
          ·
            refine ⟨29210919794786274036687767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19473946529857516024458511 29210919794786274036687767)
            ·
              refine ⟨43816379692179411055031651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29210919794786274036687767 43816379692179411055031651)
              ·
                refine ⟨65724569538269116582547477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43816379692179411055031651 65724569538269116582547477)
                ·
                  refine ⟨3080839197106364839806913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65724569538269116582547477 3080839197106364839806913)
                  ·
                    refine ⟨2310629397829773629855185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3080839197106364839806913 2310629397829773629855185)
                    ·
                      refine ⟨1732972048372330222391389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310629397829773629855185 1732972048372330222391389)
                      ·
                        rfl

theorem cell23_3374951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_3374951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374951 prefixEnd_3374951 := by exact prefixLift 3374951
  have htrace : WordTrace (prefixWord ++ tailWord_3374951) baseStart_3374951 baseEnd_3374951 := by
    simpa [prefixWord, tailWord_3374951, baseEnd_3374951] using wordTrace_append hprefix tailTrace_3374951
  have hstable : (prefixWord ++ tailWord_3374951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374951).length < 2 ^ (prefixWord ++ tailWord_3374951).sum := by decide
  have hdescent : baseEnd_3374951 < baseStart_3374951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374957 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 9]
def baseStart_3374957 : Nat := 118140960795 + 3374957 * 2 ^ 59
def prefixEnd_3374957 : Nat := 4983230072969 + 3 ^ 40 * 3374957 * 2
def baseEnd_3374957 : Nat := 192552792139584133212929

theorem tailTrace_3374957 : CollatzResearch.WordTrace tailWord_3374957 prefixEnd_3374957 192552792139584133212929 := by
  unfold tailWord_3374957
  simp only [CollatzResearch.WordTrace]
  refine ⟨123094794434114660611419125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82063196289409773740946083 123094794434114660611419125)
  ·
    refine ⟨11540136978198249432320543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123094794434114660611419125 11540136978198249432320543)
    ·
      refine ⟨17310205467297374148480815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11540136978198249432320543 17310205467297374148480815)
      ·
        refine ⟨25965308200946061222721223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17310205467297374148480815 25965308200946061222721223)
        ·
          refine ⟨38947962301419091834081835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25965308200946061222721223 38947962301419091834081835)
          ·
            refine ⟨58421943452128637751122753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38947962301419091834081835 58421943452128637751122753)
            ·
              refine ⟨43816457589096478313342065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58421943452128637751122753 43816457589096478313342065)
              ·
                refine ⟨32862343191822358735006549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43816457589096478313342065 32862343191822358735006549)
                ·
                  refine ⟨192552792139584133212929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32862343191822358735006549 192552792139584133212929)
                  ·
                    rfl

theorem cell23_3374957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_3374957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374957 prefixEnd_3374957 := by exact prefixLift 3374957
  have htrace : WordTrace (prefixWord ++ tailWord_3374957) baseStart_3374957 baseEnd_3374957 := by
    simpa [prefixWord, tailWord_3374957, baseEnd_3374957] using wordTrace_append hprefix tailTrace_3374957
  have hstable : (prefixWord ++ tailWord_3374957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374957).length < 2 ^ (prefixWord ++ tailWord_3374957).sum := by decide
  have hdescent : baseEnd_3374957 < baseStart_3374957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374987 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 6, 5]
def baseStart_3374987 : Nat := 118140960795 + 3374987 * 2 ^ 59
def prefixEnd_3374987 : Nat := 4983230072969 + 3 ^ 40 * 3374987 * 2
def baseEnd_3374987 : Nat := 577663511225297360513741

theorem tailTrace_3374987 : CollatzResearch.WordTrace tailWord_3374987 prefixEnd_3374987 577663511225297360513741 := by
  unfold tailWord_3374987
  simp only [CollatzResearch.WordTrace]
  refine ⟨123095888624005975735011215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82063925749337317156674143 123095888624005975735011215)
  ·
    refine ⟨184643832936008963602516823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123095888624005975735011215 184643832936008963602516823)
    ·
      refine ⟨276965749404013445403775235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184643832936008963602516823 276965749404013445403775235)
      ·
        refine ⟨415448624106020168105662853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276965749404013445403775235 415448624106020168105662853)
        ·
          refine ⟨77896617019878781519811785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 415448624106020168105662853 77896617019878781519811785)
          ·
            refine ⟨58422462764909086139858839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77896617019878781519811785 58422462764909086139858839)
            ·
              refine ⟨87633694147363629209788259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58422462764909086139858839 87633694147363629209788259)
              ·
                refine ⟨131450541221045443814682389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87633694147363629209788259 131450541221045443814682389)
                ·
                  refine ⟨6161744119736505178813237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131450541221045443814682389 6161744119736505178813237)
                  ·
                    refine ⟨577663511225297360513741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6161744119736505178813237 577663511225297360513741)
                    ·
                      rfl

theorem cell23_3374987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 5].length) (baseStart_3374987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374987 prefixEnd_3374987 := by exact prefixLift 3374987
  have htrace : WordTrace (prefixWord ++ tailWord_3374987) baseStart_3374987 baseEnd_3374987 := by
    simpa [prefixWord, tailWord_3374987, baseEnd_3374987] using wordTrace_append hprefix tailTrace_3374987
  have hstable : (prefixWord ++ tailWord_3374987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374987).length < 2 ^ (prefixWord ++ tailWord_3374987).sum := by decide
  have hdescent : baseEnd_3374987 < baseStart_3374987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3374997 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_3374997 : Nat := 118140960795 + 3374997 * 2 ^ 59
def prefixEnd_3374997 : Nat := 4983230072969 + 3 ^ 40 * 3374997 * 2
def baseEnd_3374997 : Nat := 1732995668482437042416177

theorem tailTrace_3374997 : CollatzResearch.WordTrace tailWord_3374997 prefixEnd_3374997 1732995668482437042416177 := by
  unfold tailWord_3374997
  simp only [CollatzResearch.WordTrace]
  refine ⟨123096253353969747442875245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82064168902646498295250163 123096253353969747442875245)
  ·
    refine ⟨46161095007738655291078217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123096253353969747442875245 46161095007738655291078217)
    ·
      refine ⟨34620821255803991468308663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46161095007738655291078217 34620821255803991468308663)
      ·
        refine ⟨51931231883705987202462995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34620821255803991468308663 51931231883705987202462995)
        ·
          refine ⟨77896847825558980803694493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51931231883705987202462995 77896847825558980803694493)
          ·
            refine ⟨29211317934584617801385435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77896847825558980803694493 29211317934584617801385435)
            ·
              refine ⟨43816976901876926702078153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29211317934584617801385435 43816976901876926702078153)
              ·
                refine ⟨32862732676407695026558615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43816976901876926702078153 32862732676407695026558615)
                ·
                  refine ⟨49294099014611542539837923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32862732676407695026558615 49294099014611542539837923)
                  ·
                    refine ⟨73941148521917313809756885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49294099014611542539837923 73941148521917313809756885)
                    ·
                      refine ⟨1732995668482437042416177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73941148521917313809756885 1732995668482437042416177)
                      ·
                        rfl

theorem cell23_3374997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_3374997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3374997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3374997 prefixEnd_3374997 := by exact prefixLift 3374997
  have htrace : WordTrace (prefixWord ++ tailWord_3374997) baseStart_3374997 baseEnd_3374997 := by
    simpa [prefixWord, tailWord_3374997, baseEnd_3374997] using wordTrace_append hprefix tailTrace_3374997
  have hstable : (prefixWord ++ tailWord_3374997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3374997).length < 2 ^ (prefixWord ++ tailWord_3374997).sum := by decide
  have hdescent : baseEnd_3374997 < baseStart_3374997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3374997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375024 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 5, 6, 2]
def baseStart_3375024 : Nat := 118140960795 + 3375024 * 2 ^ 59
def prefixEnd_3375024 : Nat := 4983230072969 + 3 ^ 40 * 3375024 * 2
def baseEnd_3375024 : Nat := 1733009532460108436778553

theorem tailTrace_3375024 : CollatzResearch.WordTrace tailWord_3375024 prefixEnd_3375024 1733009532460108436778553 := by
  unfold tailWord_3375024
  simp only [CollatzResearch.WordTrace]
  refine ⟨61548619062435965527054063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82064825416581287369405417 61548619062435965527054063)
  ·
    refine ⟨92322928593653948290581095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61548619062435965527054063 92322928593653948290581095)
    ·
      refine ⟨138484392890480922435871643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92322928593653948290581095 138484392890480922435871643)
      ·
        refine ⟨207726589335721383653807465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138484392890480922435871643 207726589335721383653807465)
        ·
          refine ⟨155794942001791037740355599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207726589335721383653807465 155794942001791037740355599)
          ·
            refine ⟨233692413002686556610533399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155794942001791037740355599 233692413002686556610533399)
            ·
              refine ⟨350538619504029834915800099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233692413002686556610533399 350538619504029834915800099)
              ·
                refine ⟨525807929256044752373700149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350538619504029834915800099 525807929256044752373700149)
                ·
                  refine ⟨49294493367754195535034389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 525807929256044752373700149 49294493367754195535034389)
                  ·
                    refine ⟨2310679376613477915704737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49294493367754195535034389 2310679376613477915704737)
                    ·
                      refine ⟨1733009532460108436778553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310679376613477915704737 1733009532460108436778553)
                      ·
                        rfl

theorem cell23_3375024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 5, 6, 2].length) (baseStart_3375024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375024 prefixEnd_3375024 := by exact prefixLift 3375024
  have htrace : WordTrace (prefixWord ++ tailWord_3375024) baseStart_3375024 baseEnd_3375024 := by
    simpa [prefixWord, tailWord_3375024, baseEnd_3375024] using wordTrace_append hprefix tailTrace_3375024
  have hstable : (prefixWord ++ tailWord_3375024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375024).length < 2 ^ (prefixWord ++ tailWord_3375024).sum := by decide
  have hdescent : baseEnd_3375024 < baseStart_3375024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375027 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 5]
def baseStart_3375027 : Nat := 118140960795 + 3375027 * 2 ^ 59
def prefixEnd_3375027 : Nat := 4983230072969 + 3 ^ 40 * 3375027 * 2
def baseEnd_3375027 : Nat := 1733011072902071925041039

theorem tailTrace_3375027 : CollatzResearch.WordTrace tailWord_3375027 prefixEnd_3375027 1733011072902071925041039 := by
  unfold tailWord_3375027
  simp only [CollatzResearch.WordTrace]
  refine ⟨123097347543861062566467335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82064898362574041710978223 123097347543861062566467335)
  ·
    refine ⟨184646021315791593849701003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123097347543861062566467335 184646021315791593849701003)
    ·
      refine ⟨276969031973687390774551505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184646021315791593849701003 276969031973687390774551505)
      ·
        refine ⟨207726773980265543080913629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276969031973687390774551505 207726773980265543080913629)
        ·
          refine ⟨77897540242599578655342611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207726773980265543080913629 77897540242599578655342611)
          ·
            refine ⟨116846310363899367983013917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77897540242599578655342611 116846310363899367983013917)
            ·
              refine ⟨43817366386462262993630219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116846310363899367983013917 43817366386462262993630219)
              ·
                refine ⟨65726049579693394490445329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43817366386462262993630219 65726049579693394490445329)
                ·
                  refine ⟨49294537184770045867833997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65726049579693394490445329 49294537184770045867833997)
                  ·
                    refine ⟨18485451444288767200437749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49294537184770045867833997 18485451444288767200437749)
                    ·
                      refine ⟨1733011072902071925041039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18485451444288767200437749 1733011072902071925041039)
                      ·
                        rfl

theorem cell23_3375027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_3375027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375027 prefixEnd_3375027 := by exact prefixLift 3375027
  have htrace : WordTrace (prefixWord ++ tailWord_3375027) baseStart_3375027 baseEnd_3375027 := by
    simpa [prefixWord, tailWord_3375027, baseEnd_3375027] using wordTrace_append hprefix tailTrace_3375027
  have hstable : (prefixWord ++ tailWord_3375027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375027).length < 2 ^ (prefixWord ++ tailWord_3375027).sum := by decide
  have hdescent : baseEnd_3375027 < baseStart_3375027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375047 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 10]
def baseStart_3375047 : Nat := 118140960795 + 3375047 * 2 ^ 59
def prefixEnd_3375047 : Nat := 4983230072969 + 3 ^ 40 * 3375047 * 2
def baseEnd_3375047 : Nat := 192557926946129094087883

theorem tailTrace_3375047 : CollatzResearch.WordTrace tailWord_3375047 prefixEnd_3375047 192557926946129094087883 := by
  unfold tailWord_3375047
  simp only [CollatzResearch.WordTrace]
  refine ⟨123098077003788605982195395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82065384669192403988130263 123098077003788605982195395)
  ·
    refine ⟨184647115505682908973293093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123098077003788605982195395 184647115505682908973293093)
    ·
      refine ⟨34621334157315545432492455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184647115505682908973293093 34621334157315545432492455)
      ·
        refine ⟨51932001235973318148738683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34621334157315545432492455 51932001235973318148738683)
        ·
          refine ⟨77898001853959977223108025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51932001235973318148738683 77898001853959977223108025)
          ·
            refine ⟨58423501390469982917331019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77898001853959977223108025 58423501390469982917331019)
            ·
              refine ⟨87635252085704974375996529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58423501390469982917331019 87635252085704974375996529)
              ·
                refine ⟨65726439064278730781997397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87635252085704974375996529 65726439064278730781997397)
                ·
                  refine ⟨192557926946129094087883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 65726439064278730781997397 192557926946129094087883)
                  ·
                    rfl

theorem cell23_3375047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 10].length) (baseStart_3375047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375047 prefixEnd_3375047 := by exact prefixLift 3375047
  have htrace : WordTrace (prefixWord ++ tailWord_3375047) baseStart_3375047 baseEnd_3375047 := by
    simpa [prefixWord, tailWord_3375047, baseEnd_3375047] using wordTrace_append hprefix tailTrace_3375047
  have hstable : (prefixWord ++ tailWord_3375047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375047).length < 2 ^ (prefixWord ++ tailWord_3375047).sum := by decide
  have hdescent : baseEnd_3375047 < baseStart_3375047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375061 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3375061 : Nat := 118140960795 + 3375061 * 2 ^ 59
def prefixEnd_3375061 : Nat := 4983230072969 + 3 ^ 40 * 3375061 * 2
def baseEnd_3375061 : Nat := 1733028531244324792015883

theorem tailTrace_3375061 : CollatzResearch.WordTrace tailWord_3375061 prefixEnd_3375061 1733028531244324792015883 := by
  unfold tailWord_3375061
  simp only [CollatzResearch.WordTrace]
  refine ⟨123098587625737886373205037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82065725083825257582136691 123098587625737886373205037)
  ·
    refine ⟨46161970359651707389951889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123098587625737886373205037 46161970359651707389951889)
    ·
      refine ⟨34621477769738780542463917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46161970359651707389951889 34621477769738780542463917)
      ·
        refine ⟨12983054163652042703423969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34621477769738780542463917 12983054163652042703423969)
        ·
          refine ⟨9737290622739032027567977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12983054163652042703423969 9737290622739032027567977)
          ·
            refine ⟨7302967967054274020675983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9737290622739032027567977 7302967967054274020675983)
            ·
              refine ⟨10954451950581411031013975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7302967967054274020675983 10954451950581411031013975)
              ·
                refine ⟨16431677925872116546520963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10954451950581411031013975 16431677925872116546520963)
                ·
                  refine ⟨24647516888808174819781445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16431677925872116546520963 24647516888808174819781445)
                  ·
                    refine ⟨4621409416651532778709021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24647516888808174819781445 4621409416651532778709021)
                    ·
                      refine ⟨1733028531244324792015883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4621409416651532778709021 1733028531244324792015883)
                      ·
                        rfl

theorem cell23_3375061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3375061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375061 prefixEnd_3375061 := by exact prefixLift 3375061
  have htrace : WordTrace (prefixWord ++ tailWord_3375061) baseStart_3375061 baseEnd_3375061 := by
    simpa [prefixWord, tailWord_3375061, baseEnd_3375061] using wordTrace_append hprefix tailTrace_3375061
  have hstable : (prefixWord ++ tailWord_3375061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375061).length < 2 ^ (prefixWord ++ tailWord_3375061).sum := by decide
  have hdescent : baseEnd_3375061 < baseStart_3375061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375085 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_3375085 : Nat := 118140960795 + 3375085 * 2 ^ 59
def prefixEnd_3375085 : Nat := 4983230072969 + 3 ^ 40 * 3375085 * 2
def baseEnd_3375085 : Nat := 577680284926677566038591

theorem tailTrace_3375085 : CollatzResearch.WordTrace tailWord_3375085 prefixEnd_3375085 577680284926677566038591 := by
  unfold tailWord_3375085
  simp only [CollatzResearch.WordTrace]
  refine ⟨123099462977650938472078709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82066308651767292314719139 123099462977650938472078709)
  ·
    refine ⟨11540574654154775481757379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123099462977650938472078709 11540574654154775481757379)
    ·
      refine ⟨17310861981232163222636069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11540574654154775481757379 17310861981232163222636069)
      ·
        refine ⟨3245786621481030604244263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17310861981232163222636069 3245786621481030604244263)
        ·
          refine ⟨4868679932221545906366395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3245786621481030604244263 4868679932221545906366395)
          ·
            refine ⟨7303019898332318859549593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4868679932221545906366395 7303019898332318859549593)
            ·
              refine ⟨5477264923749239144662195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7303019898332318859549593 5477264923749239144662195)
              ·
                refine ⟨8215897385623858716993293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5477264923749239144662195 8215897385623858716993293)
                ·
                  refine ⟨3080961519608947018872485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8215897385623858716993293 3080961519608947018872485)
                  ·
                    refine ⟨577680284926677566038591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3080961519608947018872485 577680284926677566038591)
                    ·
                      rfl

theorem cell23_3375085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_3375085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375085 prefixEnd_3375085 := by exact prefixLift 3375085
  have htrace : WordTrace (prefixWord ++ tailWord_3375085) baseStart_3375085 baseEnd_3375085 := by
    simpa [prefixWord, tailWord_3375085, baseEnd_3375085] using wordTrace_append hprefix tailTrace_3375085
  have hstable : (prefixWord ++ tailWord_3375085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375085).length < 2 ^ (prefixWord ++ tailWord_3375085).sum := by decide
  have hdescent : baseEnd_3375085 < baseStart_3375085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375101 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 1, 5, 2]
def baseStart_3375101 : Nat := 118140960795 + 3375101 * 2 ^ 59
def prefixEnd_3375101 : Nat := 4983230072969 + 3 ^ 40 * 3375101 * 2
def baseEnd_3375101 : Nat := 1733049070470504635515699

theorem tailTrace_3375101 : CollatzResearch.WordTrace tailWord_3375101 prefixEnd_3375101 1733049070470504635515699 := by
  unfold tailWord_3375101
  simp only [CollatzResearch.WordTrace]
  refine ⟨123100046545592973204661157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82066697697061982136440771 123100046545592973204661157)
  ·
    refine ⟨23081258727298682475873967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123100046545592973204661157 23081258727298682475873967)
    ·
      refine ⟨34621888090948023713810951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23081258727298682475873967 34621888090948023713810951)
      ·
        refine ⟨51932832136422035570716427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34621888090948023713810951 51932832136422035570716427)
        ·
          refine ⟨77899248204633053356074641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51932832136422035570716427 77899248204633053356074641)
          ·
            refine ⟨58424436153474790017055981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77899248204633053356074641 58424436153474790017055981)
            ·
              refine ⟨21909163557553046256395993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58424436153474790017055981 21909163557553046256395993)
              ·
                refine ⟨16431872668164784692296995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21909163557553046256395993 16431872668164784692296995)
                ·
                  refine ⟨24647809002247177038445493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16431872668164784692296995 24647809002247177038445493)
                  ·
                    refine ⟨2310732093960672847354265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24647809002247177038445493 2310732093960672847354265)
                    ·
                      refine ⟨1733049070470504635515699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310732093960672847354265 1733049070470504635515699)
                      ·
                        rfl

theorem cell23_3375101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_3375101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375101 prefixEnd_3375101 := by exact prefixLift 3375101
  have htrace : WordTrace (prefixWord ++ tailWord_3375101) baseStart_3375101 baseEnd_3375101 := by
    simpa [prefixWord, tailWord_3375101, baseEnd_3375101] using wordTrace_append hprefix tailTrace_3375101
  have hstable : (prefixWord ++ tailWord_3375101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375101).length < 2 ^ (prefixWord ++ tailWord_3375101).sum := by decide
  have hdescent : baseEnd_3375101 < baseStart_3375101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375111 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 1, 5]
def baseStart_3375111 : Nat := 118140960795 + 3375111 * 2 ^ 59
def prefixEnd_3375111 : Nat := 4983230072969 + 3 ^ 40 * 3375111 * 2
def baseEnd_3375111 : Nat := 577684735092349865463551

theorem tailTrace_3375111 : CollatzResearch.WordTrace tailWord_3375111 prefixEnd_3375111 577684735092349865463551 := by
  unfold tailWord_3375111
  simp only [CollatzResearch.WordTrace]
  refine ⟨123100411275556744912525187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82066940850371163275016791 123100411275556744912525187)
  ·
    refine ⟨184650616913335117368787781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123100411275556744912525187 184650616913335117368787781)
    ·
      refine ⟨34621990671250334506647709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184650616913335117368787781 34621990671250334506647709)
      ·
        refine ⟨12983246501718875439992891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34621990671250334506647709 12983246501718875439992891)
        ·
          refine ⟨19474869752578313159989337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12983246501718875439992891 19474869752578313159989337)
          ·
            refine ⟨14606152314433734869992003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19474869752578313159989337 14606152314433734869992003)
            ·
              refine ⟨21909228471650602304988005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14606152314433734869992003 21909228471650602304988005)
              ·
                refine ⟨4107980338434487932185251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21909228471650602304988005 4107980338434487932185251)
                ·
                  refine ⟨6161970507651731898277877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107980338434487932185251 6161970507651731898277877)
                  ·
                    refine ⟨577684735092349865463551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6161970507651731898277877 577684735092349865463551)
                    ·
                      rfl

theorem cell23_3375111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_3375111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375111 prefixEnd_3375111 := by exact prefixLift 3375111
  have htrace : WordTrace (prefixWord ++ tailWord_3375111) baseStart_3375111 baseEnd_3375111 := by
    simpa [prefixWord, tailWord_3375111, baseEnd_3375111] using wordTrace_append hprefix tailTrace_3375111
  have hstable : (prefixWord ++ tailWord_3375111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375111).length < 2 ^ (prefixWord ++ tailWord_3375111).sum := by decide
  have hdescent : baseEnd_3375111 < baseStart_3375111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375118 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2]
def baseStart_3375118 : Nat := 118140960795 + 3375118 * 2 ^ 59
def prefixEnd_3375118 : Nat := 4983230072969 + 3 ^ 40 * 3375118 * 2
def baseEnd_3375118 : Nat := 1733057799641631069003121

theorem tailTrace_3375118 : CollatzResearch.WordTrace tailWord_3375118 prefixEnd_3375118 1733057799641631069003121 := by
  unfold tailWord_3375118
  simp only [CollatzResearch.WordTrace]
  refine ⟨15387583323316423138503751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82067111057687590072020005 15387583323316423138503751)
  ·
    refine ⟨23081374984974634707755627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15387583323316423138503751 23081374984974634707755627)
    ·
      refine ⟨34622062477461952061633441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23081374984974634707755627 34622062477461952061633441)
      ·
        refine ⟨25966546858096464046225081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34622062477461952061633441 25966546858096464046225081)
        ·
          refine ⟨19474910143572348034668811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25966546858096464046225081 19474910143572348034668811)
          ·
            refine ⟨29212365215358522052003217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19474910143572348034668811 29212365215358522052003217)
            ·
              refine ⟨21909273911518891539002413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29212365215358522052003217 21909273911518891539002413)
              ·
                refine ⟨8215977716819584327125905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21909273911518891539002413 8215977716819584327125905)
                ·
                  refine ⟨6161983287614688245344429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8215977716819584327125905 6161983287614688245344429)
                  ·
                    refine ⟨2310743732855508092004161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6161983287614688245344429 2310743732855508092004161)
                    ·
                      refine ⟨1733057799641631069003121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310743732855508092004161 1733057799641631069003121)
                      ·
                        rfl

theorem cell23_3375118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_3375118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375118 prefixEnd_3375118 := by exact prefixLift 3375118
  have htrace : WordTrace (prefixWord ++ tailWord_3375118) baseStart_3375118 baseEnd_3375118 := by
    simpa [prefixWord, tailWord_3375118, baseEnd_3375118] using wordTrace_append hprefix tailTrace_3375118
  have hstable : (prefixWord ++ tailWord_3375118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375118).length < 2 ^ (prefixWord ++ tailWord_3375118).sum := by decide
  have hdescent : baseEnd_3375118 < baseStart_3375118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375141 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 4, 4]
def baseStart_3375141 : Nat := 118140960795 + 3375141 * 2 ^ 59
def prefixEnd_3375141 : Nat := 4983230072969 + 3 ^ 40 * 3375141 * 2
def baseEnd_3375141 : Nat := 577689869898894826338505

theorem tailTrace_3375141 : CollatzResearch.WordTrace tailWord_3375141 prefixEnd_3375141 577689869898894826338505 := by
  unfold tailWord_3375141
  simp only [CollatzResearch.WordTrace]
  refine ⟨123101505465448060036117277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82067670310298706690744851 123101505465448060036117277)
  ·
    refine ⟨46163064549543022513543979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123101505465448060036117277 46163064549543022513543979)
    ·
      refine ⟨69244596824314533770315969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46163064549543022513543979 69244596824314533770315969)
      ·
        refine ⟨51933447618235900327736977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69244596824314533770315969 51933447618235900327736977)
        ·
          refine ⟨38950085713676925245802733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51933447618235900327736977 38950085713676925245802733)
          ·
            refine ⟨14606282142628846967176025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38950085713676925245802733 14606282142628846967176025)
            ·
              refine ⟨10954711606971635225382019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14606282142628846967176025 10954711606971635225382019)
              ·
                refine ⟨16432067410457452838073029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10954711606971635225382019 16432067410457452838073029)
                ·
                  refine ⟨3081012639460772407138693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16432067410457452838073029 3081012639460772407138693)
                  ·
                    refine ⟨577689869898894826338505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3081012639460772407138693 577689869898894826338505)
                    ·
                      rfl

theorem cell23_3375141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_3375141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375141 prefixEnd_3375141 := by exact prefixLift 3375141
  have htrace : WordTrace (prefixWord ++ tailWord_3375141) baseStart_3375141 baseEnd_3375141 := by
    simpa [prefixWord, tailWord_3375141, baseEnd_3375141] using wordTrace_append hprefix tailTrace_3375141
  have hstable : (prefixWord ++ tailWord_3375141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375141).length < 2 ^ (prefixWord ++ tailWord_3375141).sum := by decide
  have hdescent : baseEnd_3375141 < baseStart_3375141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375148 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 3, 2, 2]
def baseStart_3375148 : Nat := 118140960795 + 3375148 * 2 ^ 59
def prefixEnd_3375148 : Nat := 4983230072969 + 3 ^ 40 * 3375148 * 2
def baseEnd_3375148 : Nat := 1733073204061265951627983

theorem tailTrace_3375148 : CollatzResearch.WordTrace tailWord_3375148 prefixEnd_3375148 1733073204061265951627983 := by
  unfold tailWord_3375148
  simp only [CollatzResearch.WordTrace]
  refine ⟨61550880388211350115811049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82067840517615133487748065 61550880388211350115811049)
  ·
    refine ⟨46163160291158512586858287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61550880388211350115811049 46163160291158512586858287)
    ·
      refine ⟨69244740436737768880287431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46163160291158512586858287 69244740436737768880287431)
      ·
        refine ⟨103867110655106653320431147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69244740436737768880287431 103867110655106653320431147)
        ·
          refine ⟨155800665982659979980646721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103867110655106653320431147 155800665982659979980646721)
          ·
            refine ⟨116850499486994984985485041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155800665982659979980646721 116850499486994984985485041)
            ·
              refine ⟨87637874615246238739113781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116850499486994984985485041 87637874615246238739113781)
              ·
                refine ⟨8216050745179334881791917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87637874615246238739113781 8216050745179334881791917)
                ·
                  refine ⟨3081019029442250580671969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8216050745179334881791917 3081019029442250580671969)
                  ·
                    refine ⟨2310764272081687935503977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3081019029442250580671969 2310764272081687935503977)
                    ·
                      refine ⟨1733073204061265951627983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310764272081687935503977 1733073204061265951627983)
                      ·
                        rfl

theorem cell23_3375148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 2, 2].length) (baseStart_3375148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375148 prefixEnd_3375148 := by exact prefixLift 3375148
  have htrace : WordTrace (prefixWord ++ tailWord_3375148) baseStart_3375148 baseEnd_3375148 := by
    simpa [prefixWord, tailWord_3375148, baseEnd_3375148] using wordTrace_append hprefix tailTrace_3375148
  have hstable : (prefixWord ++ tailWord_3375148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375148).length < 2 ^ (prefixWord ++ tailWord_3375148).sum := by decide
  have hdescent : baseEnd_3375148 < baseStart_3375148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375154 : List Nat := [3, 2, 1, 1, 2, 3, 1, 10]
def baseStart_3375154 : Nat := 118140960795 + 3375154 * 2 ^ 59
def prefixEnd_3375154 : Nat := 4983230072969 + 3 ^ 40 * 3375154 * 2
def baseEnd_3375154 : Nat := 64188010553525664005665

theorem tailTrace_3375154 : CollatzResearch.WordTrace tailWord_3375154 prefixEnd_3375154 64188010553525664005665 := by
  unfold tailWord_3375154
  simp only [CollatzResearch.WordTrace]
  refine ⟨30775494903600240814085129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82067986409600642170893677 30775494903600240814085129)
  ·
    refine ⟨23081621177700180610563847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30775494903600240814085129 23081621177700180610563847)
    ·
      refine ⟨34622431766550270915845771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23081621177700180610563847 34622431766550270915845771)
      ·
        refine ⟨51933647649825406373768657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34622431766550270915845771 51933647649825406373768657)
        ·
          refine ⟨38950235737369054780326493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51933647649825406373768657 38950235737369054780326493)
          ·
            refine ⟨14606338401513395542622435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38950235737369054780326493 14606338401513395542622435)
            ·
              refine ⟨21909507602270093313933653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14606338401513395542622435 21909507602270093313933653)
              ·
                refine ⟨64188010553525664005665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21909507602270093313933653 64188010553525664005665)
                ·
                  rfl

theorem cell23_3375154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 10].length) (baseStart_3375154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375154 prefixEnd_3375154 := by exact prefixLift 3375154
  have htrace : WordTrace (prefixWord ++ tailWord_3375154) baseStart_3375154 baseEnd_3375154 := by
    simpa [prefixWord, tailWord_3375154, baseEnd_3375154] using wordTrace_append hprefix tailTrace_3375154
  have hstable : (prefixWord ++ tailWord_3375154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375154).length < 2 ^ (prefixWord ++ tailWord_3375154).sum := by decide
  have hdescent : baseEnd_3375154 < baseStart_3375154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375168 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 3]
def baseStart_3375168 : Nat := 118140960795 + 3375168 * 2 ^ 59
def prefixEnd_3375168 : Nat := 4983230072969 + 3 ^ 40 * 3375168 * 2
def baseEnd_3375168 : Nat := 1733083473674355873377891

theorem tailTrace_3375168 : CollatzResearch.WordTrace tailWord_3375168 prefixEnd_3375168 1733083473674355873377891 := by
  unfold tailWord_3375168
  simp only [CollatzResearch.WordTrace]
  refine ⟨61551245118175121823675079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82068326824233495764900105 61551245118175121823675079)
  ·
    refine ⟨92326867677262682735512619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61551245118175121823675079 92326867677262682735512619)
    ·
      refine ⟨138490301515894024103268929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92326867677262682735512619 138490301515894024103268929)
      ·
        refine ⟨103867726136920518077451697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138490301515894024103268929 103867726136920518077451697)
        ·
          refine ⟨77900794602690388558088773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103867726136920518077451697 77900794602690388558088773)
          ·
            refine ⟨14606398988004447854641645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77900794602690388558088773 14606398988004447854641645)
            ·
              refine ⟨5477399620501667945490617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14606398988004447854641645 5477399620501667945490617)
              ·
                refine ⟨4108049715376250959117963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5477399620501667945490617 4108049715376250959117963)
                ·
                  refine ⟨6162074573064376438676945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108049715376250959117963 6162074573064376438676945)
                  ·
                    refine ⟨4621555929798282329007709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6162074573064376438676945 4621555929798282329007709)
                    ·
                      refine ⟨1733083473674355873377891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4621555929798282329007709 1733083473674355873377891)
                      ·
                        rfl

theorem cell23_3375168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_3375168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375168 prefixEnd_3375168 := by exact prefixLift 3375168
  have htrace : WordTrace (prefixWord ++ tailWord_3375168) baseStart_3375168 baseEnd_3375168 := by
    simpa [prefixWord, tailWord_3375168, baseEnd_3375168] using wordTrace_append hprefix tailTrace_3375168
  have hstable : (prefixWord ++ tailWord_3375168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375168).length < 2 ^ (prefixWord ++ tailWord_3375168).sum := by decide
  have hdescent : baseEnd_3375168 < baseStart_3375168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375242 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2]
def baseStart_3375242 : Nat := 118140960795 + 3375242 * 2 ^ 59
def prefixEnd_3375242 : Nat := 4983230072969 + 3 ^ 40 * 3375242 * 2
def baseEnd_3375242 : Nat := 1733121471242788583852551

theorem tailTrace_3375242 : CollatzResearch.WordTrace tailWord_3375242 prefixEnd_3375242 1733121471242788583852551 := by
  unfold tailWord_3375242
  simp only [CollatzResearch.WordTrace]
  refine ⟨30776297309520538571385995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82070126158721436190362653 30776297309520538571385995)
  ·
    refine ⟨46164445964280807857078993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30776297309520538571385995 46164445964280807857078993)
    ·
      refine ⟨34623334473210605892809245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46164445964280807857078993 34623334473210605892809245)
      ·
        refine ⟨12983750427453977209803467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34623334473210605892809245 12983750427453977209803467)
        ·
          refine ⟨19475625641180965814705201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12983750427453977209803467 19475625641180965814705201)
          ·
            refine ⟨14606719230885724361028901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19475625641180965814705201 14606719230885724361028901)
            ·
              refine ⟨2738759855791073317692919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14606719230885724361028901 2738759855791073317692919)
              ·
                refine ⟨4108139783686609976539379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2738759855791073317692919 4108139783686609976539379)
                ·
                  refine ⟨6162209675529914964809069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108139783686609976539379 6162209675529914964809069)
                  ·
                    refine ⟨2310828628323718111803401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6162209675529914964809069 2310828628323718111803401)
                    ·
                      refine ⟨1733121471242788583852551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310828628323718111803401 1733121471242788583852551)
                      ·
                        rfl

theorem cell23_3375242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_3375242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375242 prefixEnd_3375242 := by exact prefixLift 3375242
  have htrace : WordTrace (prefixWord ++ tailWord_3375242) baseStart_3375242 baseEnd_3375242 := by
    simpa [prefixWord, tailWord_3375242, baseEnd_3375242] using wordTrace_append hprefix tailTrace_3375242
  have hstable : (prefixWord ++ tailWord_3375242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375242).length < 2 ^ (prefixWord ++ tailWord_3375242).sum := by decide
  have hdescent : baseEnd_3375242 < baseStart_3375242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375261 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 7]
def baseStart_3375261 : Nat := 118140960795 + 3375261 * 2 ^ 59
def prefixEnd_3375261 : Nat := 4983230072969 + 3 ^ 40 * 3375261 * 2
def baseEnd_3375261 : Nat := 192570136375024889946107

theorem tailTrace_3375261 : CollatzResearch.WordTrace tailWord_3375261 prefixEnd_3375261 192570136375024889946107 := by
  unfold tailWord_3375261
  simp only [CollatzResearch.WordTrace]
  refine ⟨123105882225013320530485637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82070588150008880353657091 123105882225013320530485637)
  ·
    refine ⟨23082352917189997599466057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123105882225013320530485637 23082352917189997599466057)
    ·
      refine ⟨17311764687892498199599543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23082352917189997599466057 17311764687892498199599543)
      ·
        refine ⟨25967647031838747299399315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17311764687892498199599543 25967647031838747299399315)
        ·
          refine ⟨38951470547758120949098973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25967647031838747299399315 38951470547758120949098973)
          ·
            refine ⟨14606801455409295355912115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38951470547758120949098973 14606801455409295355912115)
            ·
              refine ⟨21910202183113943033868173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14606801455409295355912115 21910202183113943033868173)
              ·
                refine ⟨8216325818667728637700565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21910202183113943033868173 8216325818667728637700565)
                ·
                  refine ⟨192570136375024889946107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8216325818667728637700565 192570136375024889946107)
                  ·
                    rfl

theorem cell23_3375261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_3375261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375261 prefixEnd_3375261 := by exact prefixLift 3375261
  have htrace : WordTrace (prefixWord ++ tailWord_3375261) baseStart_3375261 baseEnd_3375261 := by
    simpa [prefixWord, tailWord_3375261, baseEnd_3375261] using wordTrace_append hprefix tailTrace_3375261
  have hstable : (prefixWord ++ tailWord_3375261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375261).length < 2 ^ (prefixWord ++ tailWord_3375261).sum := by decide
  have hdescent : baseEnd_3375261 < baseStart_3375261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375291 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 2, 5]
def baseStart_3375291 : Nat := 118140960795 + 3375291 * 2 ^ 59
def prefixEnd_3375291 : Nat := 4983230072969 + 3 ^ 40 * 3375291 * 2
def baseEnd_3375291 : Nat := 577715543931619630713275

theorem tailTrace_3375291 : CollatzResearch.WordTrace tailWord_3375291 prefixEnd_3375291 577715543931619630713275 := by
  unfold tailWord_3375291
  simp only [CollatzResearch.WordTrace]
  refine ⟨123106976414904635654077727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82071317609936423769385151 123106976414904635654077727)
  ·
    refine ⟨184660464622356953481116591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123106976414904635654077727 184660464622356953481116591)
    ·
      refine ⟨276990696933535430221674887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184660464622356953481116591 276990696933535430221674887)
      ·
        refine ⟨415486045400303145332512331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276990696933535430221674887 415486045400303145332512331)
        ·
          refine ⟨623229068100454717998768497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415486045400303145332512331 623229068100454717998768497)
          ·
            refine ⟨467421801075341038499076373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 623229068100454717998768497 467421801075341038499076373)
            ·
              refine ⟨21910396925406611179644205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 467421801075341038499076373 21910396925406611179644205)
              ·
                refine ⟨8216398847027479192366577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21910396925406611179644205 8216398847027479192366577)
                ·
                  refine ⟨6162299135270609394274933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8216398847027479192366577 6162299135270609394274933)
                  ·
                    refine ⟨577715543931619630713275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6162299135270609394274933 577715543931619630713275)
                    ·
                      rfl

theorem cell23_3375291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 5].length) (baseStart_3375291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375291 prefixEnd_3375291 := by exact prefixLift 3375291
  have htrace : WordTrace (prefixWord ++ tailWord_3375291) baseStart_3375291 baseEnd_3375291 := by
    simpa [prefixWord, tailWord_3375291, baseEnd_3375291] using wordTrace_append hprefix tailTrace_3375291
  have hstable : (prefixWord ++ tailWord_3375291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375291).length < 2 ^ (prefixWord ++ tailWord_3375291).sum := by decide
  have hdescent : baseEnd_3375291 < baseStart_3375291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375328 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 1, 6, 2]
def baseStart_3375328 : Nat := 118140960795 + 3375328 * 2 ^ 59
def prefixEnd_3375328 : Nat := 4983230072969 + 3 ^ 40 * 3375328 * 2
def baseEnd_3375328 : Nat := 1733165630579075247377155

theorem tailTrace_3375328 : CollatzResearch.WordTrace tailWord_3375328 prefixEnd_3375328 1733165630579075247377155 := by
  unfold tailWord_3375328
  simp only [CollatzResearch.WordTrace]
  refine ⟨61554162957885295486587319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82072217277180393982116425 61554162957885295486587319)
  ·
    refine ⟨92331244436827943229880979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61554162957885295486587319 92331244436827943229880979)
    ·
      refine ⟨138496866655241914844821469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92331244436827943229880979 138496866655241914844821469)
      ·
        refine ⟨51936324995715718066808051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138496866655241914844821469 51936324995715718066808051)
        ·
          refine ⟨77904487493573577100212077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51936324995715718066808051 77904487493573577100212077)
          ·
            refine ⟨29214182810090091412579529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77904487493573577100212077 29214182810090091412579529)
            ·
              refine ⟨21910637107567568559434647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29214182810090091412579529 21910637107567568559434647)
              ·
                refine ⟨32865955661351352839151971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21910637107567568559434647 32865955661351352839151971)
                ·
                  refine ⟨49298933492027029258727957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32865955661351352839151971 49298933492027029258727957)
                  ·
                    refine ⟨2310887507438766996502873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49298933492027029258727957 2310887507438766996502873)
                    ·
                      refine ⟨1733165630579075247377155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2310887507438766996502873 1733165630579075247377155)
                      ·
                        rfl

theorem cell23_3375328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_3375328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375328 prefixEnd_3375328 := by exact prefixLift 3375328
  have htrace : WordTrace (prefixWord ++ tailWord_3375328) baseStart_3375328 baseEnd_3375328 := by
    simpa [prefixWord, tailWord_3375328, baseEnd_3375328] using wordTrace_append hprefix tailTrace_3375328
  have hstable : (prefixWord ++ tailWord_3375328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375328).length < 2 ^ (prefixWord ++ tailWord_3375328).sum := by decide
  have hdescent : baseEnd_3375328 < baseStart_3375328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375338 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 5, 4]
def baseStart_3375338 : Nat := 118140960795 + 3375338 * 2 ^ 59
def prefixEnd_3375338 : Nat := 4983230072969 + 3 ^ 40 * 3375338 * 2
def baseEnd_3375338 : Nat := 577723588461873402750703

theorem tailTrace_3375338 : CollatzResearch.WordTrace tailWord_3375338 prefixEnd_3375338 577723588461873402750703 := by
  unfold tailWord_3375338
  simp only [CollatzResearch.WordTrace]
  refine ⟨30777172661433590670259667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82072460430489575120692445 30777172661433590670259667)
  ·
    refine ⟨46165758992150386005389501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30777172661433590670259667 46165758992150386005389501)
    ·
      refine ⟨17312159622056394752021063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46165758992150386005389501 17312159622056394752021063)
      ·
        refine ⟨25968239433084592128031595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17312159622056394752021063 25968239433084592128031595)
        ·
          refine ⟨38952359149626888192047393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25968239433084592128031595 38952359149626888192047393)
          ·
            refine ⟨29214269362220166144035545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38952359149626888192047393 29214269362220166144035545)
            ·
              refine ⟨21910702021665124608026659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29214269362220166144035545 21910702021665124608026659)
              ·
                refine ⟨32866053032497686912039989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21910702021665124608026659 32866053032497686912039989)
                ·
                  refine ⟨3081192471796658148003749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32866053032497686912039989 3081192471796658148003749)
                  ·
                    refine ⟨577723588461873402750703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3081192471796658148003749 577723588461873402750703)
                    ·
                      rfl

theorem cell23_3375338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_3375338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375338 prefixEnd_3375338 := by exact prefixLift 3375338
  have htrace : WordTrace (prefixWord ++ tailWord_3375338) baseStart_3375338 baseEnd_3375338 := by
    simpa [prefixWord, tailWord_3375338, baseEnd_3375338] using wordTrace_append hprefix tailTrace_3375338
  have hstable : (prefixWord ++ tailWord_3375338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375338).length < 2 ^ (prefixWord ++ tailWord_3375338).sum := by decide
  have hdescent : baseEnd_3375338 < baseStart_3375338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375358 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3375358 : Nat := 118140960795 + 3375358 * 2 ^ 59
def prefixEnd_3375358 : Nat := 4983230072969 + 3 ^ 40 * 3375358 * 2
def baseEnd_3375358 : Nat := 1733181034998710130002017

theorem tailTrace_3375358 : CollatzResearch.WordTrace tailWord_3375358 prefixEnd_3375358 1733181034998710130002017 := by
  unfold tailWord_3375358
  simp only [CollatzResearch.WordTrace]
  refine ⟨15388677513207738262095841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82072946737107937397844485 15388677513207738262095841)
  ·
    refine ⟨11541508134905803696571881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15388677513207738262095841 11541508134905803696571881)
    ·
      refine ⟨8656131101179352772428911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11541508134905803696571881 8656131101179352772428911)
      ·
        refine ⟨12984196651769029158643367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8656131101179352772428911 12984196651769029158643367)
        ·
          refine ⟨19476294977653543737965051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12984196651769029158643367 19476294977653543737965051)
          ·
            refine ⟨29214442466480315606947577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19476294977653543737965051 29214442466480315606947577)
            ·
              refine ⟨21910831849860236705210683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29214442466480315606947577 21910831849860236705210683)
              ·
                refine ⟨32866247774790355057816025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21910831849860236705210683 32866247774790355057816025)
                ·
                  refine ⟨24649685831092766293362019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32866247774790355057816025 24649685831092766293362019)
                  ·
                    refine ⟨36974528746639149440043029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24649685831092766293362019 36974528746639149440043029)
                    ·
                      refine ⟨1733181034998710130002017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36974528746639149440043029 1733181034998710130002017)
                      ·
                        rfl

theorem cell23_3375358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3375358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375358 prefixEnd_3375358 := by exact prefixLift 3375358
  have htrace : WordTrace (prefixWord ++ tailWord_3375358) baseStart_3375358 baseEnd_3375358 := by
    simpa [prefixWord, tailWord_3375358, baseEnd_3375358] using wordTrace_append hprefix tailTrace_3375358
  have hstable : (prefixWord ++ tailWord_3375358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375358).length < 2 ^ (prefixWord ++ tailWord_3375358).sum := by decide
  have hdescent : baseEnd_3375358 < baseStart_3375358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375368 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 6]
def baseStart_3375368 : Nat := 118140960795 + 3375368 * 2 ^ 59
def prefixEnd_3375368 : Nat := 4983230072969 + 3 ^ 40 * 3375368 * 2
def baseEnd_3375368 : Nat := 192576241089472787875219

theorem tailTrace_3375368 : CollatzResearch.WordTrace tailWord_3375368 prefixEnd_3375368 192576241089472787875219 := by
  unfold tailWord_3375368
  simp only [CollatzResearch.WordTrace]
  refine ⟨61554892417812838902315379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82073189890417118536420505 61554892417812838902315379)
  ·
    refine ⟨92332338626719258353473069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61554892417812838902315379 92332338626719258353473069)
    ·
      refine ⟨34624626985019721882552401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92332338626719258353473069 34624626985019721882552401)
      ·
        refine ⟨25968470238764791411914301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34624626985019721882552401 25968470238764791411914301)
        ·
          refine ⟨9738176339536796779467863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25968470238764791411914301 9738176339536796779467863)
          ·
            refine ⟨14607264509305195169201795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9738176339536796779467863 14607264509305195169201795)
            ·
              refine ⟨21910896763957792753802693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14607264509305195169201795 21910896763957792753802693)
              ·
                refine ⟨4108293143242086141338005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21910896763957792753802693 4108293143242086141338005)
                ·
                  refine ⟨192576241089472787875219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4108293143242086141338005 192576241089472787875219)
                  ·
                    rfl

theorem cell23_3375368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 6].length) (baseStart_3375368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375368 prefixEnd_3375368 := by exact prefixLift 3375368
  have htrace : WordTrace (prefixWord ++ tailWord_3375368) baseStart_3375368 baseEnd_3375368 := by
    simpa [prefixWord, tailWord_3375368, baseEnd_3375368] using wordTrace_append hprefix tailTrace_3375368
  have hstable : (prefixWord ++ tailWord_3375368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375368).length < 2 ^ (prefixWord ++ tailWord_3375368).sum := by decide
  have hdescent : baseEnd_3375368 < baseStart_3375368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375371 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 6]
def baseStart_3375371 : Nat := 118140960795 + 3375371 * 2 ^ 59
def prefixEnd_3375371 : Nat := 4983230072969 + 3 ^ 40 * 3375371 * 2
def baseEnd_3375371 : Nat := 1733187710247218579139457

theorem tailTrace_3375371 : CollatzResearch.WordTrace tailWord_3375371 prefixEnd_3375371 1733187710247218579139457 := by
  unfold tailWord_3375371
  simp only [CollatzResearch.WordTrace]
  refine ⟨123109894254614809316989967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82073262836409872877993311 123109894254614809316989967)
  ·
    refine ⟨184664841381922213975484951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123109894254614809316989967 184664841381922213975484951)
    ·
      refine ⟨276997262072883320963227427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184664841381922213975484951 276997262072883320963227427)
      ·
        refine ⟨415495893109324981444841141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276997262072883320963227427 415495893109324981444841141)
        ·
          refine ⟨38952739978999217010453857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 415495893109324981444841141 38952739978999217010453857)
          ·
            refine ⟨29214554984249412757840393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38952739978999217010453857 29214554984249412757840393)
            ·
              refine ⟨21910916238187059568380295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29214554984249412757840393 21910916238187059568380295)
              ·
                refine ⟨32866374357280589352570443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21910916238187059568380295 32866374357280589352570443)
                ·
                  refine ⟨49299561535920884028855665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32866374357280589352570443 49299561535920884028855665)
                  ·
                    refine ⟨36974671151940663021641749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49299561535920884028855665 36974671151940663021641749)
                    ·
                      refine ⟨1733187710247218579139457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36974671151940663021641749 1733187710247218579139457)
                      ·
                        rfl

theorem cell23_3375371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_3375371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375371 prefixEnd_3375371 := by exact prefixLift 3375371
  have htrace : WordTrace (prefixWord ++ tailWord_3375371) baseStart_3375371 baseEnd_3375371 := by
    simpa [prefixWord, tailWord_3375371, baseEnd_3375371] using wordTrace_append hprefix tailTrace_3375371
  have hstable : (prefixWord ++ tailWord_3375371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375371).length < 2 ^ (prefixWord ++ tailWord_3375371).sum := by decide
  have hdescent : baseEnd_3375371 < baseStart_3375371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375395 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 3, 1, 3]
def baseStart_3375395 : Nat := 118140960795 + 3375395 * 2 ^ 59
def prefixEnd_3375395 : Nat := 4983230072969 + 3 ^ 40 * 3375395 * 2
def baseEnd_3375395 : Nat := 1733200033782926485239347

theorem tailTrace_3375395 : CollatzResearch.WordTrace tailWord_3375395 prefixEnd_3375395 1733200033782926485239347 := by
  unfold tailWord_3375395
  simp only [CollatzResearch.WordTrace]
  refine ⟨123110769606527861415863639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82073846404351907610575759 123110769606527861415863639)
  ·
    refine ⟨184666154409791792123795459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123110769606527861415863639 184666154409791792123795459)
    ·
      refine ⟨276999231614687688185693189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184666154409791792123795459 276999231614687688185693189)
      ·
        refine ⟨51937355927753941534817473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276999231614687688185693189 51937355927753941534817473)
        ·
          refine ⟨38953016945815456151113105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51937355927753941534817473 38953016945815456151113105)
          ·
            refine ⟨29214762709361592113334829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38953016945815456151113105 29214762709361592113334829)
            ·
              refine ⟨10955536016010597042500561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29214762709361592113334829 10955536016010597042500561)
              ·
                refine ⟨8216652012007947781875421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10955536016010597042500561 8216652012007947781875421)
                ·
                  refine ⟨3081244504502980418203283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8216652012007947781875421 3081244504502980418203283)
                  ·
                    refine ⟨4621866756754470627304925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3081244504502980418203283 4621866756754470627304925)
                    ·
                      refine ⟨1733200033782926485239347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4621866756754470627304925 1733200033782926485239347)
                      ·
                        rfl

theorem cell23_3375395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_3375395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375395 prefixEnd_3375395 := by exact prefixLift 3375395
  have htrace : WordTrace (prefixWord ++ tailWord_3375395) baseStart_3375395 baseEnd_3375395 := by
    simpa [prefixWord, tailWord_3375395, baseEnd_3375395] using wordTrace_append hprefix tailTrace_3375395
  have hstable : (prefixWord ++ tailWord_3375395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375395).length < 2 ^ (prefixWord ++ tailWord_3375395).sum := by decide
  have hdescent : baseEnd_3375395 < baseStart_3375395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375399 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3375399 : Nat := 118140960795 + 3375399 * 2 ^ 59
def prefixEnd_3375399 : Nat := 4983230072969 + 3 ^ 40 * 3375399 * 2
def baseEnd_3375399 : Nat := 1733202087705544469589329

theorem tailTrace_3375399 : CollatzResearch.WordTrace tailWord_3375399 prefixEnd_3375399 1733202087705544469589329 := by
  unfold tailWord_3375399
  simp only [CollatzResearch.WordTrace]
  refine ⟨123110915498513370099009251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82073943665675580066006167 123110915498513370099009251)
  ·
    refine ⟨184666373247770055148513877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123110915498513370099009251 184666373247770055148513877)
    ·
      refine ⟨2164059061497305333771647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 184666373247770055148513877 2164059061497305333771647)
      ·
        refine ⟨3246088592245958000657471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164059061497305333771647 3246088592245958000657471)
        ·
          refine ⟨4869132888368937000986207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246088592245958000657471 4869132888368937000986207)
          ·
            refine ⟨7303699332553405501479311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4869132888368937000986207 7303699332553405501479311)
            ·
              refine ⟨10955548998830108252218967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7303699332553405501479311 10955548998830108252218967)
              ·
                refine ⟨16433323498245162378328451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10955548998830108252218967 16433323498245162378328451)
                ·
                  refine ⟨24649985247367743567492677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16433323498245162378328451 24649985247367743567492677)
                  ·
                    refine ⟨4621872233881451918904877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24649985247367743567492677 4621872233881451918904877)
                    ·
                      refine ⟨1733202087705544469589329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4621872233881451918904877 1733202087705544469589329)
                      ·
                        rfl

theorem cell23_3375399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3375399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375399 prefixEnd_3375399 := by exact prefixLift 3375399
  have htrace : WordTrace (prefixWord ++ tailWord_3375399) baseStart_3375399 baseEnd_3375399 := by
    simpa [prefixWord, tailWord_3375399, baseEnd_3375399] using wordTrace_append hprefix tailTrace_3375399
  have hstable : (prefixWord ++ tailWord_3375399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375399).length < 2 ^ (prefixWord ++ tailWord_3375399).sum := by decide
  have hdescent : baseEnd_3375399 < baseStart_3375399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375406 : List Nat := [4, 1, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3375406 : Nat := 118140960795 + 3375406 * 2 ^ 59
def prefixEnd_3375406 : Nat := 4983230072969 + 3 ^ 40 * 3375406 * 2
def baseEnd_3375406 : Nat := 577735227356708647400599

theorem tailTrace_3375406 : CollatzResearch.WordTrace tailWord_3375406 prefixEnd_3375406 577735227356708647400599 := by
  unfold tailWord_3375406
  simp only [CollatzResearch.WordTrace]
  refine ⟨15388896351186001286814259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82074113872992006863009381 15388896351186001286814259)
  ·
    refine ⟨23083344526779001930221389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15388896351186001286814259 23083344526779001930221389)
    ·
      refine ⟨8656254197542125723833021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23083344526779001930221389 8656254197542125723833021)
      ·
        refine ⟨3246095324078297146437383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8656254197542125723833021 3246095324078297146437383)
        ·
          refine ⟨4869142986117445719656075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246095324078297146437383 4869142986117445719656075)
          ·
            refine ⟨7303714479176168579484113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4869142986117445719656075 7303714479176168579484113)
            ·
              refine ⟨5477785859382126434613085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7303714479176168579484113 5477785859382126434613085)
              ·
                refine ⟨2054169697268297412979907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5477785859382126434613085 2054169697268297412979907)
                ·
                  refine ⟨3081254545902446119469861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054169697268297412979907 3081254545902446119469861)
                  ·
                    refine ⟨577735227356708647400599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3081254545902446119469861 577735227356708647400599)
                    ·
                      rfl

theorem cell23_3375406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3375406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375406 prefixEnd_3375406 := by exact prefixLift 3375406
  have htrace : WordTrace (prefixWord ++ tailWord_3375406) baseStart_3375406 baseEnd_3375406 := by
    simpa [prefixWord, tailWord_3375406, baseEnd_3375406] using wordTrace_append hprefix tailTrace_3375406
  have hstable : (prefixWord ++ tailWord_3375406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375406).length < 2 ^ (prefixWord ++ tailWord_3375406).sum := by decide
  have hdescent : baseEnd_3375406 < baseStart_3375406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375438 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_3375438 : Nat := 118140960795 + 3375438 * 2 ^ 59
def prefixEnd_3375438 : Nat := 4983230072969 + 3 ^ 40 * 3375438 * 2
def baseEnd_3375438 : Nat := 1733222113451069817001649

theorem tailTrace_3375438 : CollatzResearch.WordTrace tailWord_3375438 prefixEnd_3375438 1733222113451069817001649 := by
  unfold tailWord_3375438
  simp only [CollatzResearch.WordTrace]
  refine ⟨15389042243171509969959871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82074891963581386506452645 15389042243171509969959871)
  ·
    refine ⟨23083563364757264954939807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15389042243171509969959871 23083563364757264954939807)
    ·
      refine ⟨34625345047135897432409711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23083563364757264954939807 34625345047135897432409711)
      ·
        refine ⟨51938017570703846148614567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34625345047135897432409711 51938017570703846148614567)
        ·
          refine ⟨77907026356055769222921851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51938017570703846148614567 77907026356055769222921851)
          ·
            refine ⟨116860539534083653834382777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77907026356055769222921851 116860539534083653834382777)
            ·
              refine ⟨87645404650562740375787083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116860539534083653834382777 87645404650562740375787083)
              ·
                refine ⟨131468106975844110563680625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87645404650562740375787083 131468106975844110563680625)
                ·
                  refine ⟨98601080231883082922760469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131468106975844110563680625 98601080231883082922760469)
                  ·
                    refine ⟨4621925635869519512004397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98601080231883082922760469 4621925635869519512004397)
                    ·
                      refine ⟨1733222113451069817001649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4621925635869519512004397 1733222113451069817001649)
                      ·
                        rfl

theorem cell23_3375438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_3375438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375438 prefixEnd_3375438 := by exact prefixLift 3375438
  have htrace : WordTrace (prefixWord ++ tailWord_3375438) baseStart_3375438 baseEnd_3375438 := by
    simpa [prefixWord, tailWord_3375438, baseEnd_3375438] using wordTrace_append hprefix tailTrace_3375438
  have hstable : (prefixWord ++ tailWord_3375438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375438).length < 2 ^ (prefixWord ++ tailWord_3375438).sum := by decide
  have hdescent : baseEnd_3375438 < baseStart_3375438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375448 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_3375448 : Nat := 118140960795 + 3375448 * 2 ^ 59
def prefixEnd_3375448 : Nat := 4983230072969 + 3 ^ 40 * 3375448 * 2
def baseEnd_3375448 : Nat := 1733227248257614777876603

theorem tailTrace_3375448 : CollatzResearch.WordTrace tailWord_3375448 prefixEnd_3375448 1733227248257614777876603 := by
  unfold tailWord_3375448
  simp only [CollatzResearch.WordTrace]
  refine ⟨61556351337667925733771499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82075135116890567645028665 61556351337667925733771499)
  ·
    refine ⟨92334527006501888600657249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61556351337667925733771499 92334527006501888600657249)
    ·
      refine ⟨69250895254876416450492937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92334527006501888600657249 69250895254876416450492937)
      ·
        refine ⟨51938171441157312337869703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69250895254876416450492937 51938171441157312337869703)
        ·
          refine ⟨77907257161735968506804555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51938171441157312337869703 77907257161735968506804555)
          ·
            refine ⟨116860885742603952760206833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77907257161735968506804555 116860885742603952760206833)
            ·
              refine ⟨87645664306952964570155125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116860885742603952760206833 87645664306952964570155125)
              ·
                refine ⟨8216781028776840428452043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87645664306952964570155125 8216781028776840428452043)
                ·
                  refine ⟨12325171543165260642678065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8216781028776840428452043 12325171543165260642678065)
                  ·
                    refine ⟨9243878657373945482008549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12325171543165260642678065 9243878657373945482008549)
                    ·
                      refine ⟨1733227248257614777876603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9243878657373945482008549 1733227248257614777876603)
                      ·
                        rfl

theorem cell23_3375448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_3375448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375448 prefixEnd_3375448 := by exact prefixLift 3375448
  have htrace : WordTrace (prefixWord ++ tailWord_3375448) baseStart_3375448 baseEnd_3375448 := by
    simpa [prefixWord, tailWord_3375448, baseEnd_3375448] using wordTrace_append hprefix tailTrace_3375448
  have hstable : (prefixWord ++ tailWord_3375448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375448).length < 2 ^ (prefixWord ++ tailWord_3375448).sum := by decide
  have hdescent : baseEnd_3375448 < baseStart_3375448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375455 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 1, 2, 3]
def baseStart_3375455 : Nat := 118140960795 + 3375455 * 2 ^ 59
def prefixEnd_3375455 : Nat := 4983230072969 + 3 ^ 40 * 3375455 * 2
def baseEnd_3375455 : Nat := 1733230842622196250489071

theorem tailTrace_3375455 : CollatzResearch.WordTrace tailWord_3375455 prefixEnd_3375455 1733230842622196250489071 := by
  unfold tailWord_3375455
  simp only [CollatzResearch.WordTrace]
  refine ⟨123112957986310491663047819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82075305324206994442031879 123112957986310491663047819)
  ·
    refine ⟨184669436979465737494571729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123112957986310491663047819 184669436979465737494571729)
    ·
      refine ⟨138502077734599303120928797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184669436979465737494571729 138502077734599303120928797)
      ·
        refine ⟨51938279150474738670348299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138502077734599303120928797 51938279150474738670348299)
        ·
          refine ⟨77907418725712108005522449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51938279150474738670348299 77907418725712108005522449)
          ·
            refine ⟨58430564044284081004141837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77907418725712108005522449 58430564044284081004141837)
            ·
              refine ⟨21911461516606530376553189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58430564044284081004141837 21911461516606530376553189)
              ·
                refine ⟨4108399034363724445603723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21911461516606530376553189 4108399034363724445603723)
                ·
                  refine ⟨6162598551545586668405585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108399034363724445603723 6162598551545586668405585)
                  ·
                    refine ⟨4621948913659190001304189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6162598551545586668405585 4621948913659190001304189)
                    ·
                      refine ⟨1733230842622196250489071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4621948913659190001304189 1733230842622196250489071)
                      ·
                        rfl

theorem cell23_3375455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_3375455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375455 prefixEnd_3375455 := by exact prefixLift 3375455
  have htrace : WordTrace (prefixWord ++ tailWord_3375455) baseStart_3375455 baseEnd_3375455 := by
    simpa [prefixWord, tailWord_3375455, baseEnd_3375455] using wordTrace_append hprefix tailTrace_3375455
  have hstable : (prefixWord ++ tailWord_3375455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375455).length < 2 ^ (prefixWord ++ tailWord_3375455).sum := by decide
  have hdescent : baseEnd_3375455 < baseStart_3375455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375545 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3375545 : Nat := 118140960795 + 3375545 * 2 ^ 59
def prefixEnd_3375545 : Nat := 4983230072969 + 3 ^ 40 * 3375545 * 2
def baseEnd_3375545 : Nat := 1733277055881100898363657

theorem tailTrace_3375545 : CollatzResearch.WordTrace tailWord_3375545 prefixEnd_3375545 1733277055881100898363657 := by
  unfold tailWord_3375545
  simp only [CollatzResearch.WordTrace]
  refine ⟨123116240555984437033824089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82077493703989624689216059 123116240555984437033824089)
  ·
    refine ⟨92337180416988327775368067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123116240555984437033824089 92337180416988327775368067)
    ·
      refine ⟨138505770625482491663052101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92337180416988327775368067 138505770625482491663052101)
      ·
        refine ⟨25969831992277967186822269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138505770625482491663052101 25969831992277967186822269)
        ·
          refine ⟨9738686997104237695058351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25969831992277967186822269 9738686997104237695058351)
          ·
            refine ⟨14608030495656356542587527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9738686997104237695058351 14608030495656356542587527)
            ·
              refine ⟨21912045743484534813881291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14608030495656356542587527 21912045743484534813881291)
              ·
                refine ⟨32868068615226802220821937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21912045743484534813881291 32868068615226802220821937)
                ·
                  refine ⟨24651051461420101665616453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32868068615226802220821937 24651051461420101665616453)
                  ·
                    refine ⟨4622072149016269062303085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24651051461420101665616453 4622072149016269062303085)
                    ·
                      refine ⟨1733277055881100898363657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4622072149016269062303085 1733277055881100898363657)
                      ·
                        rfl

theorem cell23_3375545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3375545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375545 prefixEnd_3375545 := by exact prefixLift 3375545
  have htrace : WordTrace (prefixWord ++ tailWord_3375545) baseStart_3375545 baseEnd_3375545 := by
    simpa [prefixWord, tailWord_3375545, baseEnd_3375545] using wordTrace_append hprefix tailTrace_3375545
  have hstable : (prefixWord ++ tailWord_3375545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375545).length < 2 ^ (prefixWord ++ tailWord_3375545).sum := by decide
  have hdescent : baseEnd_3375545 < baseStart_3375545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375559 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 2, 2, 2]
def baseStart_3375559 : Nat := 118140960795 + 3375559 * 2 ^ 59
def prefixEnd_3375559 : Nat := 4983230072969 + 3 ^ 40 * 3375559 * 2
def baseEnd_3375559 : Nat := 1733284244610263843588593

theorem tailTrace_3375559 : CollatzResearch.WordTrace tailWord_3375559 prefixEnd_3375559 1733284244610263843588593 := by
  unfold tailWord_3375559
  simp only [CollatzResearch.WordTrace]
  refine ⟨123116751177933717424833731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82077834118622478283222487 123116751177933717424833731)
  ·
    refine ⟨184675126766900576137250597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123116751177933717424833731 184675126766900576137250597)
    ·
      refine ⟨34626586268793858025734487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184675126766900576137250597 34626586268793858025734487)
      ·
        refine ⟨51939879403190787038601731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34626586268793858025734487 51939879403190787038601731)
        ·
          refine ⟨77909819104786180557902597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51939879403190787038601731 77909819104786180557902597)
          ·
            refine ⟨14608091082147408854606737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77909819104786180557902597 14608091082147408854606737)
            ·
              refine ⟨10956068311610556640955053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14608091082147408854606737 10956068311610556640955053)
              ·
                refine ⟨4108525616853958740358145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10956068311610556640955053 4108525616853958740358145)
                ·
                  refine ⟨3081394212640469055268609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4108525616853958740358145 3081394212640469055268609)
                  ·
                    refine ⟨2311045659480351791451457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3081394212640469055268609 2311045659480351791451457)
                    ·
                      refine ⟨1733284244610263843588593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311045659480351791451457 1733284244610263843588593)
                      ·
                        rfl

theorem cell23_3375559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_3375559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375559 prefixEnd_3375559 := by exact prefixLift 3375559
  have htrace : WordTrace (prefixWord ++ tailWord_3375559) baseStart_3375559 baseEnd_3375559 := by
    simpa [prefixWord, tailWord_3375559, baseEnd_3375559] using wordTrace_append hprefix tailTrace_3375559
  have hstable : (prefixWord ++ tailWord_3375559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375559).length < 2 ^ (prefixWord ++ tailWord_3375559).sum := by decide
  have hdescent : baseEnd_3375559 < baseStart_3375559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375625 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 5, 4]
def baseStart_3375625 : Nat := 118140960795 + 3375625 * 2 ^ 59
def prefixEnd_3375625 : Nat := 4983230072969 + 3 ^ 40 * 3375625 * 2
def baseEnd_3375625 : Nat := 577772711444486861787763

theorem tailTrace_3375625 : CollatzResearch.WordTrace tailWord_3375625 prefixEnd_3375625 577772711444486861787763 := by
  unfold tailWord_3375625
  simp only [CollatzResearch.WordTrace]
  refine ⟨123119158395694610696736329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82079438930463073797824219 123119158395694610696736329)
  ·
    refine ⟨92339368796770958022552247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123119158395694610696736329 92339368796770958022552247)
    ·
      refine ⟨138509053195156437033828371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92339368796770958022552247 138509053195156437033828371)
      ·
        refine ⟨207763579792734655550742557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138509053195156437033828371 207763579792734655550742557)
        ·
          refine ⟨77911342422275495831528459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207763579792734655550742557 77911342422275495831528459)
          ·
            refine ⟨116867013633413243747292689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77911342422275495831528459 116867013633413243747292689)
            ·
              refine ⟨87650260225059932810469517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116867013633413243747292689 87650260225059932810469517)
              ·
                refine ⟨32868847584397474803926069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87650260225059932810469517 32868847584397474803926069)
                ·
                  refine ⟨3081454461037263262868069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32868847584397474803926069 3081454461037263262868069)
                  ·
                    refine ⟨577772711444486861787763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3081454461037263262868069 577772711444486861787763)
                    ·
                      rfl

theorem cell23_3375625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 5, 4].length) (baseStart_3375625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375625 prefixEnd_3375625 := by exact prefixLift 3375625
  have htrace : WordTrace (prefixWord ++ tailWord_3375625) baseStart_3375625 baseEnd_3375625 := by
    simpa [prefixWord, tailWord_3375625, baseEnd_3375625] using wordTrace_append hprefix tailTrace_3375625
  have hstable : (prefixWord ++ tailWord_3375625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375625).length < 2 ^ (prefixWord ++ tailWord_3375625).sum := by decide
  have hdescent : baseEnd_3375625 < baseStart_3375625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375629 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3375629 : Nat := 118140960795 + 3375629 * 2 ^ 59
def prefixEnd_3375629 : Nat := 4983230072969 + 3 ^ 40 * 3375629 * 2
def baseEnd_3375629 : Nat := 577773396085359523237757

theorem tailTrace_3375629 : CollatzResearch.WordTrace tailWord_3375629 prefixEnd_3375629 577773396085359523237757 := by
  unfold tailWord_3375629
  simp only [CollatzResearch.WordTrace]
  refine ⟨123119304287680119379881941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82079536191786746253254627 123119304287680119379881941)
  ·
    refine ⟨2885608694242502797965983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 123119304287680119379881941 2885608694242502797965983)
    ·
      refine ⟨4328413041363754196948975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2885608694242502797965983 4328413041363754196948975)
      ·
        refine ⟨6492619562045631295423463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4328413041363754196948975 6492619562045631295423463)
        ·
          refine ⟨9738929343068446943135195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6492619562045631295423463 9738929343068446943135195)
          ·
            refine ⟨14608394014602670414702793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9738929343068446943135195 14608394014602670414702793)
            ·
              refine ⟨10956295510952002811027095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14608394014602670414702793 10956295510952002811027095)
              ·
                refine ⟨16434443266428004216540643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10956295510952002811027095 16434443266428004216540643)
                ·
                  refine ⟨24651664899642006324810965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16434443266428004216540643 24651664899642006324810965)
                  ·
                    refine ⟨577773396085359523237757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24651664899642006324810965 577773396085359523237757)
                    ·
                      rfl

theorem cell23_3375629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3375629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375629 prefixEnd_3375629 := by exact prefixLift 3375629
  have htrace : WordTrace (prefixWord ++ tailWord_3375629) baseStart_3375629 baseEnd_3375629 := by
    simpa [prefixWord, tailWord_3375629, baseEnd_3375629] using wordTrace_append hprefix tailTrace_3375629
  have hstable : (prefixWord ++ tailWord_3375629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375629).length < 2 ^ (prefixWord ++ tailWord_3375629).sum := by decide
  have hdescent : baseEnd_3375629 < baseStart_3375629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375635 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 3]
def baseStart_3375635 : Nat := 118140960795 + 3375635 * 2 ^ 59
def prefixEnd_3375635 : Nat := 4983230072969 + 3 ^ 40 * 3375635 * 2
def baseEnd_3375635 : Nat := 1733323269140005546238243

theorem tailTrace_3375635 : CollatzResearch.WordTrace tailWord_3375635 prefixEnd_3375635 1733323269140005546238243 := by
  unfold tailWord_3375635
  simp only [CollatzResearch.WordTrace]
  refine ⟨123119523125658382404600359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82079682083772254936400239 123119523125658382404600359)
  ·
    refine ⟨184679284688487573606900539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123119523125658382404600359 184679284688487573606900539)
    ·
      refine ⟨277018927032731360410350809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184679284688487573606900539 277018927032731360410350809)
      ·
        refine ⟨207764195274548520307763107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277018927032731360410350809 207764195274548520307763107)
        ·
          refine ⟨311646292911822780461644661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207764195274548520307763107 311646292911822780461644661)
          ·
            refine ⟨29216839960483385668279187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 311646292911822780461644661 29216839960483385668279187)
            ·
              refine ⟨43825259940725078502418781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29216839960483385668279187 43825259940725078502418781)
              ·
                refine ⟨16434472477771904438407043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43825259940725078502418781 16434472477771904438407043)
                ·
                  refine ⟨24651708716657856657610565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16434472477771904438407043 24651708716657856657610565)
                  ·
                    refine ⟨4622195384373348123301981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24651708716657856657610565 4622195384373348123301981)
                    ·
                      refine ⟨1733323269140005546238243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4622195384373348123301981 1733323269140005546238243)
                      ·
                        rfl

theorem cell23_3375635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 3].length) (baseStart_3375635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375635 prefixEnd_3375635 := by exact prefixLift 3375635
  have htrace : WordTrace (prefixWord ++ tailWord_3375635) baseStart_3375635 baseEnd_3375635 := by
    simpa [prefixWord, tailWord_3375635, baseEnd_3375635] using wordTrace_append hprefix tailTrace_3375635
  have hstable : (prefixWord ++ tailWord_3375635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375635).length < 2 ^ (prefixWord ++ tailWord_3375635).sum := by decide
  have hdescent : baseEnd_3375635 < baseStart_3375635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375686 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3375686 : Nat := 118140960795 + 3375686 * 2 ^ 59
def prefixEnd_3375686 : Nat := 4983230072969 + 3 ^ 40 * 3375686 * 2
def baseEnd_3375686 : Nat := 1733349456653384846700509

theorem tailTrace_3375686 : CollatzResearch.WordTrace tailWord_3375686 prefixEnd_3375686 1733349456653384846700509 := by
  unfold tailWord_3375686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3847543226514800566084591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82080922165649078743137941 3847543226514800566084591)
  ·
    refine ⟨5771314839772200849126887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3847543226514800566084591 5771314839772200849126887)
    ·
      refine ⟨8656972259658301273690331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5771314839772200849126887 8656972259658301273690331)
      ·
        refine ⟨12985458389487451910535497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8656972259658301273690331 12985458389487451910535497)
        ·
          refine ⟨9739093792115588932901623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12985458389487451910535497 9739093792115588932901623)
          ·
            refine ⟨14608640688173383399352435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9739093792115588932901623 14608640688173383399352435)
            ·
              refine ⟨21912961032260075099028653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14608640688173383399352435 21912961032260075099028653)
              ·
                refine ⟨8217360387097528162135745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21912961032260075099028653 8217360387097528162135745)
                ·
                  refine ⟨6163020290323146121601809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8217360387097528162135745 6163020290323146121601809)
                  ·
                    refine ⟨4622265217742359591201357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6163020290323146121601809 4622265217742359591201357)
                    ·
                      refine ⟨1733349456653384846700509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4622265217742359591201357 1733349456653384846700509)
                      ·
                        rfl

theorem cell23_3375686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3375686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375686 prefixEnd_3375686 := by exact prefixLift 3375686
  have htrace : WordTrace (prefixWord ++ tailWord_3375686) baseStart_3375686 baseEnd_3375686 := by
    simpa [prefixWord, tailWord_3375686, baseEnd_3375686] using wordTrace_append hprefix tailTrace_3375686
  have hstable : (prefixWord ++ tailWord_3375686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375686).length < 2 ^ (prefixWord ++ tailWord_3375686).sum := by decide
  have hdescent : baseEnd_3375686 < baseStart_3375686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375715 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 3, 6]
def baseStart_3375715 : Nat := 118140960795 + 3375715 * 2 ^ 59
def prefixEnd_3375715 : Nat := 4983230072969 + 3 ^ 40 * 3375715 * 2
def baseEnd_3375715 : Nat := 577788115864121744412625

theorem tailTrace_3375715 : CollatzResearch.WordTrace tailWord_3375715 prefixEnd_3375715 577788115864121744412625 := by
  unfold tailWord_3375715
  simp only [CollatzResearch.WordTrace]
  refine ⟨123122440965368556067512599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82081627310245704045008399 123122440965368556067512599)
  ·
    refine ⟨184683661448052834101268899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123122440965368556067512599 184683661448052834101268899)
    ·
      refine ⟨277025492172079251151903349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184683661448052834101268899 277025492172079251151903349)
      ·
        refine ⟨25971139891132429795490939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 277025492172079251151903349 25971139891132429795490939)
        ·
          refine ⟨38956709836698644693236409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25971139891132429795490939 38956709836698644693236409)
          ·
            refine ⟨29217532377523983519927307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38956709836698644693236409 29217532377523983519927307)
            ·
              refine ⟨43826298566285975279890961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29217532377523983519927307 43826298566285975279890961)
              ·
                refine ⟨32869723924714481459918221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43826298566285975279890961 32869723924714481459918221)
                ·
                  refine ⟨12326146471767930547469333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32869723924714481459918221 12326146471767930547469333)
                  ·
                    refine ⟨577788115864121744412625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12326146471767930547469333 577788115864121744412625)
                    ·
                      rfl

theorem cell23_3375715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 6].length) (baseStart_3375715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375715 prefixEnd_3375715 := by exact prefixLift 3375715
  have htrace : WordTrace (prefixWord ++ tailWord_3375715) baseStart_3375715 baseEnd_3375715 := by
    simpa [prefixWord, tailWord_3375715, baseEnd_3375715] using wordTrace_append hprefix tailTrace_3375715
  have hstable : (prefixWord ++ tailWord_3375715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375715).length < 2 ^ (prefixWord ++ tailWord_3375715).sum := by decide
  have hdescent : baseEnd_3375715 < baseStart_3375715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375716 : List Nat := [2, 3, 1, 1, 2, 2, 3, 4, 1, 1, 3]
def baseStart_3375716 : Nat := 118140960795 + 3375716 * 2 ^ 59
def prefixEnd_3375716 : Nat := 4983230072969 + 3 ^ 40 * 3375716 * 2
def baseEnd_3375716 : Nat := 1733364861073019729325371

theorem tailTrace_3375716 : CollatzResearch.WordTrace tailWord_3375716 prefixEnd_3375716 1733364861073019729325371 := by
  unfold tailWord_3375716
  simp only [CollatzResearch.WordTrace]
  refine ⟨61561238719182466619149501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82081651625576622158866001 61561238719182466619149501)
  ·
    refine ⟨23085464519693424982181063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61561238719182466619149501 23085464519693424982181063)
    ·
      refine ⟨34628196779540137473271595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23085464519693424982181063 34628196779540137473271595)
      ·
        refine ⟨51942295169310206209907393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34628196779540137473271595 51942295169310206209907393)
        ·
          refine ⟨38956721376982654657430545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51942295169310206209907393 38956721376982654657430545)
          ·
            refine ⟨29217541032736990993072909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38956721376982654657430545 29217541032736990993072909)
            ·
              refine ⟨10956577887276371622402341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29217541032736990993072909 10956577887276371622402341)
              ·
                refine ⟨2054358353864319679200439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10956577887276371622402341 2054358353864319679200439)
                ·
                  refine ⟨3081537530796479518800659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054358353864319679200439 3081537530796479518800659)
                  ·
                    refine ⟨4622306296194719278200989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3081537530796479518800659 4622306296194719278200989)
                    ·
                      refine ⟨1733364861073019729325371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4622306296194719278200989 1733364861073019729325371)
                      ·
                        rfl

theorem cell23_3375716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 1, 1, 3].length) (baseStart_3375716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375716 prefixEnd_3375716 := by exact prefixLift 3375716
  have htrace : WordTrace (prefixWord ++ tailWord_3375716) baseStart_3375716 baseEnd_3375716 := by
    simpa [prefixWord, tailWord_3375716, baseEnd_3375716] using wordTrace_append hprefix tailTrace_3375716
  have hstable : (prefixWord ++ tailWord_3375716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375716).length < 2 ^ (prefixWord ++ tailWord_3375716).sum := by decide
  have hdescent : baseEnd_3375716 < baseStart_3375716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375722 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3375722 : Nat := 118140960795 + 3375722 * 2 ^ 59
def prefixEnd_3375722 : Nat := 4983230072969 + 3 ^ 40 * 3375722 * 2
def baseEnd_3375722 : Nat := 1733367941956946705850343

theorem tailTrace_3375722 : CollatzResearch.WordTrace tailWord_3375722 prefixEnd_3375722 1733367941956946705850343 := by
  unfold tailWord_3375722
  simp only [CollatzResearch.WordTrace]
  refine ⟨30780674069085799065754355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82081797517562130842011613 30780674069085799065754355)
  ·
    refine ⟨46171011103628698598631533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30780674069085799065754355 46171011103628698598631533)
    ·
      refine ⟨17314129163860761974486825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46171011103628698598631533 17314129163860761974486825)
      ·
        refine ⟨12985596872895571480865119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17314129163860761974486825 12985596872895571480865119)
        ·
          refine ⟨19478395309343357221297679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12985596872895571480865119 19478395309343357221297679)
          ·
            refine ⟨29217592964015035831946519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19478395309343357221297679 29217592964015035831946519)
            ·
              refine ⟨43826389446022553747919779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29217592964015035831946519 43826389446022553747919779)
              ·
                refine ⟨65739584169033830621879669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43826389446022553747919779 65739584169033830621879669)
                ·
                  refine ⟨6163086015846921620801219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65739584169033830621879669 6163086015846921620801219)
                  ·
                    refine ⟨9244629023770382431201829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6163086015846921620801219 9244629023770382431201829)
                    ·
                      refine ⟨1733367941956946705850343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9244629023770382431201829 1733367941956946705850343)
                      ·
                        rfl

theorem cell23_3375722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3375722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375722 prefixEnd_3375722 := by exact prefixLift 3375722
  have htrace : WordTrace (prefixWord ++ tailWord_3375722) baseStart_3375722 baseEnd_3375722 := by
    simpa [prefixWord, tailWord_3375722, baseEnd_3375722] using wordTrace_append hprefix tailTrace_3375722
  have hstable : (prefixWord ++ tailWord_3375722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375722).length < 2 ^ (prefixWord ++ tailWord_3375722).sum := by decide
  have hdescent : baseEnd_3375722 < baseStart_3375722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375735 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_3375735 : Nat := 118140960795 + 3375735 * 2 ^ 59
def prefixEnd_3375735 : Nat := 4983230072969 + 3 ^ 40 * 3375735 * 2
def baseEnd_3375735 : Nat := 1733374617205455154987783

theorem tailTrace_3375735 : CollatzResearch.WordTrace tailWord_3375735 prefixEnd_3375735 1733374617205455154987783 := by
  unfold tailWord_3375735
  simp only [CollatzResearch.WordTrace]
  refine ⟨123123170425296099483240659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82082113616864066322160439 123123170425296099483240659)
  ·
    refine ⟨184684755637944149224860989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123123170425296099483240659 184684755637944149224860989)
    ·
      refine ⟨69256783364229055959322871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184684755637944149224860989 69256783364229055959322871)
      ·
        refine ⟨103885175046343583938984307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69256783364229055959322871 103885175046343583938984307)
        ·
          refine ⟨155827762569515375908476461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103885175046343583938984307 155827762569515375908476461)
          ·
            refine ⟨58435410963568265965678673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155827762569515375908476461 58435410963568265965678673)
            ·
              refine ⟨43826558222676199474259005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58435410963568265965678673 43826558222676199474259005)
              ·
                refine ⟨16434959333503574802847127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43826558222676199474259005 16434959333503574802847127)
                ·
                  refine ⟨24652439000255362204270691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16434959333503574802847127 24652439000255362204270691)
                  ·
                    refine ⟨36978658500383043306406037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24652439000255362204270691 36978658500383043306406037)
                    ·
                      refine ⟨1733374617205455154987783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36978658500383043306406037 1733374617205455154987783)
                      ·
                        rfl

theorem cell23_3375735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_3375735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375735 prefixEnd_3375735 := by exact prefixLift 3375735
  have htrace : WordTrace (prefixWord ++ tailWord_3375735) baseStart_3375735 baseEnd_3375735 := by
    simpa [prefixWord, tailWord_3375735, baseEnd_3375735] using wordTrace_append hprefix tailTrace_3375735
  have hstable : (prefixWord ++ tailWord_3375735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375735).length < 2 ^ (prefixWord ++ tailWord_3375735).sum := by decide
  have hdescent : baseEnd_3375735 < baseStart_3375735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375762 : List Nat := [3, 2, 3, 1, 2, 2, 10]
def baseStart_3375762 : Nat := 118140960795 + 3375762 * 2 ^ 59
def prefixEnd_3375762 : Nat := 4983230072969 + 3 ^ 40 * 3375762 * 2
def baseEnd_3375762 : Nat := 21399857792384278387039

theorem tailTrace_3375762 : CollatzResearch.WordTrace tailWord_3375762 prefixEnd_3375762 21399857792384278387039 := by
  unfold tailWord_3375762
  simp only [CollatzResearch.WordTrace]
  refine ⟨30781038799049570773618385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82082770130798855396315693 30781038799049570773618385)
  ·
    refine ⟨23085779099287178080213789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30781038799049570773618385 23085779099287178080213789)
    ·
      refine ⟨8657167162232691780080171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23085779099287178080213789 8657167162232691780080171)
      ·
        refine ⟨12985750743349037670120257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8657167162232691780080171 12985750743349037670120257)
        ·
          refine ⟨9739313057511778252590193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12985750743349037670120257 9739313057511778252590193)
          ·
            refine ⟨7304484793133833689442645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9739313057511778252590193 7304484793133833689442645)
            ·
              refine ⟨21399857792384278387039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7304484793133833689442645 21399857792384278387039)
              ·
                rfl

theorem cell23_3375762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 10].length) (baseStart_3375762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375762 prefixEnd_3375762 := by exact prefixLift 3375762
  have htrace : WordTrace (prefixWord ++ tailWord_3375762) baseStart_3375762 baseEnd_3375762 := by
    simpa [prefixWord, tailWord_3375762, baseEnd_3375762] using wordTrace_append hprefix tailTrace_3375762
  have hstable : (prefixWord ++ tailWord_3375762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375762).length < 2 ^ (prefixWord ++ tailWord_3375762).sum := by decide
  have hdescent : baseEnd_3375762 < baseStart_3375762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375765 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_3375765 : Nat := 118140960795 + 3375765 * 2 ^ 59
def prefixEnd_3375765 : Nat := 4983230072969 + 3 ^ 40 * 3375765 * 2
def baseEnd_3375765 : Nat := 1733390021625090037612645

theorem tailTrace_3375765 : CollatzResearch.WordTrace tailWord_3375765 prefixEnd_3375765 1733390021625090037612645 := by
  unfold tailWord_3375765
  simp only [CollatzResearch.WordTrace]
  refine ⟨123124264615187414606832749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82082843076791609737888499 123124264615187414606832749)
  ·
    refine ⟨46171599230695280477562281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123124264615187414606832749 46171599230695280477562281)
    ·
      refine ⟨34628699423021460358171711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46171599230695280477562281 34628699423021460358171711)
      ·
        refine ⟨51943049134532190537257567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34628699423021460358171711 51943049134532190537257567)
        ·
          refine ⟨77914573701798285805886351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51943049134532190537257567 77914573701798285805886351)
          ·
            refine ⟨116871860552697428708829527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77914573701798285805886351 116871860552697428708829527)
            ·
              refine ⟨175307790829046143063244291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116871860552697428708829527 175307790829046143063244291)
              ·
                refine ⟨262961686243569214594866437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175307790829046143063244291 262961686243569214594866437)
                ·
                  refine ⟨49305316170669227736537457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262961686243569214594866437 49305316170669227736537457)
                  ·
                    refine ⟨36978987128001920802403093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49305316170669227736537457 36978987128001920802403093)
                    ·
                      refine ⟨1733390021625090037612645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36978987128001920802403093 1733390021625090037612645)
                      ·
                        rfl

theorem cell23_3375765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_3375765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375765 prefixEnd_3375765 := by exact prefixLift 3375765
  have htrace : WordTrace (prefixWord ++ tailWord_3375765) baseStart_3375765 baseEnd_3375765 := by
    simpa [prefixWord, tailWord_3375765, baseEnd_3375765] using wordTrace_append hprefix tailTrace_3375765
  have hstable : (prefixWord ++ tailWord_3375765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375765).length < 2 ^ (prefixWord ++ tailWord_3375765).sum := by decide
  have hdescent : baseEnd_3375765 < baseStart_3375765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375773 : List Nat := [1, 4, 2, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_3375773 : Nat := 118140960795 + 3375773 * 2 ^ 59
def prefixEnd_3375773 : Nat := 4983230072969 + 3 ^ 40 * 3375773 * 2
def baseEnd_3375773 : Nat := 1733394129470326006312609

theorem tailTrace_3375773 : CollatzResearch.WordTrace tailWord_3375773 prefixEnd_3375773 1733394129470326006312609 := by
  unfold tailWord_3375773
  simp only [CollatzResearch.WordTrace]
  refine ⟨123124556399158431973123973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82083037599438954648749315 123124556399158431973123973)
  ·
    refine ⟨23085854324842205994960745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123124556399158431973123973 23085854324842205994960745)
    ·
      refine ⟨17314390743631654496220559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23085854324842205994960745 17314390743631654496220559)
      ·
        refine ⟨25971586115447481744330839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17314390743631654496220559 25971586115447481744330839)
        ·
          refine ⟨38957379173171222616496259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25971586115447481744330839 38957379173171222616496259)
          ·
            refine ⟨58436068759756833924744389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38957379173171222616496259 58436068759756833924744389)
            ·
              refine ⟨10956762892454406360889573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58436068759756833924744389 10956762892454406360889573)
              ·
                refine ⟨2054393042335201192666795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10956762892454406360889573 2054393042335201192666795)
                ·
                  refine ⟨3081589563502801789000193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054393042335201192666795 3081589563502801789000193)
                  ·
                    refine ⟨2311192172627101341750145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3081589563502801789000193 2311192172627101341750145)
                    ·
                      refine ⟨1733394129470326006312609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311192172627101341750145 1733394129470326006312609)
                      ·
                        rfl

theorem cell23_3375773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_3375773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375773 prefixEnd_3375773 := by exact prefixLift 3375773
  have htrace : WordTrace (prefixWord ++ tailWord_3375773) baseStart_3375773 baseEnd_3375773 := by
    simpa [prefixWord, tailWord_3375773, baseEnd_3375773] using wordTrace_append hprefix tailTrace_3375773
  have hstable : (prefixWord ++ tailWord_3375773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375773).length < 2 ^ (prefixWord ++ tailWord_3375773).sum := by decide
  have hdescent : baseEnd_3375773 < baseStart_3375773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375783 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 1, 6]
def baseStart_3375783 : Nat := 118140960795 + 3375783 * 2 ^ 59
def prefixEnd_3375783 : Nat := 4983230072969 + 3 ^ 40 * 3375783 * 2
def baseEnd_3375783 : Nat := 577799754758956989062521

theorem tailTrace_3375783 : CollatzResearch.WordTrace tailWord_3375783 prefixEnd_3375783 577799754758956989062521 := by
  unfold tailWord_3375783
  simp only [CollatzResearch.WordTrace]
  refine ⟨123124921129122203680988003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82083280752748135787325335 123124921129122203680988003)
  ·
    refine ⟨184687381693683305521482005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123124921129122203680988003 184687381693683305521482005)
    ·
      refine ⟨8657221016891404946319469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184687381693683305521482005 8657221016891404946319469)
      ·
        refine ⟨3246457881334276854869801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8657221016891404946319469 3246457881334276854869801)
        ·
          refine ⟨2434843411000707641152351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3246457881334276854869801 2434843411000707641152351)
          ·
            refine ⟨3652265116501061461728527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2434843411000707641152351 3652265116501061461728527)
            ·
              refine ⟨5478397674751592192592791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3652265116501061461728527 5478397674751592192592791)
              ·
                refine ⟨8217596512127388288889187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5478397674751592192592791 8217596512127388288889187)
                ·
                  refine ⟨12326394768191082433333781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8217596512127388288889187 12326394768191082433333781)
                  ·
                    refine ⟨577799754758956989062521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12326394768191082433333781 577799754758956989062521)
                    ·
                      rfl

theorem cell23_3375783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_3375783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375783 prefixEnd_3375783 := by exact prefixLift 3375783
  have htrace : WordTrace (prefixWord ++ tailWord_3375783) baseStart_3375783 baseEnd_3375783 := by
    simpa [prefixWord, tailWord_3375783, baseEnd_3375783] using wordTrace_append hprefix tailTrace_3375783
  have hstable : (prefixWord ++ tailWord_3375783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375783).length < 2 ^ (prefixWord ++ tailWord_3375783).sum := by decide
  have hdescent : baseEnd_3375783 < baseStart_3375783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375785 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 5]
def baseStart_3375785 : Nat := 118140960795 + 3375785 * 2 ^ 59
def prefixEnd_3375785 : Nat := 4983230072969 + 3 ^ 40 * 3375785 * 2
def baseEnd_3375785 : Nat := 1733400291238179959362553

theorem tailTrace_3375785 : CollatzResearch.WordTrace tailWord_3375785 prefixEnd_3375785 1733400291238179959362553 := by
  unfold tailWord_3375785
  simp only [CollatzResearch.WordTrace]
  refine ⟨123124994075114958022560809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82083329383409972015040539 123124994075114958022560809)
  ·
    refine ⟨92343745556336218516920607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123124994075114958022560809 92343745556336218516920607)
    ·
      refine ⟨138515618334504327775380911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92343745556336218516920607 138515618334504327775380911)
      ·
        refine ⟨207773427501756491663071367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138515618334504327775380911 207773427501756491663071367)
        ·
          refine ⟨311660141252634737494607051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207773427501756491663071367 311660141252634737494607051)
          ·
            refine ⟨467490211878952106241910577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311660141252634737494607051 467490211878952106241910577)
            ·
              refine ⟨350617658909214079681432933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467490211878952106241910577 350617658909214079681432933)
              ·
                refine ⟨65740811045477639940268675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350617658909214079681432933 65740811045477639940268675)
                ·
                  refine ⟨98611216568216459910403013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65740811045477639940268675 98611216568216459910403013)
                  ·
                    refine ⟨18489603106540586233200565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98611216568216459910403013 18489603106540586233200565)
                    ·
                      refine ⟨1733400291238179959362553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18489603106540586233200565 1733400291238179959362553)
                      ·
                        rfl

theorem cell23_3375785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_3375785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375785 prefixEnd_3375785 := by exact prefixLift 3375785
  have htrace : WordTrace (prefixWord ++ tailWord_3375785) baseStart_3375785 baseEnd_3375785 := by
    simpa [prefixWord, tailWord_3375785, baseEnd_3375785] using wordTrace_append hprefix tailTrace_3375785
  have hstable : (prefixWord ++ tailWord_3375785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375785).length < 2 ^ (prefixWord ++ tailWord_3375785).sum := by decide
  have hdescent : baseEnd_3375785 < baseStart_3375785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375786 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3375786 : Nat := 118140960795 + 3375786 * 2 ^ 59
def prefixEnd_3375786 : Nat := 4983230072969 + 3 ^ 40 * 3375786 * 2
def baseEnd_3375786 : Nat := 1733400804718834455450049

theorem tailTrace_3375786 : CollatzResearch.WordTrace tailWord_3375786 prefixEnd_3375786 1733400804718834455450049 := by
  unfold tailWord_3375786
  simp only [CollatzResearch.WordTrace]
  refine ⟨30781257637027833798336803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82083353698740890128898141 30781257637027833798336803)
  ·
    refine ⟨46171886455541750697505205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30781257637027833798336803 46171886455541750697505205)
    ·
      refine ⟨4328614355207039127891113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46171886455541750697505205 4328614355207039127891113)
      ·
        refine ⟨3246460766405279345918335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4328614355207039127891113 3246460766405279345918335)
        ·
          refine ⟨4869691149607919018877503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246460766405279345918335 4869691149607919018877503)
          ·
            refine ⟨7304536724411878528316255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4869691149607919018877503 7304536724411878528316255)
            ·
              refine ⟨10956805086617817792474383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7304536724411878528316255 10956805086617817792474383)
              ·
                refine ⟨16435207629926726688711575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10956805086617817792474383 16435207629926726688711575)
                ·
                  refine ⟨24652811444890090033067363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16435207629926726688711575 24652811444890090033067363)
                  ·
                    refine ⟨36979217167335135049601045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24652811444890090033067363 36979217167335135049601045)
                    ·
                      refine ⟨1733400804718834455450049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36979217167335135049601045 1733400804718834455450049)
                      ·
                        rfl

theorem cell23_3375786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3375786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375786 prefixEnd_3375786 := by exact prefixLift 3375786
  have htrace : WordTrace (prefixWord ++ tailWord_3375786) baseStart_3375786 baseEnd_3375786 := by
    simpa [prefixWord, tailWord_3375786, baseEnd_3375786] using wordTrace_append hprefix tailTrace_3375786
  have hstable : (prefixWord ++ tailWord_3375786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375786).length < 2 ^ (prefixWord ++ tailWord_3375786).sum := by decide
  have hdescent : baseEnd_3375786 < baseStart_3375786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
