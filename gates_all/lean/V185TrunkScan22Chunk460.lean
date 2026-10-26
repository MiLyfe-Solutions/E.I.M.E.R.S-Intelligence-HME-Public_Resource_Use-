import V185TrunkScan22Chunk459

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4099619 : List Nat := [1, 1, 1, 4, 5, 2, 1, 2, 5]
def baseStart_4099619 : Nat := 118140960795 + 4099619 * 2 ^ 59
def prefixEnd_4099619 : Nat := 4983230072969 + 3 ^ 40 * 4099619 * 2
def baseEnd_4099619 : Nat := 467794454956600212335267

theorem tailTrace_4099619 : CollatzResearch.WordTrace tailWord_4099619 prefixEnd_4099619 467794454956600212335267 := by
  unfold tailWord_4099619
  simp only [CollatzResearch.WordTrace]
  refine ⟨149525388934787997027789911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99683592623191998018526607 149525388934787997027789911)
  ·
    refine ⟨224288083402181995541684867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149525388934787997027789911 224288083402181995541684867)
    ·
      refine ⟨336432125103272993312527301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224288083402181995541684867 336432125103272993312527301)
      ·
        refine ⟨63081023456863686246098869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336432125103272993312527301 63081023456863686246098869)
        ·
          refine ⟨5913845949080970585571769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63081023456863686246098869 5913845949080970585571769)
          ·
            refine ⟨4435384461810727939178827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5913845949080970585571769 4435384461810727939178827)
            ·
              refine ⟨6653076692716091908768241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435384461810727939178827 6653076692716091908768241)
              ·
                refine ⟨4989807519537068931576181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653076692716091908768241 4989807519537068931576181)
                ·
                  refine ⟨467794454956600212335267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4989807519537068931576181 467794454956600212335267)
                  ·
                    rfl

theorem cell22_4099619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 5].length) (baseStart_4099619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099619 prefixEnd_4099619 := by exact prefixLift 4099619
  have htrace : WordTrace (prefixWord ++ tailWord_4099619) baseStart_4099619 baseEnd_4099619 := by
    simpa [prefixWord, tailWord_4099619, baseEnd_4099619] using wordTrace_append hprefix tailTrace_4099619
  have hstable : (prefixWord ++ tailWord_4099619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099619).length < 2 ^ (prefixWord ++ tailWord_4099619).sum := by decide
  have hdescent : baseEnd_4099619 < baseStart_4099619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099649 : List Nat := [1, 2, 5, 1, 1, 1, 4, 2, 1, 4]
def baseStart_4099649 : Nat := 118140960795 + 4099649 * 2 ^ 59
def prefixEnd_4099649 : Nat := 4983230072969 + 3 ^ 40 * 4099649 * 2
def baseEnd_4099649 : Nat := 1403393634482890558755709

theorem tailTrace_4099649 : CollatzResearch.WordTrace tailWord_4099649 prefixEnd_4099649 1403393634482890558755709 := by
  unfold tailWord_4099649
  simp only [CollatzResearch.WordTrace]
  refine ⟨149526483124679312151382001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99684322083119541434254667 149526483124679312151382001)
  ·
    refine ⟨112144862343509484113536501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149526483124679312151382001 112144862343509484113536501)
    ·
      refine ⟨10513580844704014135644047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112144862343509484113536501 10513580844704014135644047)
      ·
        refine ⟨15770371267056021203466071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10513580844704014135644047 15770371267056021203466071)
        ·
          refine ⟨23655556900584031805199107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15770371267056021203466071 23655556900584031805199107)
          ·
            refine ⟨35483335350876047707798661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23655556900584031805199107 35483335350876047707798661)
            ·
              refine ⟨6653125378289258945212249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35483335350876047707798661 6653125378289258945212249)
              ·
                refine ⟨4989844033716944208909187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653125378289258945212249 4989844033716944208909187)
                ·
                  refine ⟨7484766050575416313363781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4989844033716944208909187 7484766050575416313363781)
                  ·
                    refine ⟨1403393634482890558755709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7484766050575416313363781 1403393634482890558755709)
                    ·
                      rfl

theorem cell22_4099649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_4099649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099649 prefixEnd_4099649 := by exact prefixLift 4099649
  have htrace : WordTrace (prefixWord ++ tailWord_4099649) baseStart_4099649 baseEnd_4099649 := by
    simpa [prefixWord, tailWord_4099649, baseEnd_4099649] using wordTrace_append hprefix tailTrace_4099649
  have hstable : (prefixWord ++ tailWord_4099649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099649).length < 2 ^ (prefixWord ++ tailWord_4099649).sum := by decide
  have hdescent : baseEnd_4099649 < baseStart_4099649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099696 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 2, 3]
def baseStart_4099696 : Nat := 118140960795 + 4099696 * 2 ^ 59
def prefixEnd_4099696 : Nat := 4983230072969 + 3 ^ 40 * 4099696 * 2
def baseEnd_4099696 : Nat := 1403409723543398102830565

theorem tailTrace_4099696 : CollatzResearch.WordTrace tailWord_4099696 prefixEnd_4099696 1403409723543398102830565 := by
  unfold tailWord_4099696
  simp only [CollatzResearch.WordTrace]
  refine ⟨74764098677754519589171471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99685464903672692785561961 74764098677754519589171471)
  ·
    refine ⟨112146148016631779383757207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74764098677754519589171471 112146148016631779383757207)
    ·
      refine ⟨168219222024947669075635811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112146148016631779383757207 168219222024947669075635811)
      ·
        refine ⟨252328833037421503613453717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168219222024947669075635811 252328833037421503613453717)
        ·
          refine ⟨11827914048629132981880643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 252328833037421503613453717 11827914048629132981880643)
          ·
            refine ⟨17741871072943699472820965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11827914048629132981880643 17741871072943699472820965)
            ·
              refine ⟨3326600826176943651153931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17741871072943699472820965 3326600826176943651153931)
              ·
                refine ⟨4989901239265415476730897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326600826176943651153931 4989901239265415476730897)
                ·
                  refine ⟨3742425929449061607548173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4989901239265415476730897 3742425929449061607548173)
                  ·
                    refine ⟨1403409723543398102830565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3742425929449061607548173 1403409723543398102830565)
                    ·
                      rfl

theorem cell22_4099696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 2, 3].length) (baseStart_4099696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099696 prefixEnd_4099696 := by exact prefixLift 4099696
  have htrace : WordTrace (prefixWord ++ tailWord_4099696) baseStart_4099696 baseEnd_4099696 := by
    simpa [prefixWord, tailWord_4099696, baseEnd_4099696] using wordTrace_append hprefix tailTrace_4099696
  have hstable : (prefixWord ++ tailWord_4099696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099696).length < 2 ^ (prefixWord ++ tailWord_4099696).sum := by decide
  have hdescent : baseEnd_4099696 < baseStart_4099696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099707 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 5, 3]
def baseStart_4099707 : Nat := 118140960795 + 4099707 * 2 ^ 59
def prefixEnd_4099707 : Nat := 4983230072969 + 3 ^ 40 * 4099707 * 2
def baseEnd_4099707 : Nat := 1403413489068197740805531

theorem tailTrace_4099707 : CollatzResearch.WordTrace tailWord_4099707 prefixEnd_4099707 1403413489068197740805531 := by
  unfold tailWord_4099707
  simp only [CollatzResearch.WordTrace]
  refine ⟨149528598558469188056993375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99685732372312792037995583 149528598558469188056993375)
  ·
    refine ⟨224292897837703782085490063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149528598558469188056993375 224292897837703782085490063)
    ·
      refine ⟨336439346756555673128235095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224292897837703782085490063 336439346756555673128235095)
      ·
        refine ⟨504659020134833509692352643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336439346756555673128235095 504659020134833509692352643)
        ·
          refine ⟨756988530202250264538528965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504659020134833509692352643 756988530202250264538528965)
          ·
            refine ⟨141935349412921924600974181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 756988530202250264538528965 141935349412921924600974181)
            ·
              refine ⟨26612878014922860862682659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141935349412921924600974181 26612878014922860862682659)
              ·
                refine ⟨39919317022384291294023989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26612878014922860862682659 39919317022384291294023989)
                ·
                  refine ⟨3742435970848527308814749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39919317022384291294023989 3742435970848527308814749)
                  ·
                    refine ⟨1403413489068197740805531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3742435970848527308814749 1403413489068197740805531)
                    ·
                      rfl

theorem cell22_4099707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 5, 3].length) (baseStart_4099707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099707 prefixEnd_4099707 := by exact prefixLift 4099707
  have htrace : WordTrace (prefixWord ++ tailWord_4099707) baseStart_4099707 baseEnd_4099707 := by
    simpa [prefixWord, tailWord_4099707, baseEnd_4099707] using wordTrace_append hprefix tailTrace_4099707
  have hstable : (prefixWord ++ tailWord_4099707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099707).length < 2 ^ (prefixWord ++ tailWord_4099707).sum := by decide
  have hdescent : baseEnd_4099707 < baseStart_4099707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099758 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_4099758 : Nat := 118140960795 + 4099758 * 2 ^ 59
def prefixEnd_4099758 : Nat := 4983230072969 + 3 ^ 40 * 4099758 * 2
def baseEnd_4099758 : Nat := 1403430947410450607780375

theorem tailTrace_4099758 : CollatzResearch.WordTrace tailWord_4099758 prefixEnd_4099758 1403430947410450607780375 := by
  unfold tailWord_4099758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18691307335160552970887491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99686972454189615844733285 18691307335160552970887491)
  ·
    refine ⟨28036961002740829456331237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18691307335160552970887491 28036961002740829456331237)
    ·
      refine ⟨5256930188013905523062107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28036961002740829456331237 5256930188013905523062107)
      ·
        refine ⟨7885395282020858284593161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5256930188013905523062107 7885395282020858284593161)
        ·
          refine ⟨5914046461515643713444871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7885395282020858284593161 5914046461515643713444871)
          ·
            refine ⟨8871069692273465570167307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914046461515643713444871 8871069692273465570167307)
            ·
              refine ⟨13306604538410198355250961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8871069692273465570167307 13306604538410198355250961)
              ·
                refine ⟨9979953403807648766438221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13306604538410198355250961 9979953403807648766438221)
                ·
                  refine ⟨3742482526427868287414333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9979953403807648766438221 3742482526427868287414333)
                  ·
                    refine ⟨1403430947410450607780375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3742482526427868287414333 1403430947410450607780375)
                    ·
                      rfl

theorem cell22_4099758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_4099758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099758 prefixEnd_4099758 := by exact prefixLift 4099758
  have htrace : WordTrace (prefixWord ++ tailWord_4099758) baseStart_4099758 baseEnd_4099758 := by
    simpa [prefixWord, tailWord_4099758, baseEnd_4099758] using wordTrace_append hprefix tailTrace_4099758
  have hstable : (prefixWord ++ tailWord_4099758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099758).length < 2 ^ (prefixWord ++ tailWord_4099758).sum := by decide
  have hdescent : baseEnd_4099758 < baseStart_4099758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099784 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 1, 4]
def baseStart_4099784 : Nat := 118140960795 + 4099784 * 2 ^ 59
def prefixEnd_4099784 : Nat := 4983230072969 + 3 ^ 40 * 4099784 * 2
def baseEnd_4099784 : Nat := 1403439847741795206630295

theorem tailTrace_4099784 : CollatzResearch.WordTrace tailWord_4099784 prefixEnd_4099784 1403439847741795206630295 := by
  unfold tailWord_4099784
  simp only [CollatzResearch.WordTrace]
  refine ⟨74765703489595115103773203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99687604652793486805030937 74765703489595115103773203)
  ·
    refine ⟨112148555234392672655659805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74765703489595115103773203 112148555234392672655659805)
    ·
      refine ⟨42055708212897252245872427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112148555234392672655659805 42055708212897252245872427)
      ·
        refine ⟨63083562319345878368808641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42055708212897252245872427 63083562319345878368808641)
        ·
          refine ⟨47312671739509408776606481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63083562319345878368808641 47312671739509408776606481)
          ·
            refine ⟨35484503804632056582454861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47312671739509408776606481 35484503804632056582454861)
            ·
              refine ⟨13306688926737021218420573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35484503804632056582454861 13306688926737021218420573)
              ·
                refine ⟨4990008347526382956907715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13306688926737021218420573 4990008347526382956907715)
                ·
                  refine ⟨7485012521289574435361573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4990008347526382956907715 7485012521289574435361573)
                  ·
                    refine ⟨1403439847741795206630295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7485012521289574435361573 1403439847741795206630295)
                    ·
                      rfl

theorem cell22_4099784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_4099784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099784 prefixEnd_4099784 := by exact prefixLift 4099784
  have htrace : WordTrace (prefixWord ++ tailWord_4099784) baseStart_4099784 baseEnd_4099784 := by
    simpa [prefixWord, tailWord_4099784, baseEnd_4099784] using wordTrace_append hprefix tailTrace_4099784
  have hstable : (prefixWord ++ tailWord_4099784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099784).length < 2 ^ (prefixWord ++ tailWord_4099784).sum := by decide
  have hdescent : baseEnd_4099784 < baseStart_4099784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099788 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 5]
def baseStart_4099788 : Nat := 118140960795 + 4099788 * 2 ^ 59
def prefixEnd_4099788 : Nat := 4983230072969 + 3 ^ 40 * 4099788 * 2
def baseEnd_4099788 : Nat := 467813739007846843176761

theorem tailTrace_4099788 : CollatzResearch.WordTrace tailWord_4099788 prefixEnd_4099788 467813739007846843176761 := by
  unfold tailWord_4099788
  simp only [CollatzResearch.WordTrace]
  refine ⟨74765776435587869445346009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99687701914117159260461345 74765776435587869445346009)
  ·
    refine ⟨56074332326690902084009507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74765776435587869445346009 56074332326690902084009507)
    ·
      refine ⟨84111498490036353126014261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56074332326690902084009507 84111498490036353126014261)
      ·
        refine ⟨7885452983440908105563837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84111498490036353126014261 7885452983440908105563837)
        ·
          refine ⟨2957044868790340539586439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7885452983440908105563837 2957044868790340539586439)
          ·
            refine ⟨4435567303185510809379659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957044868790340539586439 4435567303185510809379659)
            ·
              refine ⟨6653350954778266214069489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435567303185510809379659 6653350954778266214069489)
              ·
                refine ⟨4990013216083699660552117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6653350954778266214069489 4990013216083699660552117)
                ·
                  refine ⟨467813739007846843176761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4990013216083699660552117 467813739007846843176761)
                  ·
                    rfl

theorem cell22_4099788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_4099788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099788 prefixEnd_4099788 := by exact prefixLift 4099788
  have htrace : WordTrace (prefixWord ++ tailWord_4099788) baseStart_4099788 baseEnd_4099788 := by
    simpa [prefixWord, tailWord_4099788, baseEnd_4099788] using wordTrace_append hprefix tailTrace_4099788
  have hstable : (prefixWord ++ tailWord_4099788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099788).length < 2 ^ (prefixWord ++ tailWord_4099788).sum := by decide
  have hdescent : baseEnd_4099788 < baseStart_4099788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099799 : List Nat := [1, 1, 3, 2, 1, 3, 1, 6, 4]
def baseStart_4099799 : Nat := 118140960795 + 4099799 * 2 ^ 59
def prefixEnd_4099799 : Nat := 4983230072969 + 3 ^ 40 * 4099799 * 2
def baseEnd_4099799 : Nat := 467814994182780055835083

theorem tailTrace_4099799 : CollatzResearch.WordTrace tailWord_4099799 prefixEnd_4099799 467814994182780055835083 := by
  unfold tailWord_4099799
  simp only [CollatzResearch.WordTrace]
  refine ⟨149531954074135887769342451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99687969382757258512894967 149531954074135887769342451)
  ·
    refine ⟨224297931111203831654013677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149531954074135887769342451 224297931111203831654013677)
    ·
      refine ⟨84111724166701436870255129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224297931111203831654013677 84111724166701436870255129)
      ·
        refine ⟨63083793125026077652691347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84111724166701436870255129 63083793125026077652691347)
        ·
          refine ⟨94625689687539116479037021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63083793125026077652691347 94625689687539116479037021)
          ·
            refine ⟨35484633632827168679638883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94625689687539116479037021 35484633632827168679638883)
            ·
              refine ⟨53226950449240753019458325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35484633632827168679638883 53226950449240753019458325)
              ·
                refine ⟨2495013302308160297787109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53226950449240753019458325 2495013302308160297787109)
                ·
                  refine ⟨467814994182780055835083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495013302308160297787109 467814994182780055835083)
                  ·
                    rfl

theorem cell22_4099799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 6, 4].length) (baseStart_4099799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099799 prefixEnd_4099799 := by exact prefixLift 4099799
  have htrace : WordTrace (prefixWord ++ tailWord_4099799) baseStart_4099799 baseEnd_4099799 := by
    simpa [prefixWord, tailWord_4099799, baseEnd_4099799] using wordTrace_append hprefix tailTrace_4099799
  have hstable : (prefixWord ++ tailWord_4099799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099799).length < 2 ^ (prefixWord ++ tailWord_4099799).sum := by decide
  have hdescent : baseEnd_4099799 < baseStart_4099799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099812 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_4099812 : Nat := 118140960795 + 4099812 * 2 ^ 59
def prefixEnd_4099812 : Nat := 4983230072969 + 3 ^ 40 * 4099812 * 2
def baseEnd_4099812 : Nat := 1403449432714012466930209

theorem tailTrace_4099812 : CollatzResearch.WordTrace tailWord_4099812 prefixEnd_4099812 1403449432714012466930209 := by
  unfold tailWord_4099812
  simp only [CollatzResearch.WordTrace]
  refine ⟨74766214111544395494782845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99688285482059193993043793 74766214111544395494782845)
  ·
    refine ⟨28037330291829148310543567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74766214111544395494782845 28037330291829148310543567)
    ·
      refine ⟨42055995437743722465815351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28037330291829148310543567 42055995437743722465815351)
      ·
        refine ⟨63083993156615583698723027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42055995437743722465815351 63083993156615583698723027)
        ·
          refine ⟨94625989734923375548084541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63083993156615583698723027 94625989734923375548084541)
          ·
            refine ⟨35484746150596265830531703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94625989734923375548084541 35484746150596265830531703)
            ·
              refine ⟨53227119225894398745797555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35484746150596265830531703 53227119225894398745797555)
              ·
                refine ⟨79840678838841598118696333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53227119225894398745797555 79840678838841598118696333)
                ·
                  refine ⟨29940254564565599294511125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79840678838841598118696333 29940254564565599294511125)
                  ·
                    refine ⟨1403449432714012466930209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29940254564565599294511125 1403449432714012466930209)
                    ·
                      rfl

theorem cell22_4099812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_4099812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099812 prefixEnd_4099812 := by exact prefixLift 4099812
  have htrace : WordTrace (prefixWord ++ tailWord_4099812) baseStart_4099812 baseEnd_4099812 := by
    simpa [prefixWord, tailWord_4099812, baseEnd_4099812] using wordTrace_append hprefix tailTrace_4099812
  have hstable : (prefixWord ++ tailWord_4099812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099812).length < 2 ^ (prefixWord ++ tailWord_4099812).sum := by decide
  have hdescent : baseEnd_4099812 < baseStart_4099812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099844 : List Nat := [2, 3, 2, 2, 1, 4, 8]
def baseStart_4099844 : Nat := 118140960795 + 4099844 * 2 ^ 59
def prefixEnd_4099844 : Nat := 4983230072969 + 3 ^ 40 * 4099844 * 2
def baseEnd_4099844 : Nat := 51980014332147224078893

theorem tailTrace_4099844 : CollatzResearch.WordTrace tailWord_4099844 prefixEnd_4099844 51980014332147224078893 := by
  unfold tailWord_4099844
  simp only [CollatzResearch.WordTrace]
  refine ⟨74766797679486430227365293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99689063572648573636487057 74766797679486430227365293)
  ·
    refine ⟨28037549129807411335261985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74766797679486430227365293 28037549129807411335261985)
    ·
      refine ⟨21028161847355558501446489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28037549129807411335261985 21028161847355558501446489)
      ·
        refine ⟨15771121385516668876084867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21028161847355558501446489 15771121385516668876084867)
        ·
          refine ⟨23656682078275003314127301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15771121385516668876084867 23656682078275003314127301)
          ·
            refine ⟨4435627889676563121398869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23656682078275003314127301 4435627889676563121398869)
            ·
              refine ⟨51980014332147224078893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4435627889676563121398869 51980014332147224078893)
              ·
                rfl

theorem cell22_4099844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 8].length) (baseStart_4099844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099844 prefixEnd_4099844 := by exact prefixLift 4099844
  have htrace : WordTrace (prefixWord ++ tailWord_4099844) baseStart_4099844 baseEnd_4099844 := by
    simpa [prefixWord, tailWord_4099844, baseEnd_4099844] using wordTrace_append hprefix tailTrace_4099844
  have hstable : (prefixWord ++ tailWord_4099844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099844).length < 2 ^ (prefixWord ++ tailWord_4099844).sum := by decide
  have hdescent : baseEnd_4099844 < baseStart_4099844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099857 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_4099857 : Nat := 118140960795 + 4099857 * 2 ^ 59
def prefixEnd_4099857 : Nat := 4983230072969 + 3 ^ 40 * 4099857 * 2
def baseEnd_4099857 : Nat := 1403464837133647349555071

theorem tailTrace_4099857 : CollatzResearch.WordTrace tailWord_4099857 prefixEnd_4099857 1403464837133647349555071 := by
  unfold tailWord_4099857
  simp only [CollatzResearch.WordTrace]
  refine ⟨149534069507925763674953825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99689379671950509116635883 149534069507925763674953825)
  ·
    refine ⟨112150552130944322756215369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149534069507925763674953825 112150552130944322756215369)
    ·
      refine ⟨84112914098208242067161527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112150552130944322756215369 84112914098208242067161527)
      ·
        refine ⟨126169371147312363100742291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84112914098208242067161527 126169371147312363100742291)
        ·
          refine ⟨189254056720968544651113437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126169371147312363100742291 189254056720968544651113437)
          ·
            refine ⟨70970271270363204244167539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189254056720968544651113437 70970271270363204244167539)
            ·
              refine ⟨106455406905544806366251309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70970271270363204244167539 106455406905544806366251309)
              ·
                refine ⟨39920777589579302387344241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106455406905544806366251309 39920777589579302387344241)
                ·
                  refine ⟨29940583192184476790508181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39920777589579302387344241 29940583192184476790508181)
                  ·
                    refine ⟨1403464837133647349555071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29940583192184476790508181 1403464837133647349555071)
                    ·
                      rfl

theorem cell22_4099857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_4099857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099857 prefixEnd_4099857 := by exact prefixLift 4099857
  have htrace : WordTrace (prefixWord ++ tailWord_4099857) baseStart_4099857 baseEnd_4099857 := by
    simpa [prefixWord, tailWord_4099857, baseEnd_4099857] using wordTrace_append hprefix tailTrace_4099857
  have hstable : (prefixWord ++ tailWord_4099857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099857).length < 2 ^ (prefixWord ++ tailWord_4099857).sum := by decide
  have hdescent : baseEnd_4099857 < baseStart_4099857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099859 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 3, 3]
def baseStart_4099859 : Nat := 118140960795 + 4099859 * 2 ^ 59
def prefixEnd_4099859 : Nat := 4983230072969 + 3 ^ 40 * 4099859 * 2
def baseEnd_4099859 : Nat := 1403465521774520011005065

theorem tailTrace_4099859 : CollatzResearch.WordTrace tailWord_4099859 prefixEnd_4099859 1403465521774520011005065 := by
  unfold tailWord_4099859
  simp only [CollatzResearch.WordTrace]
  refine ⟨149534142453918518016526631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99689428302612345344351087 149534142453918518016526631)
  ·
    refine ⟨224301213680877777024789947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149534142453918518016526631 224301213680877777024789947)
    ·
      refine ⟨336451820521316665537184921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224301213680877777024789947 336451820521316665537184921)
      ·
        refine ⟨252338865390987499152888691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336451820521316665537184921 252338865390987499152888691)
        ·
          refine ⟨378508298086481248729333037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252338865390987499152888691 378508298086481248729333037)
          ·
            refine ⟨141940611782430468273499889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 378508298086481248729333037 141940611782430468273499889)
            ·
              refine ⟨106455458836822851205124917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141940611782430468273499889 106455458836822851205124917)
              ·
                refine ⟨9980199265952142300480461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106455458836822851205124917 9980199265952142300480461)
                ·
                  refine ⟨3742574724732053362680173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9980199265952142300480461 3742574724732053362680173)
                  ·
                    refine ⟨1403465521774520011005065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3742574724732053362680173 1403465521774520011005065)
                    ·
                      rfl

theorem cell22_4099859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3, 3].length) (baseStart_4099859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099859 prefixEnd_4099859 := by exact prefixLift 4099859
  have htrace : WordTrace (prefixWord ++ tailWord_4099859) baseStart_4099859 baseEnd_4099859 := by
    simpa [prefixWord, tailWord_4099859, baseEnd_4099859] using wordTrace_append hprefix tailTrace_4099859
  have hstable : (prefixWord ++ tailWord_4099859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099859).length < 2 ^ (prefixWord ++ tailWord_4099859).sum := by decide
  have hdescent : baseEnd_4099859 < baseStart_4099859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099887 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 1, 7]
def baseStart_4099887 : Nat := 118140960795 + 4099887 * 2 ^ 59
def prefixEnd_4099887 : Nat := 4983230072969 + 3 ^ 40 * 4099887 * 2
def baseEnd_4099887 : Nat := 1403475106746737271304979

theorem tailTrace_4099887 : CollatzResearch.WordTrace tailWord_4099887 prefixEnd_4099887 1403475106746737271304979 := by
  unfold tailWord_4099887
  simp only [CollatzResearch.WordTrace]
  refine ⟨149535163697817078798545915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99690109131878052532363943 149535163697817078798545915)
  ·
    refine ⟨224302745546725618197818873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149535163697817078798545915 224302745546725618197818873)
    ·
      refine ⟨168227059160044213648364155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224302745546725618197818873 168227059160044213648364155)
      ·
        refine ⟨252340588740066320472546233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168227059160044213648364155 252340588740066320472546233)
        ·
          refine ⟨189255441555049740354409675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252340588740066320472546233 189255441555049740354409675)
          ·
            refine ⟨283883162332574610531614513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189255441555049740354409675 283883162332574610531614513)
            ·
              refine ⟨212912371749430957898710885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283883162332574610531614513 212912371749430957898710885)
              ·
                refine ⟨39921069703018304606008291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212912371749430957898710885 39921069703018304606008291)
                ·
                  refine ⟨59881604554527456909012437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39921069703018304606008291 59881604554527456909012437)
                  ·
                    refine ⟨1403475106746737271304979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59881604554527456909012437 1403475106746737271304979)
                    ·
                      rfl

theorem cell22_4099887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_4099887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099887 prefixEnd_4099887 := by exact prefixLift 4099887
  have htrace : WordTrace (prefixWord ++ tailWord_4099887) baseStart_4099887 baseEnd_4099887 := by
    simpa [prefixWord, tailWord_4099887, baseEnd_4099887] using wordTrace_append hprefix tailTrace_4099887
  have hstable : (prefixWord ++ tailWord_4099887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099887).length < 2 ^ (prefixWord ++ tailWord_4099887).sum := by decide
  have hdescent : baseEnd_4099887 < baseStart_4099887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4099996 : List Nat := [2, 2, 3, 3, 1, 2, 1, 8]
def baseStart_4099996 : Nat := 118140960795 + 4099996 * 2 ^ 59
def prefixEnd_4099996 : Nat := 4983230072969 + 3 ^ 40 * 4099996 * 2
def baseEnd_4099996 : Nat := 155945824408255257814405

theorem tailTrace_4099996 : CollatzResearch.WordTrace tailWord_4099996 prefixEnd_4099996 155945824408255257814405 := by
  unfold tailWord_4099996
  simp only [CollatzResearch.WordTrace]
  refine ⟨74769569627211095207131921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99692759502948126942842561 74769569627211095207131921)
  ·
    refine ⟨56077177220408321405348941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74769569627211095207131921 56077177220408321405348941)
    ·
      refine ⟨21028941457653120527005853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56077177220408321405348941 21028941457653120527005853)
      ·
        refine ⟨7885853046619920197627195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21028941457653120527005853 7885853046619920197627195)
        ·
          refine ⟨11828779569929880296440793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7885853046619920197627195 11828779569929880296440793)
          ·
            refine ⟨8871584677447410222330595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11828779569929880296440793 8871584677447410222330595)
            ·
              refine ⟨13307377016171115333495893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8871584677447410222330595 13307377016171115333495893)
              ·
                refine ⟨155945824408255257814405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13307377016171115333495893 155945824408255257814405)
                ·
                  rfl

theorem cell22_4099996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 8].length) (baseStart_4099996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4099996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4099996 prefixEnd_4099996 := by exact prefixLift 4099996
  have htrace : WordTrace (prefixWord ++ tailWord_4099996) baseStart_4099996 baseEnd_4099996 := by
    simpa [prefixWord, tailWord_4099996, baseEnd_4099996] using wordTrace_append hprefix tailTrace_4099996
  have hstable : (prefixWord ++ tailWord_4099996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4099996).length < 2 ^ (prefixWord ++ tailWord_4099996).sum := by decide
  have hdescent : baseEnd_4099996 < baseStart_4099996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4099996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100002 : List Nat := [3, 3, 1, 2, 4, 1, 1, 3, 4]
def baseStart_4100002 : Nat := 118140960795 + 4100002 * 2 ^ 59
def prefixEnd_4100002 : Nat := 4983230072969 + 3 ^ 40 * 4100002 * 2
def baseEnd_4100002 : Nat := 467838157865638434893209

theorem tailTrace_4100002 : CollatzResearch.WordTrace tailWord_4100002 prefixEnd_4100002 467838157865638434893209 := by
  unfold tailWord_4100002
  simp only [CollatzResearch.WordTrace]
  refine ⟨37384839523100113359745565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99692905394933635625988173 37384839523100113359745565)
  ·
    refine ⟨14019314821162542509904587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37384839523100113359745565 14019314821162542509904587)
    ·
      refine ⟨21028972231743813764856881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14019314821162542509904587 21028972231743813764856881)
      ·
        refine ⟨15771729173807860323642661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21028972231743813764856881 15771729173807860323642661)
        ·
          refine ⟨2957199220088973810682999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15771729173807860323642661 2957199220088973810682999)
          ·
            refine ⟨4435798830133460716024499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957199220088973810682999 4435798830133460716024499)
            ·
              refine ⟨6653698245200191074036749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4435798830133460716024499 6653698245200191074036749)
              ·
                refine ⟨2495136841950071652763781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6653698245200191074036749 2495136841950071652763781)
                ·
                  refine ⟨467838157865638434893209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495136841950071652763781 467838157865638434893209)
                  ·
                    rfl

theorem cell22_4100002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_4100002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100002 prefixEnd_4100002 := by exact prefixLift 4100002
  have htrace : WordTrace (prefixWord ++ tailWord_4100002) baseStart_4100002 baseEnd_4100002 := by
    simpa [prefixWord, tailWord_4100002, baseEnd_4100002] using wordTrace_append hprefix tailTrace_4100002
  have hstable : (prefixWord ++ tailWord_4100002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100002).length < 2 ^ (prefixWord ++ tailWord_4100002).sum := by decide
  have hdescent : baseEnd_4100002 < baseStart_4100002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100024 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 7]
def baseStart_4100024 : Nat := 118140960795 + 4100024 * 2 ^ 59
def prefixEnd_4100024 : Nat := 4983230072969 + 3 ^ 40 * 4100024 * 2
def baseEnd_4100024 : Nat := 467840668215504860209853

theorem tailTrace_4100024 : CollatzResearch.WordTrace tailWord_4100024 prefixEnd_4100024 467840668215504860209853 := by
  unfold tailWord_4100024
  simp only [CollatzResearch.WordTrace]
  refine ⟨74770080249160375598141563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99693440332213834130855417 74770080249160375598141563)
  ·
    refine ⟨112155120373740563397212345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74770080249160375598141563 112155120373740563397212345)
    ·
      refine ⟨84116340280305422547909259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112155120373740563397212345 84116340280305422547909259)
      ·
        refine ⟨126174510420458133821863889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84116340280305422547909259 126174510420458133821863889)
        ·
          refine ⟨94630882815343600366397917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126174510420458133821863889 94630882815343600366397917)
          ·
            refine ⟨35486581055753850137399219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94630882815343600366397917 35486581055753850137399219)
            ·
              refine ⟨53229871583630775206098829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35486581055753850137399219 53229871583630775206098829)
              ·
                refine ⟨19961201843861540702287061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53229871583630775206098829 19961201843861540702287061)
                ·
                  refine ⟨467840668215504860209853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19961201843861540702287061 467840668215504860209853)
                  ·
                    rfl

theorem cell22_4100024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_4100024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100024 prefixEnd_4100024 := by exact prefixLift 4100024
  have htrace : WordTrace (prefixWord ++ tailWord_4100024) baseStart_4100024 baseEnd_4100024 := by
    simpa [prefixWord, tailWord_4100024, baseEnd_4100024] using wordTrace_append hprefix tailTrace_4100024
  have hstable : (prefixWord ++ tailWord_4100024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100024).length < 2 ^ (prefixWord ++ tailWord_4100024).sum := by decide
  have hdescent : baseEnd_4100024 < baseStart_4100024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100039 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 1, 7]
def baseStart_4100039 : Nat := 118140960795 + 4100039 * 2 ^ 59
def prefixEnd_4100039 : Nat := 4983230072969 + 3 ^ 40 * 4100039 * 2
def baseEnd_4100039 : Nat := 1403527139453059541504513

theorem tailTrace_4100039 : CollatzResearch.WordTrace tailWord_4100039 prefixEnd_4100039 1403527139453059541504513 := by
  unfold tailWord_4100039
  simp only [CollatzResearch.WordTrace]
  refine ⟨149540707593266408758079171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99693805062177605838719447 149540707593266408758079171)
  ·
    refine ⟨224311061389899613137118757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149540707593266408758079171 224311061389899613137118757)
    ·
      refine ⟨42058324010606177463209767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224311061389899613137118757 42058324010606177463209767)
      ·
        refine ⟨63087486015909266194814651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42058324010606177463209767 63087486015909266194814651)
        ·
          refine ⟨94631229023863899292221977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63087486015909266194814651 94631229023863899292221977)
          ·
            refine ⟨70973421767897924469166483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94631229023863899292221977 70973421767897924469166483)
            ·
              refine ⟨106460132651846886703749725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70973421767897924469166483 106460132651846886703749725)
              ·
                refine ⟨39922549744442582513906147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106460132651846886703749725 39922549744442582513906147)
                ·
                  refine ⟨59883824616663873770859221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39922549744442582513906147 59883824616663873770859221)
                  ·
                    refine ⟨1403527139453059541504513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59883824616663873770859221 1403527139453059541504513)
                    ·
                      rfl

theorem cell22_4100039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_4100039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100039 prefixEnd_4100039 := by exact prefixLift 4100039
  have htrace : WordTrace (prefixWord ++ tailWord_4100039) baseStart_4100039 baseEnd_4100039 := by
    simpa [prefixWord, tailWord_4100039, baseEnd_4100039] using wordTrace_append hprefix tailTrace_4100039
  have hstable : (prefixWord ++ tailWord_4100039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100039).length < 2 ^ (prefixWord ++ tailWord_4100039).sum := by decide
  have hdescent : baseEnd_4100039 < baseStart_4100039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100101 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_4100101 : Nat := 118140960795 + 4100101 * 2 ^ 59
def prefixEnd_4100101 : Nat := 4983230072969 + 3 ^ 40 * 4100101 * 2
def baseEnd_4100101 : Nat := 1403548363320112046454323

theorem tailTrace_4100101 : CollatzResearch.WordTrace tailWord_4100101 prefixEnd_4100101 1403548363320112046454323 := by
  unfold tailWord_4100101
  simp only [CollatzResearch.WordTrace]
  refine ⟨149542968919041793346836157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99695312612694528897890771 149542968919041793346836157)
  ·
    refine ⟨56078613344640672505063559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149542968919041793346836157 56078613344640672505063559)
    ·
      refine ⟨84117920016961008757595339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56078613344640672505063559 84117920016961008757595339)
      ·
        refine ⟨126176880025441513136393009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84117920016961008757595339 126176880025441513136393009)
        ·
          refine ⟨94632660019081134852294757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126176880025441513136393009 94632660019081134852294757)
          ·
            refine ⟨17743623753577712784805267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94632660019081134852294757 17743623753577712784805267)
            ·
              refine ⟨26615435630366569177207901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17743623753577712784805267 26615435630366569177207901)
              ·
                refine ⟨9980788361387463441452963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26615435630366569177207901 9980788361387463441452963)
                ·
                  refine ⟨14971182542081195162179445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9980788361387463441452963 14971182542081195162179445)
                  ·
                    refine ⟨1403548363320112046454323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14971182542081195162179445 1403548363320112046454323)
                    ·
                      rfl

theorem cell22_4100101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_4100101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100101 prefixEnd_4100101 := by exact prefixLift 4100101
  have htrace : WordTrace (prefixWord ++ tailWord_4100101) baseStart_4100101 baseEnd_4100101 := by
    simpa [prefixWord, tailWord_4100101, baseEnd_4100101] using wordTrace_append hprefix tailTrace_4100101
  have hstable : (prefixWord ++ tailWord_4100101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100101).length < 2 ^ (prefixWord ++ tailWord_4100101).sum := by decide
  have hdescent : baseEnd_4100101 < baseStart_4100101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100152 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 2, 3]
def baseStart_4100152 : Nat := 118140960795 + 4100152 * 2 ^ 59
def prefixEnd_4100152 : Nat := 4983230072969 + 3 ^ 40 * 4100152 * 2
def baseEnd_4100152 : Nat := 1403565821662364913429167

theorem tailTrace_4100152 : CollatzResearch.WordTrace tailWord_4100152 prefixEnd_4100152 1403565821662364913429167 := by
  unfold tailWord_4100152
  simp only [CollatzResearch.WordTrace]
  refine ⟨74772414520928514528471355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99696552694571352704628473 74772414520928514528471355)
  ·
    refine ⟨112158621781392771792707033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74772414520928514528471355 112158621781392771792707033)
    ·
      refine ⟨84118966336044578844530275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112158621781392771792707033 84118966336044578844530275)
      ·
        refine ⟨126178449504066868266795413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84118966336044578844530275 126178449504066868266795413)
        ·
          refine ⟨5914614820503134450006035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126178449504066868266795413 5914614820503134450006035)
          ·
            refine ⟨8871922230754701675009053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914614820503134450006035 8871922230754701675009053)
            ·
              refine ⟨3326970836533013128128395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8871922230754701675009053 3326970836533013128128395)
              ·
                refine ⟨4990456254799519692192593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3326970836533013128128395 4990456254799519692192593)
                ·
                  refine ⟨3742842191099639769144445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4990456254799519692192593 3742842191099639769144445)
                  ·
                    refine ⟨1403565821662364913429167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3742842191099639769144445 1403565821662364913429167)
                    ·
                      rfl

theorem cell22_4100152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 2, 3].length) (baseStart_4100152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100152 prefixEnd_4100152 := by exact prefixLift 4100152
  have htrace : WordTrace (prefixWord ++ tailWord_4100152) baseStart_4100152 baseEnd_4100152 := by
    simpa [prefixWord, tailWord_4100152, baseEnd_4100152] using wordTrace_append hprefix tailTrace_4100152
  have hstable : (prefixWord ++ tailWord_4100152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100152).length < 2 ^ (prefixWord ++ tailWord_4100152).sum := by decide
  have hdescent : baseEnd_4100152 < baseStart_4100152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100191 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 2, 5]
def baseStart_4100191 : Nat := 118140960795 + 4100191 * 2 ^ 59
def prefixEnd_4100191 : Nat := 4983230072969 + 3 ^ 40 * 4100191 * 2
def baseEnd_4100191 : Nat := 1403579172159381811704047

theorem tailTrace_4100191 : CollatzResearch.WordTrace tailWord_4100191 prefixEnd_4100191 1403579172159381811704047 := by
  unfold tailWord_4100191
  simp only [CollatzResearch.WordTrace]
  refine ⟨149546251488715738717612427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99697500992477159145074951 149546251488715738717612427)
  ·
    refine ⟨224319377233073608076418641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149546251488715738717612427 224319377233073608076418641)
    ·
      refine ⟨168239532924805206057313981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224319377233073608076418641 168239532924805206057313981)
      ·
        refine ⟨63089824846801952271492743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168239532924805206057313981 63089824846801952271492743)
        ·
          refine ⟨94634737270202928407239115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63089824846801952271492743 94634737270202928407239115)
          ·
            refine ⟨141952105905304392610858673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94634737270202928407239115 141952105905304392610858673)
            ·
              refine ⟨106464079428978294458144005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141952105905304392610858673 106464079428978294458144005)
              ·
                refine ⟨19962014892933430210902001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106464079428978294458144005 19962014892933430210902001)
                ·
                  refine ⟨14971511169700072658176501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19962014892933430210902001 14971511169700072658176501)
                  ·
                    refine ⟨1403579172159381811704047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14971511169700072658176501 1403579172159381811704047)
                    ·
                      rfl

theorem cell22_4100191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_4100191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100191 prefixEnd_4100191 := by exact prefixLift 4100191
  have htrace : WordTrace (prefixWord ++ tailWord_4100191) baseStart_4100191 baseEnd_4100191 := by
    simpa [prefixWord, tailWord_4100191, baseEnd_4100191] using wordTrace_append hprefix tailTrace_4100191
  have hstable : (prefixWord ++ tailWord_4100191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100191).length < 2 ^ (prefixWord ++ tailWord_4100191).sum := by decide
  have hdescent : baseEnd_4100191 < baseStart_4100191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100210 : List Nat := [3, 2, 1, 2, 2, 2, 4, 1, 5]
def baseStart_4100210 : Nat := 118140960795 + 4100210 * 2 ^ 59
def prefixEnd_4100210 : Nat := 4983230072969 + 3 ^ 40 * 4100210 * 2
def baseEnd_4100210 : Nat := 467861892082557365159663

theorem tailTrace_4100210 : CollatzResearch.WordTrace tailWord_4100210 prefixEnd_4100210 467861892082557365159663 := by
  unfold tailWord_4100210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37386736118911726240638521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99697962983764603308369389 37386736118911726240638521)
  ·
    refine ⟨28040052089183794680478891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37386736118911726240638521 28040052089183794680478891)
    ·
      refine ⟨42060078133775692020718337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28040052089183794680478891 42060078133775692020718337)
      ·
        refine ⟨31545058600331769015538753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42060078133775692020718337 31545058600331769015538753)
        ·
          refine ⟨23658793950248826761654065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31545058600331769015538753 23658793950248826761654065)
          ·
            refine ⟨17744095462686620071240549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23658793950248826761654065 17744095462686620071240549)
            ·
              refine ⟨3327017899253741263357603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17744095462686620071240549 3327017899253741263357603)
              ·
                refine ⟨4990526848880611895036405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327017899253741263357603 4990526848880611895036405)
                ·
                  refine ⟨467861892082557365159663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4990526848880611895036405 467861892082557365159663)
                  ·
                    rfl

theorem cell22_4100210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_4100210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100210 prefixEnd_4100210 := by exact prefixLift 4100210
  have htrace : WordTrace (prefixWord ++ tailWord_4100210) baseStart_4100210 baseEnd_4100210 := by
    simpa [prefixWord, tailWord_4100210, baseEnd_4100210] using wordTrace_append hprefix tailTrace_4100210
  have hstable : (prefixWord ++ tailWord_4100210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100210).length < 2 ^ (prefixWord ++ tailWord_4100210).sum := by decide
  have hdescent : baseEnd_4100210 < baseStart_4100210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100240 : List Nat := [2, 1, 1, 1, 1, 1, 9, 1, 1, 4]
def baseStart_4100240 : Nat := 118140960795 + 4100240 * 2 ^ 59
def prefixEnd_4100240 : Nat := 4983230072969 + 3 ^ 40 * 4100240 * 2
def baseEnd_4100240 : Nat := 1403595945860762017228897

theorem tailTrace_4100240 : CollatzResearch.WordTrace tailWord_4100240 prefixEnd_4100240 1403595945860762017228897 := by
  unfold tailWord_4100240
  simp only [CollatzResearch.WordTrace]
  refine ⟨74774019332769110043073087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99698692443692146724097449 74774019332769110043073087)
  ·
    refine ⟨112161028999153665064609631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74774019332769110043073087 112161028999153665064609631)
    ·
      refine ⟨168241543498730497596914447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112161028999153665064609631 168241543498730497596914447)
      ·
        refine ⟨252362315248095746395371671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168241543498730497596914447 252362315248095746395371671)
        ·
          refine ⟨378543472872143619593057507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252362315248095746395371671 378543472872143619593057507)
          ·
            refine ⟨567815209308215429389586261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378543472872143619593057507 567815209308215429389586261)
            ·
              refine ⟨3327042242040324781579607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 567815209308215429389586261 3327042242040324781579607)
              ·
                refine ⟨4990563363060487172369411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327042242040324781579607 4990563363060487172369411)
                ·
                  refine ⟨7485845044590730758554117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4990563363060487172369411 7485845044590730758554117)
                  ·
                    refine ⟨1403595945860762017228897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7485845044590730758554117 1403595945860762017228897)
                    ·
                      rfl

theorem cell22_4100240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 1, 4].length) (baseStart_4100240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100240 prefixEnd_4100240 := by exact prefixLift 4100240
  have htrace : WordTrace (prefixWord ++ tailWord_4100240) baseStart_4100240 baseEnd_4100240 := by
    simpa [prefixWord, tailWord_4100240, baseEnd_4100240] using wordTrace_append hprefix tailTrace_4100240
  have hstable : (prefixWord ++ tailWord_4100240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100240).length < 2 ^ (prefixWord ++ tailWord_4100240).sum := by decide
  have hdescent : baseEnd_4100240 < baseStart_4100240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100283 : List Nat := [1, 1, 1, 1, 1, 2, 9, 6]
def baseStart_4100283 : Nat := 118140960795 + 4100283 * 2 ^ 59
def prefixEnd_4100283 : Nat := 4983230072969 + 3 ^ 40 * 4100283 * 2
def baseEnd_4100283 : Nat := 155956740626613804267085

theorem tailTrace_4100283 : CollatzResearch.WordTrace tailWord_4100283 prefixEnd_4100283 155956740626613804267085 := by
  unfold tailWord_4100283
  simp only [CollatzResearch.WordTrace]
  refine ⟨149549607004382438429961503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99699738002921625619974335 149549607004382438429961503)
  ·
    refine ⟨224324410506573657644942255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149549607004382438429961503 224324410506573657644942255)
    ·
      refine ⟨336486615759860486467413383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224324410506573657644942255 336486615759860486467413383)
      ·
        refine ⟨504729923639790729701120075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336486615759860486467413383 504729923639790729701120075)
        ·
          refine ⟨757094885459686094551680113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504729923639790729701120075 757094885459686094551680113)
          ·
            refine ⟨567821164094764570913760085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757094885459686094551680113 567821164094764570913760085)
            ·
              refine ⟨3327077133367761157697813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 567821164094764570913760085 3327077133367761157697813)
              ·
                refine ⟨155956740626613804267085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3327077133367761157697813 155956740626613804267085)
                ·
                  rfl

theorem cell22_4100283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 6].length) (baseStart_4100283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100283 prefixEnd_4100283 := by exact prefixLift 4100283
  have htrace : WordTrace (prefixWord ++ tailWord_4100283) baseStart_4100283 baseEnd_4100283 := by
    simpa [prefixWord, tailWord_4100283, baseEnd_4100283] using wordTrace_append hprefix tailTrace_4100283
  have hstable : (prefixWord ++ tailWord_4100283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100283).length < 2 ^ (prefixWord ++ tailWord_4100283).sum := by decide
  have hdescent : baseEnd_4100283 < baseStart_4100283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100289 : List Nat := [1, 2, 6, 1, 2, 1, 2, 3, 4]
def baseStart_4100289 : Nat := 118140960795 + 4100289 * 2 ^ 59
def prefixEnd_4100289 : Nat := 4983230072969 + 3 ^ 40 * 4100289 * 2
def baseEnd_4100289 : Nat := 467870906520714074251249

theorem tailTrace_4100289 : CollatzResearch.WordTrace tailWord_4100289 prefixEnd_4100289 467870906520714074251249 := by
  unfold tailWord_4100289
  simp only [CollatzResearch.WordTrace]
  refine ⟨149549825842360701454679921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99699883894907134303119947 149549825842360701454679921)
  ·
    refine ⟨112162369381770526091009941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149549825842360701454679921 112162369381770526091009941)
    ·
      refine ⟨5257611064770493410516091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 112162369381770526091009941 5257611064770493410516091)
      ·
        refine ⟨7886416597155740115774137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5257611064770493410516091 7886416597155740115774137)
        ·
          refine ⟨5914812447866805086830603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7886416597155740115774137 5914812447866805086830603)
          ·
            refine ⟨8872218671800207630245905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914812447866805086830603 8872218671800207630245905)
            ·
              refine ⟨6654164003850155722684429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8872218671800207630245905 6654164003850155722684429)
              ·
                refine ⟨2495311501443808396006661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6654164003850155722684429 2495311501443808396006661)
                ·
                  refine ⟨467870906520714074251249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495311501443808396006661 467870906520714074251249)
                  ·
                    rfl

theorem cell22_4100289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 4].length) (baseStart_4100289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100289 prefixEnd_4100289 := by exact prefixLift 4100289
  have htrace : WordTrace (prefixWord ++ tailWord_4100289) baseStart_4100289 baseEnd_4100289 := by
    simpa [prefixWord, tailWord_4100289, baseEnd_4100289] using wordTrace_append hprefix tailTrace_4100289
  have hstable : (prefixWord ++ tailWord_4100289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100289).length < 2 ^ (prefixWord ++ tailWord_4100289).sum := by decide
  have hdescent : baseEnd_4100289 < baseStart_4100289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100300 : List Nat := [2, 2, 1, 6, 1, 1, 9]
def baseStart_4100300 : Nat := 118140960795 + 4100300 * 2 ^ 59
def prefixEnd_4100300 : Nat := 4983230072969 + 3 ^ 40 * 4100300 * 2
def baseEnd_4100300 : Nat := 51985795743960809656619

theorem tailTrace_4100300 : CollatzResearch.WordTrace tailWord_4100300 prefixEnd_4100300 51985795743960809656619 := by
  unfold tailWord_4100300
  simp only [CollatzResearch.WordTrace]
  refine ⟨74775113522660425166665177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99700151363547233555553569 74775113522660425166665177)
  ·
    refine ⟨56081335141995318874998883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74775113522660425166665177 56081335141995318874998883)
    ·
      refine ⟨84122002712992978312498325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56081335141995318874998883 84122002712992978312498325)
      ·
        refine ⟨3943218877171545858398359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84122002712992978312498325 3943218877171545858398359)
        ·
          refine ⟨5914828315757318787597539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943218877171545858398359 5914828315757318787597539)
          ·
            refine ⟨8872242473635978181396309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914828315757318787597539 8872242473635978181396309)
            ·
              refine ⟨51985795743960809656619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8872242473635978181396309 51985795743960809656619)
              ·
                rfl

theorem cell22_4100300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 9].length) (baseStart_4100300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100300 prefixEnd_4100300 := by exact prefixLift 4100300
  have htrace : WordTrace (prefixWord ++ tailWord_4100300) baseStart_4100300 baseEnd_4100300 := by
    simpa [prefixWord, tailWord_4100300, baseEnd_4100300] using wordTrace_append hprefix tailTrace_4100300
  have hstable : (prefixWord ++ tailWord_4100300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100300).length < 2 ^ (prefixWord ++ tailWord_4100300).sum := by decide
  have hdescent : baseEnd_4100300 < baseStart_4100300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100392 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 3, 4]
def baseStart_4100392 : Nat := 118140960795 + 4100392 * 2 ^ 59
def prefixEnd_4100392 : Nat := 4983230072969 + 3 ^ 40 * 4100392 * 2
def baseEnd_4100392 : Nat := 1403647978567084287428431

theorem tailTrace_4100392 : CollatzResearch.WordTrace tailWord_4100392 prefixEnd_4100392 1403647978567084287428431 := by
  unfold tailWord_4100392
  simp only [CollatzResearch.WordTrace]
  refine ⟨74776791280493775022839715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99702388373991700030452953 74776791280493775022839715)
  ·
    refine ⟨112165186920740662534259573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74776791280493775022839715 112165186920740662534259573)
    ·
      refine ⟨10515486273819437112586835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112165186920740662534259573 10515486273819437112586835)
      ·
        refine ⟨15773229410729155668880253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10515486273819437112586835 15773229410729155668880253)
        ·
          refine ⟨5914961029023433375830095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15773229410729155668880253 5914961029023433375830095)
          ·
            refine ⟨8872441543535150063745143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5914961029023433375830095 8872441543535150063745143)
            ·
              refine ⟨13308662315302725095617715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872441543535150063745143 13308662315302725095617715)
              ·
                refine ⟨19962993472954087643426573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13308662315302725095617715 19962993472954087643426573)
                ·
                  refine ⟨7486122552357782866284965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19962993472954087643426573 7486122552357782866284965)
                  ·
                    refine ⟨1403647978567084287428431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7486122552357782866284965 1403647978567084287428431)
                    ·
                      rfl

theorem cell22_4100392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_4100392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100392 prefixEnd_4100392 := by exact prefixLift 4100392
  have htrace : WordTrace (prefixWord ++ tailWord_4100392) baseStart_4100392 baseEnd_4100392 := by
    simpa [prefixWord, tailWord_4100392, baseEnd_4100392] using wordTrace_append hprefix tailTrace_4100392
  have hstable : (prefixWord ++ tailWord_4100392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100392).length < 2 ^ (prefixWord ++ tailWord_4100392).sum := by decide
  have hdescent : baseEnd_4100392 < baseStart_4100392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100405 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_4100405 : Nat := 118140960795 + 4100405 * 2 ^ 59
def prefixEnd_4100405 : Nat := 4983230072969 + 3 ^ 40 * 4100405 * 2
def baseEnd_4100405 : Nat := 1403652428732756586853391

theorem tailTrace_4100405 : CollatzResearch.WordTrace tailWord_4100405 prefixEnd_4100405 1403652428732756586853391 := by
  unfold tailWord_4100405
  simp only [CollatzResearch.WordTrace]
  refine ⟨149554056709940453265902669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99702704473293635510601779 149554056709940453265902669)
  ·
    refine ⟨56082771266227669974713501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149554056709940453265902669 56082771266227669974713501)
    ·
      refine ⟨21031039224835376240517563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56082771266227669974713501 21031039224835376240517563)
      ·
        refine ⟨31546558837253064360776345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21031039224835376240517563 31546558837253064360776345)
        ·
          refine ⟨23659919127939798270582259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31546558837253064360776345 23659919127939798270582259)
          ·
            refine ⟨35489878691909697405873389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23659919127939798270582259 35489878691909697405873389)
            ·
              refine ⟨13308704509466136527202521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35489878691909697405873389 13308704509466136527202521)
              ·
                refine ⟨9981528382099602395401891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13308704509466136527202521 9981528382099602395401891)
                ·
                  refine ⟨14972292573149403593102837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9981528382099602395401891 14972292573149403593102837)
                  ·
                    refine ⟨1403652428732756586853391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14972292573149403593102837 1403652428732756586853391)
                    ·
                      rfl

theorem cell22_4100405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_4100405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100405 prefixEnd_4100405 := by exact prefixLift 4100405
  have htrace : WordTrace (prefixWord ++ tailWord_4100405) baseStart_4100405 baseEnd_4100405 := by
    simpa [prefixWord, tailWord_4100405, baseEnd_4100405] using wordTrace_append hprefix tailTrace_4100405
  have hstable : (prefixWord ++ tailWord_4100405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100405).length < 2 ^ (prefixWord ++ tailWord_4100405).sum := by decide
  have hdescent : baseEnd_4100405 < baseStart_4100405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100409 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 1, 4]
def baseStart_4100409 : Nat := 118140960795 + 4100409 * 2 ^ 59
def prefixEnd_4100409 : Nat := 4983230072969 + 3 ^ 40 * 4100409 * 2
def baseEnd_4100409 : Nat := 1403653798014501909753379

theorem tailTrace_4100409 : CollatzResearch.WordTrace tailWord_4100409 prefixEnd_4100409 1403653798014501909753379 := by
  unfold tailWord_4100409
  simp only [CollatzResearch.WordTrace]
  refine ⟨149554202601925961949048281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99702801734617307966032187 149554202601925961949048281)
  ·
    refine ⟨112165651951444471461786211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149554202601925961949048281 112165651951444471461786211)
    ·
      refine ⟨168248477927166707192679317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112165651951444471461786211 168248477927166707192679317)
      ·
        refine ⟨7886647402835939399656843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 168248477927166707192679317 7886647402835939399656843)
        ·
          refine ⟨11829971104253909099485265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7886647402835939399656843 11829971104253909099485265)
          ·
            refine ⟨8872478328190431824613949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11829971104253909099485265 8872478328190431824613949)
            ·
              refine ⟨3327179373071411934230231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8872478328190431824613949 3327179373071411934230231)
              ·
                refine ⟨4990769059607117901345347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327179373071411934230231 4990769059607117901345347)
                ·
                  refine ⟨7486153589410676852018021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4990769059607117901345347 7486153589410676852018021)
                  ·
                    refine ⟨1403653798014501909753379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7486153589410676852018021 1403653798014501909753379)
                    ·
                      rfl

theorem cell22_4100409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 1, 4].length) (baseStart_4100409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100409 prefixEnd_4100409 := by exact prefixLift 4100409
  have htrace : WordTrace (prefixWord ++ tailWord_4100409) baseStart_4100409 baseEnd_4100409 := by
    simpa [prefixWord, tailWord_4100409, baseEnd_4100409] using wordTrace_append hprefix tailTrace_4100409
  have hstable : (prefixWord ++ tailWord_4100409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100409).length < 2 ^ (prefixWord ++ tailWord_4100409).sum := by decide
  have hdescent : baseEnd_4100409 < baseStart_4100409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100484 : List Nat := [2, 3, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_4100484 : Nat := 118140960795 + 4100484 * 2 ^ 59
def prefixEnd_4100484 : Nat := 4983230072969 + 3 ^ 40 * 4100484 * 2
def baseEnd_4100484 : Nat := 1403679472047226714128149

theorem tailTrace_4100484 : CollatzResearch.WordTrace tailWord_4100484 prefixEnd_4100484 1403679472047226714128149 := by
  unfold tailWord_4100484
  simp only [CollatzResearch.WordTrace]
  refine ⟨74778469038327124879014253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99704625384436166505352337 74778469038327124879014253)
  ·
    refine ⟨28041925889372671829630345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74778469038327124879014253 28041925889372671829630345)
    ·
      refine ⟨21031444417029503872222759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28041925889372671829630345 21031444417029503872222759)
      ·
        refine ⟨31547166625544255808334139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21031444417029503872222759 31547166625544255808334139)
        ·
          refine ⟨47320749938316383712501209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31547166625544255808334139 47320749938316383712501209)
          ·
            refine ⟨35490562453737287784375907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47320749938316383712501209 35490562453737287784375907)
            ·
              refine ⟨53235843680605931676563861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35490562453737287784375907 53235843680605931676563861)
              ·
                refine ⟨2495430172528403047338931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53235843680605931676563861 2495430172528403047338931)
                ·
                  refine ⟨3743145258792604571008397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495430172528403047338931 3743145258792604571008397)
                  ·
                    refine ⟨1403679472047226714128149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3743145258792604571008397 1403679472047226714128149)
                    ·
                      rfl

theorem cell22_4100484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_4100484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100484 prefixEnd_4100484 := by exact prefixLift 4100484
  have htrace : WordTrace (prefixWord ++ tailWord_4100484) baseStart_4100484 baseEnd_4100484 := by
    simpa [prefixWord, tailWord_4100484, baseEnd_4100484] using wordTrace_append hprefix tailTrace_4100484
  have hstable : (prefixWord ++ tailWord_4100484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100484).length < 2 ^ (prefixWord ++ tailWord_4100484).sum := by decide
  have hdescent : baseEnd_4100484 < baseStart_4100484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100542 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_4100542 : Nat := 118140960795 + 4100542 * 2 ^ 59
def prefixEnd_4100542 : Nat := 4983230072969 + 3 ^ 40 * 4100542 * 2
def baseEnd_4100542 : Nat := 467899775544177965392657

theorem tailTrace_4100542 : CollatzResearch.WordTrace tailWord_4100542 prefixEnd_4100542 467899775544177965392657 := by
  unfold tailWord_4100542
  simp only [CollatzResearch.WordTrace]
  refine ⟨18694881688805515707954985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99706035673629417109093253 18694881688805515707954985)
  ·
    refine ⟨14021161266604136780966239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18694881688805515707954985 14021161266604136780966239)
    ·
      refine ⟨21031741899906205171449359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14021161266604136780966239 21031741899906205171449359)
      ·
        refine ⟨31547612849859307757174039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21031741899906205171449359 31547612849859307757174039)
        ·
          refine ⟨47321419274788961635761059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31547612849859307757174039 47321419274788961635761059)
          ·
            refine ⟨70982128912183442453641589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47321419274788961635761059 70982128912183442453641589)
            ·
              refine ⟨6654574585517197730028899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70982128912183442453641589 6654574585517197730028899)
              ·
                refine ⟨9981861878275796595043349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6654574585517197730028899 9981861878275796595043349)
                ·
                  refine ⟨467899775544177965392657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9981861878275796595043349 467899775544177965392657)
                  ·
                    rfl

theorem cell22_4100542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_4100542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100542 prefixEnd_4100542 := by exact prefixLift 4100542
  have htrace : WordTrace (prefixWord ++ tailWord_4100542) baseStart_4100542 baseEnd_4100542 := by
    simpa [prefixWord, tailWord_4100542, baseEnd_4100542] using wordTrace_append hprefix tailTrace_4100542
  have hstable : (prefixWord ++ tailWord_4100542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100542).length < 2 ^ (prefixWord ++ tailWord_4100542).sum := by decide
  have hdescent : baseEnd_4100542 < baseStart_4100542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100548 : List Nat := [2, 3, 3, 2, 3, 1, 2, 1, 5]
def baseStart_4100548 : Nat := 118140960795 + 4100548 * 2 ^ 59
def prefixEnd_4100548 : Nat := 4983230072969 + 3 ^ 40 * 4100548 * 2
def baseEnd_4100548 : Nat := 467900460185050626842651

theorem tailTrace_4100548 : CollatzResearch.WordTrace tailWord_4100548 prefixEnd_4100548 467900460185050626842651 := by
  unfold tailWord_4100548
  simp only [CollatzResearch.WordTrace]
  refine ⟨74779636174211194344179149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99706181565614925792238865 74779636174211194344179149)
  ·
    refine ⟨28042363565329197879067181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74779636174211194344179149 28042363565329197879067181)
    ·
      refine ⟨10515886336998449204650193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28042363565329197879067181 10515886336998449204650193)
      ·
        refine ⟨7886914752748836903487645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10515886336998449204650193 7886914752748836903487645)
        ·
          refine ⟨2957593032280813838807867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7886914752748836903487645 2957593032280813838807867)
          ·
            refine ⟨4436389548421220758211801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957593032280813838807867 4436389548421220758211801)
            ·
              refine ⟨3327292161315915568658851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4436389548421220758211801 3327292161315915568658851)
              ·
                refine ⟨4990938241973873352988277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327292161315915568658851 4990938241973873352988277)
                ·
                  refine ⟨467900460185050626842651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4990938241973873352988277 467900460185050626842651)
                  ·
                    rfl

theorem cell22_4100548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_4100548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100548 prefixEnd_4100548 := by exact prefixLift 4100548
  have htrace : WordTrace (prefixWord ++ tailWord_4100548) baseStart_4100548 baseEnd_4100548 := by
    simpa [prefixWord, tailWord_4100548, baseEnd_4100548] using wordTrace_append hprefix tailTrace_4100548
  have hstable : (prefixWord ++ tailWord_4100548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100548).length < 2 ^ (prefixWord ++ tailWord_4100548).sum := by decide
  have hdescent : baseEnd_4100548 < baseStart_4100548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100555 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 6, 4]
def baseStart_4100555 : Nat := 118140960795 + 4100555 * 2 ^ 59
def prefixEnd_4100555 : Nat := 4983230072969 + 3 ^ 40 * 4100555 * 2
def baseEnd_4100555 : Nat := 1403703776798206195602931

theorem tailTrace_4100555 : CollatzResearch.WordTrace tailWord_4100555 prefixEnd_4100555 1403703776798206195602931 := by
  unfold tailWord_4100555
  simp only [CollatzResearch.WordTrace]
  refine ⟨149559527659397028883863119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99706351772931352589242079 149559527659397028883863119)
  ·
    refine ⟨224339291489095543325794679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149559527659397028883863119 224339291489095543325794679)
    ·
      refine ⟨336508937233643314988692019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224339291489095543325794679 336508937233643314988692019)
      ·
        refine ⟨504763405850464972483038029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336508937233643314988692019 504763405850464972483038029)
        ·
          refine ⟨189286277193924364681139261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 504763405850464972483038029 189286277193924364681139261)
          ·
            refine ⟨70982353947721636755427223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189286277193924364681139261 70982353947721636755427223)
            ·
              refine ⟨106473530921582455133140835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70982353947721636755427223 106473530921582455133140835)
              ·
                refine ⟨159710296382373682699711253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106473530921582455133140835 159710296382373682699711253)
                ·
                  refine ⟨7486420142923766376548965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159710296382373682699711253 7486420142923766376548965)
                  ·
                    refine ⟨1403703776798206195602931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7486420142923766376548965 1403703776798206195602931)
                    ·
                      rfl

theorem cell22_4100555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 4].length) (baseStart_4100555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100555 prefixEnd_4100555 := by exact prefixLift 4100555
  have htrace : WordTrace (prefixWord ++ tailWord_4100555) baseStart_4100555 baseEnd_4100555 := by
    simpa [prefixWord, tailWord_4100555, baseEnd_4100555] using wordTrace_append hprefix tailTrace_4100555
  have hstable : (prefixWord ++ tailWord_4100555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100555).length < 2 ^ (prefixWord ++ tailWord_4100555).sum := by decide
  have hdescent : baseEnd_4100555 < baseStart_4100555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100570 : List Nat := [3, 1, 1, 2, 3, 1, 1, 10]
def baseStart_4100570 : Nat := 118140960795 + 4100570 * 2 ^ 59
def prefixEnd_4100570 : Nat := 4983230072969 + 3 ^ 40 * 4100570 * 2
def baseEnd_4100570 : Nat := 155967656844972350719765

theorem tailTrace_4100570 : CollatzResearch.WordTrace tailWord_4100570 prefixEnd_4100570 155967656844972350719765 := by
  unfold tailWord_4100570
  simp only [CollatzResearch.WordTrace]
  refine ⟨37390018688585671611414791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99706716502895124297106109 37390018688585671611414791)
  ·
    refine ⟨56085028032878507417122187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37390018688585671611414791 56085028032878507417122187)
    ·
      refine ⟨84127542049317761125683281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56085028032878507417122187 84127542049317761125683281)
      ·
        refine ⟨63095656536988320844262461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84127542049317761125683281 63095656536988320844262461)
        ·
          refine ⟨23660871201370620316598423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63095656536988320844262461 23660871201370620316598423)
          ·
            refine ⟨35491306802055930474897635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23660871201370620316598423 35491306802055930474897635)
            ·
              refine ⟨53236960203083895712346453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35491306802055930474897635 53236960203083895712346453)
              ·
                refine ⟨155967656844972350719765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53236960203083895712346453 155967656844972350719765)
                ·
                  rfl

theorem cell22_4100570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_4100570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100570 prefixEnd_4100570 := by exact prefixLift 4100570
  have htrace : WordTrace (prefixWord ++ tailWord_4100570) baseStart_4100570 baseEnd_4100570 := by
    simpa [prefixWord, tailWord_4100570, baseEnd_4100570] using wordTrace_append hprefix tailTrace_4100570
  have hstable : (prefixWord ++ tailWord_4100570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100570).length < 2 ^ (prefixWord ++ tailWord_4100570).sum := by decide
  have hdescent : baseEnd_4100570 < baseStart_4100570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100589 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_4100589 : Nat := 118140960795 + 4100589 * 2 ^ 59
def prefixEnd_4100589 : Nat := 4983230072969 + 3 ^ 40 * 4100589 * 2
def baseEnd_4100589 : Nat := 1403715415693041440252827

theorem tailTrace_4100589 : CollatzResearch.WordTrace tailWord_4100589 prefixEnd_4100589 1403715415693041440252827 := by
  unfold tailWord_4100589
  simp only [CollatzResearch.WordTrace]
  refine ⟨149560767741273852690600821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99707178494182568460400547 149560767741273852690600821)
  ·
    refine ⟨14021321975744423689743827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149560767741273852690600821 14021321975744423689743827)
    ·
      refine ⟨21031982963616635534615741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14021321975744423689743827 21031982963616635534615741)
      ·
        refine ⟨7886993611356238325480903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21031982963616635534615741 7886993611356238325480903)
        ·
          refine ⟨11830490417034357488221355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7886993611356238325480903 11830490417034357488221355)
          ·
            refine ⟨17745735625551536232332033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11830490417034357488221355 17745735625551536232332033)
            ·
              refine ⟨13309301719163652174249025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17745735625551536232332033 13309301719163652174249025)
              ·
                refine ⟨9981976289372739130686769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13309301719163652174249025 9981976289372739130686769)
                ·
                  refine ⟨7486482217029554348015077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9981976289372739130686769 7486482217029554348015077)
                  ·
                    refine ⟨1403715415693041440252827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7486482217029554348015077 1403715415693041440252827)
                    ·
                      rfl

theorem cell22_4100589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_4100589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100589 prefixEnd_4100589 := by exact prefixLift 4100589
  have htrace : WordTrace (prefixWord ++ tailWord_4100589) baseStart_4100589 baseEnd_4100589 := by
    simpa [prefixWord, tailWord_4100589, baseEnd_4100589] using wordTrace_append hprefix tailTrace_4100589
  have hstable : (prefixWord ++ tailWord_4100589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100589).length < 2 ^ (prefixWord ++ tailWord_4100589).sum := by decide
  have hdescent : baseEnd_4100589 < baseStart_4100589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100600 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 1, 8]
def baseStart_4100600 : Nat := 118140960795 + 4100600 * 2 ^ 59
def prefixEnd_4100600 : Nat := 4983230072969 + 3 ^ 40 * 4100600 * 2
def baseEnd_4100600 : Nat := 1403719181217841078227793

theorem tailTrace_4100600 : CollatzResearch.WordTrace tailWord_4100600 prefixEnd_4100600 1403719181217841078227793 := by
  unfold tailWord_4100600
  simp only [CollatzResearch.WordTrace]
  refine ⟨74780584472117000784625627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99707445962822667712834169 74780584472117000784625627)
  ·
    refine ⟨112170876708175501176938441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74780584472117000784625627 112170876708175501176938441)
    ·
      refine ⟨84128157531131625882703831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112170876708175501176938441 84128157531131625882703831)
      ·
        refine ⟨126192236296697438824055747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84128157531131625882703831 126192236296697438824055747)
        ·
          refine ⟨189288354445046158236083621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126192236296697438824055747 189288354445046158236083621)
          ·
            refine ⟨35491566458446154669265679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 189288354445046158236083621 35491566458446154669265679)
            ·
              refine ⟨53237349687669232003898519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35491566458446154669265679 53237349687669232003898519)
              ·
                refine ⟨79856024531503848005847779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53237349687669232003898519 79856024531503848005847779)
                ·
                  refine ⟨119784036797255772008771669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79856024531503848005847779 119784036797255772008771669)
                  ·
                    refine ⟨1403719181217841078227793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119784036797255772008771669 1403719181217841078227793)
                    ·
                      rfl

theorem cell22_4100600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_4100600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100600 prefixEnd_4100600 := by exact prefixLift 4100600
  have htrace : WordTrace (prefixWord ++ tailWord_4100600) baseStart_4100600 baseEnd_4100600 := by
    simpa [prefixWord, tailWord_4100600, baseEnd_4100600] using wordTrace_append hprefix tailTrace_4100600
  have hstable : (prefixWord ++ tailWord_4100600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100600).length < 2 ^ (prefixWord ++ tailWord_4100600).sum := by decide
  have hdescent : baseEnd_4100600 < baseStart_4100600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100619 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 3, 3]
def baseStart_4100619 : Nat := 118140960795 + 4100619 * 2 ^ 59
def prefixEnd_4100619 : Nat := 4983230072969 + 3 ^ 40 * 4100619 * 2
def baseEnd_4100619 : Nat := 1403725685306131362002735

theorem tailTrace_4100619 : CollatzResearch.WordTrace tailWord_4100619 prefixEnd_4100619 1403725685306131362002735 := by
  unfold tailWord_4100619
  simp only [CollatzResearch.WordTrace]
  refine ⟨149561861931165167814192911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99707907954110111876128607 149561861931165167814192911)
  ·
    refine ⟨224342792896747751721289367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149561861931165167814192911 224342792896747751721289367)
    ·
      refine ⟨336514189345121627581934051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224342792896747751721289367 336514189345121627581934051)
      ·
        refine ⟨504771284017682441372901077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336514189345121627581934051 504771284017682441372901077)
        ·
          refine ⟨11830576969164432219677369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 504771284017682441372901077 11830576969164432219677369)
          ·
            refine ⟨8872932726873324164758027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11830576969164432219677369 8872932726873324164758027)
            ·
              refine ⟨13309399090309986247137041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8872932726873324164758027 13309399090309986247137041)
              ·
                refine ⟨9982049317732489685352781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13309399090309986247137041 9982049317732489685352781)
                ·
                  refine ⟨3743268494149683632007293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9982049317732489685352781 3743268494149683632007293)
                  ·
                    refine ⟨1403725685306131362002735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3743268494149683632007293 1403725685306131362002735)
                    ·
                      rfl

theorem cell22_4100619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 3].length) (baseStart_4100619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100619 prefixEnd_4100619 := by exact prefixLift 4100619
  have htrace : WordTrace (prefixWord ++ tailWord_4100619) baseStart_4100619 baseEnd_4100619 := by
    simpa [prefixWord, tailWord_4100619, baseEnd_4100619] using wordTrace_append hprefix tailTrace_4100619
  have hstable : (prefixWord ++ tailWord_4100619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100619).length < 2 ^ (prefixWord ++ tailWord_4100619).sum := by decide
  have hdescent : baseEnd_4100619 < baseStart_4100619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100636 : List Nat := [2, 2, 3, 1, 2, 2, 1, 5, 1, 3]
def baseStart_4100636 : Nat := 118140960795 + 4100636 * 2 ^ 59
def prefixEnd_4100636 : Nat := 4983230072969 + 3 ^ 40 * 4100636 * 2
def baseEnd_4100636 : Nat := 1403731504753548984327683

theorem tailTrace_4100636 : CollatzResearch.WordTrace tailWord_4100636 prefixEnd_4100636 1403731504753548984327683 := by
  unfold tailWord_4100636
  simp only [CollatzResearch.WordTrace]
  refine ⟨74781240986051789858780881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99708321314735719811707841 74781240986051789858780881)
  ·
    refine ⟨56085930739538842394085661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74781240986051789858780881 56085930739538842394085661)
    ·
      refine ⟨21032224027327065897782123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56085930739538842394085661 21032224027327065897782123)
      ·
        refine ⟨31548336040990598846673185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21032224027327065897782123 31548336040990598846673185)
        ·
          refine ⟨23661252030742949135004889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31548336040990598846673185 23661252030742949135004889)
          ·
            refine ⟨17745939023057211851253667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23661252030742949135004889 17745939023057211851253667)
            ·
              refine ⟨26618908534585817776880501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17745939023057211851253667 26618908534585817776880501)
              ·
                refine ⟨2495522675117420416582547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26618908534585817776880501 2495522675117420416582547)
                ·
                  refine ⟨3743284012676130624873821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495522675117420416582547 3743284012676130624873821)
                  ·
                    refine ⟨1403731504753548984327683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3743284012676130624873821 1403731504753548984327683)
                    ·
                      rfl

theorem cell22_4100636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_4100636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100636 prefixEnd_4100636 := by exact prefixLift 4100636
  have htrace : WordTrace (prefixWord ++ tailWord_4100636) baseStart_4100636 baseEnd_4100636 := by
    simpa [prefixWord, tailWord_4100636, baseEnd_4100636] using wordTrace_append hprefix tailTrace_4100636
  have hstable : (prefixWord ++ tailWord_4100636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100636).length < 2 ^ (prefixWord ++ tailWord_4100636).sum := by decide
  have hdescent : baseEnd_4100636 < baseStart_4100636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100677 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 6]
def baseStart_4100677 : Nat := 118140960795 + 4100677 * 2 ^ 59
def prefixEnd_4100677 : Nat := 4983230072969 + 3 ^ 40 * 4100677 * 2
def baseEnd_4100677 : Nat := 467915179963812848017519

theorem tailTrace_4100677 : CollatzResearch.WordTrace tailWord_4100677 prefixEnd_4100677 467915179963812848017519 := by
  unfold tailWord_4100677
  simp only [CollatzResearch.WordTrace]
  refine ⟨149563977364955043719804285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99709318243303362479869523 149563977364955043719804285)
  ·
    refine ⟨56086491511858141394926607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149563977364955043719804285 56086491511858141394926607)
    ·
      refine ⟨84129737267787212092389911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56086491511858141394926607 84129737267787212092389911)
      ·
        refine ⟨126194605901680818138584867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84129737267787212092389911 126194605901680818138584867)
        ·
          refine ⟨189291908852521227207877301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126194605901680818138584867 189291908852521227207877301)
          ·
            refine ⟨17746116454923865050738497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189291908852521227207877301 17746116454923865050738497)
            ·
              refine ⟨13309587341192898788053873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17746116454923865050738497 13309587341192898788053873)
              ·
                refine ⟨9982190505894674091040405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13309587341192898788053873 9982190505894674091040405)
                ·
                  refine ⟨467915179963812848017519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9982190505894674091040405 467915179963812848017519)
                  ·
                    rfl

theorem cell22_4100677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_4100677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100677 prefixEnd_4100677 := by exact prefixLift 4100677
  have htrace : WordTrace (prefixWord ++ tailWord_4100677) baseStart_4100677 baseEnd_4100677 := by
    simpa [prefixWord, tailWord_4100677, baseEnd_4100677] using wordTrace_append hprefix tailTrace_4100677
  have hstable : (prefixWord ++ tailWord_4100677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100677).length < 2 ^ (prefixWord ++ tailWord_4100677).sum := by decide
  have hdescent : baseEnd_4100677 < baseStart_4100677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100679 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 1, 4]
def baseStart_4100679 : Nat := 118140960795 + 4100679 * 2 ^ 59
def prefixEnd_4100679 : Nat := 4983230072969 + 3 ^ 40 * 4100679 * 2
def baseEnd_4100679 : Nat := 1403746224532311205502551

theorem tailTrace_4100679 : CollatzResearch.WordTrace tailWord_4100679 prefixEnd_4100679 1403746224532311205502551 := by
  unfold tailWord_4100679
  simp only [CollatzResearch.WordTrace]
  refine ⟨149564050310947798061377091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99709366873965198707584727 149564050310947798061377091)
  ·
    refine ⟨224346075466421697092065637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149564050310947798061377091 224346075466421697092065637)
    ·
      refine ⟨42064889149954068204762307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224346075466421697092065637 42064889149954068204762307)
      ·
        refine ⟨63097333724931102307143461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42064889149954068204762307 63097333724931102307143461)
        ·
          refine ⟨11830750073424581682589399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63097333724931102307143461 11830750073424581682589399)
          ·
            refine ⟨17746125110136872523884099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11830750073424581682589399 17746125110136872523884099)
            ·
              refine ⟨26619187665205308785826149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17746125110136872523884099 26619187665205308785826149)
              ·
                refine ⟨4991097687225995397342403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26619187665205308785826149 4991097687225995397342403)
                ·
                  refine ⟨7486646530838993096013605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991097687225995397342403 7486646530838993096013605)
                  ·
                    refine ⟨1403746224532311205502551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7486646530838993096013605 1403746224532311205502551)
                    ·
                      rfl

theorem cell22_4100679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_4100679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100679 prefixEnd_4100679 := by exact prefixLift 4100679
  have htrace : WordTrace (prefixWord ++ tailWord_4100679) baseStart_4100679 baseEnd_4100679 := by
    simpa [prefixWord, tailWord_4100679, baseEnd_4100679] using wordTrace_append hprefix tailTrace_4100679
  have hstable : (prefixWord ++ tailWord_4100679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100679).length < 2 ^ (prefixWord ++ tailWord_4100679).sum := by decide
  have hdescent : baseEnd_4100679 < baseStart_4100679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100762 : List Nat := [3, 1, 1, 6, 2, 1, 2, 2, 4]
def baseStart_4100762 : Nat := 118140960795 + 4100762 * 2 ^ 59
def prefixEnd_4100762 : Nat := 4983230072969 + 3 ^ 40 * 4100762 * 2
def baseEnd_4100762 : Nat := 467924879042842218559099

theorem tailTrace_4100762 : CollatzResearch.WordTrace tailWord_4100762 prefixEnd_4100762 467924879042842218559099 := by
  unfold tailWord_4100762
  simp only [CollatzResearch.WordTrace]
  refine ⟨37391769392411775809162135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99711385046431402157765693 37391769392411775809162135)
  ·
    refine ⟨56087654088617663713743203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37391769392411775809162135 56087654088617663713743203)
    ·
      refine ⟨84131481132926495570614805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56087654088617663713743203 84131481132926495570614805)
      ·
        refine ⟨3943663178105929479872569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84131481132926495570614805 3943663178105929479872569)
        ·
          refine ⟨2957747383579447109904427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3943663178105929479872569 2957747383579447109904427)
          ·
            refine ⟨4436621075369170664856641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957747383579447109904427 4436621075369170664856641)
            ·
              refine ⟨3327465806526877998642481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4436621075369170664856641 3327465806526877998642481)
              ·
                refine ⟨2495599354895158498981861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3327465806526877998642481 2495599354895158498981861)
                ·
                  refine ⟨467924879042842218559099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2495599354895158498981861 467924879042842218559099)
                  ·
                    rfl

theorem cell22_4100762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_4100762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100762 prefixEnd_4100762 := by exact prefixLift 4100762
  have htrace : WordTrace (prefixWord ++ tailWord_4100762) baseStart_4100762 baseEnd_4100762 := by
    simpa [prefixWord, tailWord_4100762, baseEnd_4100762] using wordTrace_append hprefix tailTrace_4100762
  have hstable : (prefixWord ++ tailWord_4100762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100762).length < 2 ^ (prefixWord ++ tailWord_4100762).sum := by decide
  have hdescent : baseEnd_4100762 < baseStart_4100762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100818 : List Nat := [3, 2, 2, 2, 3, 2, 1, 2, 5]
def baseStart_4100818 : Nat := 118140960795 + 4100818 * 2 ^ 59
def prefixEnd_4100818 : Nat := 4983230072969 + 3 ^ 40 * 4100818 * 2
def baseEnd_4100818 : Nat := 467931269024320392092375

theorem tailTrace_4100818 : CollatzResearch.WordTrace tailWord_4100818 prefixEnd_4100818 467931269024320392092375 := by
  unfold tailWord_4100818
  simp only [CollatzResearch.WordTrace]
  refine ⟨37392280014361056200171777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99712746704962816533791405 37392280014361056200171777)
  ·
    refine ⟨28044210010770792150128833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37392280014361056200171777 28044210010770792150128833)
    ·
      refine ⟨21033157508078094112596625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28044210010770792150128833 21033157508078094112596625)
      ·
        refine ⟨15774868131058570584447469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21033157508078094112596625 15774868131058570584447469)
        ·
          refine ⟨5915575549146963969167801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15774868131058570584447469 5915575549146963969167801)
          ·
            refine ⟨4436681661860222976875851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5915575549146963969167801 4436681661860222976875851)
            ·
              refine ⟨6655022492790334465313777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436681661860222976875851 6655022492790334465313777)
              ·
                refine ⟨4991266869592750848985333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6655022492790334465313777 4991266869592750848985333)
                ·
                  refine ⟨467931269024320392092375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4991266869592750848985333 467931269024320392092375)
                  ·
                    rfl

theorem cell22_4100818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_4100818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100818 prefixEnd_4100818 := by exact prefixLift 4100818
  have htrace : WordTrace (prefixWord ++ tailWord_4100818) baseStart_4100818 baseEnd_4100818 := by
    simpa [prefixWord, tailWord_4100818, baseEnd_4100818] using wordTrace_append hprefix tailTrace_4100818
  have hstable : (prefixWord ++ tailWord_4100818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100818).length < 2 ^ (prefixWord ++ tailWord_4100818).sum := by decide
  have hdescent : baseEnd_4100818 < baseStart_4100818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100895 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 2, 3]
def baseStart_4100895 : Nat := 118140960795 + 4100895 * 2 ^ 59
def prefixEnd_4100895 : Nat := 4983230072969 + 3 ^ 40 * 4100895 * 2
def baseEnd_4100895 : Nat := 1403820165746558642101889

theorem tailTrace_4100895 : CollatzResearch.WordTrace tailWord_4100895 prefixEnd_4100895 1403820165746558642101889 := by
  unfold tailWord_4100895
  simp only [CollatzResearch.WordTrace]
  refine ⟨149571928478165266951240139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99714618985443511300826759 149571928478165266951240139)
  ·
    refine ⟨224357892717247900426860209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149571928478165266951240139 224357892717247900426860209)
    ·
      refine ⟨168268419537935925320145157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224357892717247900426860209 168268419537935925320145157)
      ·
        refine ⟨31550328663362985997527217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168268419537935925320145157 31550328663362985997527217)
        ·
          refine ⟨23662746497522239498145413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31550328663362985997527217 23662746497522239498145413)
          ·
            refine ⟨4436764968285419905902265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23662746497522239498145413 4436764968285419905902265)
            ·
              refine ⟨3327573726214064929426699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4436764968285419905902265 3327573726214064929426699)
              ·
                refine ⟨4991360589321097394140049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327573726214064929426699 4991360589321097394140049)
                ·
                  refine ⟨3743520441990823045605037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4991360589321097394140049 3743520441990823045605037)
                  ·
                    refine ⟨1403820165746558642101889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3743520441990823045605037 1403820165746558642101889)
                    ·
                      rfl

theorem cell22_4100895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 2, 3].length) (baseStart_4100895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100895 prefixEnd_4100895 := by exact prefixLift 4100895
  have htrace : WordTrace (prefixWord ++ tailWord_4100895) baseStart_4100895 baseEnd_4100895 := by
    simpa [prefixWord, tailWord_4100895, baseEnd_4100895] using wordTrace_append hprefix tailTrace_4100895
  have hstable : (prefixWord ++ tailWord_4100895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100895).length < 2 ^ (prefixWord ++ tailWord_4100895).sum := by decide
  have hdescent : baseEnd_4100895 < baseStart_4100895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100936 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 5]
def baseStart_4100936 : Nat := 118140960795 + 4100936 * 2 ^ 59
def prefixEnd_4100936 : Nat := 4983230072969 + 3 ^ 40 * 4100936 * 2
def baseEnd_4100936 : Nat := 467944733628149400608921

theorem tailTrace_4100936 : CollatzResearch.WordTrace tailWord_4100936 prefixEnd_4100936 467944733628149400608921 := by
  unfold tailWord_4100936
  simp only [CollatzResearch.WordTrace]
  refine ⟨74786711935508365476741331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99715615914011153968988441 74786711935508365476741331)
  ·
    refine ⟨112180067903262548215111997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74786711935508365476741331 112180067903262548215111997)
    ·
      refine ⟨42067525463723455580666999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112180067903262548215111997 42067525463723455580666999)
      ·
        refine ⟨63101288195585183371000499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42067525463723455580666999 63101288195585183371000499)
        ·
          refine ⟨94651932293377775056500749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63101288195585183371000499 94651932293377775056500749)
          ·
            refine ⟨35494474610016665646187781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94651932293377775056500749 35494474610016665646187781)
            ·
              refine ⟨6655213989378124808660209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35494474610016665646187781 6655213989378124808660209)
              ·
                refine ⟨4991410492033593606495157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6655213989378124808660209 4991410492033593606495157)
                ·
                  refine ⟨467944733628149400608921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4991410492033593606495157 467944733628149400608921)
                  ·
                    rfl

theorem cell22_4100936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_4100936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100936 prefixEnd_4100936 := by exact prefixLift 4100936
  have htrace : WordTrace (prefixWord ++ tailWord_4100936) baseStart_4100936 baseEnd_4100936 := by
    simpa [prefixWord, tailWord_4100936, baseEnd_4100936] using wordTrace_append hprefix tailTrace_4100936
  have hstable : (prefixWord ++ tailWord_4100936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100936).length < 2 ^ (prefixWord ++ tailWord_4100936).sum := by decide
  have hdescent : baseEnd_4100936 < baseStart_4100936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100940 : List Nat := [2, 2, 1, 3, 3, 2, 1, 4, 1, 3]
def baseStart_4100940 : Nat := 118140960795 + 4100940 * 2 ^ 59
def prefixEnd_4100940 : Nat := 4983230072969 + 3 ^ 40 * 4100940 * 2
def baseEnd_4100940 : Nat := 1403835570166193524726751

theorem tailTrace_4100940 : CollatzResearch.WordTrace tailWord_4100940 prefixEnd_4100940 1403835570166193524726751 := by
  unfold tailWord_4100940
  simp only [CollatzResearch.WordTrace]
  refine ⟨74786784881501119818314137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99715713175334826424418849 74786784881501119818314137)
  ·
    refine ⟨56090088661125839863735603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74786784881501119818314137 56090088661125839863735603)
    ·
      refine ⟨84135132991688759795603405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56090088661125839863735603 84135132991688759795603405)
      ·
        refine ⟨31550674871883284923351277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84135132991688759795603405 31550674871883284923351277)
        ·
          refine ⟨11831503076956231846256729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31550674871883284923351277 11831503076956231846256729)
          ·
            refine ⟨8873627307717173884692547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11831503076956231846256729 8873627307717173884692547)
            ·
              refine ⟨13310440961575760827038821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8873627307717173884692547 13310440961575760827038821)
              ·
                refine ⟨2495707680295455155069779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13310440961575760827038821 2495707680295455155069779)
                ·
                  refine ⟨3743561520443182732604669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495707680295455155069779 3743561520443182732604669)
                  ·
                    refine ⟨1403835570166193524726751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3743561520443182732604669 1403835570166193524726751)
                    ·
                      rfl

theorem cell22_4100940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_4100940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100940 prefixEnd_4100940 := by exact prefixLift 4100940
  have htrace : WordTrace (prefixWord ++ tailWord_4100940) baseStart_4100940 baseEnd_4100940 := by
    simpa [prefixWord, tailWord_4100940, baseEnd_4100940] using wordTrace_append hprefix tailTrace_4100940
  have hstable : (prefixWord ++ tailWord_4100940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100940).length < 2 ^ (prefixWord ++ tailWord_4100940).sum := by decide
  have hdescent : baseEnd_4100940 < baseStart_4100940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4100951 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 2, 5]
def baseStart_4100951 : Nat := 118140960795 + 4100951 * 2 ^ 59
def prefixEnd_4100951 : Nat := 4983230072969 + 3 ^ 40 * 4100951 * 2
def baseEnd_4100951 : Nat := 1403839335690993162701717

theorem tailTrace_4100951 : CollatzResearch.WordTrace tailWord_4100951 prefixEnd_4100951 1403839335690993162701717 := by
  unfold tailWord_4100951
  simp only [CollatzResearch.WordTrace]
  refine ⟨149573970965962388515278707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99715980643974925676852471 149573970965962388515278707)
  ·
    refine ⟨224360956448943582772918061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149573970965962388515278707 224360956448943582772918061)
    ·
      refine ⟨84135358668353843539844273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224360956448943582772918061 84135358668353843539844273)
      ·
        refine ⟨63101519001265382654883205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84135358668353843539844273 63101519001265382654883205)
        ·
          refine ⟨11831534812737259247790601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63101519001265382654883205 11831534812737259247790601)
          ·
            refine ⟨8873651109552944435842951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11831534812737259247790601 8873651109552944435842951)
            ·
              refine ⟨13310476664329416653764427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8873651109552944435842951 13310476664329416653764427)
              ·
                refine ⟨19965714996494124980646641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13310476664329416653764427 19965714996494124980646641)
                ·
                  refine ⟨14974286247370593735484981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19965714996494124980646641 14974286247370593735484981)
                  ·
                    refine ⟨1403839335690993162701717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14974286247370593735484981 1403839335690993162701717)
                    ·
                      rfl

theorem cell22_4100951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_4100951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4100951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4100951 prefixEnd_4100951 := by exact prefixLift 4100951
  have htrace : WordTrace (prefixWord ++ tailWord_4100951) baseStart_4100951 baseEnd_4100951 := by
    simpa [prefixWord, tailWord_4100951, baseEnd_4100951] using wordTrace_append hprefix tailTrace_4100951
  have hstable : (prefixWord ++ tailWord_4100951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4100951).length < 2 ^ (prefixWord ++ tailWord_4100951).sum := by decide
  have hdescent : baseEnd_4100951 < baseStart_4100951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4100951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101009 : List Nat := [1, 2, 2, 1, 1, 1, 3, 11]
def baseStart_4101009 : Nat := 118140960795 + 4101009 * 2 ^ 59
def prefixEnd_4101009 : Nat := 4983230072969 + 3 ^ 40 * 4101009 * 2
def baseEnd_4101009 : Nat := 155984354475144482750171

theorem tailTrace_4101009 : CollatzResearch.WordTrace tailWord_4101009 prefixEnd_4101009 155984354475144482750171 := by
  unfold tailWord_4101009
  simp only [CollatzResearch.WordTrace]
  refine ⟨149576086399752264420890081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99717390933168176280593387 149576086399752264420890081)
  ·
    refine ⟨112182064799814198315667561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149576086399752264420890081 112182064799814198315667561)
    ·
      refine ⟨84136548599860648736750671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112182064799814198315667561 84136548599860648736750671)
      ·
        refine ⟨126204822899790973105126007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84136548599860648736750671 126204822899790973105126007)
        ·
          refine ⟨189307234349686459657689011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126204822899790973105126007 189307234349686459657689011)
          ·
            refine ⟨283960851524529689486533517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189307234349686459657689011 283960851524529689486533517)
            ·
              refine ⟨106485319321698633557450069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283960851524529689486533517 106485319321698633557450069)
              ·
                refine ⟨155984354475144482750171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 106485319321698633557450069 155984354475144482750171)
                ·
                  rfl

theorem cell22_4101009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 11].length) (baseStart_4101009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101009 prefixEnd_4101009 := by exact prefixLift 4101009
  have htrace : WordTrace (prefixWord ++ tailWord_4101009) baseStart_4101009 baseEnd_4101009 := by
    simpa [prefixWord, tailWord_4101009, baseEnd_4101009] using wordTrace_append hprefix tailTrace_4101009
  have hstable : (prefixWord ++ tailWord_4101009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101009).length < 2 ^ (prefixWord ++ tailWord_4101009).sum := by decide
  have hdescent : baseEnd_4101009 < baseStart_4101009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101013 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 1, 5]
def baseStart_4101013 : Nat := 118140960795 + 4101013 * 2 ^ 59
def prefixEnd_4101013 : Nat := 4983230072969 + 3 ^ 40 * 4101013 * 2
def baseEnd_4101013 : Nat := 1403860559558045667651527

theorem tailTrace_4101013 : CollatzResearch.WordTrace tailWord_4101013 prefixEnd_4101013 1403860559558045667651527 := by
  unfold tailWord_4101013
  simp only [CollatzResearch.WordTrace]
  refine ⟨149576232291737773104035693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99717488194491848736023795 149576232291737773104035693)
  ·
    refine ⟨56091087109401664914013385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149576232291737773104035693 56091087109401664914013385)
    ·
      refine ⟨42068315332051248685510039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56091087109401664914013385 42068315332051248685510039)
      ·
        refine ⟨63102472998076873028265059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42068315332051248685510039 63102472998076873028265059)
        ·
          refine ⟨94653709497115309542397589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63102472998076873028265059 94653709497115309542397589)
          ·
            refine ⟨4436892632677280134799887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94653709497115309542397589 4436892632677280134799887)
            ·
              refine ⟨6655338949015920202199831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4436892632677280134799887 6655338949015920202199831)
              ·
                refine ⟨9983008423523880303299747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655338949015920202199831 9983008423523880303299747)
                ·
                  refine ⟨14974512635285820454949621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9983008423523880303299747 14974512635285820454949621)
                  ·
                    refine ⟨1403860559558045667651527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14974512635285820454949621 1403860559558045667651527)
                    ·
                      rfl

theorem cell22_4101013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_4101013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101013 prefixEnd_4101013 := by exact prefixLift 4101013
  have htrace : WordTrace (prefixWord ++ tailWord_4101013) baseStart_4101013 baseEnd_4101013 := by
    simpa [prefixWord, tailWord_4101013, baseEnd_4101013] using wordTrace_append hprefix tailTrace_4101013
  have hstable : (prefixWord ++ tailWord_4101013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101013).length < 2 ^ (prefixWord ++ tailWord_4101013).sum := by decide
  have hdescent : baseEnd_4101013 < baseStart_4101013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101060 : List Nat := [2, 3, 3, 3, 1, 1, 2, 7]
def baseStart_4101060 : Nat := 118140960795 + 4101060 * 2 ^ 59
def prefixEnd_4101060 : Nat := 4983230072969 + 3 ^ 40 * 4101060 * 2
def baseEnd_4101060 : Nat := 155986294290950356858487

theorem tailTrace_4101060 : CollatzResearch.WordTrace tailWord_4101060 prefixEnd_4101060 155986294290950356858487 := by
  unfold tailWord_4101060
  simp only [CollatzResearch.WordTrace]
  refine ⟨74788973261283750065498317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99718631015045000087331089 74788973261283750065498317)
  ·
    refine ⟨28045864972981406274561869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74788973261283750065498317 28045864972981406274561869)
    ·
      refine ⟨10517199364868027352960701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28045864972981406274561869 10517199364868027352960701)
      ·
        refine ⟨3943949761825510257360263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10517199364868027352960701 3943949761825510257360263)
        ·
          refine ⟨5915924642738265386040395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3943949761825510257360263 5915924642738265386040395)
          ·
            refine ⟨8873886964107398079060593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5915924642738265386040395 8873886964107398079060593)
            ·
              refine ⟨6655415223080548559295445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8873886964107398079060593 6655415223080548559295445)
              ·
                refine ⟨155986294290950356858487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6655415223080548559295445 155986294290950356858487)
                ·
                  rfl

theorem cell22_4101060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 7].length) (baseStart_4101060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101060 prefixEnd_4101060 := by exact prefixLift 4101060
  have htrace : WordTrace (prefixWord ++ tailWord_4101060) baseStart_4101060 baseEnd_4101060 := by
    simpa [prefixWord, tailWord_4101060, baseEnd_4101060] using wordTrace_append hprefix tailTrace_4101060
  have hstable : (prefixWord ++ tailWord_4101060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101060).length < 2 ^ (prefixWord ++ tailWord_4101060).sum := by decide
  have hdescent : baseEnd_4101060 < baseStart_4101060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101064 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 2, 3]
def baseStart_4101064 : Nat := 118140960795 + 4101064 * 2 ^ 59
def prefixEnd_4101064 : Nat := 4983230072969 + 3 ^ 40 * 4101064 * 2
def baseEnd_4101064 : Nat := 1403878017900298534626371

theorem tailTrace_4101064 : CollatzResearch.WordTrace tailWord_4101064 prefixEnd_4101064 1403878017900298534626371 := by
  unfold tailWord_4101064
  simp only [CollatzResearch.WordTrace]
  refine ⟨74789046207276504407071123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99718728276368672542761497 74789046207276504407071123)
  ·
    refine ⟨112183569310914756610606685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74789046207276504407071123 112183569310914756610606685)
    ·
      refine ⟨42068838491593033728977507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112183569310914756610606685 42068838491593033728977507)
      ·
        refine ⟨63103257737389550593466261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42068838491593033728977507 63103257737389550593466261)
        ·
          refine ⟨2957965206440135184068731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63103257737389550593466261 2957965206440135184068731)
          ·
            refine ⟨4436947809660202776103097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957965206440135184068731 4436947809660202776103097)
            ·
              refine ⟨3327710857245152082077323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4436947809660202776103097 3327710857245152082077323)
              ·
                refine ⟨4991566285867728123115985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327710857245152082077323 4991566285867728123115985)
                ·
                  refine ⟨3743674714400796092336989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4991566285867728123115985 3743674714400796092336989)
                  ·
                    refine ⟨1403878017900298534626371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3743674714400796092336989 1403878017900298534626371)
                    ·
                      rfl

theorem cell22_4101064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_4101064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101064 prefixEnd_4101064 := by exact prefixLift 4101064
  have htrace : WordTrace (prefixWord ++ tailWord_4101064) baseStart_4101064 baseEnd_4101064 := by
    simpa [prefixWord, tailWord_4101064, baseEnd_4101064] using wordTrace_append hprefix tailTrace_4101064
  have hstable : (prefixWord ++ tailWord_4101064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101064).length < 2 ^ (prefixWord ++ tailWord_4101064).sum := by decide
  have hdescent : baseEnd_4101064 < baseStart_4101064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101152 : List Nat := [2, 1, 1, 7, 1, 1, 1, 3, 1, 4]
def baseStart_4101152 : Nat := 118140960795 + 4101152 * 2 ^ 59
def prefixEnd_4101152 : Nat := 4983230072969 + 3 ^ 40 * 4101152 * 2
def baseEnd_4101152 : Nat := 1403908142098695638426101

theorem tailTrace_4101152 : CollatzResearch.WordTrace tailWord_4101152 prefixEnd_4101152 1403908142098695638426101 := by
  unfold tailWord_4101152
  simp only [CollatzResearch.WordTrace]
  refine ⟨74790651019117099921672855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99720868025489466562230473 74790651019117099921672855)
  ·
    refine ⟨112185976528675649882509283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74790651019117099921672855 112185976528675649882509283)
    ·
      refine ⟨168278964793013474823763925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112185976528675649882509283 168278964793013474823763925)
      ·
        refine ⟨3944038237336253316181967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 168278964793013474823763925 3944038237336253316181967)
        ·
          refine ⟨5916057356004379974272951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944038237336253316181967 5916057356004379974272951)
          ·
            refine ⟨8874086034006569961409427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916057356004379974272951 8874086034006569961409427)
            ·
              refine ⟨13311129051009854942114141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8874086034006569961409427 13311129051009854942114141)
              ·
                refine ⟨4991673394128695603292803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13311129051009854942114141 4991673394128695603292803)
                ·
                  refine ⟨7487510091193043404939205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4991673394128695603292803 7487510091193043404939205)
                  ·
                    refine ⟨1403908142098695638426101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7487510091193043404939205 1403908142098695638426101)
                    ·
                      rfl

theorem cell22_4101152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 1, 4].length) (baseStart_4101152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101152 prefixEnd_4101152 := by exact prefixLift 4101152
  have htrace : WordTrace (prefixWord ++ tailWord_4101152) baseStart_4101152 baseEnd_4101152 := by
    simpa [prefixWord, tailWord_4101152, baseEnd_4101152] using wordTrace_append hprefix tailTrace_4101152
  have hstable : (prefixWord ++ tailWord_4101152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101152).length < 2 ^ (prefixWord ++ tailWord_4101152).sum := by decide
  have hdescent : baseEnd_4101152 < baseStart_4101152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101182 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_4101182 : Nat := 118140960795 + 4101182 * 2 ^ 59
def prefixEnd_4101182 : Nat := 4983230072969 + 3 ^ 40 * 4101182 * 2
def baseEnd_4101182 : Nat := 1403918411711785560176009

theorem tailTrace_4101182 : CollatzResearch.WordTrace tailWord_4101182 prefixEnd_4101182 1403918411711785560176009 := by
  unfold tailWord_4101182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18697799528515689370867225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99721597485417009977958533 18697799528515689370867225)
  ·
    refine ⟨14023349646386767028150419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18697799528515689370867225 14023349646386767028150419)
    ·
      refine ⟨21035024469580150542225629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14023349646386767028150419 21035024469580150542225629)
      ·
        refine ⟨7888134176092556453334611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21035024469580150542225629 7888134176092556453334611)
        ·
          refine ⟨11832201264138834680001917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7888134176092556453334611 11832201264138834680001917)
          ·
            refine ⟨4437075474052063005000719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11832201264138834680001917 4437075474052063005000719)
            ·
              refine ⟨6655613211078094507501079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437075474052063005000719 6655613211078094507501079)
              ·
                refine ⟨9983419816617141761251619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6655613211078094507501079 9983419816617141761251619)
                ·
                  refine ⟨14975129724925712641877429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9983419816617141761251619 14975129724925712641877429)
                  ·
                    refine ⟨1403918411711785560176009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14975129724925712641877429 1403918411711785560176009)
                    ·
                      rfl

theorem cell22_4101182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_4101182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101182 prefixEnd_4101182 := by exact prefixLift 4101182
  have htrace : WordTrace (prefixWord ++ tailWord_4101182) baseStart_4101182 baseEnd_4101182 := by
    simpa [prefixWord, tailWord_4101182, baseEnd_4101182] using wordTrace_append hprefix tailTrace_4101182
  have hstable : (prefixWord ++ tailWord_4101182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101182).length < 2 ^ (prefixWord ++ tailWord_4101182).sum := by decide
  have hdescent : baseEnd_4101182 < baseStart_4101182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101193 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 5, 3]
def baseStart_4101193 : Nat := 118140960795 + 4101193 * 2 ^ 59
def prefixEnd_4101193 : Nat := 4983230072969 + 3 ^ 40 * 4101193 * 2
def baseEnd_4101193 : Nat := 1403922177236585198150975

theorem tailTrace_4101193 : CollatzResearch.WordTrace tailWord_4101193 prefixEnd_4101193 1403922177236585198150975 := by
  unfold tailWord_4101193
  simp only [CollatzResearch.WordTrace]
  refine ⟨149582797431085663845588233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99721864954057109230392155 149582797431085663845588233)
  ·
    refine ⟨112187098073314247884191175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149582797431085663845588233 112187098073314247884191175)
    ·
      refine ⟨168280647109971371826286763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112187098073314247884191175 168280647109971371826286763)
      ·
        refine ⟨252420970664957057739430145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168280647109971371826286763 252420970664957057739430145)
        ·
          refine ⟨189315727998717793304572609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252420970664957057739430145 189315727998717793304572609)
          ·
            refine ⟨141986795999038344978429457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189315727998717793304572609 141986795999038344978429457)
            ·
              refine ⟨106490096999278758733822093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141986795999038344978429457 106490096999278758733822093)
              ·
                refine ⟨39933786374729534525183285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106490096999278758733822093 39933786374729534525183285)
                ·
                  refine ⟨3743792472630893861735933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39933786374729534525183285 3743792472630893861735933)
                  ·
                    refine ⟨1403922177236585198150975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3743792472630893861735933 1403922177236585198150975)
                    ·
                      rfl

theorem cell22_4101193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 3].length) (baseStart_4101193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101193 prefixEnd_4101193 := by exact prefixLift 4101193
  have htrace : WordTrace (prefixWord ++ tailWord_4101193) baseStart_4101193 baseEnd_4101193 := by
    simpa [prefixWord, tailWord_4101193, baseEnd_4101193] using wordTrace_append hprefix tailTrace_4101193
  have hstable : (prefixWord ++ tailWord_4101193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101193).length < 2 ^ (prefixWord ++ tailWord_4101193).sum := by decide
  have hdescent : baseEnd_4101193 < baseStart_4101193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101214 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4101214 : Nat := 118140960795 + 4101214 * 2 ^ 59
def prefixEnd_4101214 : Nat := 4983230072969 + 3 ^ 40 * 4101214 * 2
def baseEnd_4101214 : Nat := 1403929365965748143375911

theorem tailTrace_4101214 : CollatzResearch.WordTrace tailWord_4101214 prefixEnd_4101214 1403929365965748143375911 := by
  unfold tailWord_4101214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18697945420501198054012837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99722375576006389621401797 18697945420501198054012837)
  ·
    refine ⟨3505864766343974635127407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18697945420501198054012837 3505864766343974635127407)
    ·
      refine ⟨5258797149515961952691111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3505864766343974635127407 5258797149515961952691111)
      ·
        refine ⟨7888195724273942929036667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5258797149515961952691111 7888195724273942929036667)
        ·
          refine ⟨11832293586410914393555001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7888195724273942929036667 11832293586410914393555001)
          ·
            refine ⟨8874220189808185795166251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11832293586410914393555001 8874220189808185795166251)
            ·
              refine ⟨13311330284712278692749377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8874220189808185795166251 13311330284712278692749377)
              ·
                refine ⟨9983497713534209019562033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13311330284712278692749377 9983497713534209019562033)
                ·
                  refine ⟨7487623285150656764671525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9983497713534209019562033 7487623285150656764671525)
                  ·
                    refine ⟨1403929365965748143375911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7487623285150656764671525 1403929365965748143375911)
                    ·
                      rfl

theorem cell22_4101214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4101214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101214 prefixEnd_4101214 := by exact prefixLift 4101214
  have htrace : WordTrace (prefixWord ++ tailWord_4101214) baseStart_4101214 baseEnd_4101214 := by
    simpa [prefixWord, tailWord_4101214, baseEnd_4101214] using wordTrace_append hprefix tailTrace_4101214
  have hstable : (prefixWord ++ tailWord_4101214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101214).length < 2 ^ (prefixWord ++ tailWord_4101214).sum := by decide
  have hdescent : baseEnd_4101214 < baseStart_4101214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101223 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 7]
def baseStart_4101223 : Nat := 118140960795 + 4101223 * 2 ^ 59
def prefixEnd_4101223 : Nat := 4983230072969 + 3 ^ 40 * 4101223 * 2
def baseEnd_4101223 : Nat := 467977482283225039966961

theorem tailTrace_4101223 : CollatzResearch.WordTrace tailWord_4101223 prefixEnd_4101223 467977482283225039966961 := by
  unfold tailWord_4101223
  simp only [CollatzResearch.WordTrace]
  refine ⟨149583891620976978969180323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99722594413984652646120215 149583891620976978969180323)
  ·
    refine ⟨224375837431465468453770485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149583891620976978969180323 224375837431465468453770485)
    ·
      refine ⟨21035234759199887667540983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224375837431465468453770485 21035234759199887667540983)
      ·
        refine ⟨31552852138799831501311475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21035234759199887667540983 31552852138799831501311475)
        ·
          refine ⟨47329278208199747251967213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31552852138799831501311475 47329278208199747251967213)
          ·
            refine ⟨17748479328074905219487705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47329278208199747251967213 17748479328074905219487705)
            ·
              refine ⟨13311359496056178914615779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17748479328074905219487705 13311359496056178914615779)
              ·
                refine ⟨19967039244084268371923669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13311359496056178914615779 19967039244084268371923669)
                ·
                  refine ⟨467977482283225039966961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19967039244084268371923669 467977482283225039966961)
                  ·
                    rfl

theorem cell22_4101223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 7].length) (baseStart_4101223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101223 prefixEnd_4101223 := by exact prefixLift 4101223
  have htrace : WordTrace (prefixWord ++ tailWord_4101223) baseStart_4101223 baseEnd_4101223 := by
    simpa [prefixWord, tailWord_4101223, baseEnd_4101223] using wordTrace_append hprefix tailTrace_4101223
  have hstable : (prefixWord ++ tailWord_4101223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101223).length < 2 ^ (prefixWord ++ tailWord_4101223).sum := by decide
  have hdescent : baseEnd_4101223 < baseStart_4101223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101240 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 5]
def baseStart_4101240 : Nat := 118140960795 + 4101240 * 2 ^ 59
def prefixEnd_4101240 : Nat := 4983230072969 + 3 ^ 40 * 4101240 * 2
def baseEnd_4101240 : Nat := 467979422099030914075277

theorem tailTrace_4101240 : CollatzResearch.WordTrace tailWord_4101240 prefixEnd_4101240 467979422099030914075277 := by
  unfold tailWord_4101240
  simp only [CollatzResearch.WordTrace]
  refine ⟨74792255830957695436274587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99723007774610260581699449 74792255830957695436274587)
  ·
    refine ⟨112188383746436543154411881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74792255830957695436274587 112188383746436543154411881)
    ·
      refine ⟨84141287809827407365808911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112188383746436543154411881 84141287809827407365808911)
      ·
        refine ⟨126211931714741111048713367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84141287809827407365808911 126211931714741111048713367)
        ·
          refine ⟨189317897572111666573070051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126211931714741111048713367 189317897572111666573070051)
          ·
            refine ⟨283976846358167499859605077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189317897572111666573070051 283976846358167499859605077)
            ·
              refine ⟨3327853668259775388979747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 283976846358167499859605077 3327853668259775388979747)
              ·
                refine ⟨4991780502389663083469621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327853668259775388979747 4991780502389663083469621)
                ·
                  refine ⟨467979422099030914075277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4991780502389663083469621 467979422099030914075277)
                  ·
                    rfl

theorem cell22_4101240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 5].length) (baseStart_4101240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101240 prefixEnd_4101240 := by exact prefixLift 4101240
  have htrace : WordTrace (prefixWord ++ tailWord_4101240) baseStart_4101240 baseEnd_4101240 := by
    simpa [prefixWord, tailWord_4101240, baseEnd_4101240] using wordTrace_append hprefix tailTrace_4101240
  have hstable : (prefixWord ++ tailWord_4101240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101240).length < 2 ^ (prefixWord ++ tailWord_4101240).sum := by decide
  have hdescent : baseEnd_4101240 < baseStart_4101240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101278 : List Nat := [4, 3, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_4101278 : Nat := 118140960795 + 4101278 * 2 ^ 59
def prefixEnd_4101278 : Nat := 4983230072969 + 3 ^ 40 * 4101278 * 2
def baseEnd_4101278 : Nat := 1403951274473673309775715

theorem tailTrace_4101278 : CollatzResearch.WordTrace tailWord_4101278 prefixEnd_4101278 1403951274473673309775715 := by
  unfold tailWord_4101278
  simp only [CollatzResearch.WordTrace]
  refine ⟨18698237204472215420304061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99723931757185148908288325 18698237204472215420304061)
  ·
    refine ⟨7011838951677080782614023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18698237204472215420304061 7011838951677080782614023)
    ·
      refine ⟨10517758427515621173921035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7011838951677080782614023 10517758427515621173921035)
      ·
        refine ⟨15776637641273431760881553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10517758427515621173921035 15776637641273431760881553)
        ·
          refine ⟨11832478230955073820661165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15776637641273431760881553 11832478230955073820661165)
          ·
            refine ⟨4437179336608152682747937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11832478230955073820661165 4437179336608152682747937)
            ·
              refine ⟨3327884502456114512060953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4437179336608152682747937 3327884502456114512060953)
              ·
                refine ⟨2495913376842085884045715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3327884502456114512060953 2495913376842085884045715)
                ·
                  refine ⟨3743870065263128826068573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495913376842085884045715 3743870065263128826068573)
                  ·
                    refine ⟨1403951274473673309775715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3743870065263128826068573 1403951274473673309775715)
                    ·
                      rfl

theorem cell22_4101278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_4101278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101278 prefixEnd_4101278 := by exact prefixLift 4101278
  have htrace : WordTrace (prefixWord ++ tailWord_4101278) baseStart_4101278 baseEnd_4101278 := by
    simpa [prefixWord, tailWord_4101278, baseEnd_4101278] using wordTrace_append hprefix tailTrace_4101278
  have hstable : (prefixWord ++ tailWord_4101278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101278).length < 2 ^ (prefixWord ++ tailWord_4101278).sum := by decide
  have hdescent : baseEnd_4101278 < baseStart_4101278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101343 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 1, 8]
def baseStart_4101343 : Nat := 118140960795 + 4101343 * 2 ^ 59
def prefixEnd_4101343 : Nat := 4983230072969 + 3 ^ 40 * 4101343 * 2
def baseEnd_4101343 : Nat := 1403973525302034806900515

theorem tailTrace_4101343 : CollatzResearch.WordTrace tailWord_4101343 prefixEnd_4101343 1403973525302034806900515 := by
  unfold tailWord_4101343
  simp only [CollatzResearch.WordTrace]
  refine ⟨149588268380542239463548683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99725512253694826309032455 149588268380542239463548683)
  ·
    refine ⟨224382402570813359195323025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149588268380542239463548683 224382402570813359195323025)
    ·
      refine ⟨168286801928110019396492269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224382402570813359195323025 168286801928110019396492269)
      ·
        refine ⟨63107550723041257273684601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168286801928110019396492269 63107550723041257273684601)
        ·
          refine ⟨47330663042280942955263451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63107550723041257273684601 47330663042280942955263451)
          ·
            refine ⟨70995994563421414432895177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47330663042280942955263451 70995994563421414432895177)
            ·
              refine ⟨53246995922566060824671383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70995994563421414432895177 53246995922566060824671383)
              ·
                refine ⟨79870493883849091237007075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53246995922566060824671383 79870493883849091237007075)
                ·
                  refine ⟨119805740825773636855510613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79870493883849091237007075 119805740825773636855510613)
                  ·
                    refine ⟨1403973525302034806900515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119805740825773636855510613 1403973525302034806900515)
                    ·
                      rfl

theorem cell22_4101343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_4101343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101343 prefixEnd_4101343 := by exact prefixLift 4101343
  have htrace : WordTrace (prefixWord ++ tailWord_4101343) baseStart_4101343 baseEnd_4101343 := by
    simpa [prefixWord, tailWord_4101343, baseEnd_4101343] using wordTrace_append hprefix tailTrace_4101343
  have hstable : (prefixWord ++ tailWord_4101343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101343).length < 2 ^ (prefixWord ++ tailWord_4101343).sum := by decide
  have hdescent : baseEnd_4101343 < baseStart_4101343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101351 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 2, 3]
def baseStart_4101351 : Nat := 118140960795 + 4101351 * 2 ^ 59
def prefixEnd_4101351 : Nat := 4983230072969 + 3 ^ 40 * 4101351 * 2
def baseEnd_4101351 : Nat := 1403976263865525452700491

theorem tailTrace_4101351 : CollatzResearch.WordTrace tailWord_4101351 prefixEnd_4101351 1403976263865525452700491 := by
  unfold tailWord_4101351
  simp only [CollatzResearch.WordTrace]
  refine ⟨149588560164513256829839907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99725706776342171219893271 149588560164513256829839907)
  ·
    refine ⟨224382840246769885244759861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149588560164513256829839907 224382840246769885244759861)
    ·
      refine ⟨21035891273134676741696237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224382840246769885244759861 21035891273134676741696237)
      ·
        refine ⟨7888459227425503778136089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21035891273134676741696237 7888459227425503778136089)
        ·
          refine ⟨5916344420569127833602067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7888459227425503778136089 5916344420569127833602067)
          ·
            refine ⟨8874516630853691750403101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5916344420569127833602067 8874516630853691750403101)
            ·
              refine ⟨3327943736570134406401163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8874516630853691750403101 3327943736570134406401163)
              ·
                refine ⟨4991915604855201609601745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3327943736570134406401163 4991915604855201609601745)
                ·
                  refine ⟨3743936703641401207201309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4991915604855201609601745 3743936703641401207201309)
                  ·
                    refine ⟨1403976263865525452700491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3743936703641401207201309 1403976263865525452700491)
                    ·
                      rfl

theorem cell22_4101351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_4101351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101351 prefixEnd_4101351 := by exact prefixLift 4101351
  have htrace : WordTrace (prefixWord ++ tailWord_4101351) baseStart_4101351 baseEnd_4101351 := by
    simpa [prefixWord, tailWord_4101351, baseEnd_4101351] using wordTrace_append hprefix tailTrace_4101351
  have hstable : (prefixWord ++ tailWord_4101351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101351).length < 2 ^ (prefixWord ++ tailWord_4101351).sum := by decide
  have hdescent : baseEnd_4101351 < baseStart_4101351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101379 : List Nat := [1, 1, 1, 3, 2, 4, 3, 3, 1, 3]
def baseStart_4101379 : Nat := 118140960795 + 4101379 * 2 ^ 59
def prefixEnd_4101379 : Nat := 4983230072969 + 3 ^ 40 * 4101379 * 2
def baseEnd_4101379 : Nat := 1403985848837742713000405

theorem tailTrace_4101379 : CollatzResearch.WordTrace tailWord_4101379 prefixEnd_4101379 1403985848837742713000405 := by
  unfold tailWord_4101379
  simp only [CollatzResearch.WordTrace]
  refine ⟨149589581408411817611859191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99726387605607878407906127 149589581408411817611859191)
  ·
    refine ⟨224384372112617726417788787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149589581408411817611859191 224384372112617726417788787)
    ·
      refine ⟨336576558168926589626683181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224384372112617726417788787 336576558168926589626683181)
      ·
        refine ⟨126216209313347471110006193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336576558168926589626683181 126216209313347471110006193)
        ·
          refine ⟨94662156985010603332504645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126216209313347471110006193 94662156985010603332504645)
          ·
            refine ⟨17749154434689488124844621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94662156985010603332504645 17749154434689488124844621)
            ·
              refine ⟨6655932913008558046816733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17749154434689488124844621 6655932913008558046816733)
              ·
                refine ⟨2495974842378209267556275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6655932913008558046816733 2495974842378209267556275)
                ·
                  refine ⟨3743962263567313901334413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2495974842378209267556275 3743962263567313901334413)
                  ·
                    refine ⟨1403985848837742713000405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3743962263567313901334413 1403985848837742713000405)
                    ·
                      rfl

theorem cell22_4101379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 1, 3].length) (baseStart_4101379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101379 prefixEnd_4101379 := by exact prefixLift 4101379
  have htrace : WordTrace (prefixWord ++ tailWord_4101379) baseStart_4101379 baseEnd_4101379 := by
    simpa [prefixWord, tailWord_4101379, baseEnd_4101379] using wordTrace_append hprefix tailTrace_4101379
  have hstable : (prefixWord ++ tailWord_4101379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101379).length < 2 ^ (prefixWord ++ tailWord_4101379).sum := by decide
  have hdescent : baseEnd_4101379 < baseStart_4101379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101439 : List Nat := [1, 1, 2, 2, 4, 3, 3, 1, 1, 4]
def baseStart_4101439 : Nat := 118140960795 + 4101439 * 2 ^ 59
def prefixEnd_4101439 : Nat := 4983230072969 + 3 ^ 40 * 4101439 * 2
def baseEnd_4101439 : Nat := 1404006388063922556500221

theorem tailTrace_4101439 : CollatzResearch.WordTrace tailWord_4101439 prefixEnd_4101439 1404006388063922556500221 := by
  unfold tailWord_4101439
  simp only [CollatzResearch.WordTrace]
  refine ⟨149591769788194447859043371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99727846525462965239362247 149591769788194447859043371)
  ·
    refine ⟨224387654682291671788565057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149591769788194447859043371 224387654682291671788565057)
    ·
      refine ⟨168290741011718753841423793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224387654682291671788565057 168290741011718753841423793)
      ·
        refine ⟨126218055758789065381067845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168290741011718753841423793 126218055758789065381067845)
        ·
          refine ⟨23665885454772949758950221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126218055758789065381067845 23665885454772949758950221)
          ·
            refine ⟨8874707045539856159606333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23665885454772949758950221 8874707045539856159606333)
            ·
              refine ⟨3328015142077446059852375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8874707045539856159606333 3328015142077446059852375)
              ·
                refine ⟨4992022713116169089778563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328015142077446059852375 4992022713116169089778563)
                ·
                  refine ⟨7488034069674253634667845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992022713116169089778563 7488034069674253634667845)
                  ·
                    refine ⟨1404006388063922556500221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7488034069674253634667845 1404006388063922556500221)
                    ·
                      rfl

theorem cell22_4101439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 1, 4].length) (baseStart_4101439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101439 prefixEnd_4101439 := by exact prefixLift 4101439
  have htrace : WordTrace (prefixWord ++ tailWord_4101439) baseStart_4101439 baseEnd_4101439 := by
    simpa [prefixWord, tailWord_4101439, baseEnd_4101439] using wordTrace_append hprefix tailTrace_4101439
  have hstable : (prefixWord ++ tailWord_4101439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101439).length < 2 ^ (prefixWord ++ tailWord_4101439).sum := by decide
  have hdescent : baseEnd_4101439 < baseStart_4101439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101465 : List Nat := [1, 2, 1, 2, 2, 2, 5, 7]
def baseStart_4101465 : Nat := 118140960795 + 4101465 * 2 ^ 59
def prefixEnd_4101465 : Nat := 4983230072969 + 3 ^ 40 * 4101465 * 2
def baseEnd_4101465 : Nat := 156001698710585239483349

theorem tailTrace_4101465 : CollatzResearch.WordTrace tailWord_4101465 prefixEnd_4101465 156001698710585239483349 := by
  unfold tailWord_4101465
  simp only [CollatzResearch.WordTrace]
  refine ⟨149592718086100254299489849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99728478724066836199659899 149592718086100254299489849)
  ·
    refine ⟨112194538564575190724617387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149592718086100254299489849 112194538564575190724617387)
    ·
      refine ⟨168291807846862786086926081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112194538564575190724617387 168291807846862786086926081)
      ·
        refine ⟨126218855885147089565194561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168291807846862786086926081 126218855885147089565194561)
        ·
          refine ⟨94664141913860317173895921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126218855885147089565194561 94664141913860317173895921)
          ·
            refine ⟨70998106435395237880421941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94664141913860317173895921 70998106435395237880421941)
            ·
              refine ⟨6656072478318303551289557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70998106435395237880421941 6656072478318303551289557)
              ·
                refine ⟨156001698710585239483349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6656072478318303551289557 156001698710585239483349)
                ·
                  rfl

theorem cell22_4101465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 7].length) (baseStart_4101465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101465 prefixEnd_4101465 := by exact prefixLift 4101465
  have htrace : WordTrace (prefixWord ++ tailWord_4101465) baseStart_4101465 baseEnd_4101465 := by
    simpa [prefixWord, tailWord_4101465, baseEnd_4101465] using wordTrace_append hprefix tailTrace_4101465
  have hstable : (prefixWord ++ tailWord_4101465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101465).length < 2 ^ (prefixWord ++ tailWord_4101465).sum := by decide
  have hdescent : baseEnd_4101465 < baseStart_4101465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101484 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 2, 4]
def baseStart_4101484 : Nat := 118140960795 + 4101484 * 2 ^ 59
def prefixEnd_4101484 : Nat := 4983230072969 + 3 ^ 40 * 4101484 * 2
def baseEnd_4101484 : Nat := 1404021792483557439125083

theorem tailTrace_4101484 : CollatzResearch.WordTrace tailWord_4101484 prefixEnd_4101484 1404021792483557439125083 := by
  unfold tailWord_4101484
  simp only [CollatzResearch.WordTrace]
  refine ⟨74796705536515710272215753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99728940715354280362954337 74796705536515710272215753)
  ·
    refine ⟨56097529152386782704161815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74796705536515710272215753 56097529152386782704161815)
    ·
      refine ⟨84146293728580174056242723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56097529152386782704161815 84146293728580174056242723)
      ·
        refine ⟨126219440592870261084364085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84146293728580174056242723 126219440592870261084364085)
        ·
          refine ⟨11833072555581586976659133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126219440592870261084364085 11833072555581586976659133)
          ·
            refine ⟨4437402208343095116247175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11833072555581586976659133 4437402208343095116247175)
            ·
              refine ⟨6656103312514642674370763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437402208343095116247175 6656103312514642674370763)
              ·
                refine ⟨9984154968771964011556145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6656103312514642674370763 9984154968771964011556145)
                ·
                  refine ⟨7488116226578973008667109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9984154968771964011556145 7488116226578973008667109)
                  ·
                    refine ⟨1404021792483557439125083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7488116226578973008667109 1404021792483557439125083)
                    ·
                      rfl

theorem cell22_4101484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_4101484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101484 prefixEnd_4101484 := by exact prefixLift 4101484
  have htrace : WordTrace (prefixWord ++ tailWord_4101484) baseStart_4101484 baseEnd_4101484 := by
    simpa [prefixWord, tailWord_4101484, baseEnd_4101484] using wordTrace_append hprefix tailTrace_4101484
  have hstable : (prefixWord ++ tailWord_4101484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101484).length < 2 ^ (prefixWord ++ tailWord_4101484).sum := by decide
  have hdescent : baseEnd_4101484 < baseStart_4101484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101555 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 8]
def baseStart_4101555 : Nat := 118140960795 + 4101555 * 2 ^ 59
def prefixEnd_4101555 : Nat := 4983230072969 + 3 ^ 40 * 4101555 * 2
def baseEnd_4101555 : Nat := 468015365744845640199955

theorem tailTrace_4101555 : CollatzResearch.WordTrace tailWord_4101555 prefixEnd_4101555 468015365744845640199955 := by
  unfold tailWord_4101555
  simp only [CollatzResearch.WordTrace]
  refine ⟨149596000655774199670266119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99730667103849466446844079 149596000655774199670266119)
  ·
    refine ⟨224394000983661299505399179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149596000655774199670266119 224394000983661299505399179)
    ·
      refine ⟨336591001475491949258098769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224394000983661299505399179 336591001475491949258098769)
      ·
        refine ⟨252443251106618961943574077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336591001475491949258098769 252443251106618961943574077)
        ·
          refine ⟨94666219164982110728840279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252443251106618961943574077 94666219164982110728840279)
          ·
            refine ⟨141999328747473166093260419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94666219164982110728840279 141999328747473166093260419)
            ·
              refine ⟨212998993121209749139890629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141999328747473166093260419 212998993121209749139890629)
              ·
                refine ⟨39937311210226827963729493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212998993121209749139890629 39937311210226827963729493)
                ·
                  refine ⟨468015365744845640199955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39937311210226827963729493 468015365744845640199955)
                  ·
                    rfl

theorem cell22_4101555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 8].length) (baseStart_4101555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101555 prefixEnd_4101555 := by exact prefixLift 4101555
  have htrace : WordTrace (prefixWord ++ tailWord_4101555) baseStart_4101555 baseEnd_4101555 := by
    simpa [prefixWord, tailWord_4101555, baseEnd_4101555] using wordTrace_append hprefix tailTrace_4101555
  have hstable : (prefixWord ++ tailWord_4101555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101555).length < 2 ^ (prefixWord ++ tailWord_4101555).sum := by decide
  have hdescent : baseEnd_4101555 < baseStart_4101555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101649 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 3, 3]
def baseStart_4101649 : Nat := 118140960795 + 4101649 * 2 ^ 59
def prefixEnd_4101649 : Nat := 4983230072969 + 3 ^ 40 * 4101649 * 2
def baseEnd_4101649 : Nat := 1404078275355552008749577

theorem tailTrace_4101649 : CollatzResearch.WordTrace tailWord_4101649 prefixEnd_4101649 1404078275355552008749577 := by
  unfold tailWord_4101649
  simp only [CollatzResearch.WordTrace]
  refine ⟨149599429117433653724188001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99732952744955769149458667 149599429117433653724188001)
  ·
    refine ⟨112199571838075240293141001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149599429117433653724188001 112199571838075240293141001)
    ·
      refine ⟨84149678878556430219855751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112199571838075240293141001 84149678878556430219855751)
      ·
        refine ⟨126224518317834645329783627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84149678878556430219855751 126224518317834645329783627)
        ·
          refine ⟨189336777476751967994675441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126224518317834645329783627 189336777476751967994675441)
          ·
            refine ⟨142002583107563975996006581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189336777476751967994675441 142002583107563975996006581)
            ·
              refine ⟨13312742166334122749625617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 142002583107563975996006581 13312742166334122749625617)
              ·
                refine ⟨9984556624750592062219213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13312742166334122749625617 9984556624750592062219213)
                ·
                  refine ⟨3744208734281472023332205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9984556624750592062219213 3744208734281472023332205)
                  ·
                    refine ⟨1404078275355552008749577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3744208734281472023332205 1404078275355552008749577)
                    ·
                      rfl

theorem cell22_4101649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_4101649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101649 prefixEnd_4101649 := by exact prefixLift 4101649
  have htrace : WordTrace (prefixWord ++ tailWord_4101649) baseStart_4101649 baseEnd_4101649 := by
    simpa [prefixWord, tailWord_4101649, baseEnd_4101649] using wordTrace_append hprefix tailTrace_4101649
  have hstable : (prefixWord ++ tailWord_4101649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101649).length < 2 ^ (prefixWord ++ tailWord_4101649).sum := by decide
  have hdescent : baseEnd_4101649 < baseStart_4101649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101790 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_4101790 : Nat := 118140960795 + 4101790 * 2 ^ 59
def prefixEnd_4101790 : Nat := 4983230072969 + 3 ^ 40 * 4101790 * 2
def baseEnd_4101790 : Nat := 1404126542537074640974145

theorem tailTrace_4101790 : CollatzResearch.WordTrace tailWord_4101790 prefixEnd_4101790 1404126542537074640974145 := by
  unfold tailWord_4101790
  simp only [CollatzResearch.WordTrace]
  refine ⟨18700571476240354350633853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99736381206615223203380549 18700571476240354350633853)
  ·
    refine ⟨7012714303590132881487695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18700571476240354350633853 7012714303590132881487695)
    ·
      refine ⟨10519071455385199322231543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7012714303590132881487695 10519071455385199322231543)
      ·
        refine ⟨15778607183077798983347315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10519071455385199322231543 15778607183077798983347315)
        ·
          refine ⟨23667910774616698475020973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15778607183077798983347315 23667910774616698475020973)
          ·
            refine ⟨8875466540481261928132865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23667910774616698475020973 8875466540481261928132865)
            ·
              refine ⟨6656599905360946446099649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8875466540481261928132865 6656599905360946446099649)
              ·
                refine ⟨4992449929020709834574737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6656599905360946446099649 4992449929020709834574737)
                ·
                  refine ⟨3744337446765532375931053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4992449929020709834574737 3744337446765532375931053)
                  ·
                    refine ⟨1404126542537074640974145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3744337446765532375931053 1404126542537074640974145)
                    ·
                      rfl

theorem cell22_4101790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_4101790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101790 prefixEnd_4101790 := by exact prefixLift 4101790
  have htrace : WordTrace (prefixWord ++ tailWord_4101790) baseStart_4101790 baseEnd_4101790 := by
    simpa [prefixWord, tailWord_4101790, baseEnd_4101790] using wordTrace_append hprefix tailTrace_4101790
  have hstable : (prefixWord ++ tailWord_4101790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101790).length < 2 ^ (prefixWord ++ tailWord_4101790).sum := by decide
  have hdescent : baseEnd_4101790 < baseStart_4101790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101878 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_4101878 : Nat := 118140960795 + 4101878 * 2 ^ 59
def prefixEnd_4101878 : Nat := 4983230072969 + 3 ^ 40 * 4101878 * 2
def baseEnd_4101878 : Nat := 1404156666735471744773875

theorem tailTrace_4101878 : CollatzResearch.WordTrace tailWord_4101878 prefixEnd_4101878 1404156666735471744773875 := by
  unfold tailWord_4101878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9350486339600251614642143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99738520955736017222849525 9350486339600251614642143)
  ·
    refine ⟨14025729509400377421963215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9350486339600251614642143 14025729509400377421963215)
    ·
      refine ⟨21038594264100566132944823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14025729509400377421963215 21038594264100566132944823)
      ·
        refine ⟨31557891396150849199417235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21038594264100566132944823 31557891396150849199417235)
        ·
          refine ⟨47336837094226273799125853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31557891396150849199417235 47336837094226273799125853)
          ·
            refine ⟨17751313910334852674672195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47336837094226273799125853 17751313910334852674672195)
            ·
              refine ⟨26626970865502279012008293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17751313910334852674672195 26626970865502279012008293)
              ·
                refine ⟨4992557037281677314751555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26626970865502279012008293 4992557037281677314751555)
                ·
                  refine ⟨7488835555922515972127333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4992557037281677314751555 7488835555922515972127333)
                  ·
                    refine ⟨1404156666735471744773875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7488835555922515972127333 1404156666735471744773875)
                    ·
                      rfl

theorem cell22_4101878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_4101878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101878 prefixEnd_4101878 := by exact prefixLift 4101878
  have htrace : WordTrace (prefixWord ++ tailWord_4101878) baseStart_4101878 baseEnd_4101878 := by
    simpa [prefixWord, tailWord_4101878, baseEnd_4101878] using wordTrace_append hprefix tailTrace_4101878
  have hstable : (prefixWord ++ tailWord_4101878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101878).length < 2 ^ (prefixWord ++ tailWord_4101878).sum := by decide
  have hdescent : baseEnd_4101878 < baseStart_4101878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101891 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 4, 3]
def baseStart_4101891 : Nat := 118140960795 + 4101891 * 2 ^ 59
def prefixEnd_4101891 : Nat := 4983230072969 + 3 ^ 40 * 4101891 * 2
def baseEnd_4101891 : Nat := 1404161116901144044198835

theorem tailTrace_4101891 : CollatzResearch.WordTrace tailWord_4101891 prefixEnd_4101891 1404161116901144044198835 := by
  unfold tailWord_4101891
  simp only [CollatzResearch.WordTrace]
  refine ⟨149608255582556929054497527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99738837055037952702998351 149608255582556929054497527)
  ·
    refine ⟨224412383373835393581746291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149608255582556929054497527 224412383373835393581746291)
    ·
      refine ⟨336618575060753090372619437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224412383373835393581746291 336618575060753090372619437)
      ·
        refine ⟨126231965647782408889732289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336618575060753090372619437 126231965647782408889732289)
        ·
          refine ⟨94673974235836806667299217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126231965647782408889732289 94673974235836806667299217)
          ·
            refine ⟨71005480676877605000474413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94673974235836806667299217 71005480676877605000474413)
            ·
              refine ⟨26627055253829101875177905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71005480676877605000474413 26627055253829101875177905)
              ·
                refine ⟨19970291440371826406383429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26627055253829101875177905 19970291440371826406383429)
                ·
                  refine ⟨3744429645069717451196893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19970291440371826406383429 3744429645069717451196893)
                  ·
                    refine ⟨1404161116901144044198835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3744429645069717451196893 1404161116901144044198835)
                    ·
                      rfl

theorem cell22_4101891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 4, 3].length) (baseStart_4101891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101891 prefixEnd_4101891 := by exact prefixLift 4101891
  have htrace : WordTrace (prefixWord ++ tailWord_4101891) baseStart_4101891 baseEnd_4101891 := by
    simpa [prefixWord, tailWord_4101891, baseEnd_4101891] using wordTrace_append hprefix tailTrace_4101891
  have hstable : (prefixWord ++ tailWord_4101891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101891).length < 2 ^ (prefixWord ++ tailWord_4101891).sum := by decide
  have hdescent : baseEnd_4101891 < baseStart_4101891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101921 : List Nat := [1, 2, 3, 2, 1, 4, 2, 7]
def baseStart_4101921 : Nat := 118140960795 + 4101921 * 2 ^ 59
def prefixEnd_4101921 : Nat := 4983230072969 + 3 ^ 40 * 4101921 * 2
def baseEnd_4101921 : Nat := 156019042946025996216527

theorem tailTrace_4101921 : CollatzResearch.WordTrace tailWord_4101921 prefixEnd_4101921 156019042946025996216527 := by
  unfold tailWord_4101921
  simp only [CollatzResearch.WordTrace]
  refine ⟨149609349772448244178089617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99739566514965496118726411 149609349772448244178089617)
  ·
    refine ⟨112207012329336183133567213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149609349772448244178089617 112207012329336183133567213)
    ·
      refine ⟨42077629623501068675087705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112207012329336183133567213 42077629623501068675087705)
      ·
        refine ⟨31558222217625801506315779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42077629623501068675087705 31558222217625801506315779)
        ·
          refine ⟨47337333326438702259473669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31558222217625801506315779 47337333326438702259473669)
          ·
            refine ⟨8875749998707256673651313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47337333326438702259473669 8875749998707256673651313)
            ·
              refine ⟨6656812499030442505238485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8875749998707256673651313 6656812499030442505238485)
              ·
                refine ⟨156019042946025996216527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6656812499030442505238485 156019042946025996216527)
                ·
                  rfl

theorem cell22_4101921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 7].length) (baseStart_4101921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101921 prefixEnd_4101921 := by exact prefixLift 4101921
  have htrace : WordTrace (prefixWord ++ tailWord_4101921) baseStart_4101921 baseEnd_4101921 := by
    simpa [prefixWord, tailWord_4101921, baseEnd_4101921] using wordTrace_append hprefix tailTrace_4101921
  have hstable : (prefixWord ++ tailWord_4101921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101921).length < 2 ^ (prefixWord ++ tailWord_4101921).sum := by decide
  have hdescent : baseEnd_4101921 < baseStart_4101921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101925 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 2, 3]
def baseStart_4101925 : Nat := 118140960795 + 4101925 * 2 ^ 59
def prefixEnd_4101925 : Nat := 4983230072969 + 3 ^ 40 * 4101925 * 2
def baseEnd_4101925 : Nat := 1404172755795979288848731

theorem tailTrace_4101925 : CollatzResearch.WordTrace tailWord_4101925 prefixEnd_4101925 1404172755795979288848731 := by
  unfold tailWord_4101925
  simp only [CollatzResearch.WordTrace]
  refine ⟨149609495664433752861235229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99739663776289168574156819 149609495664433752861235229)
  ·
    refine ⟨56103560874162657322963211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149609495664433752861235229 56103560874162657322963211)
    ·
      refine ⟨84155341311243985984444817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56103560874162657322963211 84155341311243985984444817)
      ·
        refine ⟨63116505983432989488333613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84155341311243985984444817 63116505983432989488333613)
        ·
          refine ⟨23668689743787371058125105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63116505983432989488333613 23668689743787371058125105)
          ·
            refine ⟨17751517307840528293593829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23668689743787371058125105 17751517307840528293593829)
            ·
              refine ⟨3328409495220099055048843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17751517307840528293593829 3328409495220099055048843)
              ·
                refine ⟨4992614242830148582573265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328409495220099055048843 4992614242830148582573265)
                ·
                  refine ⟨3744460682122611436929949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4992614242830148582573265 3744460682122611436929949)
                  ·
                    refine ⟨1404172755795979288848731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3744460682122611436929949 1404172755795979288848731)
                    ·
                      rfl

theorem cell22_4101925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_4101925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101925 prefixEnd_4101925 := by exact prefixLift 4101925
  have htrace : WordTrace (prefixWord ++ tailWord_4101925) baseStart_4101925 baseEnd_4101925 := by
    simpa [prefixWord, tailWord_4101925, baseEnd_4101925] using wordTrace_append hprefix tailTrace_4101925
  have hstable : (prefixWord ++ tailWord_4101925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101925).length < 2 ^ (prefixWord ++ tailWord_4101925).sum := by decide
  have hdescent : baseEnd_4101925 < baseStart_4101925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4101940 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4101940 : Nat := 118140960795 + 4101940 * 2 ^ 59
def prefixEnd_4101940 : Nat := 4983230072969 + 3 ^ 40 * 4101940 * 2
def baseEnd_4101940 : Nat := 1404177890602524249723685

theorem tailTrace_4101940 : CollatzResearch.WordTrace tailWord_4101940 prefixEnd_4101940 1404177890602524249723685 := by
  unfold tailWord_4101940
  simp only [CollatzResearch.WordTrace]
  refine ⟨74805021379689705211515637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99740028506252940282020849 74805021379689705211515637)
  ·
    refine ⟨7012970754345909863579591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74805021379689705211515637 7012970754345909863579591)
    ·
      refine ⟨10519456131518864795369387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7012970754345909863579591 10519456131518864795369387)
      ·
        refine ⟨15779184197278297193054081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10519456131518864795369387 15779184197278297193054081)
        ·
          refine ⟨11834388147958722894790561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15779184197278297193054081 11834388147958722894790561)
          ·
            refine ⟨8875791110969042171092921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11834388147958722894790561 8875791110969042171092921)
            ·
              refine ⟨6656843333226781628319691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8875791110969042171092921 6656843333226781628319691)
              ·
                refine ⟨9985264999840172442479537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6656843333226781628319691 9985264999840172442479537)
                ·
                  refine ⟨7488948749880129331859653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9985264999840172442479537 7488948749880129331859653)
                  ·
                    refine ⟨1404177890602524249723685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7488948749880129331859653 1404177890602524249723685)
                    ·
                      rfl

theorem cell22_4101940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4101940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4101940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4101940 prefixEnd_4101940 := by exact prefixLift 4101940
  have htrace : WordTrace (prefixWord ++ tailWord_4101940) baseStart_4101940 baseEnd_4101940 := by
    simpa [prefixWord, tailWord_4101940, baseEnd_4101940] using wordTrace_append hprefix tailTrace_4101940
  have hstable : (prefixWord ++ tailWord_4101940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4101940).length < 2 ^ (prefixWord ++ tailWord_4101940).sum := by decide
  have hdescent : baseEnd_4101940 < baseStart_4101940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4101940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102017 : List Nat := [1, 2, 4, 4, 1, 2, 1, 2, 5]
def baseStart_4102017 : Nat := 118140960795 + 4102017 * 2 ^ 59
def prefixEnd_4102017 : Nat := 4983230072969 + 3 ^ 40 * 4102017 * 2
def baseEnd_4102017 : Nat := 468068083092040571849483

theorem tailTrace_4102017 : CollatzResearch.WordTrace tailWord_4102017 prefixEnd_4102017 468068083092040571849483 := by
  unfold tailWord_4102017
  simp only [CollatzResearch.WordTrace]
  refine ⟨149612851180100452573584305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99741900786733635049056203 149612851180100452573584305)
  ·
    refine ⟨112209638385075339430188229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149612851180100452573584305 112209638385075339430188229)
    ·
      refine ⟨21039307197201626143160293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112209638385075339430188229 21039307197201626143160293)
      ·
        refine ⟨3944870099475304901842555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21039307197201626143160293 3944870099475304901842555)
        ·
          refine ⟨5917305149212957352763833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3944870099475304901842555 5917305149212957352763833)
          ·
            refine ⟨4437978861909718014572875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917305149212957352763833 4437978861909718014572875)
            ·
              refine ⟨6656968292864577021859313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4437978861909718014572875 6656968292864577021859313)
              ·
                refine ⟨4992726219648432766394485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6656968292864577021859313 4992726219648432766394485)
                ·
                  refine ⟨468068083092040571849483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4992726219648432766394485 468068083092040571849483)
                  ·
                    rfl

theorem cell22_4102017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 5].length) (baseStart_4102017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102017 prefixEnd_4102017 := by exact prefixLift 4102017
  have htrace : WordTrace (prefixWord ++ tailWord_4102017) baseStart_4102017 baseEnd_4102017 := by
    simpa [prefixWord, tailWord_4102017, baseEnd_4102017] using wordTrace_append hprefix tailTrace_4102017
  have hstable : (prefixWord ++ tailWord_4102017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102017).length < 2 ^ (prefixWord ++ tailWord_4102017).sum := by decide
  have hdescent : baseEnd_4102017 < baseStart_4102017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102041 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_4102041 : Nat := 118140960795 + 4102041 * 2 ^ 59
def prefixEnd_4102041 : Nat := 4983230072969 + 3 ^ 40 * 4102041 * 2
def baseEnd_4102041 : Nat := 1404212464966593652948375

theorem tailTrace_4102041 : CollatzResearch.WordTrace tailWord_4102041 prefixEnd_4102041 1404212464966593652948375 := by
  unfold tailWord_4102041
  simp only [CollatzResearch.WordTrace]
  refine ⟨149613726532013504672457977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99742484354675669781638651 149613726532013504672457977)
  ·
    refine ⟨112210294899010128504343483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149613726532013504672457977 112210294899010128504343483)
    ·
      refine ⟨168315442348515192756515225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112210294899010128504343483 168315442348515192756515225)
      ·
        refine ⟨126236581761386394567386419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168315442348515192756515225 126236581761386394567386419)
        ·
          refine ⟨189354872642079591851079629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126236581761386394567386419 189354872642079591851079629)
          ·
            refine ⟨71008077240779846944154861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189354872642079591851079629 71008077240779846944154861)
            ·
              refine ⟨26628028965292442604058073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71008077240779846944154861 26628028965292442604058073)
              ·
                refine ⟨19971021723969331953043555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26628028965292442604058073 19971021723969331953043555)
                ·
                  refine ⟨29956532585953997929565333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19971021723969331953043555 29956532585953997929565333)
                  ·
                    refine ⟨1404212464966593652948375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29956532585953997929565333 1404212464966593652948375)
                    ·
                      rfl

theorem cell22_4102041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_4102041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102041 prefixEnd_4102041 := by exact prefixLift 4102041
  have htrace : WordTrace (prefixWord ++ tailWord_4102041) baseStart_4102041 baseEnd_4102041 := by
    simpa [prefixWord, tailWord_4102041, baseEnd_4102041] using wordTrace_append hprefix tailTrace_4102041
  have hstable : (prefixWord ++ tailWord_4102041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102041).length < 2 ^ (prefixWord ++ tailWord_4102041).sum := by decide
  have hdescent : baseEnd_4102041 < baseStart_4102041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102122 : List Nat := [3, 1, 3, 1, 2, 1, 2, 5, 1, 3]
def baseStart_4102122 : Nat := 118140960795 + 4102122 * 2 ^ 59
def prefixEnd_4102122 : Nat := 4983230072969 + 3 ^ 40 * 4102122 * 2
def baseEnd_4102122 : Nat := 1404240192921936441673127

theorem tailTrace_4102122 : CollatzResearch.WordTrace tailWord_4102122 prefixEnd_4102122 1404240192921936441673127 := by
  unfold tailWord_4102122
  simp only [CollatzResearch.WordTrace]
  refine ⟨37404170211180013876539155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99744453896480037004104413 37404170211180013876539155)
  ·
    refine ⟨56106255316770020814808733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37404170211180013876539155 56106255316770020814808733)
    ·
      refine ⟨21039845743788757805553275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56106255316770020814808733 21039845743788757805553275)
      ·
        refine ⟨31559768615683136708329913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21039845743788757805553275 31559768615683136708329913)
        ·
          refine ⟨23669826461762352531247435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31559768615683136708329913 23669826461762352531247435)
          ·
            refine ⟨35504739692643528796871153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23669826461762352531247435 35504739692643528796871153)
            ·
              refine ⟨26628554769482646597653365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35504739692643528796871153 26628554769482646597653365)
              ·
                refine ⟨2496427009638998118530003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26628554769482646597653365 2496427009638998118530003)
                ·
                  refine ⟨3744640514458497177795005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496427009638998118530003 3744640514458497177795005)
                  ·
                    refine ⟨1404240192921936441673127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3744640514458497177795005 1404240192921936441673127)
                    ·
                      rfl

theorem cell22_4102122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_4102122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102122 prefixEnd_4102122 := by exact prefixLift 4102122
  have htrace : WordTrace (prefixWord ++ tailWord_4102122) baseStart_4102122 baseEnd_4102122 := by
    simpa [prefixWord, tailWord_4102122, baseEnd_4102122] using wordTrace_append hprefix tailTrace_4102122
  have hstable : (prefixWord ++ tailWord_4102122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102122).length < 2 ^ (prefixWord ++ tailWord_4102122).sum := by decide
  have hdescent : baseEnd_4102122 < baseStart_4102122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102242 : List Nat := [3, 3, 2, 2, 2, 2, 8]
def baseStart_4102242 : Nat := 118140960795 + 4102242 * 2 ^ 59
def prefixEnd_4102242 : Nat := 4983230072969 + 3 ^ 40 * 4102242 * 2
def baseEnd_4102242 : Nat := 52010417458307264024917

theorem tailTrace_4102242 : CollatzResearch.WordTrace tailWord_4102242 prefixEnd_4102242 52010417458307264024917 := by
  unfold tailWord_4102242
  simp only [CollatzResearch.WordTrace]
  refine ⟨37405264401071329000131245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99747371736190210667016653 37405264401071329000131245)
  ·
    refine ⟨14026974150401748375049217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37405264401071329000131245 14026974150401748375049217)
    ·
      refine ⟨10520230612801311281286913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14026974150401748375049217 10520230612801311281286913)
      ·
        refine ⟨7890172959600983460965185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10520230612801311281286913 7890172959600983460965185)
        ·
          refine ⟨5917629719700737595723889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7890172959600983460965185 5917629719700737595723889)
          ·
            refine ⟨4438222289775553196792917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917629719700737595723889 4438222289775553196792917)
            ·
              refine ⟨52010417458307264024917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4438222289775553196792917 52010417458307264024917)
              ·
                rfl

theorem cell22_4102242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 8].length) (baseStart_4102242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102242 prefixEnd_4102242 := by exact prefixLift 4102242
  have htrace : WordTrace (prefixWord ++ tailWord_4102242) baseStart_4102242 baseEnd_4102242 := by
    simpa [prefixWord, tailWord_4102242, baseEnd_4102242] using wordTrace_append hprefix tailTrace_4102242
  have hstable : (prefixWord ++ tailWord_4102242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102242).length < 2 ^ (prefixWord ++ tailWord_4102242).sum := by decide
  have hdescent : baseEnd_4102242 < baseStart_4102242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102308 : List Nat := [2, 3, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_4102308 : Nat := 118140960795 + 4102308 * 2 ^ 59
def prefixEnd_4102308 : Nat := 4983230072969 + 3 ^ 40 * 4102308 * 2
def baseEnd_4102308 : Nat := 1404303864523093956522557

theorem tailTrace_4102308 : CollatzResearch.WordTrace tailWord_4102308 prefixEnd_4102308 1404303864523093956522557 := by
  unfold tailWord_4102308
  simp only [CollatzResearch.WordTrace]
  refine ⟨74811732411023104636213789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99748976548030806181618385 74811732411023104636213789)
  ·
    refine ⟨28054399654133664238580171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74811732411023104636213789 28054399654133664238580171)
    ·
      refine ⟨42081599481200496357870257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28054399654133664238580171 42081599481200496357870257)
      ·
        refine ⟨31561199610900372268402693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42081599481200496357870257 31561199610900372268402693)
        ·
          refine ⟨5917724927043819800325505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31561199610900372268402693 5917724927043819800325505)
          ·
            refine ⟨4438293695282864850244129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917724927043819800325505 4438293695282864850244129)
            ·
              refine ⟨3328720271462148637683097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4438293695282864850244129 3328720271462148637683097)
              ·
                refine ⟨2496540203596611478262323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3328720271462148637683097 2496540203596611478262323)
                ·
                  refine ⟨3744810305394917217393485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496540203596611478262323 3744810305394917217393485)
                  ·
                    refine ⟨1404303864523093956522557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3744810305394917217393485 1404303864523093956522557)
                    ·
                      rfl

theorem cell22_4102308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_4102308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102308 prefixEnd_4102308 := by exact prefixLift 4102308
  have htrace : WordTrace (prefixWord ++ tailWord_4102308) baseStart_4102308 baseEnd_4102308 := by
    simpa [prefixWord, tailWord_4102308, baseEnd_4102308] using wordTrace_append hprefix tailTrace_4102308
  have hstable : (prefixWord ++ tailWord_4102308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102308).length < 2 ^ (prefixWord ++ tailWord_4102308).sum := by decide
  have hdescent : baseEnd_4102308 < baseStart_4102308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102313 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_4102313 : Nat := 118140960795 + 4102313 * 2 ^ 59
def prefixEnd_4102313 : Nat := 4983230072969 + 3 ^ 40 * 4102313 * 2
def baseEnd_4102313 : Nat := 1404305576125275610147541

theorem tailTrace_4102313 : CollatzResearch.WordTrace tailWord_4102313 prefixEnd_4102313 1404305576125275610147541 := by
  unfold tailWord_4102313
  simp only [CollatzResearch.WordTrace]
  refine ⟨149623647187028095126359593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99749098124685396750906395 149623647187028095126359593)
  ·
    refine ⟨112217735390271071344769695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149623647187028095126359593 112217735390271071344769695)
    ·
      refine ⟨168326603085406607017154543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112217735390271071344769695 168326603085406607017154543)
      ·
        refine ⟨252489904628109910525731815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168326603085406607017154543 252489904628109910525731815)
        ·
          refine ⟨378734856942164865788597723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252489904628109910525731815 378734856942164865788597723)
          ·
            refine ⟨568102285413247298682896585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378734856942164865788597723 568102285413247298682896585)
            ·
              refine ⟨426076714059935474012172439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568102285413247298682896585 426076714059935474012172439)
              ·
                refine ⟨639115071089903211018258659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426076714059935474012172439 639115071089903211018258659)
                ·
                  refine ⟨958672606634854816527387989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639115071089903211018258659 958672606634854816527387989)
                  ·
                    refine ⟨1404305576125275610147541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 958672606634854816527387989 1404305576125275610147541)
                    ·
                      rfl

theorem cell22_4102313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_4102313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102313 prefixEnd_4102313 := by exact prefixLift 4102313
  have htrace : WordTrace (prefixWord ++ tailWord_4102313) baseStart_4102313 baseEnd_4102313 := by
    simpa [prefixWord, tailWord_4102313, baseEnd_4102313] using wordTrace_append hprefix tailTrace_4102313
  have hstable : (prefixWord ++ tailWord_4102313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102313).length < 2 ^ (prefixWord ++ tailWord_4102313).sum := by decide
  have hdescent : baseEnd_4102313 < baseStart_4102313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102317 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_4102317 : Nat := 118140960795 + 4102317 * 2 ^ 59
def prefixEnd_4102317 : Nat := 4983230072969 + 3 ^ 40 * 4102317 * 2
def baseEnd_4102317 : Nat := 1404306945407020933047529

theorem tailTrace_4102317 : CollatzResearch.WordTrace tailWord_4102317 prefixEnd_4102317 1404306945407020933047529 := by
  unfold tailWord_4102317
  simp only [CollatzResearch.WordTrace]
  refine ⟨149623793079013603809505205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99749195386009069206336803 149623793079013603809505205)
  ·
    refine ⟨14027230601157525357141113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149623793079013603809505205 14027230601157525357141113)
    ·
      refine ⟨10520422950868144017855835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14027230601157525357141113 10520422950868144017855835)
      ·
        refine ⟨15780634426302216026783753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10520422950868144017855835 15780634426302216026783753)
        ·
          refine ⟨11835475819726662020087815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15780634426302216026783753 11835475819726662020087815)
          ·
            refine ⟨17753213729589993030131723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11835475819726662020087815 17753213729589993030131723)
            ·
              refine ⟨26629820594384989545197585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17753213729589993030131723 26629820594384989545197585)
              ·
                refine ⟨19972365445788742158898189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26629820594384989545197585 19972365445788742158898189)
                ·
                  refine ⟨7489637042170778309586821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19972365445788742158898189 7489637042170778309586821)
                  ·
                    refine ⟨1404306945407020933047529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7489637042170778309586821 1404306945407020933047529)
                    ·
                      rfl

theorem cell22_4102317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_4102317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102317 prefixEnd_4102317 := by exact prefixLift 4102317
  have htrace : WordTrace (prefixWord ++ tailWord_4102317) baseStart_4102317 baseEnd_4102317 := by
    simpa [prefixWord, tailWord_4102317, baseEnd_4102317] using wordTrace_append hprefix tailTrace_4102317
  have hstable : (prefixWord ++ tailWord_4102317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102317).length < 2 ^ (prefixWord ++ tailWord_4102317).sum := by decide
  have hdescent : baseEnd_4102317 < baseStart_4102317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102330 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_4102330 : Nat := 118140960795 + 4102330 * 2 ^ 59
def prefixEnd_4102330 : Nat := 4983230072969 + 3 ^ 40 * 4102330 * 2
def baseEnd_4102330 : Nat := 1404311395572693232472489

theorem tailTrace_4102330 : CollatzResearch.WordTrace tailWord_4102330 prefixEnd_4102330 1404311395572693232472489 := by
  unfold tailWord_4102330
  simp only [CollatzResearch.WordTrace]
  refine ⟨37406066806991626757432111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99749511485311004686485629 37406066806991626757432111)
  ·
    refine ⟨56109100210487440136148167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37406066806991626757432111 56109100210487440136148167)
    ·
      refine ⟨84163650315731160204222251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56109100210487440136148167 84163650315731160204222251)
      ·
        refine ⟨126245475473596740306333377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84163650315731160204222251 126245475473596740306333377)
        ·
          refine ⟨94684106605197555229750033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126245475473596740306333377 94684106605197555229750033)
          ·
            refine ⟨71013079953898166422312525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94684106605197555229750033 71013079953898166422312525)
            ·
              refine ⟨26629904982711812408367197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71013079953898166422312525 26629904982711812408367197)
              ·
                refine ⟨9986214368516929653137699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26629904982711812408367197 9986214368516929653137699)
                ·
                  refine ⟨14979321552775394479706549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9986214368516929653137699 14979321552775394479706549)
                  ·
                    refine ⟨1404311395572693232472489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14979321552775394479706549 1404311395572693232472489)
                    ·
                      rfl

theorem cell22_4102330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_4102330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102330 prefixEnd_4102330 := by exact prefixLift 4102330
  have htrace : WordTrace (prefixWord ++ tailWord_4102330) baseStart_4102330 baseEnd_4102330 := by
    simpa [prefixWord, tailWord_4102330, baseEnd_4102330] using wordTrace_append hprefix tailTrace_4102330
  have hstable : (prefixWord ++ tailWord_4102330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102330).length < 2 ^ (prefixWord ++ tailWord_4102330).sum := by decide
  have hdescent : baseEnd_4102330 < baseStart_4102330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102332 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 6]
def baseStart_4102332 : Nat := 118140960795 + 4102332 * 2 ^ 59
def prefixEnd_4102332 : Nat := 4983230072969 + 3 ^ 40 * 4102332 * 2
def baseEnd_4102332 : Nat := 468104026737855297974161

theorem tailTrace_4102332 : CollatzResearch.WordTrace tailWord_4102332 prefixEnd_4102332 468104026737855297974161 := by
  unfold tailWord_4102332
  simp only [CollatzResearch.WordTrace]
  refine ⟨74812170086979630685650625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99749560115972840914200833 74812170086979630685650625)
  ·
    refine ⟨56109127565234723014237969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74812170086979630685650625 56109127565234723014237969)
    ·
      refine ⟨42081845673926042260678477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56109127565234723014237969 42081845673926042260678477)
      ·
        refine ⟨15780692127722265847754429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42081845673926042260678477 15780692127722265847754429)
        ·
          refine ⟨5917759547895849692907911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15780692127722265847754429 5917759547895849692907911)
          ·
            refine ⟨8876639321843774539361867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5917759547895849692907911 8876639321843774539361867)
            ·
              refine ⟨13314958982765661809042801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8876639321843774539361867 13314958982765661809042801)
              ·
                refine ⟨9986219237074246356782101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13314958982765661809042801 9986219237074246356782101)
                ·
                  refine ⟨468104026737855297974161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9986219237074246356782101 468104026737855297974161)
                  ·
                    rfl

theorem cell22_4102332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_4102332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102332 prefixEnd_4102332 := by exact prefixLift 4102332
  have htrace : WordTrace (prefixWord ++ tailWord_4102332) baseStart_4102332 baseEnd_4102332 := by
    simpa [prefixWord, tailWord_4102332, baseEnd_4102332] using wordTrace_append hprefix tailTrace_4102332
  have hstable : (prefixWord ++ tailWord_4102332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102332).length < 2 ^ (prefixWord ++ tailWord_4102332).sum := by decide
  have hdescent : baseEnd_4102332 < baseStart_4102332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102345 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 2, 4]
def baseStart_4102345 : Nat := 118140960795 + 4102345 * 2 ^ 59
def prefixEnd_4102345 : Nat := 4983230072969 + 3 ^ 40 * 4102345 * 2
def baseEnd_4102345 : Nat := 1404316530379238193347443

theorem tailTrace_4102345 : CollatzResearch.WordTrace tailWord_4102345 prefixEnd_4102345 1404316530379238193347443 := by
  unfold tailWord_4102345
  simp only [CollatzResearch.WordTrace]
  refine ⟨149624814322912164591524489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99749876215274776394349659 149624814322912164591524489)
  ·
    refine ⟨112218610742184123443643367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149624814322912164591524489 112218610742184123443643367)
    ·
      refine ⟨168327916113276185165465051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112218610742184123443643367 168327916113276185165465051)
      ·
        refine ⟨252491874169914277748197577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168327916113276185165465051 252491874169914277748197577)
        ·
          refine ⟨189368905627435708311148183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252491874169914277748197577 189368905627435708311148183)
          ·
            refine ⟨284053358441153562466722275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189368905627435708311148183 284053358441153562466722275)
            ·
              refine ⟨426080037661730343700083413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284053358441153562466722275 426080037661730343700083413)
              ·
                refine ⟨9986250882696804930470705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 426080037661730343700083413 9986250882696804930470705)
                ·
                  refine ⟨7489688162022603697853029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9986250882696804930470705 7489688162022603697853029)
                  ·
                    refine ⟨1404316530379238193347443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7489688162022603697853029 1404316530379238193347443)
                    ·
                      rfl

theorem cell22_4102345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_4102345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102345 prefixEnd_4102345 := by exact prefixLift 4102345
  have htrace : WordTrace (prefixWord ++ tailWord_4102345) baseStart_4102345 baseEnd_4102345 := by
    simpa [prefixWord, tailWord_4102345, baseEnd_4102345] using wordTrace_append hprefix tailTrace_4102345
  have hstable : (prefixWord ++ tailWord_4102345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102345).length < 2 ^ (prefixWord ++ tailWord_4102345).sum := by decide
  have hdescent : baseEnd_4102345 < baseStart_4102345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102360 : List Nat := [2, 1, 2, 2, 4, 2, 9]
def baseStart_4102360 : Nat := 118140960795 + 4102360 * 2 ^ 59
def prefixEnd_4102360 : Nat := 4983230072969 + 3 ^ 40 * 4102360 * 2
def baseEnd_4102360 : Nat := 52011913525399376082311

theorem tailTrace_4102360 : CollatzResearch.WordTrace tailWord_4102360 prefixEnd_4102360 52011913525399376082311 := by
  unfold tailWord_4102360
  simp only [CollatzResearch.WordTrace]
  refine ⟨74812680708928911076660267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99750240945238548102213689 74812680708928911076660267)
  ·
    refine ⟨112219021063393366614990401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74812680708928911076660267 112219021063393366614990401)
    ·
      refine ⟨84164265797545024961242801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112219021063393366614990401 84164265797545024961242801)
      ·
        refine ⟨63123199348158768720932101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84164265797545024961242801 63123199348158768720932101)
        ·
          refine ⟨11835599877779769135174769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63123199348158768720932101 11835599877779769135174769)
          ·
            refine ⟨8876699908334826851381077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11835599877779769135174769 8876699908334826851381077)
            ·
              refine ⟨52011913525399376082311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8876699908334826851381077 52011913525399376082311)
              ·
                rfl

theorem cell22_4102360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 9].length) (baseStart_4102360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102360 prefixEnd_4102360 := by exact prefixLift 4102360
  have htrace : WordTrace (prefixWord ++ tailWord_4102360) baseStart_4102360 baseEnd_4102360 := by
    simpa [prefixWord, tailWord_4102360, baseEnd_4102360] using wordTrace_append hprefix tailTrace_4102360
  have hstable : (prefixWord ++ tailWord_4102360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102360).length < 2 ^ (prefixWord ++ tailWord_4102360).sum := by decide
  have hdescent : baseEnd_4102360 < baseStart_4102360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102381 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_4102381 : Nat := 118140960795 + 4102381 * 2 ^ 59
def prefixEnd_4102381 : Nat := 4983230072969 + 3 ^ 40 * 4102381 * 2
def baseEnd_4102381 : Nat := 1404328853914946099447333

theorem tailTrace_4102381 : CollatzResearch.WordTrace tailWord_4102381 prefixEnd_4102381 1404328853914946099447333 := by
  unfold tailWord_4102381
  simp only [CollatzResearch.WordTrace]
  refine ⟨149626127350781742739834997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99750751567187828493223331 149626127350781742739834997)
  ·
    refine ⟨14027449439135788381859531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149626127350781742739834997 14027449439135788381859531)
    ·
      refine ⟨21041174158703682572789297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14027449439135788381859531 21041174158703682572789297)
      ·
        refine ⟨15780880619027761929591973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21041174158703682572789297 15780880619027761929591973)
        ·
          refine ⟨2958915116067705361798495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15780880619027761929591973 2958915116067705361798495)
          ·
            refine ⟨4438372674101558042697743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2958915116067705361798495 4438372674101558042697743)
            ·
              refine ⟨6657559011152337064046615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438372674101558042697743 6657559011152337064046615)
              ·
                refine ⟨9986338516728505596069923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657559011152337064046615 9986338516728505596069923)
                ·
                  refine ⟨14979507775092758394104885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9986338516728505596069923 14979507775092758394104885)
                  ·
                    refine ⟨1404328853914946099447333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14979507775092758394104885 1404328853914946099447333)
                    ·
                      rfl

theorem cell22_4102381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_4102381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102381 prefixEnd_4102381 := by exact prefixLift 4102381
  have htrace : WordTrace (prefixWord ++ tailWord_4102381) baseStart_4102381 baseEnd_4102381 := by
    simpa [prefixWord, tailWord_4102381, baseEnd_4102381] using wordTrace_append hprefix tailTrace_4102381
  have hstable : (prefixWord ++ tailWord_4102381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102381).length < 2 ^ (prefixWord ++ tailWord_4102381).sum := by decide
  have hdescent : baseEnd_4102381 < baseStart_4102381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102426 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 3, 3]
def baseStart_4102426 : Nat := 118140960795 + 4102426 * 2 ^ 59
def prefixEnd_4102426 : Nat := 4983230072969 + 3 ^ 40 * 4102426 * 2
def baseEnd_4102426 : Nat := 1404344258334580982072195

theorem tailTrace_4102426 : CollatzResearch.WordTrace tailWord_4102426 prefixEnd_4102426 1404344258334580982072195 := by
  unfold tailWord_4102426
  simp only [CollatzResearch.WordTrace]
  refine ⟨37406942158904678856305783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99751845757079143616815421 37406942158904678856305783)
  ·
    refine ⟨56110413238357018284458675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37406942158904678856305783 56110413238357018284458675)
    ·
      refine ⟨84165619857535527426688013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56110413238357018284458675 84165619857535527426688013)
      ·
        refine ⟨31562107446575822785008005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84165619857535527426688013 31562107446575822785008005)
        ·
          refine ⟨5917895146232966772189001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31562107446575822785008005 5917895146232966772189001)
          ·
            refine ⟨4438421359674725079141751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5917895146232966772189001 4438421359674725079141751)
            ·
              refine ⟨6657632039512087618712627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438421359674725079141751 6657632039512087618712627)
              ·
                refine ⟨9986448059268131428068941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657632039512087618712627 9986448059268131428068941)
                ·
                  refine ⟨3744918022225549285525853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9986448059268131428068941 3744918022225549285525853)
                  ·
                    refine ⟨1404344258334580982072195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3744918022225549285525853 1404344258334580982072195)
                    ·
                      rfl

theorem cell22_4102426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_4102426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102426 prefixEnd_4102426 := by exact prefixLift 4102426
  have htrace : WordTrace (prefixWord ++ tailWord_4102426) baseStart_4102426 baseEnd_4102426 := by
    simpa [prefixWord, tailWord_4102426, baseEnd_4102426] using wordTrace_append hprefix tailTrace_4102426
  have hstable : (prefixWord ++ tailWord_4102426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102426).length < 2 ^ (prefixWord ++ tailWord_4102426).sum := by decide
  have hdescent : baseEnd_4102426 < baseStart_4102426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102499 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 2, 3]
def baseStart_4102499 : Nat := 118140960795 + 4102499 * 2 ^ 59
def prefixEnd_4102499 : Nat := 4983230072969 + 3 ^ 40 * 4102499 * 2
def baseEnd_4102499 : Nat := 1404369247726433124996971

theorem tailTrace_4102499 : CollatzResearch.WordTrace tailWord_4102499 prefixEnd_4102499 1404369247726433124996971 := by
  unfold tailWord_4102499
  simp only [CollatzResearch.WordTrace]
  refine ⟨149630431164354248892630551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99753620776236165928420367 149630431164354248892630551)
  ·
    refine ⟨224445646746531373338945827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149630431164354248892630551 224445646746531373338945827)
    ·
      refine ⟨336668470119797060008418741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224445646746531373338945827 336668470119797060008418741)
      ·
        refine ⟨31562669073730974375789257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 336668470119797060008418741 31562669073730974375789257)
        ·
          refine ⟨23672001805298230781841943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31562669073730974375789257 23672001805298230781841943)
          ·
            refine ⟨35508002707947346172762915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23672001805298230781841943 35508002707947346172762915)
            ·
              refine ⟨53262004061921019259144373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35508002707947346172762915 53262004061921019259144373)
              ·
                refine ⟨4993312880805095555544785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53262004061921019259144373 4993312880805095555544785)
                ·
                  refine ⟨3744984660603821666658589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4993312880805095555544785 3744984660603821666658589)
                  ·
                    refine ⟨1404369247726433124996971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3744984660603821666658589 1404369247726433124996971)
                    ·
                      rfl

theorem cell22_4102499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 2, 3].length) (baseStart_4102499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102499 prefixEnd_4102499 := by exact prefixLift 4102499
  have htrace : WordTrace (prefixWord ++ tailWord_4102499) baseStart_4102499 baseEnd_4102499 := by
    simpa [prefixWord, tailWord_4102499, baseEnd_4102499] using wordTrace_append hprefix tailTrace_4102499
  have hstable : (prefixWord ++ tailWord_4102499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102499).length < 2 ^ (prefixWord ++ tailWord_4102499).sum := by decide
  have hdescent : baseEnd_4102499 < baseStart_4102499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102514 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_4102514 : Nat := 118140960795 + 4102514 * 2 ^ 59
def prefixEnd_4102514 : Nat := 4983230072969 + 3 ^ 40 * 4102514 * 2
def baseEnd_4102514 : Nat := 1404374382532978085871925

theorem tailTrace_4102514 : CollatzResearch.WordTrace tailWord_4102514 prefixEnd_4102514 1404374382532978085871925 := by
  unfold tailWord_4102514
  simp only [CollatzResearch.WordTrace]
  refine ⟨37407744564824976613606649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99753985506199937636284397 37407744564824976613606649)
  ·
    refine ⟨28055808423618732460204987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37407744564824976613606649 28055808423618732460204987)
    ·
      refine ⟨42083712635428098690307481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28055808423618732460204987 42083712635428098690307481)
      ·
        refine ⟨31562784476571074017730611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42083712635428098690307481 31562784476571074017730611)
        ·
          refine ⟨47344176714856611026595917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31562784476571074017730611 47344176714856611026595917)
          ·
            refine ⟨17754066268071229134973469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47344176714856611026595917 17754066268071229134973469)
            ·
              refine ⟨6657774850526710925615051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17754066268071229134973469 6657774850526710925615051)
              ·
                refine ⟨9986662275790066388422577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6657774850526710925615051 9986662275790066388422577)
                ·
                  refine ⟨7489996706842549791316933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9986662275790066388422577 7489996706842549791316933)
                  ·
                    refine ⟨1404374382532978085871925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7489996706842549791316933 1404374382532978085871925)
                    ·
                      rfl

theorem cell22_4102514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_4102514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102514 prefixEnd_4102514 := by exact prefixLift 4102514
  have htrace : WordTrace (prefixWord ++ tailWord_4102514) baseStart_4102514 baseEnd_4102514 := by
    simpa [prefixWord, tailWord_4102514, baseEnd_4102514] using wordTrace_append hprefix tailTrace_4102514
  have hstable : (prefixWord ++ tailWord_4102514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102514).length < 2 ^ (prefixWord ++ tailWord_4102514).sum := by decide
  have hdescent : baseEnd_4102514 < baseStart_4102514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102634 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_4102634 : Nat := 118140960795 + 4102634 * 2 ^ 59
def prefixEnd_4102634 : Nat := 4983230072969 + 3 ^ 40 * 4102634 * 2
def baseEnd_4102634 : Nat := 1404415460985337772871557

theorem tailTrace_4102634 : CollatzResearch.WordTrace tailWord_4102634 prefixEnd_4102634 1404415460985337772871557 := by
  unfold tailWord_4102634
  simp only [CollatzResearch.WordTrace]
  refine ⟨37408838754716291737198739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99756903345910111299196637 37408838754716291737198739)
  ·
    refine ⟨56113258132074437605798109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37408838754716291737198739 56113258132074437605798109)
    ·
      refine ⟨21042471799527914102174291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56113258132074437605798109 21042471799527914102174291)
      ·
        refine ⟨31563707699291871153261437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21042471799527914102174291 31563707699291871153261437)
        ·
          refine ⟨11836390387234451682473039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31563707699291871153261437 11836390387234451682473039)
          ·
            refine ⟨17754585580851677523709559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11836390387234451682473039 17754585580851677523709559)
            ·
              refine ⟨26631878371277516285564339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17754585580851677523709559 26631878371277516285564339)
              ·
                refine ⟨39947817556916274428346509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26631878371277516285564339 39947817556916274428346509)
                ·
                  refine ⟨14980431583843602910629941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39947817556916274428346509 14980431583843602910629941)
                  ·
                    refine ⟨1404415460985337772871557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14980431583843602910629941 1404415460985337772871557)
                    ·
                      rfl

theorem cell22_4102634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_4102634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102634 prefixEnd_4102634 := by exact prefixLift 4102634
  have htrace : WordTrace (prefixWord ++ tailWord_4102634) baseStart_4102634 baseEnd_4102634 := by
    simpa [prefixWord, tailWord_4102634, baseEnd_4102634] using wordTrace_append hprefix tailTrace_4102634
  have hstable : (prefixWord ++ tailWord_4102634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102634).length < 2 ^ (prefixWord ++ tailWord_4102634).sum := by decide
  have hdescent : baseEnd_4102634 < baseStart_4102634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102638 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_4102638 : Nat := 118140960795 + 4102638 * 2 ^ 59
def prefixEnd_4102638 : Nat := 4983230072969 + 3 ^ 40 * 4102638 * 2
def baseEnd_4102638 : Nat := 1404416830267083095771545

theorem tailTrace_4102638 : CollatzResearch.WordTrace tailWord_4102638 prefixEnd_4102638 1404416830267083095771545 := by
  unfold tailWord_4102638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18704437613856334453992571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99757000607233783754627045 18704437613856334453992571)
  ·
    refine ⟨28056656420784501680988857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18704437613856334453992571 28056656420784501680988857)
    ·
      refine ⟨21042492315588376260741643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28056656420784501680988857 21042492315588376260741643)
      ·
        refine ⟨31563738473382564391112465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21042492315588376260741643 31563738473382564391112465)
        ·
          refine ⟨23672803855036923293334349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31563738473382564391112465 23672803855036923293334349)
          ·
            refine ⟨8877301445638846235000381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23672803855036923293334349 8877301445638846235000381)
            ·
              refine ⟨3328988042114567338125143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8877301445638846235000381 3328988042114567338125143)
              ·
                refine ⟨4993482063171851007187715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3328988042114567338125143 4993482063171851007187715)
                ·
                  refine ⟨7490223094757776510781573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993482063171851007187715 7490223094757776510781573)
                  ·
                    refine ⟨1404416830267083095771545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7490223094757776510781573 1404416830267083095771545)
                    ·
                      rfl

theorem cell22_4102638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_4102638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102638 prefixEnd_4102638 := by exact prefixLift 4102638
  have htrace : WordTrace (prefixWord ++ tailWord_4102638) baseStart_4102638 baseEnd_4102638 := by
    simpa [prefixWord, tailWord_4102638, baseEnd_4102638] using wordTrace_append hprefix tailTrace_4102638
  have hstable : (prefixWord ++ tailWord_4102638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102638).length < 2 ^ (prefixWord ++ tailWord_4102638).sum := by decide
  have hdescent : baseEnd_4102638 < baseStart_4102638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102649 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 2, 4]
def baseStart_4102649 : Nat := 118140960795 + 4102649 * 2 ^ 59
def prefixEnd_4102649 : Nat := 4983230072969 + 3 ^ 40 * 4102649 * 2
def baseEnd_4102649 : Nat := 1404420595791882733746511

theorem tailTrace_4102649 : CollatzResearch.WordTrace tailWord_4102649 prefixEnd_4102649 1404420595791882733746511 := by
  unfold tailWord_4102649
  simp only [CollatzResearch.WordTrace]
  refine ⟨149635902113810824510591001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99757268075873883007060667 149635902113810824510591001)
  ·
    refine ⟨112226926585358118382943251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149635902113810824510591001 112226926585358118382943251)
    ·
      refine ⟨168340389878037177574414877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112226926585358118382943251 168340389878037177574414877)
      ·
        refine ⟨63127646204263941590405579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168340389878037177574414877 63127646204263941590405579)
        ·
          refine ⟨94691469306395912385608369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63127646204263941590405579 94691469306395912385608369)
          ·
            refine ⟨71018601979796934289206277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94691469306395912385608369 71018601979796934289206277)
            ·
              refine ⟨13315987871211925179226177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71018601979796934289206277 13315987871211925179226177)
              ·
                refine ⟨9986990903408943884419633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13315987871211925179226177 9986990903408943884419633)
                ·
                  refine ⟨7490243177556707913314725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9986990903408943884419633 7490243177556707913314725)
                  ·
                    refine ⟨1404420595791882733746511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7490243177556707913314725 1404420595791882733746511)
                    ·
                      rfl

theorem cell22_4102649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_4102649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102649 prefixEnd_4102649 := by exact prefixLift 4102649
  have htrace : WordTrace (prefixWord ++ tailWord_4102649) baseStart_4102649 baseEnd_4102649 := by
    simpa [prefixWord, tailWord_4102649, baseEnd_4102649] using wordTrace_append hprefix tailTrace_4102649
  have hstable : (prefixWord ++ tailWord_4102649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102649).length < 2 ^ (prefixWord ++ tailWord_4102649).sum := by decide
  have hdescent : baseEnd_4102649 < baseStart_4102649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102702 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_4102702 : Nat := 118140960795 + 4102702 * 2 ^ 59
def prefixEnd_4102702 : Nat := 4983230072969 + 3 ^ 40 * 4102702 * 2
def baseEnd_4102702 : Nat := 1404438738775008262171349

theorem tailTrace_4102702 : CollatzResearch.WordTrace tailWord_4102702 prefixEnd_4102702 1404438738775008262171349 := by
  unfold tailWord_4102702
  simp only [CollatzResearch.WordTrace]
  refine ⟨18704729397827351820283795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99758556788412543041513573 18704729397827351820283795)
  ·
    refine ⟨28057094096741027730425693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18704729397827351820283795 28057094096741027730425693)
    ·
      refine ⟨10521410286277885398909635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28057094096741027730425693 10521410286277885398909635)
      ·
        refine ⟨15782115429416828098364453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10521410286277885398909635 15782115429416828098364453)
        ·
          refine ⟨2959146643015655268443335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15782115429416828098364453 2959146643015655268443335)
          ·
            refine ⟨4438719964523482902665003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959146643015655268443335 4438719964523482902665003)
            ·
              refine ⟨6658079946785224353997505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4438719964523482902665003 6658079946785224353997505)
              ·
                refine ⟨4993559960088918265498129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658079946785224353997505 4993559960088918265498129)
                ·
                  refine ⟨3745169970066688699123597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4993559960088918265498129 3745169970066688699123597)
                  ·
                    refine ⟨1404438738775008262171349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745169970066688699123597 1404438738775008262171349)
                    ·
                      rfl

theorem cell22_4102702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_4102702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102702 prefixEnd_4102702 := by exact prefixLift 4102702
  have htrace : WordTrace (prefixWord ++ tailWord_4102702) baseStart_4102702 baseEnd_4102702 := by
    simpa [prefixWord, tailWord_4102702, baseEnd_4102702] using wordTrace_append hprefix tailTrace_4102702
  have hstable : (prefixWord ++ tailWord_4102702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102702).length < 2 ^ (prefixWord ++ tailWord_4102702).sum := by decide
  have hdescent : baseEnd_4102702 < baseStart_4102702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102709 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 7]
def baseStart_4102709 : Nat := 118140960795 + 4102709 * 2 ^ 59
def prefixEnd_4102709 : Nat := 4983230072969 + 3 ^ 40 * 4102709 * 2
def baseEnd_4102709 : Nat := 468147045006020859082109

theorem tailTrace_4102709 : CollatzResearch.WordTrace tailWord_4102709 prefixEnd_4102709 468147045006020859082109 := by
  unfold tailWord_4102709
  simp only [CollatzResearch.WordTrace]
  refine ⟨149638090493593454757775181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99758726995728969838516787 149638090493593454757775181)
  ·
    refine ⟨56114283935097545534165693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149638090493593454757775181 56114283935097545534165693)
    ·
      refine ⟨21042856475661579575312135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56114283935097545534165693 21042856475661579575312135)
      ·
        refine ⟨31564284713492369362968203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21042856475661579575312135 31564284713492369362968203)
        ·
          refine ⟨47346427070238554044452305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31564284713492369362968203 47346427070238554044452305)
          ·
            refine ⟨35509820302678915533339229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47346427070238554044452305 35509820302678915533339229)
            ·
              refine ⟨13316182613504593325002211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35509820302678915533339229 13316182613504593325002211)
              ·
                refine ⟨19974273920256889987503317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13316182613504593325002211 19974273920256889987503317)
                ·
                  refine ⟨468147045006020859082109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19974273920256889987503317 468147045006020859082109)
                  ·
                    rfl

theorem cell22_4102709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_4102709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102709 prefixEnd_4102709 := by exact prefixLift 4102709
  have htrace : WordTrace (prefixWord ++ tailWord_4102709) baseStart_4102709 baseEnd_4102709 := by
    simpa [prefixWord, tailWord_4102709, baseEnd_4102709] using wordTrace_append hprefix tailTrace_4102709
  have hstable : (prefixWord ++ tailWord_4102709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102709).length < 2 ^ (prefixWord ++ tailWord_4102709).sum := by decide
  have hdescent : baseEnd_4102709 < baseStart_4102709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102713 : List Nat := [1, 2, 1, 5, 1, 1, 1, 6, 1, 3]
def baseStart_4102713 : Nat := 118140960795 + 4102713 * 2 ^ 59
def prefixEnd_4102713 : Nat := 4983230072969 + 3 ^ 40 * 4102713 * 2
def baseEnd_4102713 : Nat := 1404442504299807900146315

theorem tailTrace_4102713 : CollatzResearch.WordTrace tailWord_4102713 prefixEnd_4102713 1404442504299807900146315 := by
  unfold tailWord_4102713
  simp only [CollatzResearch.WordTrace]
  refine ⟨149638236385578963440920793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99758824257052642293947195 149638236385578963440920793)
  ·
    refine ⟨112228677289184222580690595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149638236385578963440920793 112228677289184222580690595)
    ·
      refine ⟨168343015933776333871035893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112228677289184222580690595 168343015933776333871035893)
      ·
        refine ⟨15782157743791531300409615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 168343015933776333871035893 15782157743791531300409615)
        ·
          refine ⟨23673236615687296950614423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15782157743791531300409615 23673236615687296950614423)
          ·
            refine ⟨35509854923530945425921635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23673236615687296950614423 35509854923530945425921635)
            ·
              refine ⟨53264782385296418138882453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35509854923530945425921635 53264782385296418138882453)
              ·
                refine ⟨2496786674310769600260115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53264782385296418138882453 2496786674310769600260115)
                ·
                  refine ⟨3745180011466154400390173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496786674310769600260115 3745180011466154400390173)
                  ·
                    refine ⟨1404442504299807900146315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745180011466154400390173 1404442504299807900146315)
                    ·
                      rfl

theorem cell22_4102713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 1, 3].length) (baseStart_4102713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102713 prefixEnd_4102713 := by exact prefixLift 4102713
  have htrace : WordTrace (prefixWord ++ tailWord_4102713) baseStart_4102713 baseEnd_4102713 := by
    simpa [prefixWord, tailWord_4102713, baseEnd_4102713] using wordTrace_append hprefix tailTrace_4102713
  have hstable : (prefixWord ++ tailWord_4102713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102713).length < 2 ^ (prefixWord ++ tailWord_4102713).sum := by decide
  have hdescent : baseEnd_4102713 < baseStart_4102713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102756 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_4102756 : Nat := 118140960795 + 4102756 * 2 ^ 59
def prefixEnd_4102756 : Nat := 4983230072969 + 3 ^ 40 * 4102756 * 2
def baseEnd_4102756 : Nat := 1404457224078570121321183

theorem tailTrace_4102756 : CollatzResearch.WordTrace tailWord_4102756 prefixEnd_4102756 1404457224078570121321183 := by
  unfold tailWord_4102756
  simp only [CollatzResearch.WordTrace]
  refine ⟨74819902362211590892368061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99759869816282121189824081 74819902362211590892368061)
  ·
    refine ⟨28057463385829346584638023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74819902362211590892368061 28057463385829346584638023)
    ·
      refine ⟨42086195078744019876957035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28057463385829346584638023 42086195078744019876957035)
      ·
        refine ⟨63129292618116029815435553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42086195078744019876957035 63129292618116029815435553)
        ·
          refine ⟨47346969463587022361576665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63129292618116029815435553 47346969463587022361576665)
          ·
            refine ⟨35510227097690266771182499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47346969463587022361576665 35510227097690266771182499)
            ·
              refine ⟨53265340646535400156773749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35510227097690266771182499 53265340646535400156773749)
              ·
                refine ⟨4993625685612693764697539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53265340646535400156773749 4993625685612693764697539)
                ·
                  refine ⟨7490438528419040647046309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993625685612693764697539 7490438528419040647046309)
                  ·
                    refine ⟨1404457224078570121321183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7490438528419040647046309 1404457224078570121321183)
                    ·
                      rfl

theorem cell22_4102756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_4102756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102756 prefixEnd_4102756 := by exact prefixLift 4102756
  have htrace : WordTrace (prefixWord ++ tailWord_4102756) baseStart_4102756 baseEnd_4102756 := by
    simpa [prefixWord, tailWord_4102756, baseEnd_4102756] using wordTrace_append hprefix tailTrace_4102756
  have hstable : (prefixWord ++ tailWord_4102756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102756).length < 2 ^ (prefixWord ++ tailWord_4102756).sum := by decide
  have hdescent : baseEnd_4102756 < baseStart_4102756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102816 : List Nat := [2, 1, 1, 4, 5, 9]
def baseStart_4102816 : Nat := 118140960795 + 4102816 * 2 ^ 59
def prefixEnd_4102816 : Nat := 4983230072969 + 3 ^ 40 * 4102816 * 2
def baseEnd_4102816 : Nat := 17339231645737653886679

theorem tailTrace_4102816 : CollatzResearch.WordTrace tailWord_4102816 prefixEnd_4102816 17339231645737653886679 := by
  unfold tailWord_4102816
  simp only [CollatzResearch.WordTrace]
  refine ⟨74820996552102906015960151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99761328736137208021280201 74820996552102906015960151)
  ·
    refine ⟨112231494828154359023940227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74820996552102906015960151 112231494828154359023940227)
    ·
      refine ⟨168347242242231538535910341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112231494828154359023940227 168347242242231538535910341)
      ·
        refine ⟨31565107920418413475483189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168347242242231538535910341 31565107920418413475483189)
        ·
          refine ⟨2959228867539226263326549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31565107920418413475483189 2959228867539226263326549)
          ·
            refine ⟨17339231645737653886679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2959228867539226263326549 17339231645737653886679)
            ·
              rfl

theorem cell22_4102816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 9].length) (baseStart_4102816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102816 prefixEnd_4102816 := by exact prefixLift 4102816
  have htrace : WordTrace (prefixWord ++ tailWord_4102816) baseStart_4102816 baseEnd_4102816 := by
    simpa [prefixWord, tailWord_4102816, baseEnd_4102816] using wordTrace_append hprefix tailTrace_4102816
  have hstable : (prefixWord ++ tailWord_4102816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102816).length < 2 ^ (prefixWord ++ tailWord_4102816).sum := by decide
  have hdescent : baseEnd_4102816 < baseStart_4102816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102846 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_4102846 : Nat := 118140960795 + 4102846 * 2 ^ 59
def prefixEnd_4102846 : Nat := 4983230072969 + 3 ^ 40 * 4102846 * 2
def baseEnd_4102846 : Nat := 1404488032917839886570907

theorem tailTrace_4102846 : CollatzResearch.WordTrace tailWord_4102846 prefixEnd_4102846 1404488032917839886570907 := by
  unfold tailWord_4102846
  simp only [CollatzResearch.WordTrace]
  refine ⟨18705385911762140894439049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99762058196064751437008261 18705385911762140894439049)
  ·
    refine ⟨14029039433821605670829287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18705385911762140894439049 14029039433821605670829287)
    ·
      refine ⟨21043559150732408506243931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14029039433821605670829287 21043559150732408506243931)
      ·
        refine ⟨31565338726098612759365897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21043559150732408506243931 31565338726098612759365897)
        ·
          refine ⟨23674004044573959569524423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31565338726098612759365897 23674004044573959569524423)
          ·
            refine ⟨35511006066860939354286635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23674004044573959569524423 35511006066860939354286635)
            ·
              refine ⟨53266509100291409031429953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35511006066860939354286635 53266509100291409031429953)
              ·
                refine ⟨39949881825218556773572465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53266509100291409031429953 39949881825218556773572465)
                ·
                  refine ⟨29962411368913917580179349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39949881825218556773572465 29962411368913917580179349)
                  ·
                    refine ⟨1404488032917839886570907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29962411368913917580179349 1404488032917839886570907)
                    ·
                      rfl

theorem cell22_4102846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_4102846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102846 prefixEnd_4102846 := by exact prefixLift 4102846
  have htrace : WordTrace (prefixWord ++ tailWord_4102846) baseStart_4102846 baseEnd_4102846 := by
    simpa [prefixWord, tailWord_4102846, baseEnd_4102846] using wordTrace_append hprefix tailTrace_4102846
  have hstable : (prefixWord ++ tailWord_4102846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102846).length < 2 ^ (prefixWord ++ tailWord_4102846).sum := by decide
  have hdescent : baseEnd_4102846 < baseStart_4102846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102848 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 3, 3]
def baseStart_4102848 : Nat := 118140960795 + 4102848 * 2 ^ 59
def prefixEnd_4102848 : Nat := 4983230072969 + 3 ^ 40 * 4102848 * 2
def baseEnd_4102848 : Nat := 1404488717558712548020901

theorem tailTrace_4102848 : CollatzResearch.WordTrace tailWord_4102848 prefixEnd_4102848 1404488717558712548020901 := by
  unfold tailWord_4102848
  simp only [CollatzResearch.WordTrace]
  refine ⟨74821580120044940748542599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99762106826726587664723465 74821580120044940748542599)
  ·
    refine ⟨112232370180067411122813899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74821580120044940748542599 112232370180067411122813899)
    ·
      refine ⟨168348555270101116684220849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112232370180067411122813899 168348555270101116684220849)
      ·
        refine ⟨126261416452575837513165637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168348555270101116684220849 126261416452575837513165637)
        ·
          refine ⟨23674015584857969533718557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126261416452575837513165637 23674015584857969533718557)
          ·
            refine ⟨8877755844321738575144459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23674015584857969533718557 8877755844321738575144459)
            ·
              refine ⟨13316633766482607862716689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8877755844321738575144459 13316633766482607862716689)
              ·
                refine ⟨9987475324861955897037517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13316633766482607862716689 9987475324861955897037517)
                ·
                  refine ⟨3745303246823233461389069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9987475324861955897037517 3745303246823233461389069)
                  ·
                    refine ⟨1404488717558712548020901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745303246823233461389069 1404488717558712548020901)
                    ·
                      rfl

theorem cell22_4102848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 3, 3].length) (baseStart_4102848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102848 prefixEnd_4102848 := by exact prefixLift 4102848
  have htrace : WordTrace (prefixWord ++ tailWord_4102848) baseStart_4102848 baseEnd_4102848 := by
    simpa [prefixWord, tailWord_4102848, baseEnd_4102848] using wordTrace_append hprefix tailTrace_4102848
  have hstable : (prefixWord ++ tailWord_4102848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102848).length < 2 ^ (prefixWord ++ tailWord_4102848).sum := by decide
  have hdescent : baseEnd_4102848 < baseStart_4102848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102865 : List Nat := [1, 2, 2, 1, 2, 3, 4, 3, 1, 3]
def baseStart_4102865 : Nat := 118140960795 + 4102865 * 2 ^ 59
def prefixEnd_4102865 : Nat := 4983230072969 + 3 ^ 40 * 4102865 * 2
def baseEnd_4102865 : Nat := 1404494537006130170345849

theorem tailTrace_4102865 : CollatzResearch.WordTrace tailWord_4102865 prefixEnd_4102865 1404494537006130170345849 := by
  unfold tailWord_4102865
  simp only [CollatzResearch.WordTrace]
  refine ⟨149643780281028293400454049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99762520187352195600302699 149643780281028293400454049)
  ·
    refine ⟨112232835210771220050340537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149643780281028293400454049 112232835210771220050340537)
    ·
      refine ⟨84174626408078415037755403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112232835210771220050340537 84174626408078415037755403)
      ·
        refine ⟨126261939612117622556633105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84174626408078415037755403 126261939612117622556633105)
        ·
          refine ⟨94696454709088216917474829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126261939612117622556633105 94696454709088216917474829)
          ·
            refine ⟨35511170515908081344053061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94696454709088216917474829 35511170515908081344053061)
            ·
              refine ⟨6658344471732765252009949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35511170515908081344053061 6658344471732765252009949)
              ·
                refine ⟨2496879176899786969503731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6658344471732765252009949 2496879176899786969503731)
                ·
                  refine ⟨3745318765349680454255597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2496879176899786969503731 3745318765349680454255597)
                  ·
                    refine ⟨1404494537006130170345849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745318765349680454255597 1404494537006130170345849)
                    ·
                      rfl

theorem cell22_4102865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_4102865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102865 prefixEnd_4102865 := by exact prefixLift 4102865
  have htrace : WordTrace (prefixWord ++ tailWord_4102865) baseStart_4102865 baseEnd_4102865 := by
    simpa [prefixWord, tailWord_4102865, baseEnd_4102865] using wordTrace_append hprefix tailTrace_4102865
  have hstable : (prefixWord ++ tailWord_4102865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102865).length < 2 ^ (prefixWord ++ tailWord_4102865).sum := by decide
  have hdescent : baseEnd_4102865 < baseStart_4102865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102906 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_4102906 : Nat := 118140960795 + 4102906 * 2 ^ 59
def prefixEnd_4102906 : Nat := 4983230072969 + 3 ^ 40 * 4102906 * 2
def baseEnd_4102906 : Nat := 468169524048006576690241

theorem tailTrace_4102906 : CollatzResearch.WordTrace tailWord_4102906 prefixEnd_4102906 468169524048006576690241 := by
  unfold tailWord_4102906
  simp only [CollatzResearch.WordTrace]
  refine ⟨37411318918469939350674143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99763517115919838268464381 37411318918469939350674143)
  ·
    refine ⟨56116978377704909026011215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37411318918469939350674143 56116978377704909026011215)
    ·
      refine ⟨84175467566557363539016823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56116978377704909026011215 84175467566557363539016823)
      ·
        refine ⟨126263201349836045308525235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84175467566557363539016823 126263201349836045308525235)
        ·
          refine ⟨189394802024754067962787853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126263201349836045308525235 189394802024754067962787853)
          ·
            refine ⟨71023050759282775486045445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189394802024754067962787853 71023050759282775486045445)
            ·
              refine ⟨13316822017365520403633521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71023050759282775486045445 13316822017365520403633521)
              ·
                refine ⟨9987616513024140302725141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13316822017365520403633521 9987616513024140302725141)
                ·
                  refine ⟨468169524048006576690241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9987616513024140302725141 468169524048006576690241)
                  ·
                    rfl

theorem cell22_4102906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_4102906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102906 prefixEnd_4102906 := by exact prefixLift 4102906
  have htrace : WordTrace (prefixWord ++ tailWord_4102906) baseStart_4102906 baseEnd_4102906 := by
    simpa [prefixWord, tailWord_4102906, baseEnd_4102906] using wordTrace_append hprefix tailTrace_4102906
  have hstable : (prefixWord ++ tailWord_4102906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102906).length < 2 ^ (prefixWord ++ tailWord_4102906).sum := by decide
  have hdescent : baseEnd_4102906 < baseStart_4102906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102908 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_4102908 : Nat := 118140960795 + 4102908 * 2 ^ 59
def prefixEnd_4102908 : Nat := 4983230072969 + 3 ^ 40 * 4102908 * 2
def baseEnd_4102908 : Nat := 1404509256784892391520717

theorem tailTrace_4102908 : CollatzResearch.WordTrace tailWord_4102908 prefixEnd_4102908 1404509256784892391520717 := by
  unfold tailWord_4102908
  simp only [CollatzResearch.WordTrace]
  refine ⟨74822674309936255872134689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99763565746581674496179585 74822674309936255872134689)
  ·
    refine ⟨56117005732452191904101017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74822674309936255872134689 56117005732452191904101017)
    ·
      refine ⟨42087754299339143928075763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56117005732452191904101017 42087754299339143928075763)
      ·
        refine ⟨63131631449008715892113645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42087754299339143928075763 63131631449008715892113645)
        ·
          refine ⟨23674361793378268459542617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63131631449008715892113645 23674361793378268459542617)
          ·
            refine ⟨17755771345033701344656963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23674361793378268459542617 17755771345033701344656963)
            ·
              refine ⟨26633657017550552016985445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17755771345033701344656963 26633657017550552016985445)
              ·
                refine ⟨4993810690790728503184771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26633657017550552016985445 4993810690790728503184771)
                ·
                  refine ⟨7490716036186092754777157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4993810690790728503184771 7490716036186092754777157)
                  ·
                    refine ⟨1404509256784892391520717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7490716036186092754777157 1404509256784892391520717)
                    ·
                      rfl

theorem cell22_4102908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_4102908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102908 prefixEnd_4102908 := by exact prefixLift 4102908
  have htrace : WordTrace (prefixWord ++ tailWord_4102908) baseStart_4102908 baseEnd_4102908 := by
    simpa [prefixWord, tailWord_4102908, baseEnd_4102908] using wordTrace_append hprefix tailTrace_4102908
  have hstable : (prefixWord ++ tailWord_4102908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102908).length < 2 ^ (prefixWord ++ tailWord_4102908).sum := by decide
  have hdescent : baseEnd_4102908 < baseStart_4102908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102921 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 1, 5]
def baseStart_4102921 : Nat := 118140960795 + 4102921 * 2 ^ 59
def prefixEnd_4102921 : Nat := 4983230072969 + 3 ^ 40 * 4102921 * 2
def baseEnd_4102921 : Nat := 1404513706950564690945677

theorem tailTrace_4102921 : CollatzResearch.WordTrace tailWord_4102921 prefixEnd_4102921 1404513706950564690945677 := by
  unfold tailWord_4102921
  simp only [CollatzResearch.WordTrace]
  refine ⟨149645822768825414964492617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99763881845883609976328411 149645822768825414964492617)
  ·
    refine ⟨112234367076619061223369463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149645822768825414964492617 112234367076619061223369463)
    ·
      refine ⟨168351550614928591835054195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112234367076619061223369463 168351550614928591835054195)
      ·
        refine ⟨252527325922392887752581293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168351550614928591835054195 252527325922392887752581293)
        ·
          refine ⟨94697747220897332907217985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252527325922392887752581293 94697747220897332907217985)
          ·
            refine ⟨71023310415672999680413489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94697747220897332907217985 71023310415672999680413489)
            ·
              refine ⟨53267482811754749760310117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71023310415672999680413489 53267482811754749760310117)
              ·
                refine ⟨9987653027204015580058147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53267482811754749760310117 9987653027204015580058147)
                ·
                  refine ⟨14981479540806023370087221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9987653027204015580058147 14981479540806023370087221)
                  ·
                    refine ⟨1404513706950564690945677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14981479540806023370087221 1404513706950564690945677)
                    ·
                      rfl

theorem cell22_4102921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_4102921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102921 prefixEnd_4102921 := by exact prefixLift 4102921
  have htrace : WordTrace (prefixWord ++ tailWord_4102921) baseStart_4102921 baseEnd_4102921 := by
    simpa [prefixWord, tailWord_4102921, baseEnd_4102921] using wordTrace_append hprefix tailTrace_4102921
  have hstable : (prefixWord ++ tailWord_4102921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102921).length < 2 ^ (prefixWord ++ tailWord_4102921).sum := by decide
  have hdescent : baseEnd_4102921 < baseStart_4102921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102938 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 4, 3]
def baseStart_4102938 : Nat := 118140960795 + 4102938 * 2 ^ 59
def prefixEnd_4102938 : Nat := 4983230072969 + 3 ^ 40 * 4102938 * 2
def baseEnd_4102938 : Nat := 1404519526397982313270625

theorem tailTrace_4102938 : CollatzResearch.WordTrace tailWord_4102938 prefixEnd_4102938 1404519526397982313270625 := by
  unfold tailWord_4102938
  simp only [CollatzResearch.WordTrace]
  refine ⟨37411610702440956716965367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99764295206509217911907645 37411610702440956716965367)
  ·
    refine ⟨56117416053661435075448051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37411610702440956716965367 56117416053661435075448051)
    ·
      refine ⟨84176124080492152613172077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56117416053661435075448051 84176124080492152613172077)
      ·
        refine ⟨31566046530184557229939529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84176124080492152613172077 31566046530184557229939529)
        ·
          refine ⟨23674534897638417922454647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31566046530184557229939529 23674534897638417922454647)
          ·
            refine ⟨35511802346457626883681971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23674534897638417922454647 35511802346457626883681971)
            ·
              refine ⟨53267703519686440325522957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35511802346457626883681971 53267703519686440325522957)
              ·
                refine ⟨19975388819882415122071109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53267703519686440325522957 19975388819882415122071109)
                ·
                  refine ⟨3745385403727952835388333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19975388819882415122071109 3745385403727952835388333)
                  ·
                    refine ⟨1404519526397982313270625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745385403727952835388333 1404519526397982313270625)
                    ·
                      rfl

theorem cell22_4102938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_4102938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102938 prefixEnd_4102938 := by exact prefixLift 4102938
  have htrace : WordTrace (prefixWord ++ tailWord_4102938) baseStart_4102938 baseEnd_4102938 := by
    simpa [prefixWord, tailWord_4102938, baseEnd_4102938] using wordTrace_append hprefix tailTrace_4102938
  have hstable : (prefixWord ++ tailWord_4102938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102938).length < 2 ^ (prefixWord ++ tailWord_4102938).sum := by decide
  have hdescent : baseEnd_4102938 < baseStart_4102938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102970 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_4102970 : Nat := 118140960795 + 4102970 * 2 ^ 59
def prefixEnd_4102970 : Nat := 4983230072969 + 3 ^ 40 * 4102970 * 2
def baseEnd_4102970 : Nat := 1404530480651944896470527

theorem tailTrace_4102970 : CollatzResearch.WordTrace tailWord_4102970 prefixEnd_4102970 1404530480651944896470527 := by
  unfold tailWord_4102970
  simp only [CollatzResearch.WordTrace]
  refine ⟨37411902486411974083256591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99765073297098597555350909 37411902486411974083256591)
  ·
    refine ⟨56117853729617961124884887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37411902486411974083256591 56117853729617961124884887)
    ·
      refine ⟨84176780594426941687327331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56117853729617961124884887 84176780594426941687327331)
      ·
        refine ⟨126265170891640412530990997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84176780594426941687327331 126265170891640412530990997)
        ·
          refine ⟨5918679885545644337390203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126265170891640412530990997 5918679885545644337390203)
          ·
            refine ⟨8878019828318466506085305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5918679885545644337390203 8878019828318466506085305)
            ·
              refine ⟨6658514871238849879563979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8878019828318466506085305 6658514871238849879563979)
              ·
                refine ⟨9987772306858274819345969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6658514871238849879563979 9987772306858274819345969)
                ·
                  refine ⟨7490829230143706114509477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9987772306858274819345969 7490829230143706114509477)
                  ·
                    refine ⟨1404530480651944896470527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7490829230143706114509477 1404530480651944896470527)
                    ·
                      rfl

theorem cell22_4102970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_4102970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102970 prefixEnd_4102970 := by exact prefixLift 4102970
  have htrace : WordTrace (prefixWord ++ tailWord_4102970) baseStart_4102970 baseEnd_4102970 := by
    simpa [prefixWord, tailWord_4102970, baseEnd_4102970] using wordTrace_append hprefix tailTrace_4102970
  have hstable : (prefixWord ++ tailWord_4102970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102970).length < 2 ^ (prefixWord ++ tailWord_4102970).sum := by decide
  have hdescent : baseEnd_4102970 < baseStart_4102970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4102989 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_4102989 : Nat := 118140960795 + 4102989 * 2 ^ 59
def prefixEnd_4102989 : Nat := 4983230072969 + 3 ^ 40 * 4102989 * 2
def baseEnd_4102989 : Nat := 1404536984740235180245469

theorem tailTrace_4102989 : CollatzResearch.WordTrace tailWord_4102989 prefixEnd_4102989 1404536984740235180245469 := by
  unfold tailWord_4102989
  simp only [CollatzResearch.WordTrace]
  refine ⟨149648302932579062577968021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99765535288386041718645347 149648302932579062577968021)
  ·
    refine ⟨7014764199964643558342251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149648302932579062577968021 7014764199964643558342251)
    ·
      refine ⟨10522146299946965337513377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7014764199964643558342251 10522146299946965337513377)
      ·
        refine ⟨7891609724960224003135033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10522146299946965337513377 7891609724960224003135033)
        ·
          refine ⟨5918707293720168002351275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7891609724960224003135033 5918707293720168002351275)
          ·
            refine ⟨8878060940580252003526913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5918707293720168002351275 8878060940580252003526913)
            ·
              refine ⟨6658545705435189002645185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8878060940580252003526913 6658545705435189002645185)
              ·
                refine ⟨4993909279076391751983889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6658545705435189002645185 4993909279076391751983889)
                ·
                  refine ⟨3745431959307293813987917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4993909279076391751983889 3745431959307293813987917)
                  ·
                    refine ⟨1404536984740235180245469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745431959307293813987917 1404536984740235180245469)
                    ·
                      rfl

theorem cell22_4102989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_4102989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4102989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4102989 prefixEnd_4102989 := by exact prefixLift 4102989
  have htrace : WordTrace (prefixWord ++ tailWord_4102989) baseStart_4102989 baseEnd_4102989 := by
    simpa [prefixWord, tailWord_4102989, baseEnd_4102989] using wordTrace_append hprefix tailTrace_4102989
  have hstable : (prefixWord ++ tailWord_4102989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4102989).length < 2 ^ (prefixWord ++ tailWord_4102989).sum := by decide
  have hdescent : baseEnd_4102989 < baseStart_4102989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4102989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103013 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 5]
def baseStart_4103013 : Nat := 118140960795 + 4103013 * 2 ^ 59
def prefixEnd_4103013 : Nat := 4983230072969 + 3 ^ 40 * 4103013 * 2
def baseEnd_4103013 : Nat := 468181733476902372548465

theorem tailTrace_4103013 : CollatzResearch.WordTrace tailWord_4103013 prefixEnd_4103013 468181733476902372548465 := by
  unfold tailWord_4103013
  simp only [CollatzResearch.WordTrace]
  refine ⟨149649178284492114676841693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99766118856328076451227795 149649178284492114676841693)
  ·
    refine ⟨56118441856684543003815635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149649178284492114676841693 56118441856684543003815635)
    ·
      refine ⟨84177662785026814505723453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56118441856684543003815635 84177662785026814505723453)
      ·
        refine ⟨31566623544385055439646295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84177662785026814505723453 31566623544385055439646295)
        ·
          refine ⟨47349935316577583159469443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31566623544385055439646295 47349935316577583159469443)
          ·
            refine ⟨71024902974866374739204165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47349935316577583159469443 71024902974866374739204165)
            ·
              refine ⟨13317169307787445263600781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71024902974866374739204165 13317169307787445263600781)
              ·
                refine ⟨4993938490420291973850293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13317169307787445263600781 4993938490420291973850293)
                ·
                  refine ⟨468181733476902372548465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4993938490420291973850293 468181733476902372548465)
                  ·
                    rfl

theorem cell22_4103013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_4103013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103013 prefixEnd_4103013 := by exact prefixLift 4103013
  have htrace : WordTrace (prefixWord ++ tailWord_4103013) baseStart_4103013 baseEnd_4103013 := by
    simpa [prefixWord, tailWord_4103013, baseEnd_4103013] using wordTrace_append hprefix tailTrace_4103013
  have hstable : (prefixWord ++ tailWord_4103013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103013).length < 2 ^ (prefixWord ++ tailWord_4103013).sum := by decide
  have hdescent : baseEnd_4103013 < baseStart_4103013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103124 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_4103124 : Nat := 118140960795 + 4103124 * 2 ^ 59
def prefixEnd_4103124 : Nat := 4983230072969 + 3 ^ 40 * 4103124 * 2
def baseEnd_4103124 : Nat := 1404583197999139828120055

theorem tailTrace_4103124 : CollatzResearch.WordTrace tailWord_4103124 prefixEnd_4103124 1404583197999139828120055 := by
  unfold tailWord_4103124
  simp only [CollatzResearch.WordTrace]
  refine ⟨74826613393544990317066213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99768817858059987089421617 74826613393544990317066213)
  ·
    refine ⟨14029990011289685684449915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74826613393544990317066213 14029990011289685684449915)
    ·
      refine ⟨21044985016934528526674873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14029990011289685684449915 21044985016934528526674873)
      ·
        refine ⟨15783738762700896395006155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21044985016934528526674873 15783738762700896395006155)
        ·
          refine ⟨23675608144051344592509233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15783738762700896395006155 23675608144051344592509233)
          ·
            refine ⟨17756706108038508444381925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23675608144051344592509233 17756706108038508444381925)
            ·
              refine ⟨3329382395257220333321611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17756706108038508444381925 3329382395257220333321611)
              ·
                refine ⟨4994073592885830499982417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329382395257220333321611 4994073592885830499982417)
                ·
                  refine ⟨3745555194664372874986813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4994073592885830499982417 3745555194664372874986813)
                  ·
                    refine ⟨1404583197999139828120055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745555194664372874986813 1404583197999139828120055)
                    ·
                      rfl

theorem cell22_4103124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_4103124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103124 prefixEnd_4103124 := by exact prefixLift 4103124
  have htrace : WordTrace (prefixWord ++ tailWord_4103124) baseStart_4103124 baseEnd_4103124 := by
    simpa [prefixWord, tailWord_4103124, baseEnd_4103124] using wordTrace_append hprefix tailTrace_4103124
  have hstable : (prefixWord ++ tailWord_4103124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103124).length < 2 ^ (prefixWord ++ tailWord_4103124).sum := by decide
  have hdescent : baseEnd_4103124 < baseStart_4103124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103152 : List Nat := [2, 1, 1, 1, 3, 2, 1, 7, 1, 3]
def baseStart_4103152 : Nat := 118140960795 + 4103152 * 2 ^ 59
def prefixEnd_4103152 : Nat := 4983230072969 + 3 ^ 40 * 4103152 * 2
def baseEnd_4103152 : Nat := 1404592782971357088419969

theorem tailTrace_4103152 : CollatzResearch.WordTrace tailWord_4103152 prefixEnd_4103152 1404592782971357088419969 := by
  unfold tailWord_4103152
  simp only [CollatzResearch.WordTrace]
  refine ⟨74827124015494270708075855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99769498687325694277434473 74827124015494270708075855)
  ·
    refine ⟨112240686023241406062113783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74827124015494270708075855 112240686023241406062113783)
    ·
      refine ⟨168361029034862109093170675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112240686023241406062113783 168361029034862109093170675)
      ·
        refine ⟨252541543552293163639756013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168361029034862109093170675 252541543552293163639756013)
        ·
          refine ⟨94703078832109936364908505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252541543552293163639756013 94703078832109936364908505)
          ·
            refine ⟨71027309124082452273681379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94703078832109936364908505 71027309124082452273681379)
            ·
              refine ⟨106540963686123678410522069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71027309124082452273681379 106540963686123678410522069)
              ·
                refine ⟨2497053836393523712746611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106540963686123678410522069 2497053836393523712746611)
                ·
                  refine ⟨3745580754590285569119917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497053836393523712746611 3745580754590285569119917)
                  ·
                    refine ⟨1404592782971357088419969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745580754590285569119917 1404592782971357088419969)
                    ·
                      rfl

theorem cell22_4103152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 1, 3].length) (baseStart_4103152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103152 prefixEnd_4103152 := by exact prefixLift 4103152
  have htrace : WordTrace (prefixWord ++ tailWord_4103152) baseStart_4103152 baseEnd_4103152 := by
    simpa [prefixWord, tailWord_4103152, baseEnd_4103152] using wordTrace_append hprefix tailTrace_4103152
  have hstable : (prefixWord ++ tailWord_4103152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103152).length < 2 ^ (prefixWord ++ tailWord_4103152).sum := by decide
  have hdescent : baseEnd_4103152 < baseStart_4103152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103163 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 2, 5]
def baseStart_4103163 : Nat := 118140960795 + 4103163 * 2 ^ 59
def prefixEnd_4103163 : Nat := 4983230072969 + 3 ^ 40 * 4103163 * 2
def baseEnd_4103163 : Nat := 1404596548496156726394935

theorem tailTrace_4103163 : CollatzResearch.WordTrace tailWord_4103163 prefixEnd_4103163 1404596548496156726394935 := by
  unfold tailWord_4103163
  simp only [CollatzResearch.WordTrace]
  refine ⟨149654649233948690294802143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99769766155965793529868095 149654649233948690294802143)
  ·
    refine ⟨224481973850923035442203215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149654649233948690294802143 224481973850923035442203215)
    ·
      refine ⟨336722960776384553163304823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224481973850923035442203215 336722960776384553163304823)
      ·
        refine ⟨505084441164576829744957235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336722960776384553163304823 505084441164576829744957235)
        ·
          refine ⟨757626661746865244617435853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505084441164576829744957235 757626661746865244617435853)
          ·
            refine ⟨284109998155074466731538445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 757626661746865244617435853 284109998155074466731538445)
            ·
              refine ⟨106541249308152925024326917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284109998155074466731538445 106541249308152925024326917)
              ·
                refine ⟨19976484245278673442061297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106541249308152925024326917 19976484245278673442061297)
                ·
                  refine ⟨14982363183959005081545973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19976484245278673442061297 14982363183959005081545973)
                  ·
                    refine ⟨1404596548496156726394935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14982363183959005081545973 1404596548496156726394935)
                    ·
                      rfl

theorem cell22_4103163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 5].length) (baseStart_4103163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103163 prefixEnd_4103163 := by exact prefixLift 4103163
  have htrace : WordTrace (prefixWord ++ tailWord_4103163) baseStart_4103163 baseEnd_4103163 := by
    simpa [prefixWord, tailWord_4103163, baseEnd_4103163] using wordTrace_append hprefix tailTrace_4103163
  have hstable : (prefixWord ++ tailWord_4103163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103163).length < 2 ^ (prefixWord ++ tailWord_4103163).sum := by decide
  have hdescent : baseEnd_4103163 < baseStart_4103163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103169 : List Nat := [1, 2, 4, 1, 2, 3, 1, 4, 1, 3]
def baseStart_4103169 : Nat := 118140960795 + 4103169 * 2 ^ 59
def prefixEnd_4103169 : Nat := 4983230072969 + 3 ^ 40 * 4103169 * 2
def baseEnd_4103169 : Nat := 1404598602418774710744917

theorem tailTrace_4103169 : CollatzResearch.WordTrace tailWord_4103169 prefixEnd_4103169 1404598602418774710744917 := by
  unfold tailWord_4103169
  simp only [CollatzResearch.WordTrace]
  refine ⟨149654868071926953319520561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99769912047951302213013707 149654868071926953319520561)
  ·
    refine ⟨112241151053945214989640421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149654868071926953319520561 112241151053945214989640421)
    ·
      refine ⟨21045215822614727810557579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112241151053945214989640421 21045215822614727810557579)
      ·
        refine ⟨31567823733922091715836369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21045215822614727810557579 31567823733922091715836369)
        ·
          refine ⟨23675867800441568786877277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31567823733922091715836369 23675867800441568786877277)
          ·
            refine ⟨8878450425165588295078979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23675867800441568786877277 8878450425165588295078979)
            ·
              refine ⟨13317675637748382442618469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8878450425165588295078979 13317675637748382442618469)
              ·
                refine ⟨2497064182077821707990963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13317675637748382442618469 2497064182077821707990963)
                ·
                  refine ⟨3745596273116732561986445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497064182077821707990963 3745596273116732561986445)
                  ·
                    refine ⟨1404598602418774710744917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745596273116732561986445 1404598602418774710744917)
                    ·
                      rfl

theorem cell22_4103169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_4103169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103169 prefixEnd_4103169 := by exact prefixLift 4103169
  have htrace : WordTrace (prefixWord ++ tailWord_4103169) baseStart_4103169 baseEnd_4103169 := by
    simpa [prefixWord, tailWord_4103169, baseEnd_4103169] using wordTrace_append hprefix tailTrace_4103169
  have hstable : (prefixWord ++ tailWord_4103169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103169).length < 2 ^ (prefixWord ++ tailWord_4103169).sum := by decide
  have hdescent : baseEnd_4103169 < baseStart_4103169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103180 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_4103180 : Nat := 118140960795 + 4103180 * 2 ^ 59
def prefixEnd_4103180 : Nat := 4983230072969 + 3 ^ 40 * 4103180 * 2
def baseEnd_4103180 : Nat := 1404602367943574348719883

theorem tailTrace_4103180 : CollatzResearch.WordTrace tailWord_4103180 prefixEnd_4103180 1404602367943574348719883 := by
  unfold tailWord_4103180
  simp only [CollatzResearch.WordTrace]
  refine ⟨74827634637443551099085497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99770179516591401465447329 74827634637443551099085497)
  ·
    refine ⟨56120725978082663324314123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74827634637443551099085497 56120725978082663324314123)
    ·
      refine ⟨84181088967123994986471185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56120725978082663324314123 84181088967123994986471185)
      ·
        refine ⟨63135816725342996239853389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84181088967123994986471185 63135816725342996239853389)
        ·
          refine ⟨23675931272003623589945021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63135816725342996239853389 23675931272003623589945021)
          ·
            refine ⟨8878474227001358846229383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23675931272003623589945021 8878474227001358846229383)
            ·
              refine ⟨13317711340502038269344075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8878474227001358846229383 13317711340502038269344075)
              ·
                refine ⟨19976567010753057404016113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13317711340502038269344075 19976567010753057404016113)
                ·
                  refine ⟨14982425258064793053012085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19976567010753057404016113 14982425258064793053012085)
                  ·
                    refine ⟨1404602367943574348719883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14982425258064793053012085 1404602367943574348719883)
                    ·
                      rfl

theorem cell22_4103180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_4103180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103180 prefixEnd_4103180 := by exact prefixLift 4103180
  have htrace : WordTrace (prefixWord ++ tailWord_4103180) baseStart_4103180 baseEnd_4103180 := by
    simpa [prefixWord, tailWord_4103180, baseEnd_4103180] using wordTrace_append hprefix tailTrace_4103180
  have hstable : (prefixWord ++ tailWord_4103180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103180).length < 2 ^ (prefixWord ++ tailWord_4103180).sum := by decide
  have hdescent : baseEnd_4103180 < baseStart_4103180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103193 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 8]
def baseStart_4103193 : Nat := 118140960795 + 4103193 * 2 ^ 59
def prefixEnd_4103193 : Nat := 4983230072969 + 3 ^ 40 * 4103193 * 2
def baseEnd_4103193 : Nat := 468202272703082216048281

theorem tailTrace_4103193 : CollatzResearch.WordTrace tailWord_4103193 prefixEnd_4103193 468202272703082216048281 := by
  unfold tailWord_4103193
  simp only [CollatzResearch.WordTrace]
  refine ⟨149655743423840005418394233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99770495615893336945596155 149655743423840005418394233)
  ·
    refine ⟨112241807567880004063795675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149655743423840005418394233 112241807567880004063795675)
    ·
      refine ⟨168362711351820006095693513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112241807567880004063795675 168362711351820006095693513)
      ·
        refine ⟨126272033513865004571770135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168362711351820006095693513 126272033513865004571770135)
        ·
          refine ⟨189408050270797506857655203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126272033513865004571770135 189408050270797506857655203)
          ·
            refine ⟨284112075406196260286482805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189408050270797506857655203 284112075406196260286482805)
            ·
              refine ⟨26635507069330899401857763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 284112075406196260286482805 26635507069330899401857763)
              ·
                refine ⟨39953260603996349102786645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26635507069330899401857763 39953260603996349102786645)
                ·
                  refine ⟨468202272703082216048281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39953260603996349102786645 468202272703082216048281)
                  ·
                    rfl

theorem cell22_4103193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_4103193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103193 prefixEnd_4103193 := by exact prefixLift 4103193
  have htrace : WordTrace (prefixWord ++ tailWord_4103193) baseStart_4103193 baseEnd_4103193 := by
    simpa [prefixWord, tailWord_4103193, baseEnd_4103193] using wordTrace_append hprefix tailTrace_4103193
  have hstable : (prefixWord ++ tailWord_4103193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103193).length < 2 ^ (prefixWord ++ tailWord_4103193).sum := by decide
  have hdescent : baseEnd_4103193 < baseStart_4103193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103242 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 2, 3]
def baseStart_4103242 : Nat := 118140960795 + 4103242 * 2 ^ 59
def prefixEnd_4103242 : Nat := 4983230072969 + 3 ^ 40 * 4103242 * 2
def baseEnd_4103242 : Nat := 1404623591810626853669693

theorem tailTrace_4103242 : CollatzResearch.WordTrace tailWord_4103242 prefixEnd_4103242 1404623591810626853669693 := by
  unfold tailWord_4103242
  simp only [CollatzResearch.WordTrace]
  refine ⟨37414382650165621696731995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99771687067108324524618653 37414382650165621696731995)
  ·
    refine ⟨56121573975248432545097993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37414382650165621696731995 56121573975248432545097993)
    ·
      refine ⟨42091180481436324408823495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56121573975248432545097993 42091180481436324408823495)
      ·
        refine ⟨63136770722154486613235243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42091180481436324408823495 63136770722154486613235243)
        ·
          refine ⟨94705156083231729919852865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63136770722154486613235243 94705156083231729919852865)
          ·
            refine ⟨71028867062423797439889649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94705156083231729919852865 71028867062423797439889649)
            ·
              refine ⟨53271650296817848079917237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71028867062423797439889649 53271650296817848079917237)
              ·
                refine ⟨4994217215326673257492241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53271650296817848079917237 4994217215326673257492241)
                ·
                  refine ⟨3745662911495004943119181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4994217215326673257492241 3745662911495004943119181)
                  ·
                    refine ⟨1404623591810626853669693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745662911495004943119181 1404623591810626853669693)
                    ·
                      rfl

theorem cell22_4103242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_4103242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103242 prefixEnd_4103242 := by exact prefixLift 4103242
  have htrace : WordTrace (prefixWord ++ tailWord_4103242) baseStart_4103242 baseEnd_4103242 := by
    simpa [prefixWord, tailWord_4103242, baseEnd_4103242] using wordTrace_append hprefix tailTrace_4103242
  have hstable : (prefixWord ++ tailWord_4103242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103242).length < 2 ^ (prefixWord ++ tailWord_4103242).sum := by decide
  have hdescent : baseEnd_4103242 < baseStart_4103242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103338 : List Nat := [3, 1, 5, 1, 1, 2, 1, 4, 1, 3]
def baseStart_4103338 : Nat := 118140960795 + 4103338 * 2 ^ 59
def prefixEnd_4103338 : Nat := 4983230072969 + 3 ^ 40 * 4103338 * 2
def baseEnd_4103338 : Nat := 1404656454572514603269399

theorem tailTrace_4103338 : CollatzResearch.WordTrace tailWord_4103338 prefixEnd_4103338 1404656454572514603269399 := by
  unfold tailWord_4103338
  simp only [CollatzResearch.WordTrace]
  refine ⟨37415258002078673795605667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99774021338876463454948445 37415258002078673795605667)
  ·
    refine ⟨56122887003118010693408501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37415258002078673795605667 56122887003118010693408501)
    ·
      refine ⟨5261520656542313502507047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56122887003118010693408501 5261520656542313502507047)
      ·
        refine ⟨7892280984813470253760571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5261520656542313502507047 7892280984813470253760571)
        ·
          refine ⟨11838421477220205380640857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7892280984813470253760571 11838421477220205380640857)
          ·
            refine ⟨8878816107915154035480643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11838421477220205380640857 8878816107915154035480643)
            ·
              refine ⟨13318224161872731053220965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8878816107915154035480643 13318224161872731053220965)
              ·
                refine ⟨2497167030351137072478931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13318224161872731053220965 2497167030351137072478931)
                ·
                  refine ⟨3745750545526705608718397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497167030351137072478931 3745750545526705608718397)
                  ·
                    refine ⟨1404656454572514603269399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745750545526705608718397 1404656454572514603269399)
                    ·
                      rfl

theorem cell22_4103338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_4103338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103338 prefixEnd_4103338 := by exact prefixLift 4103338
  have htrace : WordTrace (prefixWord ++ tailWord_4103338) baseStart_4103338 baseEnd_4103338 := by
    simpa [prefixWord, tailWord_4103338, baseEnd_4103338] using wordTrace_append hprefix tailTrace_4103338
  have hstable : (prefixWord ++ tailWord_4103338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103338).length < 2 ^ (prefixWord ++ tailWord_4103338).sum := by decide
  have hdescent : baseEnd_4103338 < baseStart_4103338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103377 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 4, 3]
def baseStart_4103377 : Nat := 118140960795 + 4103377 * 2 ^ 59
def prefixEnd_4103377 : Nat := 4983230072969 + 3 ^ 40 * 4103377 * 2
def baseEnd_4103377 : Nat := 1404669805069531501544279

theorem tailTrace_4103377 : CollatzResearch.WordTrace tailWord_4103377 prefixEnd_4103377 1404669805069531501544279 := by
  unfold tailWord_4103377
  simp only [CollatzResearch.WordTrace]
  refine ⟨149662454455173404843092385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99774969636782269895394923 149662454455173404843092385)
  ·
    refine ⟨112246840841380053632319289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149662454455173404843092385 112246840841380053632319289)
    ·
      refine ⟨84185130631035040224239467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112246840841380053632319289 84185130631035040224239467)
      ·
        refine ⟨126277695946552560336359201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84185130631035040224239467 126277695946552560336359201)
        ·
          refine ⟨94708271959914420252269401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126277695946552560336359201 94708271959914420252269401)
          ·
            refine ⟨71031203969935815189202051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94708271959914420252269401 71031203969935815189202051)
            ·
              refine ⟨106546805954903722783803077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71031203969935815189202051 106546805954903722783803077)
              ·
                refine ⟨19977526116544448021963077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106546805954903722783803077 19977526116544448021963077)
                ·
                  refine ⟨3745786146852084004118077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19977526116544448021963077 3745786146852084004118077)
                  ·
                    refine ⟨1404669805069531501544279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745786146852084004118077 1404669805069531501544279)
                    ·
                      rfl

theorem cell22_4103377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_4103377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103377 prefixEnd_4103377 := by exact prefixLift 4103377
  have htrace : WordTrace (prefixWord ++ tailWord_4103377) baseStart_4103377 baseEnd_4103377 := by
    simpa [prefixWord, tailWord_4103377, baseEnd_4103377] using wordTrace_append hprefix tailTrace_4103377
  have hstable : (prefixWord ++ tailWord_4103377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103377).length < 2 ^ (prefixWord ++ tailWord_4103377).sum := by decide
  have hdescent : baseEnd_4103377 < baseStart_4103377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103381 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 1, 4]
def baseStart_4103381 : Nat := 118140960795 + 4103381 * 2 ^ 59
def prefixEnd_4103381 : Nat := 4983230072969 + 3 ^ 40 * 4103381 * 2
def baseEnd_4103381 : Nat := 1404671174351276824444267

theorem tailTrace_4103381 : CollatzResearch.WordTrace tailWord_4103381 prefixEnd_4103381 1404671174351276824444267 := by
  unfold tailWord_4103381
  simp only [CollatzResearch.WordTrace]
  refine ⟨149662600347158913526237997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99775066898105942350825331 149662600347158913526237997)
  ·
    refine ⟨56123475130184592572339249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149662600347158913526237997 56123475130184592572339249)
    ·
      refine ⟨42092606347638444429254437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56123475130184592572339249 42092606347638444429254437)
      ·
        refine ⟨7892363690182208330485207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42092606347638444429254437 7892363690182208330485207)
        ·
          refine ⟨11838545535273312495727811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7892363690182208330485207 11838545535273312495727811)
          ·
            refine ⟨17757818302909968743591717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11838545535273312495727811 17757818302909968743591717)
            ·
              refine ⟨3329590931795619139423447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17757818302909968743591717 3329590931795619139423447)
              ·
                refine ⟨4994386397693428709135171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329590931795619139423447 4994386397693428709135171)
                ·
                  refine ⟨7491579596540143063702757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994386397693428709135171 7491579596540143063702757)
                  ·
                    refine ⟨1404671174351276824444267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7491579596540143063702757 1404671174351276824444267)
                    ·
                      rfl

theorem cell22_4103381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_4103381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103381 prefixEnd_4103381 := by exact prefixLift 4103381
  have htrace : WordTrace (prefixWord ++ tailWord_4103381) baseStart_4103381 baseEnd_4103381 := by
    simpa [prefixWord, tailWord_4103381, baseEnd_4103381] using wordTrace_append hprefix tailTrace_4103381
  have hstable : (prefixWord ++ tailWord_4103381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103381).length < 2 ^ (prefixWord ++ tailWord_4103381).sum := by decide
  have hdescent : baseEnd_4103381 < baseStart_4103381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103411 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 2, 3]
def baseStart_4103411 : Nat := 118140960795 + 4103411 * 2 ^ 59
def prefixEnd_4103411 : Nat := 4983230072969 + 3 ^ 40 * 4103411 * 2
def baseEnd_4103411 : Nat := 1404681443964366746194175

theorem tailTrace_4103411 : CollatzResearch.WordTrace tailWord_4103411 prefixEnd_4103411 1404681443964366746194175 := by
  unfold tailWord_4103411
  simp only [CollatzResearch.WordTrace]
  refine ⟨149663694537050228649830087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99775796358033485766553391 149663694537050228649830087)
  ·
    refine ⟨224495541805575342974745131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149663694537050228649830087 224495541805575342974745131)
    ·
      refine ⟨336743312708363014462117697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224495541805575342974745131 336743312708363014462117697)
      ·
        refine ⟨252557484531272260846588273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336743312708363014462117697 252557484531272260846588273)
        ·
          refine ⟨189418113398454195634941205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252557484531272260846588273 189418113398454195634941205)
          ·
            refine ⟨8878974065552540420387869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 189418113398454195634941205 8878974065552540420387869)
            ·
              refine ⟨3329615274582202657645451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8878974065552540420387869 3329615274582202657645451)
              ·
                refine ⟨4994422911873303986468177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3329615274582202657645451 4994422911873303986468177)
                ·
                  refine ⟨3745817183904977989851133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4994422911873303986468177 3745817183904977989851133)
                  ·
                    refine ⟨1404681443964366746194175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745817183904977989851133 1404681443964366746194175)
                    ·
                      rfl

theorem cell22_4103411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 2, 3].length) (baseStart_4103411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103411 prefixEnd_4103411 := by exact prefixLift 4103411
  have htrace : WordTrace (prefixWord ++ tailWord_4103411) baseStart_4103411 baseEnd_4103411 := by
    simpa [prefixWord, tailWord_4103411, baseEnd_4103411] using wordTrace_append hprefix tailTrace_4103411
  have hstable : (prefixWord ++ tailWord_4103411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103411).length < 2 ^ (prefixWord ++ tailWord_4103411).sum := by decide
  have hdescent : baseEnd_4103411 < baseStart_4103411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103452 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 7]
def baseStart_4103452 : Nat := 118140960795 + 4103452 * 2 ^ 59
def prefixEnd_4103452 : Nat := 4983230072969 + 3 ^ 40 * 4103452 * 2
def baseEnd_4103452 : Nat := 468231826367418768639683

theorem tailTrace_4103452 : CollatzResearch.WordTrace tailWord_4103452 prefixEnd_4103452 468231826367418768639683 := by
  unfold tailWord_4103452
  simp only [CollatzResearch.WordTrace]
  refine ⟨74832594964950846326036305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99776793286601128434715073 74832594964950846326036305)
  ·
    refine ⟨56124446223713134744527229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74832594964950846326036305 56124446223713134744527229)
    ·
      refine ⟨21046667333892425529197711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56124446223713134744527229 21046667333892425529197711)
      ·
        refine ⟨31570001000838638293796567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21046667333892425529197711 31570001000838638293796567)
        ·
          refine ⟨47355001501257957440694851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31570001000838638293796567 47355001501257957440694851)
          ·
            refine ⟨71032502251886936161042277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47355001501257957440694851 71032502251886936161042277)
            ·
              refine ⟨13318594172228800530195427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71032502251886936161042277 13318594172228800530195427)
              ·
                refine ⟨19977891258343200795293141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13318594172228800530195427 19977891258343200795293141)
                ·
                  refine ⟨468231826367418768639683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19977891258343200795293141 468231826367418768639683)
                  ·
                    rfl

theorem cell22_4103452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_4103452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103452 prefixEnd_4103452 := by exact prefixLift 4103452
  have htrace : WordTrace (prefixWord ++ tailWord_4103452) baseStart_4103452 baseEnd_4103452 := by
    simpa [prefixWord, tailWord_4103452, baseEnd_4103452] using wordTrace_append hprefix tailTrace_4103452
  have hstable : (prefixWord ++ tailWord_4103452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103452).length < 2 ^ (prefixWord ++ tailWord_4103452).sum := by decide
  have hdescent : baseEnd_4103452 < baseStart_4103452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103512 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 3, 5]
def baseStart_4103512 : Nat := 118140960795 + 4103512 * 2 ^ 59
def prefixEnd_4103512 : Nat := 4983230072969 + 3 ^ 40 * 4103512 * 2
def baseEnd_4103512 : Nat := 1404716018328436149418865

theorem tailTrace_4103512 : CollatzResearch.WordTrace tailWord_4103512 prefixEnd_4103512 1404716018328436149418865 := by
  unfold tailWord_4103512
  simp only [CollatzResearch.WordTrace]
  refine ⟨74833689154842161449628395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99778252206456215266171193 74833689154842161449628395)
  ·
    refine ⟨112250533732263242174442593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74833689154842161449628395 112250533732263242174442593)
    ·
      refine ⟨84187900299197431630831945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112250533732263242174442593 84187900299197431630831945)
      ·
        refine ⟨63140925224398073723123959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84187900299197431630831945 63140925224398073723123959)
        ·
          refine ⟨94711387836597110584685939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63140925224398073723123959 94711387836597110584685939)
          ·
            refine ⟨142067081754895665877028909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94711387836597110584685939 142067081754895665877028909)
            ·
              refine ⟨53275155658085874703885841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142067081754895665877028909 53275155658085874703885841)
              ·
                refine ⟨39956366743564406027914381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53275155658085874703885841 39956366743564406027914381)
                ·
                  refine ⟨14983637528836652260467893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39956366743564406027914381 14983637528836652260467893)
                  ·
                    refine ⟨1404716018328436149418865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14983637528836652260467893 1404716018328436149418865)
                    ·
                      rfl

theorem cell22_4103512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_4103512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103512 prefixEnd_4103512 := by exact prefixLift 4103512
  have htrace : WordTrace (prefixWord ++ tailWord_4103512) baseStart_4103512 baseEnd_4103512 := by
    simpa [prefixWord, tailWord_4103512, baseEnd_4103512] using wordTrace_append hprefix tailTrace_4103512
  have hstable : (prefixWord ++ tailWord_4103512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103512).length < 2 ^ (prefixWord ++ tailWord_4103512).sum := by decide
  have hdescent : baseEnd_4103512 < baseStart_4103512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103550 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_4103550 : Nat := 118140960795 + 4103550 * 2 ^ 59
def prefixEnd_4103550 : Nat := 4983230072969 + 3 ^ 40 * 4103550 * 2
def baseEnd_4103550 : Nat := 1404729026505016716968749

theorem tailTrace_4103550 : CollatzResearch.WordTrace tailWord_4103550 prefixEnd_4103550 1404729026505016716968749 := by
  unfold tailWord_4103550
  simp only [CollatzResearch.WordTrace]
  refine ⟨18708595535443331923642513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99779176189031103592760069 18708595535443331923642513)
  ·
    refine ⟨14031446651582498942731885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18708595535443331923642513 14031446651582498942731885)
    ·
      refine ⟨5261792494343437103524457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14031446651582498942731885 5261792494343437103524457)
      ·
        refine ⟨3946344370757577827643343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5261792494343437103524457 3946344370757577827643343)
        ·
          refine ⟨5919516556136366741465015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3946344370757577827643343 5919516556136366741465015)
          ·
            refine ⟨8879274834204550112197523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5919516556136366741465015 8879274834204550112197523)
            ·
              refine ⟨13318912251306825168296285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879274834204550112197523 13318912251306825168296285)
              ·
                refine ⟨4994592094240059438111107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13318912251306825168296285 4994592094240059438111107)
                ·
                  refine ⟨7491888141360089157166661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4994592094240059438111107 7491888141360089157166661)
                  ·
                    refine ⟨1404729026505016716968749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7491888141360089157166661 1404729026505016716968749)
                    ·
                      rfl

theorem cell22_4103550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_4103550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103550 prefixEnd_4103550 := by exact prefixLift 4103550
  have htrace : WordTrace (prefixWord ++ tailWord_4103550) baseStart_4103550 baseEnd_4103550 := by
    simpa [prefixWord, tailWord_4103550, baseEnd_4103550] using wordTrace_append hprefix tailTrace_4103550
  have hstable : (prefixWord ++ tailWord_4103550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103550).length < 2 ^ (prefixWord ++ tailWord_4103550).sum := by decide
  have hdescent : baseEnd_4103550 < baseStart_4103550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103580 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 1, 5]
def baseStart_4103580 : Nat := 118140960795 + 4103580 * 2 ^ 59
def prefixEnd_4103580 : Nat := 4983230072969 + 3 ^ 40 * 4103580 * 2
def baseEnd_4103580 : Nat := 1404739296118106638718657

theorem tailTrace_4103580 : CollatzResearch.WordTrace tailWord_4103580 prefixEnd_4103580 1404739296118106638718657 := by
  unfold tailWord_4103580
  simp only [CollatzResearch.WordTrace]
  refine ⟨74834929236718985256366097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99779905648958647008488129 74834929236718985256366097)
  ·
    refine ⟨56126196927539238942274573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74834929236718985256366097 56126196927539238942274573)
    ·
      refine ⟨21047323847827214603352965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56126196927539238942274573 21047323847827214603352965)
      ·
        refine ⟨3946373221467602738128681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21047323847827214603352965 3946373221467602738128681)
        ·
          refine ⟨2959779916100702053596511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3946373221467602738128681 2959779916100702053596511)
          ·
            refine ⟨4439669874151053080394767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959779916100702053596511 4439669874151053080394767)
            ·
              refine ⟨6659504811226579620592151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439669874151053080394767 6659504811226579620592151)
              ·
                refine ⟨9989257216839869430888227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659504811226579620592151 9989257216839869430888227)
                ·
                  refine ⟨14983885825259804146332341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9989257216839869430888227 14983885825259804146332341)
                  ·
                    refine ⟨1404739296118106638718657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14983885825259804146332341 1404739296118106638718657)
                    ·
                      rfl

theorem cell22_4103580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_4103580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103580 prefixEnd_4103580 := by exact prefixLift 4103580
  have htrace : WordTrace (prefixWord ++ tailWord_4103580) baseStart_4103580 baseEnd_4103580 := by
    simpa [prefixWord, tailWord_4103580, baseEnd_4103580] using wordTrace_append hprefix tailTrace_4103580
  have hstable : (prefixWord ++ tailWord_4103580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103580).length < 2 ^ (prefixWord ++ tailWord_4103580).sum := by decide
  have hdescent : baseEnd_4103580 < baseStart_4103580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103591 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 3, 3]
def baseStart_4103591 : Nat := 118140960795 + 4103591 * 2 ^ 59
def prefixEnd_4103591 : Nat := 4983230072969 + 3 ^ 40 * 4103591 * 2
def baseEnd_4103591 : Nat := 1404743061642906276693623

theorem tailTrace_4103591 : CollatzResearch.WordTrace tailWord_4103591 prefixEnd_4103591 1404743061642906276693623 := by
  unfold tailWord_4103591
  simp only [CollatzResearch.WordTrace]
  refine ⟨149670259676398119391382627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99780173117598746260921751 149670259676398119391382627)
  ·
    refine ⟨224505389514597179087073941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149670259676398119391382627 224505389514597179087073941)
    ·
      refine ⟨10523690133496742769706591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 224505389514597179087073941 10523690133496742769706591)
      ·
        refine ⟨15785535200245114154559887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10523690133496742769706591 15785535200245114154559887)
        ·
          refine ⟨23678302800367671231839831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15785535200245114154559887 23678302800367671231839831)
          ·
            refine ⟨35517454200551506847759747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23678302800367671231839831 35517454200551506847759747)
            ·
              refine ⟨53276181300827260271639621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35517454200551506847759747 53276181300827260271639621)
              ·
                refine ⟨9989283993905111300932429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53276181300827260271639621 9989283993905111300932429)
                ·
                  refine ⟨3745981497714416737849661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9989283993905111300932429 3745981497714416737849661)
                  ·
                    refine ⟨1404743061642906276693623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745981497714416737849661 1404743061642906276693623)
                    ·
                      rfl

theorem cell22_4103591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_4103591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103591 prefixEnd_4103591 := by exact prefixLift 4103591
  have htrace : WordTrace (prefixWord ++ tailWord_4103591) baseStart_4103591 baseEnd_4103591 := by
    simpa [prefixWord, tailWord_4103591, baseEnd_4103591] using wordTrace_append hprefix tailTrace_4103591
  have hstable : (prefixWord ++ tailWord_4103591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103591).length < 2 ^ (prefixWord ++ tailWord_4103591).sum := by decide
  have hdescent : baseEnd_4103591 < baseStart_4103591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103608 : List Nat := [2, 1, 2, 1, 2, 2, 5, 3, 1, 3]
def baseStart_4103608 : Nat := 118140960795 + 4103608 * 2 ^ 59
def prefixEnd_4103608 : Nat := 4983230072969 + 3 ^ 40 * 4103608 * 2
def baseEnd_4103608 : Nat := 1404748881090323899018571

theorem tailTrace_4103608 : CollatzResearch.WordTrace tailWord_4103608 prefixEnd_4103608 1404748881090323899018571 := by
  unfold tailWord_4103608
  simp only [CollatzResearch.WordTrace]
  refine ⟨74835439858668265647375739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99780586478224354196500985 74835439858668265647375739)
  ·
    refine ⟨112253159788002398471063609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74835439858668265647375739 112253159788002398471063609)
    ·
      refine ⟨84189869841001798853297707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112253159788002398471063609 84189869841001798853297707)
      ·
        refine ⟨126284804761502698279946561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84189869841001798853297707 126284804761502698279946561)
        ·
          refine ⟨94713603571127023709959921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126284804761502698279946561 94713603571127023709959921)
          ·
            refine ⟨71035202678345267782469941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94713603571127023709959921 71035202678345267782469941)
            ·
              refine ⟨6659550251094868854606557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71035202678345267782469941 6659550251094868854606557)
              ·
                refine ⟨2497331344160575820477459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6659550251094868854606557 2497331344160575820477459)
                ·
                  refine ⟨3745997016240863730716189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497331344160575820477459 3745997016240863730716189)
                  ·
                    refine ⟨1404748881090323899018571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3745997016240863730716189 1404748881090323899018571)
                    ·
                      rfl

theorem cell22_4103608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_4103608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103608 prefixEnd_4103608 := by exact prefixLift 4103608
  have htrace : WordTrace (prefixWord ++ tailWord_4103608) baseStart_4103608 baseEnd_4103608 := by
    simpa [prefixWord, tailWord_4103608, baseEnd_4103608] using wordTrace_append hprefix tailTrace_4103608
  have hstable : (prefixWord ++ tailWord_4103608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103608).length < 2 ^ (prefixWord ++ tailWord_4103608).sum := by decide
  have hdescent : baseEnd_4103608 < baseStart_4103608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103638 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_4103638 : Nat := 118140960795 + 4103638 * 2 ^ 59
def prefixEnd_4103638 : Nat := 4983230072969 + 3 ^ 40 * 4103638 * 2
def baseEnd_4103638 : Nat := 468253050234471273589493

theorem tailTrace_4103638 : CollatzResearch.WordTrace tailWord_4103638 prefixEnd_4103638 468253050234471273589493 := by
  unfold tailWord_4103638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9354498369201740401146473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99781315938151897612229045 9354498369201740401146473)
  ·
    refine ⟨7015873776901305300859855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9354498369201740401146473 7015873776901305300859855)
    ·
      refine ⟨10523810665351957951289783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7015873776901305300859855 10523810665351957951289783)
      ·
        refine ⟨15785715998027936926934675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10523810665351957951289783 15785715998027936926934675)
        ·
          refine ⟨23678573997041905390402013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15785715998027936926934675 23678573997041905390402013)
          ·
            refine ⟨8879465248890714521400755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23678573997041905390402013 8879465248890714521400755)
            ·
              refine ⟨13319197873336071782101133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879465248890714521400755 13319197873336071782101133)
              ·
                refine ⟨4994699202501026918287925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13319197873336071782101133 4994699202501026918287925)
                ·
                  refine ⟨468253050234471273589493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4994699202501026918287925 468253050234471273589493)
                  ·
                    rfl

theorem cell22_4103638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_4103638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103638 prefixEnd_4103638 := by exact prefixLift 4103638
  have htrace : WordTrace (prefixWord ++ tailWord_4103638) baseStart_4103638 baseEnd_4103638 := by
    simpa [prefixWord, tailWord_4103638, baseEnd_4103638] using wordTrace_append hprefix tailTrace_4103638
  have hstable : (prefixWord ++ tailWord_4103638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103638).length < 2 ^ (prefixWord ++ tailWord_4103638).sum := by decide
  have hdescent : baseEnd_4103638 < baseStart_4103638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103651 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 3, 4]
def baseStart_4103651 : Nat := 118140960795 + 4103651 * 2 ^ 59
def prefixEnd_4103651 : Nat := 4983230072969 + 3 ^ 40 * 4103651 * 2
def baseEnd_4103651 : Nat := 1404763600869086120193439

theorem tailTrace_4103651 : CollatzResearch.WordTrace tailWord_4103651 prefixEnd_4103651 1404763600869086120193439 := by
  unfold tailWord_4103651
  simp only [CollatzResearch.WordTrace]
  refine ⟨149672448056180749638566807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99781632037453833092377871 149672448056180749638566807)
  ·
    refine ⟨224508672084271124457850211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149672448056180749638566807 224508672084271124457850211)
    ·
      refine ⟨336763008126406686686775317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224508672084271124457850211 336763008126406686686775317)
      ·
        refine ⟨15785766005925313438442593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 336763008126406686686775317 15785766005925313438442593)
        ·
          refine ⟨11839324504443985078831945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15785766005925313438442593 11839324504443985078831945)
          ·
            refine ⟨8879493378332988809123959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11839324504443985078831945 8879493378332988809123959)
            ·
              refine ⟨13319240067499483213685939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8879493378332988809123959 13319240067499483213685939)
              ·
                refine ⟨19978860101249224820528909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13319240067499483213685939 19978860101249224820528909)
                ·
                  refine ⟨7492072537968459307698341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19978860101249224820528909 7492072537968459307698341)
                  ·
                    refine ⟨1404763600869086120193439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7492072537968459307698341 1404763600869086120193439)
                    ·
                      rfl

theorem cell22_4103651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 4].length) (baseStart_4103651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103651 prefixEnd_4103651 := by exact prefixLift 4103651
  have htrace : WordTrace (prefixWord ++ tailWord_4103651) baseStart_4103651 baseEnd_4103651 := by
    simpa [prefixWord, tailWord_4103651, baseEnd_4103651] using wordTrace_append hprefix tailTrace_4103651
  have hstable : (prefixWord ++ tailWord_4103651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103651).length < 2 ^ (prefixWord ++ tailWord_4103651).sum := by decide
  have hdescent : baseEnd_4103651 < baseStart_4103651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103664 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 3, 5]
def baseStart_4103664 : Nat := 118140960795 + 4103664 * 2 ^ 59
def prefixEnd_4103664 : Nat := 4983230072969 + 3 ^ 40 * 4103664 * 2
def baseEnd_4103664 : Nat := 1404768051034758419618399

theorem tailTrace_4103664 : CollatzResearch.WordTrace tailWord_4103664 prefixEnd_4103664 1404768051034758419618399 := by
  unfold tailWord_4103664
  simp only [CollatzResearch.WordTrace]
  refine ⟨74836461102566826429395023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99781948136755768572526697 74836461102566826429395023)
  ·
    refine ⟨112254691653850239644092535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74836461102566826429395023 112254691653850239644092535)
    ·
      refine ⟨168382037480775359466138803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112254691653850239644092535 168382037480775359466138803)
      ·
        refine ⟨252573056221163039199208205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168382037480775359466138803 252573056221163039199208205)
        ·
          refine ⟨94714896082936139699703077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252573056221163039199208205 94714896082936139699703077)
          ·
            refine ⟨17759043015550526193694327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94714896082936139699703077 17759043015550526193694327)
            ·
              refine ⟨26638564523325789290541491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17759043015550526193694327 26638564523325789290541491)
              ·
                refine ⟨39957846784988683935812237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26638564523325789290541491 39957846784988683935812237)
                ·
                  refine ⟨14984192544370756475929589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39957846784988683935812237 14984192544370756475929589)
                  ·
                    refine ⟨1404768051034758419618399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14984192544370756475929589 1404768051034758419618399)
                    ·
                      rfl

theorem cell22_4103664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_4103664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103664 prefixEnd_4103664 := by exact prefixLift 4103664
  have htrace : WordTrace (prefixWord ++ tailWord_4103664) baseStart_4103664 baseEnd_4103664 := by
    simpa [prefixWord, tailWord_4103664, baseEnd_4103664] using wordTrace_append hprefix tailTrace_4103664
  have hstable : (prefixWord ++ tailWord_4103664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103664).length < 2 ^ (prefixWord ++ tailWord_4103664).sum := by decide
  have hdescent : baseEnd_4103664 < baseStart_4103664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103679 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 4, 4]
def baseStart_4103679 : Nat := 118140960795 + 4103679 * 2 ^ 59
def prefixEnd_4103679 : Nat := 4983230072969 + 3 ^ 40 * 4103679 * 2
def baseEnd_4103679 : Nat := 1404773185841303380493353

theorem tailTrace_4103679 : CollatzResearch.WordTrace tailWord_4103679 prefixEnd_4103679 1404773185841303380493353 := by
  unfold tailWord_4103679
  simp only [CollatzResearch.WordTrace]
  refine ⟨149673469300079310420586091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99782312866719540280390727 149673469300079310420586091)
  ·
    refine ⟨224510203950118965630879137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149673469300079310420586091 224510203950118965630879137)
    ·
      refine ⟨168382652962589224223159353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224510203950118965630879137 168382652962589224223159353)
      ·
        refine ⟨126286989721941918167369515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168382652962589224223159353 126286989721941918167369515)
        ·
          refine ⟨189430484582912877251054273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126286989721941918167369515 189430484582912877251054273)
          ·
            refine ⟨142072863437184657938290705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189430484582912877251054273 142072863437184657938290705)
            ·
              refine ⟨106554647577888493453718029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142072863437184657938290705 106554647577888493453718029)
              ·
                refine ⟨39957992841708185045144261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106554647577888493453718029 39957992841708185045144261)
                ·
                  refine ⟨7492123657820284695964549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39957992841708185045144261 7492123657820284695964549)
                  ·
                    refine ⟨1404773185841303380493353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7492123657820284695964549 1404773185841303380493353)
                    ·
                      rfl

theorem cell22_4103679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_4103679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103679 prefixEnd_4103679 := by exact prefixLift 4103679
  have htrace : WordTrace (prefixWord ++ tailWord_4103679) baseStart_4103679 baseEnd_4103679 := by
    simpa [prefixWord, tailWord_4103679, baseEnd_4103679] using wordTrace_append hprefix tailTrace_4103679
  have hstable : (prefixWord ++ tailWord_4103679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103679).length < 2 ^ (prefixWord ++ tailWord_4103679).sum := by decide
  have hdescent : baseEnd_4103679 < baseStart_4103679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103713 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 2, 4]
def baseStart_4103713 : Nat := 118140960795 + 4103713 * 2 ^ 59
def prefixEnd_4103713 : Nat := 4983230072969 + 3 ^ 40 * 4103713 * 2
def baseEnd_4103713 : Nat := 1404784824736138625143249

theorem tailTrace_4103713 : CollatzResearch.WordTrace tailWord_4103713 prefixEnd_4103713 1404784824736138625143249 := by
  unfold tailWord_4103713
  simp only [CollatzResearch.WordTrace]
  refine ⟨149674709381956134227323793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99783139587970756151549195 149674709381956134227323793)
  ·
    refine ⟨112256032036467100670492845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149674709381956134227323793 112256032036467100670492845)
    ·
      refine ⟨42096012013675162751434817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112256032036467100670492845 42096012013675162751434817)
      ·
        refine ⟨31572009010256372063576113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42096012013675162751434817 31572009010256372063576113)
        ·
          refine ⟨23679006757692279047682085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31572009010256372063576113 23679006757692279047682085)
          ·
            refine ⟨4439813767067302321440391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23679006757692279047682085 4439813767067302321440391)
            ·
              refine ⟨6659720650600953482160587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439813767067302321440391 6659720650600953482160587)
              ·
                refine ⟨9989580975901430223240881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659720650600953482160587 9989580975901430223240881)
                ·
                  refine ⟨7492185731926072667430661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9989580975901430223240881 7492185731926072667430661)
                  ·
                    refine ⟨1404784824736138625143249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7492185731926072667430661 1404784824736138625143249)
                    ·
                      rfl

theorem cell22_4103713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_4103713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103713 prefixEnd_4103713 := by exact prefixLift 4103713
  have htrace : WordTrace (prefixWord ++ tailWord_4103713) baseStart_4103713 baseEnd_4103713 := by
    simpa [prefixWord, tailWord_4103713, baseEnd_4103713] using wordTrace_append hprefix tailTrace_4103713
  have hstable : (prefixWord ++ tailWord_4103713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103713).length < 2 ^ (prefixWord ++ tailWord_4103713).sum := by decide
  have hdescent : baseEnd_4103713 < baseStart_4103713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103743 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 3, 3]
def baseStart_4103743 : Nat := 118140960795 + 4103743 * 2 ^ 59
def prefixEnd_4103743 : Nat := 4983230072969 + 3 ^ 40 * 4103743 * 2
def baseEnd_4103743 : Nat := 1404795094349228546893157

theorem tailTrace_4103743 : CollatzResearch.WordTrace tailWord_4103743 prefixEnd_4103743 1404795094349228546893157 := by
  unfold tailWord_4103743
  simp only [CollatzResearch.WordTrace]
  refine ⟨149675803571847449350915883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99783869047898299567277255 149675803571847449350915883)
  ·
    refine ⟨224513705357771174026373825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149675803571847449350915883 224513705357771174026373825)
    ·
      refine ⟨168385279018328380519780369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224513705357771174026373825 168385279018328380519780369)
      ·
        refine ⟨126288959263746285389835277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168385279018328380519780369 126288959263746285389835277)
        ·
          refine ⟨47358359723904857021188229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126288959263746285389835277 47358359723904857021188229)
          ·
            refine ⟨8879692448232160691472793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47358359723904857021188229 8879692448232160691472793)
            ·
              refine ⟨6659769336174120518604595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8879692448232160691472793 6659769336174120518604595)
              ·
                refine ⟨9989654004261180777906893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659769336174120518604595 9989654004261180777906893)
                ·
                  refine ⟨3746120251597942791715085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9989654004261180777906893 3746120251597942791715085)
                  ·
                    refine ⟨1404795094349228546893157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3746120251597942791715085 1404795094349228546893157)
                    ·
                      rfl

theorem cell22_4103743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 3].length) (baseStart_4103743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103743 prefixEnd_4103743 := by exact prefixLift 4103743
  have htrace : WordTrace (prefixWord ++ tailWord_4103743) baseStart_4103743 baseEnd_4103743 := by
    simpa [prefixWord, tailWord_4103743, baseEnd_4103743] using wordTrace_append hprefix tailTrace_4103743
  have hstable : (prefixWord ++ tailWord_4103743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103743).length < 2 ^ (prefixWord ++ tailWord_4103743).sum := by decide
  have hdescent : baseEnd_4103743 < baseStart_4103743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103769 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_4103769 : Nat := 118140960795 + 4103769 * 2 ^ 59
def prefixEnd_4103769 : Nat := 4983230072969 + 3 ^ 40 * 4103769 * 2
def baseEnd_4103769 : Nat := 1404803994680573145743077

theorem tailTrace_4103769 : CollatzResearch.WordTrace tailWord_4103769 prefixEnd_4103769 1404803994680573145743077 := by
  unfold tailWord_4103769
  simp only [CollatzResearch.WordTrace]
  refine ⟨149676751869753255791362361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99784501246502170527574907 149676751869753255791362361)
  ·
    refine ⟨112257563902314941843521771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149676751869753255791362361 112257563902314941843521771)
    ·
      refine ⟨168386345853472412765282657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112257563902314941843521771 168386345853472412765282657)
      ·
        refine ⟨126289759390104309573961993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168386345853472412765282657 126289759390104309573961993)
        ·
          refine ⟨94717319542578232180471495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126289759390104309573961993 94717319542578232180471495)
          ·
            refine ⟨142075979313867348270707243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94717319542578232180471495 142075979313867348270707243)
            ·
              refine ⟨213113968970801022406060865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142075979313867348270707243 213113968970801022406060865)
              ·
                refine ⟨159835476728100766804545649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213113968970801022406060865 159835476728100766804545649)
                ·
                  refine ⟨119876607546075575103409237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159835476728100766804545649 119876607546075575103409237)
                  ·
                    refine ⟨1404803994680573145743077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119876607546075575103409237 1404803994680573145743077)
                    ·
                      rfl

theorem cell22_4103769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_4103769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103769 prefixEnd_4103769 := by exact prefixLift 4103769
  have htrace : WordTrace (prefixWord ++ tailWord_4103769) baseStart_4103769 baseEnd_4103769 := by
    simpa [prefixWord, tailWord_4103769, baseEnd_4103769] using wordTrace_append hprefix tailTrace_4103769
  have hstable : (prefixWord ++ tailWord_4103769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103769).length < 2 ^ (prefixWord ++ tailWord_4103769).sum := by decide
  have hdescent : baseEnd_4103769 < baseStart_4103769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103863 : List Nat := [1, 1, 3, 1, 5, 3, 1, 7]
def baseStart_4103863 : Nat := 118140960795 + 4103863 * 2 ^ 59
def prefixEnd_4103863 : Nat := 4983230072969 + 3 ^ 40 * 4103863 * 2
def baseEnd_4103863 : Nat := 156092908089065359321421

theorem tailTrace_4103863 : CollatzResearch.WordTrace tailWord_4103863 prefixEnd_4103863 156092908089065359321421 := by
  unfold tailWord_4103863
  simp only [CollatzResearch.WordTrace]
  refine ⟨149680180331412709845284243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99786786887608473230189495 149680180331412709845284243)
  ·
    refine ⟨224520270497119064767926365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149680180331412709845284243 224520270497119064767926365)
    ·
      refine ⟨84195101436419649287972387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 224520270497119064767926365 84195101436419649287972387)
      ·
        refine ⟨126292652154629473931958581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84195101436419649287972387 126292652154629473931958581)
        ·
          refine ⟨11839936139496513181121117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 126292652154629473931958581 11839936139496513181121117)
          ·
            refine ⟨4439976052311192442920419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11839936139496513181121117 4439976052311192442920419)
            ·
              refine ⟨6659964078466788664380629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439976052311192442920419 6659964078466788664380629)
              ·
                refine ⟨156092908089065359321421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6659964078466788664380629 156092908089065359321421)
                ·
                  rfl

theorem cell22_4103863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 7].length) (baseStart_4103863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103863 prefixEnd_4103863 := by exact prefixLift 4103863
  have htrace : WordTrace (prefixWord ++ tailWord_4103863) baseStart_4103863 baseEnd_4103863 := by
    simpa [prefixWord, tailWord_4103863, baseEnd_4103863] using wordTrace_append hprefix tailTrace_4103863
  have hstable : (prefixWord ++ tailWord_4103863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103863).length < 2 ^ (prefixWord ++ tailWord_4103863).sum := by decide
  have hdescent : baseEnd_4103863 < baseStart_4103863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103882 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 2, 4]
def baseStart_4103882 : Nat := 118140960795 + 4103882 * 2 ^ 59
def prefixEnd_4103882 : Nat := 4983230072969 + 3 ^ 40 * 4103882 * 2
def baseEnd_4103882 : Nat := 1404842676889878517667731

theorem tailTrace_4103882 : CollatzResearch.WordTrace tailWord_4103882 prefixEnd_4103882 1404842676889878517667731 := by
  unfold tailWord_4103882
  simp only [CollatzResearch.WordTrace]
  refine ⟨37420218329585969022556475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99787248878895917393483933 37420218329585969022556475)
  ·
    refine ⟨56130327494378953533834713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37420218329585969022556475 56130327494378953533834713)
    ·
      refine ⟨42097745620784215150376035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56130327494378953533834713 42097745620784215150376035)
      ·
        refine ⟨63146618431176322725564053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42097745620784215150376035 63146618431176322725564053)
        ·
          refine ⟨2959997738961390127760815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63146618431176322725564053 2959997738961390127760815)
          ·
            refine ⟨4439996608442085191641223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2959997738961390127760815 4439996608442085191641223)
            ·
              refine ⟨6659994912663127787461835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4439996608442085191641223 6659994912663127787461835)
              ·
                refine ⟨9989992368994691681192753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6659994912663127787461835 9989992368994691681192753)
                ·
                  refine ⟨7492494276746018760894565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9989992368994691681192753 7492494276746018760894565)
                  ·
                    refine ⟨1404842676889878517667731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7492494276746018760894565 1404842676889878517667731)
                    ·
                      rfl

theorem cell22_4103882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_4103882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103882 prefixEnd_4103882 := by exact prefixLift 4103882
  have htrace : WordTrace (prefixWord ++ tailWord_4103882) baseStart_4103882 baseEnd_4103882 := by
    simpa [prefixWord, tailWord_4103882, baseEnd_4103882] using wordTrace_append hprefix tailTrace_4103882
  have hstable : (prefixWord ++ tailWord_4103882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103882).length < 2 ^ (prefixWord ++ tailWord_4103882).sum := by decide
  have hdescent : baseEnd_4103882 < baseStart_4103882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103901 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_4103901 : Nat := 118140960795 + 4103901 * 2 ^ 59
def prefixEnd_4103901 : Nat := 4983230072969 + 3 ^ 40 * 4103901 * 2
def baseEnd_4103901 : Nat := 1404849180978168801442673

theorem tailTrace_4103901 : CollatzResearch.WordTrace tailWord_4103901 prefixEnd_4103901 1404849180978168801442673 := by
  unfold tailWord_4103901
  simp only [CollatzResearch.WordTrace]
  refine ⟨149681566305275042335167557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99787710870183361556778371 149681566305275042335167557)
  ·
    refine ⟨28065293682239070437843917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149681566305275042335167557 28065293682239070437843917)
    ·
      refine ⟨10524485130839651414191469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28065293682239070437843917 10524485130839651414191469)
      ·
        refine ⟨3946681924064869280321801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10524485130839651414191469 3946681924064869280321801)
        ·
          refine ⟨2960011443048651960241351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3946681924064869280321801 2960011443048651960241351)
          ·
            refine ⟨4440017164572977940362027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960011443048651960241351 4440017164572977940362027)
            ·
              refine ⟨6660025746859466910543041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4440017164572977940362027 6660025746859466910543041)
              ·
                refine ⟨4995019310144600182907281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6660025746859466910543041 4995019310144600182907281)
                ·
                  refine ⟨3746264482608450137180461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4995019310144600182907281 3746264482608450137180461)
                  ·
                    refine ⟨1404849180978168801442673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3746264482608450137180461 1404849180978168801442673)
                    ·
                      rfl

theorem cell22_4103901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_4103901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103901 prefixEnd_4103901 := by exact prefixLift 4103901
  have htrace : WordTrace (prefixWord ++ tailWord_4103901) baseStart_4103901 baseEnd_4103901 := by
    simpa [prefixWord, tailWord_4103901, baseEnd_4103901] using wordTrace_append hprefix tailTrace_4103901
  have hstable : (prefixWord ++ tailWord_4103901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103901).length < 2 ^ (prefixWord ++ tailWord_4103901).sum := by decide
  have hdescent : baseEnd_4103901 < baseStart_4103901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103912 : List Nat := [2, 1, 4, 1, 3, 1, 2, 4, 1, 3]
def baseStart_4103912 : Nat := 118140960795 + 4103912 * 2 ^ 59
def prefixEnd_4103912 : Nat := 4983230072969 + 3 ^ 40 * 4103912 * 2
def baseEnd_4103912 : Nat := 1404852946502968439417639

theorem tailTrace_4103912 : CollatzResearch.WordTrace tailWord_4103912 prefixEnd_4103912 1404852946502968439417639 := by
  unfold tailWord_4103912
  simp only [CollatzResearch.WordTrace]
  refine ⟨74840983754117595606908995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99787978338823460809211993 74840983754117595606908995)
  ·
    refine ⟨112261475631176393410363493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74840983754117595606908995 112261475631176393410363493)
    ·
      refine ⟨21049026680845573764443155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112261475631176393410363493 21049026680845573764443155)
      ·
        refine ⟨31573540021268360646664733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21049026680845573764443155 31573540021268360646664733)
        ·
          refine ⟨11840077507975635242499275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31573540021268360646664733 11840077507975635242499275)
          ·
            refine ⟨17760116261963452863748913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11840077507975635242499275 17760116261963452863748913)
            ·
              refine ⟨13320087196472589647811685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17760116261963452863748913 13320087196472589647811685)
              ·
                refine ⟨2497516349338610558964691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13320087196472589647811685 2497516349338610558964691)
                ·
                  refine ⟨3746274524007915838447037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497516349338610558964691 3746274524007915838447037)
                  ·
                    refine ⟨1404852946502968439417639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3746274524007915838447037 1404852946502968439417639)
                    ·
                      rfl

theorem cell22_4103912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_4103912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103912 prefixEnd_4103912 := by exact prefixLift 4103912
  have htrace : WordTrace (prefixWord ++ tailWord_4103912) baseStart_4103912 baseEnd_4103912 := by
    simpa [prefixWord, tailWord_4103912, baseEnd_4103912] using wordTrace_append hprefix tailTrace_4103912
  have hstable : (prefixWord ++ tailWord_4103912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103912).length < 2 ^ (prefixWord ++ tailWord_4103912).sum := by decide
  have hdescent : baseEnd_4103912 < baseStart_4103912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4103989 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 1, 4]
def baseStart_4103989 : Nat := 118140960795 + 4103989 * 2 ^ 59
def prefixEnd_4103989 : Nat := 4983230072969 + 3 ^ 40 * 4103989 * 2
def baseEnd_4103989 : Nat := 1404879305176565905242403

theorem tailTrace_4103989 : CollatzResearch.WordTrace tailWord_4103989 prefixEnd_4103989 1404879305176565905242403 := by
  unfold tailWord_4103989
  simp only [CollatzResearch.WordTrace]
  refine ⟨149684775928956233364371021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99789850619304155576247347 149684775928956233364371021)
  ·
    refine ⟨56131790973358587511639133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149684775928956233364371021 56131790973358587511639133)
    ·
      refine ⟨21049421615009470316864675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56131790973358587511639133 21049421615009470316864675)
      ·
        refine ⟨31574132422514205475297013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21049421615009470316864675 31574132422514205475297013)
        ·
          refine ⟨2960074914610706763309095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31574132422514205475297013 2960074914610706763309095)
          ·
            refine ⟨4440112371916060144963643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960074914610706763309095 4440112371916060144963643)
            ·
              refine ⟨6660168557874090217445465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4440112371916060144963643 6660168557874090217445465)
              ·
                refine ⟨4995126418405567663084099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6660168557874090217445465 4995126418405567663084099)
                ·
                  refine ⟨7492689627608351494626149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995126418405567663084099 7492689627608351494626149)
                  ·
                    refine ⟨1404879305176565905242403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7492689627608351494626149 1404879305176565905242403)
                    ·
                      rfl

theorem cell22_4103989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_4103989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4103989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4103989 prefixEnd_4103989 := by exact prefixLift 4103989
  have htrace : WordTrace (prefixWord ++ tailWord_4103989) baseStart_4103989 baseEnd_4103989 := by
    simpa [prefixWord, tailWord_4103989, baseEnd_4103989] using wordTrace_append hprefix tailTrace_4103989
  have hstable : (prefixWord ++ tailWord_4103989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4103989).length < 2 ^ (prefixWord ++ tailWord_4103989).sum := by decide
  have hdescent : baseEnd_4103989 < baseStart_4103989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4103989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104006 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_4104006 : Nat := 118140960795 + 4104006 * 2 ^ 59
def prefixEnd_4104006 : Nat := 4983230072969 + 3 ^ 40 * 4104006 * 2
def baseEnd_4104006 : Nat := 1404885124623983527567351

theorem tailTrace_4104006 : CollatzResearch.WordTrace tailWord_4104006 prefixEnd_4104006 1404885124623983527567351 := by
  unfold tailWord_4104006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4677668624059207664616871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99790263979929763511826581 4677668624059207664616871)
  ·
    refine ⟨7016502936088811496925307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4677668624059207664616871 7016502936088811496925307)
    ·
      refine ⟨10524754404133217245387961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7016502936088811496925307 10524754404133217245387961)
      ·
        refine ⟨7893565803099912934040971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10524754404133217245387961 7893565803099912934040971)
        ·
          refine ⟨11840348704649869401061457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7893565803099912934040971 11840348704649869401061457)
          ·
            refine ⟨8880261528487402050796093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11840348704649869401061457 8880261528487402050796093)
            ·
              refine ⟨3330098073182775769048535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8880261528487402050796093 3330098073182775769048535)
              ·
                refine ⟨4995147109774163653572803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3330098073182775769048535 4995147109774163653572803)
                ·
                  refine ⟨7492720664661245480359205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995147109774163653572803 7492720664661245480359205)
                  ·
                    refine ⟨1404885124623983527567351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7492720664661245480359205 1404885124623983527567351)
                    ·
                      rfl

theorem cell22_4104006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_4104006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104006 prefixEnd_4104006 := by exact prefixLift 4104006
  have htrace : WordTrace (prefixWord ++ tailWord_4104006) baseStart_4104006 baseEnd_4104006 := by
    simpa [prefixWord, tailWord_4104006, baseEnd_4104006] using wordTrace_append hprefix tailTrace_4104006
  have hstable : (prefixWord ++ tailWord_4104006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104006).length < 2 ^ (prefixWord ++ tailWord_4104006).sum := by decide
  have hdescent : baseEnd_4104006 < baseStart_4104006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104120 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 6, 3]
def baseStart_4104120 : Nat := 118140960795 + 4104120 * 2 ^ 59
def prefixEnd_4104120 : Nat := 4983230072969 + 3 ^ 40 * 4104120 * 2
def baseEnd_4104120 : Nat := 1404924149153725230217001

theorem tailTrace_4104120 : CollatzResearch.WordTrace tailWord_4104120 prefixEnd_4104120 1404924149153725230217001 := by
  unfold tailWord_4104120
  simp only [CollatzResearch.WordTrace]
  refine ⟨74844776945740821368694907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99793035927654428491593209 74844776945740821368694907)
  ·
    refine ⟨112267165418611232053042361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74844776945740821368694907 112267165418611232053042361)
    ·
      refine ⟨84200374063958424039781771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112267165418611232053042361 84200374063958424039781771)
      ·
        refine ⟨126300561095937636059672657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84200374063958424039781771 126300561095937636059672657)
        ·
          refine ⟨94725420821953227044754493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126300561095937636059672657 94725420821953227044754493)
          ·
            refine ⟨35522032808232460141782935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94725420821953227044754493 35522032808232460141782935)
            ·
              refine ⟨53283049212348690212674403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35522032808232460141782935 53283049212348690212674403)
              ·
                refine ⟨79924573818523035319011605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53283049212348690212674403 79924573818523035319011605)
                ·
                  refine ⟨3746464397743267280578669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79924573818523035319011605 3746464397743267280578669)
                  ·
                    refine ⟨1404924149153725230217001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3746464397743267280578669 1404924149153725230217001)
                    ·
                      rfl

theorem cell22_4104120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_4104120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104120 prefixEnd_4104120 := by exact prefixLift 4104120
  have htrace : WordTrace (prefixWord ++ tailWord_4104120) baseStart_4104120 baseEnd_4104120 := by
    simpa [prefixWord, tailWord_4104120, baseEnd_4104120] using wordTrace_append hprefix tailTrace_4104120
  have hstable : (prefixWord ++ tailWord_4104120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104120).length < 2 ^ (prefixWord ++ tailWord_4104120).sum := by decide
  have hdescent : baseEnd_4104120 < baseStart_4104120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104154 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 2, 3]
def baseStart_4104154 : Nat := 118140960795 + 4104154 * 2 ^ 59
def prefixEnd_4104154 : Nat := 4983230072969 + 3 ^ 40 * 4104154 * 2
def baseEnd_4104154 : Nat := 1404935788048560474866897

theorem tailTrace_4104154 : CollatzResearch.WordTrace tailWord_4104154 prefixEnd_4104154 1404935788048560474866897 := by
  unfold tailWord_4104154
  simp only [CollatzResearch.WordTrace]
  refine ⟨37422698493339616636031879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99793862648905644362751677 37422698493339616636031879)
  ·
    refine ⟨56134047740009424954047819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37422698493339616636031879 56134047740009424954047819)
    ·
      refine ⟨84201071610014137431071729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56134047740009424954047819 84201071610014137431071729)
      ·
        refine ⟨63150803707510603073303797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84201071610014137431071729 63150803707510603073303797)
        ·
          refine ⟨5920387847579119038122231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63150803707510603073303797 5920387847579119038122231)
          ·
            refine ⟨8880581771368678557183347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5920387847579119038122231 8880581771368678557183347)
            ·
              refine ⟨13320872657053017835775021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8880581771368678557183347 13320872657053017835775021)
              ·
                refine ⟨4995327246394881688415633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13320872657053017835775021 4995327246394881688415633)
                ·
                  refine ⟨3746495434796161266311725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4995327246394881688415633 3746495434796161266311725)
                  ·
                    refine ⟨1404935788048560474866897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3746495434796161266311725 1404935788048560474866897)
                    ·
                      rfl

theorem cell22_4104154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_4104154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104154 prefixEnd_4104154 := by exact prefixLift 4104154
  have htrace : WordTrace (prefixWord ++ tailWord_4104154) baseStart_4104154 baseEnd_4104154 := by
    simpa [prefixWord, tailWord_4104154, baseEnd_4104154] using wordTrace_append hprefix tailTrace_4104154
  have hstable : (prefixWord ++ tailWord_4104154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104154).length < 2 ^ (prefixWord ++ tailWord_4104154).sum := by decide
  have hdescent : baseEnd_4104154 < baseStart_4104154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104255 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 3, 5]
def baseStart_4104255 : Nat := 118140960795 + 4104255 * 2 ^ 59
def prefixEnd_4104255 : Nat := 4983230072969 + 3 ^ 40 * 4104255 * 2
def baseEnd_4104255 : Nat := 1404970362412629878091587

theorem tailTrace_4104255 : CollatzResearch.WordTrace tailWord_4104255 prefixEnd_4104255 1404970362412629878091587 := by
  unfold tailWord_4104255
  simp only [CollatzResearch.WordTrace]
  refine ⟨149694477745992560793554219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99796318497328373862369479 149694477745992560793554219)
  ·
    refine ⟨224541716618988841190331329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149694477745992560793554219 224541716618988841190331329)
    ·
      refine ⟨168406287464241630892748497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224541716618988841190331329 168406287464241630892748497)
      ·
        refine ⟨126304715598181223169561373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168406287464241630892748497 126304715598181223169561373)
        ·
          refine ⟨47364268349317958688585515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126304715598181223169561373 47364268349317958688585515)
          ·
            refine ⟨71046402523976938032878273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47364268349317958688585515 71046402523976938032878273)
            ·
              refine ⟨53284801892982703524658705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71046402523976938032878273 53284801892982703524658705)
              ·
                refine ⟨39963601419737027643494029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53284801892982703524658705 39963601419737027643494029)
                ·
                  refine ⟨14986350532401385366310261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39963601419737027643494029 14986350532401385366310261)
                  ·
                    refine ⟨1404970362412629878091587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14986350532401385366310261 1404970362412629878091587)
                    ·
                      rfl

theorem cell22_4104255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_4104255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104255 prefixEnd_4104255 := by exact prefixLift 4104255
  have htrace : WordTrace (prefixWord ++ tailWord_4104255) baseStart_4104255 baseEnd_4104255 := by
    simpa [prefixWord, tailWord_4104255, baseEnd_4104255] using wordTrace_append hprefix tailTrace_4104255
  have hstable : (prefixWord ++ tailWord_4104255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104255).length < 2 ^ (prefixWord ++ tailWord_4104255).sum := by decide
  have hdescent : baseEnd_4104255 < baseStart_4104255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104257 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 6]
def baseStart_4104257 : Nat := 118140960795 + 4104257 * 2 ^ 59
def prefixEnd_4104257 : Nat := 4983230072969 + 3 ^ 40 * 4104257 * 2
def baseEnd_4104257 : Nat := 468323682351167513180527

theorem tailTrace_4104257 : CollatzResearch.WordTrace tailWord_4104257 prefixEnd_4104257 468323682351167513180527 := by
  unfold tailWord_4104257
  simp only [CollatzResearch.WordTrace]
  refine ⟨149694550691985315135127025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99796367127990210090084683 149694550691985315135127025)
  ·
    refine ⟨112270913018988986351345269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149694550691985315135127025 112270913018988986351345269)
    ·
      refine ⟨10525398095530217470438619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112270913018988986351345269 10525398095530217470438619)
      ·
        refine ⟨15788097143295326205657929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10525398095530217470438619 15788097143295326205657929)
        ·
          refine ⟨11841072857471494654243447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15788097143295326205657929 11841072857471494654243447)
          ·
            refine ⟨17761609286207241981365171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11841072857471494654243447 17761609286207241981365171)
            ·
              refine ⟨26642413929310862972047757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17761609286207241981365171 26642413929310862972047757)
              ·
                refine ⟨9990905223491573614517909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26642413929310862972047757 9990905223491573614517909)
                ·
                  refine ⟨468323682351167513180527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9990905223491573614517909 468323682351167513180527)
                  ·
                    rfl

theorem cell22_4104257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_4104257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104257 prefixEnd_4104257 := by exact prefixLift 4104257
  have htrace : WordTrace (prefixWord ++ tailWord_4104257) baseStart_4104257 baseEnd_4104257 := by
    simpa [prefixWord, tailWord_4104257, baseEnd_4104257] using wordTrace_append hprefix tailTrace_4104257
  have hstable : (prefixWord ++ tailWord_4104257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104257).length < 2 ^ (prefixWord ++ tailWord_4104257).sum := by decide
  have hdescent : baseEnd_4104257 < baseStart_4104257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104377 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 5, 4]
def baseStart_4104377 : Nat := 118140960795 + 4104377 * 2 ^ 59
def prefixEnd_4104377 : Nat := 4983230072969 + 3 ^ 40 * 4104377 * 2
def baseEnd_4104377 : Nat := 1405012125505862226541213

theorem tailTrace_4104377 : CollatzResearch.WordTrace tailWord_4104377 prefixEnd_4104377 1405012125505862226541213 := by
  unfold tailWord_4104377
  simp only [CollatzResearch.WordTrace]
  refine ⟨149698927451550575629495385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99799284967700383752996923 149698927451550575629495385)
  ·
    refine ⟨112274195588662931722121539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149698927451550575629495385 112274195588662931722121539)
    ·
      refine ⟨168411293382994397583182309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112274195588662931722121539 168411293382994397583182309)
      ·
        refine ⟨31577117509311449546846683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168411293382994397583182309 31577117509311449546846683)
        ·
          refine ⟨47365676263967174320270025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31577117509311449546846683 47365676263967174320270025)
          ·
            refine ⟨35524257197975380740202519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47365676263967174320270025 35524257197975380740202519)
            ·
              refine ⟨53286385796963071110303779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35524257197975380740202519 53286385796963071110303779)
              ·
                refine ⟨79929578695444606665455669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53286385796963071110303779 79929578695444606665455669)
                ·
                  refine ⟨7493398002697931874886469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79929578695444606665455669 7493398002697931874886469)
                  ·
                    refine ⟨1405012125505862226541213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7493398002697931874886469 1405012125505862226541213)
                    ·
                      rfl

theorem cell22_4104377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_4104377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104377 prefixEnd_4104377 := by exact prefixLift 4104377
  have htrace : WordTrace (prefixWord ++ tailWord_4104377) baseStart_4104377 baseEnd_4104377 := by
    simpa [prefixWord, tailWord_4104377, baseEnd_4104377] using wordTrace_append hprefix tailTrace_4104377
  have hstable : (prefixWord ++ tailWord_4104377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104377).length < 2 ^ (prefixWord ++ tailWord_4104377).sum := by decide
  have hdescent : baseEnd_4104377 < baseStart_4104377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104394 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_4104394 : Nat := 118140960795 + 4104394 * 2 ^ 59
def prefixEnd_4104394 : Nat := 4983230072969 + 3 ^ 40 * 4104394 * 2
def baseEnd_4104394 : Nat := 1405017944953279848866161

theorem tailTrace_4104394 : CollatzResearch.WordTrace tailWord_4104394 prefixEnd_4104394 1405017944953279848866161 := by
  unfold tailWord_4104394
  simp only [CollatzResearch.WordTrace]
  refine ⟨37424886873122246883216059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99799698328325991688576157 37424886873122246883216059)
  ·
    refine ⟨56137330309683370324824089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37424886873122246883216059 56137330309683370324824089)
    ·
      refine ⟨42102997732262527743618067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56137330309683370324824089 42102997732262527743618067)
      ·
        refine ⟨63154496598393791615427101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42102997732262527743618067 63154496598393791615427101)
        ·
          refine ⟨23682936224397671855785163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63154496598393791615427101 23682936224397671855785163)
          ·
            refine ⟨35524404336596507783677745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23682936224397671855785163 35524404336596507783677745)
            ·
              refine ⟨26643303252447380837758309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35524404336596507783677745 26643303252447380837758309)
              ·
                refine ⟨4995619359833883907079683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26643303252447380837758309 4995619359833883907079683)
                ·
                  refine ⟨7493429039750825860619525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995619359833883907079683 7493429039750825860619525)
                  ·
                    refine ⟨1405017944953279848866161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7493429039750825860619525 1405017944953279848866161)
                    ·
                      rfl

theorem cell22_4104394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_4104394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104394 prefixEnd_4104394 := by exact prefixLift 4104394
  have htrace : WordTrace (prefixWord ++ tailWord_4104394) baseStart_4104394 baseEnd_4104394 := by
    simpa [prefixWord, tailWord_4104394, baseEnd_4104394] using wordTrace_append hprefix tailTrace_4104394
  have hstable : (prefixWord ++ tailWord_4104394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104394).length < 2 ^ (prefixWord ++ tailWord_4104394).sum := by decide
  have hdescent : baseEnd_4104394 < baseStart_4104394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104409 : List Nat := [1, 2, 1, 2, 3, 1, 3, 5, 4]
def baseStart_4104409 : Nat := 118140960795 + 4104409 * 2 ^ 59
def prefixEnd_4104409 : Nat := 4983230072969 + 3 ^ 40 * 4104409 * 2
def baseEnd_4104409 : Nat := 468341026586608269913705

theorem tailTrace_4104409 : CollatzResearch.WordTrace tailWord_4104409 prefixEnd_4104409 468341026586608269913705 := by
  unfold tailWord_4104409
  simp only [CollatzResearch.WordTrace]
  refine ⟨149700094587434645094660281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99800063058289763396440187 149700094587434645094660281)
  ·
    refine ⟨112275070940575983820995211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149700094587434645094660281 112275070940575983820995211)
    ·
      refine ⟨168412606410863975731492817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112275070940575983820995211 168412606410863975731492817)
      ·
        refine ⟨126309454808147981798619613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168412606410863975731492817 126309454808147981798619613)
        ·
          refine ⟨47366045553055493174482355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126309454808147981798619613 47366045553055493174482355)
          ·
            refine ⟨71049068329583239761723533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47366045553055493174482355 71049068329583239761723533)
            ·
              refine ⟨26643400623593714910646325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71049068329583239761723533 26643400623593714910646325)
              ·
                refine ⟨2497818808461910772873093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26643400623593714910646325 2497818808461910772873093)
                ·
                  refine ⟨468341026586608269913705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2497818808461910772873093 468341026586608269913705)
                  ·
                    rfl

theorem cell22_4104409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 4].length) (baseStart_4104409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104409 prefixEnd_4104409 := by exact prefixLift 4104409
  have htrace : WordTrace (prefixWord ++ tailWord_4104409) baseStart_4104409 baseEnd_4104409 := by
    simpa [prefixWord, tailWord_4104409, baseEnd_4104409] using wordTrace_append hprefix tailTrace_4104409
  have hstable : (prefixWord ++ tailWord_4104409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104409).length < 2 ^ (prefixWord ++ tailWord_4104409).sum := by decide
  have hdescent : baseEnd_4104409 < baseStart_4104409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104469 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 5, 3]
def baseStart_4104469 : Nat := 118140960795 + 4104469 * 2 ^ 59
def prefixEnd_4104469 : Nat := 4983230072969 + 3 ^ 40 * 4104469 * 2
def baseEnd_4104469 : Nat := 1405043618986004653240931

theorem tailTrace_4104469 : CollatzResearch.WordTrace tailWord_4104469 prefixEnd_4104469 1405043618986004653240931 := by
  unfold tailWord_4104469
  simp only [CollatzResearch.WordTrace]
  refine ⟨149702282967217275341844461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99801521978144850227896307 149702282967217275341844461)
  ·
    refine ⟨56138356112706478253191673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149702282967217275341844461 56138356112706478253191673)
    ·
      refine ⟨42103767084529858689893755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56138356112706478253191673 42103767084529858689893755)
      ·
        refine ⟨63155650626794788034840633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42103767084529858689893755 63155650626794788034840633)
        ·
          refine ⟨47366737970096091026130475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63155650626794788034840633 47366737970096091026130475)
          ·
            refine ⟨71050106955144136539195713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47366737970096091026130475 71050106955144136539195713)
            ·
              refine ⟨53287580216358102404396785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71050106955144136539195713 53287580216358102404396785)
              ·
                refine ⟨39965685162268576803297589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53287580216358102404396785 39965685162268576803297589)
                ·
                  refine ⟨3746782983962679075309149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39965685162268576803297589 3746782983962679075309149)
                  ·
                    refine ⟨1405043618986004653240931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3746782983962679075309149 1405043618986004653240931)
                    ·
                      rfl

theorem cell22_4104469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_4104469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104469 prefixEnd_4104469 := by exact prefixLift 4104469
  have htrace : WordTrace (prefixWord ++ tailWord_4104469) baseStart_4104469 baseEnd_4104469 := by
    simpa [prefixWord, tailWord_4104469, baseEnd_4104469] using wordTrace_append hprefix tailTrace_4104469
  have hstable : (prefixWord ++ tailWord_4104469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104469).length < 2 ^ (prefixWord ++ tailWord_4104469).sum := by decide
  have hdescent : baseEnd_4104469 < baseStart_4104469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104499 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 5]
def baseStart_4104499 : Nat := 118140960795 + 4104499 * 2 ^ 59
def prefixEnd_4104499 : Nat := 4983230072969 + 3 ^ 40 * 4104499 * 2
def baseEnd_4104499 : Nat := 468351296199698191663613

theorem tailTrace_4104499 : CollatzResearch.WordTrace tailWord_4104499 prefixEnd_4104499 468351296199698191663613 := by
  unfold tailWord_4104499
  simp only [CollatzResearch.WordTrace]
  refine ⟨149703377157108590465436551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99802251438072393643624367 149703377157108590465436551)
  ·
    refine ⟨224555065735662885698154827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149703377157108590465436551 224555065735662885698154827)
    ·
      refine ⟨336832598603494328547232241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224555065735662885698154827 336832598603494328547232241)
      ·
        refine ⟨252624448952620746410424181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336832598603494328547232241 252624448952620746410424181)
        ·
          refine ⟨23683542089308194975977267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 252624448952620746410424181 23683542089308194975977267)
          ·
            refine ⟨35525313133962292463965901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23683542089308194975977267 35525313133962292463965901)
            ·
              refine ⟨13321992425235859673987213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35525313133962292463965901 13321992425235859673987213)
              ·
                refine ⟨4995747159463447377745205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13321992425235859673987213 4995747159463447377745205)
                ·
                  refine ⟨468351296199698191663613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4995747159463447377745205 468351296199698191663613)
                  ·
                    rfl

theorem cell22_4104499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 5].length) (baseStart_4104499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104499 prefixEnd_4104499 := by exact prefixLift 4104499
  have htrace : WordTrace (prefixWord ++ tailWord_4104499) baseStart_4104499 baseEnd_4104499 := by
    simpa [prefixWord, tailWord_4104499, baseEnd_4104499] using wordTrace_append hprefix tailTrace_4104499
  have hstable : (prefixWord ++ tailWord_4104499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104499).length < 2 ^ (prefixWord ++ tailWord_4104499).sum := by decide
  have hdescent : baseEnd_4104499 < baseStart_4104499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104527 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 10]
def baseStart_4104527 : Nat := 118140960795 + 4104527 * 2 ^ 59
def prefixEnd_4104527 : Nat := 4983230072969 + 3 ^ 40 * 4104527 * 2
def baseEnd_4104527 : Nat := 468354491190437278430251

theorem tailTrace_4104527 : CollatzResearch.WordTrace tailWord_4104527 prefixEnd_4104527 468354491190437278430251 := by
  unfold tailWord_4104527
  simp only [CollatzResearch.WordTrace]
  refine ⟨149704398401007151247455835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99802932267338100831637223 149704398401007151247455835)
  ·
    refine ⟨224556597601510726871183753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149704398401007151247455835 224556597601510726871183753)
    ·
      refine ⟨168417448201133045153387815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224556597601510726871183753 168417448201133045153387815)
      ·
        refine ⟨252626172301699567730081723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168417448201133045153387815 252626172301699567730081723)
        ·
          refine ⟨378939258452549351595122585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252626172301699567730081723 378939258452549351595122585)
          ·
            refine ⟨284204443839412013696341939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378939258452549351595122585 284204443839412013696341939)
            ·
              refine ⟨426306665759118020544512909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284204443839412013696341939 426306665759118020544512909)
              ·
                refine ⟨159864999659669257704192341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426306665759118020544512909 159864999659669257704192341)
                ·
                  refine ⟨468354491190437278430251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 159864999659669257704192341 468354491190437278430251)
                  ·
                    rfl

theorem cell22_4104527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 10].length) (baseStart_4104527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104527 prefixEnd_4104527 := by exact prefixLift 4104527
  have htrace : WordTrace (prefixWord ++ tailWord_4104527) baseStart_4104527 baseEnd_4104527 := by
    simpa [prefixWord, tailWord_4104527, baseEnd_4104527] using wordTrace_append hprefix tailTrace_4104527
  have hstable : (prefixWord ++ tailWord_4104527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104527).length < 2 ^ (prefixWord ++ tailWord_4104527).sum := by decide
  have hdescent : baseEnd_4104527 < baseStart_4104527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104546 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_4104546 : Nat := 118140960795 + 4104546 * 2 ^ 59
def prefixEnd_4104546 : Nat := 4983230072969 + 3 ^ 40 * 4104546 * 2
def baseEnd_4104546 : Nat := 1405069977659602119065695

theorem tailTrace_4104546 : CollatzResearch.WordTrace tailWord_4104546 prefixEnd_4104546 1405069977659602119065695 := by
  unfold tailWord_4104546
  simp only [CollatzResearch.WordTrace]
  refine ⟨37426272846984579373099373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99803394258625544994931661 37426272846984579373099373)
  ·
    refine ⟨14034852317619217264912265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37426272846984579373099373 14034852317619217264912265)
    ·
      refine ⟨10526139238214412948684199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14034852317619217264912265 10526139238214412948684199)
      ·
        refine ⟨15789208857321619423026299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10526139238214412948684199 15789208857321619423026299)
        ·
          refine ⟨23683813285982429134539449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15789208857321619423026299 23683813285982429134539449)
          ·
            refine ⟨17762859964486821850904587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23683813285982429134539449 17762859964486821850904587)
            ·
              refine ⟨26644289946730232776356881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17762859964486821850904587 26644289946730232776356881)
              ·
                refine ⟨19983217460047674582267661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26644289946730232776356881 19983217460047674582267661)
                ·
                  refine ⟨7493706547517877968350373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19983217460047674582267661 7493706547517877968350373)
                  ·
                    refine ⟨1405069977659602119065695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7493706547517877968350373 1405069977659602119065695)
                    ·
                      rfl

theorem cell22_4104546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_4104546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104546 prefixEnd_4104546 := by exact prefixLift 4104546
  have htrace : WordTrace (prefixWord ++ tailWord_4104546) baseStart_4104546 baseEnd_4104546 := by
    simpa [prefixWord, tailWord_4104546, baseEnd_4104546] using wordTrace_append hprefix tailTrace_4104546
  have hstable : (prefixWord ++ tailWord_4104546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104546).length < 2 ^ (prefixWord ++ tailWord_4104546).sum := by decide
  have hdescent : baseEnd_4104546 < baseStart_4104546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104610 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_4104610 : Nat := 118140960795 + 4104610 * 2 ^ 59
def prefixEnd_4104610 : Nat := 4983230072969 + 3 ^ 40 * 4104610 * 2
def baseEnd_4104610 : Nat := 1405091886167527285465499

theorem tailTrace_4104610 : CollatzResearch.WordTrace tailWord_4104610 prefixEnd_4104610 1405091886167527285465499 := by
  unfold tailWord_4104610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37426856414926614105681821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99804950439804304281818189 37426856414926614105681821)
  ·
    refine ⟨14035071155597480289630683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37426856414926614105681821 14035071155597480289630683)
    ·
      refine ⟨21052606733396220434446025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14035071155597480289630683 21052606733396220434446025)
      ·
        refine ⟨15789455050047165325834519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21052606733396220434446025 15789455050047165325834519)
        ·
          refine ⟨23684182575070747988751779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15789455050047165325834519 23684182575070747988751779)
          ·
            refine ⟨35526273862606121983127669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23684182575070747988751779 35526273862606121983127669)
            ·
              refine ⟨3330588174619323935918219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35526273862606121983127669 3330588174619323935918219)
              ·
                refine ⟨4995882261928985903877329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3330588174619323935918219 4995882261928985903877329)
                ·
                  refine ⟨3746911696446739427907997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4995882261928985903877329 3746911696446739427907997)
                  ·
                    refine ⟨1405091886167527285465499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3746911696446739427907997 1405091886167527285465499)
                    ·
                      rfl

theorem cell22_4104610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_4104610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104610 prefixEnd_4104610 := by exact prefixLift 4104610
  have htrace : WordTrace (prefixWord ++ tailWord_4104610) baseStart_4104610 baseEnd_4104610 := by
    simpa [prefixWord, tailWord_4104610, baseEnd_4104610] using wordTrace_append hprefix tailTrace_4104610
  have hstable : (prefixWord ++ tailWord_4104610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104610).length < 2 ^ (prefixWord ++ tailWord_4104610).sum := by decide
  have hdescent : baseEnd_4104610 < baseStart_4104610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104649 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_4104649 : Nat := 118140960795 + 4104649 * 2 ^ 59
def prefixEnd_4104649 : Nat := 4983230072969 + 3 ^ 40 * 4104649 * 2
def baseEnd_4104649 : Nat := 1405105236664544183740379

theorem tailTrace_4104649 : CollatzResearch.WordTrace tailWord_4104649 prefixEnd_4104649 1405105236664544183740379 := by
  unfold tailWord_4104649
  simp only [CollatzResearch.WordTrace]
  refine ⟨149708848106565166083397001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99805898737710110722264667 149708848106565166083397001)
  ·
    refine ⟨112281636079923874562547751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149708848106565166083397001 112281636079923874562547751)
    ·
      refine ⟨168422454119885811843821627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112281636079923874562547751 168422454119885811843821627)
      ·
        refine ⟨252633681179828717765732441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168422454119885811843821627 252633681179828717765732441)
        ·
          refine ⟨189475260884871538324299331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252633681179828717765732441 189475260884871538324299331)
          ·
            refine ⟨284212891327307307486448997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189475260884871538324299331 284212891327307307486448997)
            ·
              refine ⟨53289917123870120153709187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 284212891327307307486448997 53289917123870120153709187)
              ·
                refine ⟨79934875685805180230563781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53289917123870120153709187 79934875685805180230563781)
                ·
                  refine ⟨14987789191088471293230709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79934875685805180230563781 14987789191088471293230709)
                  ·
                    refine ⟨1405105236664544183740379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14987789191088471293230709 1405105236664544183740379)
                    ·
                      rfl

theorem cell22_4104649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_4104649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104649 prefixEnd_4104649 := by exact prefixLift 4104649
  have htrace : WordTrace (prefixWord ++ tailWord_4104649) baseStart_4104649 baseEnd_4104649 := by
    simpa [prefixWord, tailWord_4104649, baseEnd_4104649] using wordTrace_append hprefix tailTrace_4104649
  have hstable : (prefixWord ++ tailWord_4104649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104649).length < 2 ^ (prefixWord ++ tailWord_4104649).sum := by decide
  have hdescent : baseEnd_4104649 < baseStart_4104649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104664 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 2, 8]
def baseStart_4104664 : Nat := 118140960795 + 4104664 * 2 ^ 59
def prefixEnd_4104664 : Nat := 4983230072969 + 3 ^ 40 * 4104664 * 2
def baseEnd_4104664 : Nat := 1405110371471089144615333

theorem tailTrace_4104664 : CollatzResearch.WordTrace tailWord_4104664 prefixEnd_4104664 1405110371471089144615333 := by
  unfold tailWord_4104664
  simp only [CollatzResearch.WordTrace]
  refine ⟨74854697600755411822596523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99806263467673882430128697 74854697600755411822596523)
  ·
    refine ⟨112282046401133117733894785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74854697600755411822596523 112282046401133117733894785)
    ·
      refine ⟨84211534800849838300421089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112282046401133117733894785 84211534800849838300421089)
      ·
        refine ⟨63158651100637378725315817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84211534800849838300421089 63158651100637378725315817)
        ·
          refine ⟨47368988325478034043986863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63158651100637378725315817 47368988325478034043986863)
          ·
            refine ⟨71053482488217051065980295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47368988325478034043986863 71053482488217051065980295)
            ·
              refine ⟨106580223732325576598970443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71053482488217051065980295 106580223732325576598970443)
              ·
                refine ⟨159870335598488364898455665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106580223732325576598970443 159870335598488364898455665)
                ·
                  refine ⟨119902751698866273673841749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159870335598488364898455665 119902751698866273673841749)
                  ·
                    refine ⟨1405110371471089144615333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119902751698866273673841749 1405110371471089144615333)
                    ·
                      rfl

theorem cell22_4104664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_4104664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104664 prefixEnd_4104664 := by exact prefixLift 4104664
  have htrace : WordTrace (prefixWord ++ tailWord_4104664) baseStart_4104664 baseEnd_4104664 := by
    simpa [prefixWord, tailWord_4104664, baseEnd_4104664] using wordTrace_append hprefix tailTrace_4104664
  have hstable : (prefixWord ++ tailWord_4104664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104664).length < 2 ^ (prefixWord ++ tailWord_4104664).sum := by decide
  have hdescent : baseEnd_4104664 < baseStart_4104664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104681 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 1, 4]
def baseStart_4104681 : Nat := 118140960795 + 4104681 * 2 ^ 59
def prefixEnd_4104681 : Nat := 4983230072969 + 3 ^ 40 * 4104681 * 2
def baseEnd_4104681 : Nat := 1405116190918506766940281

theorem tailTrace_4104681 : CollatzResearch.WordTrace tailWord_4104681 prefixEnd_4104681 1405116190918506766940281 := by
  unfold tailWord_4104681
  simp only [CollatzResearch.WordTrace]
  refine ⟨149710015242449235548561897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99806676828299490365707931 149710015242449235548561897)
  ·
    refine ⟨112282511431836926661421423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149710015242449235548561897 112282511431836926661421423)
    ·
      refine ⟨168423767147755389992132135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112282511431836926661421423 168423767147755389992132135)
      ·
        refine ⟨252635650721633084988198203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168423767147755389992132135 252635650721633084988198203)
        ·
          refine ⟨378953476082449627482297305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252635650721633084988198203 378953476082449627482297305)
          ·
            refine ⟨284215107061837220611722979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378953476082449627482297305 284215107061837220611722979)
            ·
              refine ⟨426322660592755830917584469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284215107061837220611722979 426322660592755830917584469)
              ·
                refine ⟨4995968678821357393565443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 426322660592755830917584469 4995968678821357393565443)
                ·
                  refine ⟨7493953018232036090348165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4995968678821357393565443 7493953018232036090348165)
                  ·
                    refine ⟨1405116190918506766940281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7493953018232036090348165 1405116190918506766940281)
                    ·
                      rfl

theorem cell22_4104681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_4104681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104681 prefixEnd_4104681 := by exact prefixLift 4104681
  have htrace : WordTrace (prefixWord ++ tailWord_4104681) baseStart_4104681 baseEnd_4104681 := by
    simpa [prefixWord, tailWord_4104681, baseEnd_4104681] using wordTrace_append hprefix tailTrace_4104681
  have hstable : (prefixWord ++ tailWord_4104681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104681).length < 2 ^ (prefixWord ++ tailWord_4104681).sum := by decide
  have hdescent : baseEnd_4104681 < baseStart_4104681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104706 : List Nat := [3, 4, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_4104706 : Nat := 118140960795 + 4104706 * 2 ^ 59
def prefixEnd_4104706 : Nat := 4983230072969 + 3 ^ 40 * 4104706 * 2
def baseEnd_4104706 : Nat := 1405124748929415035065205

theorem tailTrace_4104706 : CollatzResearch.WordTrace tailWord_4104706 prefixEnd_4104706 1405124748929415035065205 := by
  unfold tailWord_4104706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37427731766839666204555493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99807284711572443212147981 37427731766839666204555493)
  ·
    refine ⟨7017699706282437413354155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37427731766839666204555493 7017699706282437413354155)
    ·
      refine ⟨10526549559423656120031233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7017699706282437413354155 10526549559423656120031233)
      ·
        refine ⟨7894912169567742090023425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10526549559423656120031233 7894912169567742090023425)
        ·
          refine ⟨5921184127175806567517569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7894912169567742090023425 5921184127175806567517569)
          ·
            refine ⟨4440888095381854925638177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5921184127175806567517569 4440888095381854925638177)
            ·
              refine ⟨3330666071536391194228633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4440888095381854925638177 3330666071536391194228633)
              ·
                refine ⟨2497999553652293395671475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3330666071536391194228633 2497999553652293395671475)
                ·
                  refine ⟨3746999330478440093507213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2497999553652293395671475 3746999330478440093507213)
                  ·
                    refine ⟨1405124748929415035065205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3746999330478440093507213 1405124748929415035065205)
                    ·
                      rfl

theorem cell22_4104706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_4104706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104706 prefixEnd_4104706 := by exact prefixLift 4104706
  have htrace : WordTrace (prefixWord ++ tailWord_4104706) baseStart_4104706 baseEnd_4104706 := by
    simpa [prefixWord, tailWord_4104706, baseEnd_4104706] using wordTrace_append hprefix tailTrace_4104706
  have hstable : (prefixWord ++ tailWord_4104706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104706).length < 2 ^ (prefixWord ++ tailWord_4104706).sum := by decide
  have hdescent : baseEnd_4104706 < baseStart_4104706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104728 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 1, 5]
def baseStart_4104728 : Nat := 118140960795 + 4104728 * 2 ^ 59
def prefixEnd_4104728 : Nat := 4983230072969 + 3 ^ 40 * 4104728 * 2
def baseEnd_4104728 : Nat := 1405132279979014311015137

theorem tailTrace_4104728 : CollatzResearch.WordTrace tailWord_4104728 prefixEnd_4104728 1405132279979014311015137 := by
  unfold tailWord_4104728
  simp only [CollatzResearch.WordTrace]
  refine ⟨74855864736639481287761419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99807819648852641717015225 74855864736639481287761419)
  ·
    refine ⟨112283797104959221931642129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74855864736639481287761419 112283797104959221931642129)
    ·
      refine ⟨84212847828719416448731597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112283797104959221931642129 84212847828719416448731597)
      ·
        refine ⟨31579817935769781168274349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84212847828719416448731597 31579817935769781168274349)
        ·
          refine ⟨11842431725913667938102881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31579817935769781168274349 11842431725913667938102881)
          ·
            refine ⟨8881823794435250953577161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11842431725913667938102881 8881823794435250953577161)
            ·
              refine ⟨6661367845826438215182871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8881823794435250953577161 6661367845826438215182871)
              ·
                refine ⟨9992051768739657322774307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661367845826438215182871 9992051768739657322774307)
                ·
                  refine ⟨14988077653109485984161461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9992051768739657322774307 14988077653109485984161461)
                  ·
                    refine ⟨1405132279979014311015137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14988077653109485984161461 1405132279979014311015137)
                    ·
                      rfl

theorem cell22_4104728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_4104728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104728 prefixEnd_4104728 := by exact prefixLift 4104728
  have htrace : WordTrace (prefixWord ++ tailWord_4104728) baseStart_4104728 baseEnd_4104728 := by
    simpa [prefixWord, tailWord_4104728, baseEnd_4104728] using wordTrace_append hprefix tailTrace_4104728
  have hstable : (prefixWord ++ tailWord_4104728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104728).length < 2 ^ (prefixWord ++ tailWord_4104728).sum := by decide
  have hdescent : baseEnd_4104728 < baseStart_4104728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104749 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4104749 : Nat := 118140960795 + 4104749 * 2 ^ 59
def prefixEnd_4104749 : Nat := 4983230072969 + 3 ^ 40 * 4104749 * 2
def baseEnd_4104749 : Nat := 1405139468708177256240073

theorem tailTrace_4104749 : CollatzResearch.WordTrace tailWord_4104749 prefixEnd_4104749 1405139468708177256240073 := by
  unfold tailWord_4104749
  simp only [CollatzResearch.WordTrace]
  refine ⟨149712495406202883162037301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99808330270801922108024867 149712495406202883162037301)
  ·
    refine ⟨14035546444331520296440997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149712495406202883162037301 14035546444331520296440997)
    ·
      refine ⟨2631664958312160055582687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14035546444331520296440997 2631664958312160055582687)
      ·
        refine ⟨3947497437468240083374031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2631664958312160055582687 3947497437468240083374031)
        ·
          refine ⟨5921246156202360125061047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3947497437468240083374031 5921246156202360125061047)
          ·
            refine ⟨8881869234303540187591571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921246156202360125061047 8881869234303540187591571)
            ·
              refine ⟨13322803851455310281387357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8881869234303540187591571 13322803851455310281387357)
              ·
                refine ⟨4996051444295741355520259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13322803851455310281387357 4996051444295741355520259)
                ·
                  refine ⟨7494077166443612033280389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996051444295741355520259 7494077166443612033280389)
                  ·
                    refine ⟨1405139468708177256240073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7494077166443612033280389 1405139468708177256240073)
                    ·
                      rfl

theorem cell22_4104749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4104749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104749 prefixEnd_4104749 := by exact prefixLift 4104749
  have htrace : WordTrace (prefixWord ++ tailWord_4104749) baseStart_4104749 baseEnd_4104749 := by
    simpa [prefixWord, tailWord_4104749, baseEnd_4104749] using wordTrace_append hprefix tailTrace_4104749
  have hstable : (prefixWord ++ tailWord_4104749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104749).length < 2 ^ (prefixWord ++ tailWord_4104749).sum := by decide
  have hdescent : baseEnd_4104749 < baseStart_4104749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104758 : List Nat := [5, 1, 2, 1, 2, 2, 9]
def baseStart_4104758 : Nat := 118140960795 + 4104758 * 2 ^ 59
def prefixEnd_4104758 : Nat := 4983230072969 + 3 ^ 40 * 4104758 * 2
def baseEnd_4104758 : Nat := 52042316651559416028335

theorem tailTrace_4104758 : CollatzResearch.WordTrace tailWord_4104758 prefixEnd_4104758 52042316651559416028335 := by
  unfold tailWord_4104758
  simp only [CollatzResearch.WordTrace]
  refine ⟨9357051478948142356194683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99808549108780185132743285 9357051478948142356194683)
  ·
    refine ⟨14035577218422213534292025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9357051478948142356194683 14035577218422213534292025)
    ·
      refine ⟨10526682913816660150719019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14035577218422213534292025 10526682913816660150719019)
      ·
        refine ⟨15790024370724990226078529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10526682913816660150719019 15790024370724990226078529)
        ·
          refine ⟨11842518278043742669558897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15790024370724990226078529 11842518278043742669558897)
          ·
            refine ⟨8881888708532807002169173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11842518278043742669558897 8881888708532807002169173)
            ·
              refine ⟨52042316651559416028335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8881888708532807002169173 52042316651559416028335)
              ·
                rfl

theorem cell22_4104758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 9].length) (baseStart_4104758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104758 prefixEnd_4104758 := by exact prefixLift 4104758
  have htrace : WordTrace (prefixWord ++ tailWord_4104758) baseStart_4104758 baseEnd_4104758 := by
    simpa [prefixWord, tailWord_4104758, baseEnd_4104758] using wordTrace_append hprefix tailTrace_4104758
  have hstable : (prefixWord ++ tailWord_4104758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104758).length < 2 ^ (prefixWord ++ tailWord_4104758).sum := by decide
  have hdescent : baseEnd_4104758 < baseStart_4104758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104773 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 3, 3]
def baseStart_4104773 : Nat := 118140960795 + 4104773 * 2 ^ 59
def prefixEnd_4104773 : Nat := 4983230072969 + 3 ^ 40 * 4104773 * 2
def baseEnd_4104773 : Nat := 1405147684398649193639999

theorem tailTrace_4104773 : CollatzResearch.WordTrace tailWord_4104773 prefixEnd_4104773 1405147684398649193639999 := by
  unfold tailWord_4104773
  simp only [CollatzResearch.WordTrace]
  refine ⟨149713370758115935260910973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99808913838743956840607315 149713370758115935260910973)
  ·
    refine ⟨56142514034293475722841615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149713370758115935260910973 56142514034293475722841615)
    ·
      refine ⟨84213771051440213584262423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56142514034293475722841615 84213771051440213584262423)
      ·
        refine ⟨126320656577160320376393635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84213771051440213584262423 126320656577160320376393635)
        ·
          refine ⟨189480984865740480564590453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126320656577160320376393635 189480984865740480564590453)
          ·
            refine ⟨17763842331163170052930355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 189480984865740480564590453 17763842331163170052930355)
            ·
              refine ⟨26645763496744755079395533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17763842331163170052930355 26645763496744755079395533)
              ·
                refine ⟨9992161311279283154773325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26645763496744755079395533 9992161311279283154773325)
                ·
                  refine ⟨3747060491729731183039997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9992161311279283154773325 3747060491729731183039997)
                  ·
                    refine ⟨1405147684398649193639999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3747060491729731183039997 1405147684398649193639999)
                    ·
                      rfl

theorem cell22_4104773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_4104773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104773 prefixEnd_4104773 := by exact prefixLift 4104773
  have htrace : WordTrace (prefixWord ++ tailWord_4104773) baseStart_4104773 baseEnd_4104773 := by
    simpa [prefixWord, tailWord_4104773, baseEnd_4104773] using wordTrace_append hprefix tailTrace_4104773
  have hstable : (prefixWord ++ tailWord_4104773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104773).length < 2 ^ (prefixWord ++ tailWord_4104773).sum := by decide
  have hdescent : baseEnd_4104773 < baseStart_4104773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104798 : List Nat := [4, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4104798 : Nat := 118140960795 + 4104798 * 2 ^ 59
def prefixEnd_4104798 : Nat := 4983230072969 + 3 ^ 40 * 4104798 * 2
def baseEnd_4104798 : Nat := 468385414136519153921641

theorem tailTrace_4104798 : CollatzResearch.WordTrace tailWord_4104798 prefixEnd_4104798 468385414136519153921641 := by
  unfold tailWord_4104798
  simp only [CollatzResearch.WordTrace]
  refine ⟨18714285322878170566321381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99809521722016909687047365 18714285322878170566321381)
  ·
    refine ⟨3508928498039656981185259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18714285322878170566321381 3508928498039656981185259)
    ·
      refine ⟨5263392747059485471777889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3508928498039656981185259 5263392747059485471777889)
      ·
        refine ⟨3947544560294614103833417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5263392747059485471777889 3947544560294614103833417)
        ·
          refine ⟨2960658420220960577875063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3947544560294614103833417 2960658420220960577875063)
          ·
            refine ⟨4440987630331440866812595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960658420220960577875063 4440987630331440866812595)
            ·
              refine ⟨6661481445497161300218893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4440987630331440866812595 6661481445497161300218893)
              ·
                refine ⟨2498055542061435487582085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6661481445497161300218893 2498055542061435487582085)
                ·
                  refine ⟨468385414136519153921641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2498055542061435487582085 468385414136519153921641)
                  ·
                    rfl

theorem cell22_4104798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4104798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104798 prefixEnd_4104798 := by exact prefixLift 4104798
  have htrace : WordTrace (prefixWord ++ tailWord_4104798) baseStart_4104798 baseEnd_4104798 := by
    simpa [prefixWord, tailWord_4104798, baseEnd_4104798] using wordTrace_append hprefix tailTrace_4104798
  have hstable : (prefixWord ++ tailWord_4104798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104798).length < 2 ^ (prefixWord ++ tailWord_4104798).sum := by decide
  have hdescent : baseEnd_4104798 < baseStart_4104798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104831 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 6]
def baseStart_4104831 : Nat := 118140960795 + 4104831 * 2 ^ 59
def prefixEnd_4104831 : Nat := 4983230072969 + 3 ^ 40 * 4104831 * 2
def baseEnd_4104831 : Nat := 468389179661318791896607

theorem tailTrace_4104831 : CollatzResearch.WordTrace tailWord_4104831 prefixEnd_4104831 468389179661318791896607 := by
  unfold tailWord_4104831
  simp only [CollatzResearch.WordTrace]
  refine ⟨149715486191905811166522347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99810324127937207444348231 149715486191905811166522347)
  ·
    refine ⟨224573229287858716749783521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149715486191905811166522347 224573229287858716749783521)
    ·
      refine ⟨168429921965894037562337641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224573229287858716749783521 168429921965894037562337641)
      ·
        refine ⟨126322441474420528171753231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168429921965894037562337641 126322441474420528171753231)
        ·
          refine ⟨189483662211630792257629847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126322441474420528171753231 189483662211630792257629847)
          ·
            refine ⟨284225493317446188386444771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189483662211630792257629847 284225493317446188386444771)
            ·
              refine ⟨426338239976169282579667157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284225493317446188386444771 426338239976169282579667157)
              ·
                refine ⟨9992302499441467560460949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 426338239976169282579667157 9992302499441467560460949)
                ·
                  refine ⟨468389179661318791896607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9992302499441467560460949 468389179661318791896607)
                  ·
                    rfl

theorem cell22_4104831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 6].length) (baseStart_4104831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104831 prefixEnd_4104831 := by exact prefixLift 4104831
  have htrace : WordTrace (prefixWord ++ tailWord_4104831) baseStart_4104831 baseEnd_4104831 := by
    simpa [prefixWord, tailWord_4104831, baseEnd_4104831] using wordTrace_append hprefix tailTrace_4104831
  have hstable : (prefixWord ++ tailWord_4104831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104831).length < 2 ^ (prefixWord ++ tailWord_4104831).sum := by decide
  have hdescent : baseEnd_4104831 < baseStart_4104831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104833 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 3, 4]
def baseStart_4104833 : Nat := 118140960795 + 4104833 * 2 ^ 59
def prefixEnd_4104833 : Nat := 4983230072969 + 3 ^ 40 * 4104833 * 2
def baseEnd_4104833 : Nat := 1405168223624829037139815

theorem tailTrace_4104833 : CollatzResearch.WordTrace tailWord_4104833 prefixEnd_4104833 1405168223624829037139815 := by
  unfold tailWord_4104833
  simp only [CollatzResearch.WordTrace]
  refine ⟨149715559137898565508095153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99810372758599043672063435 149715559137898565508095153)
  ·
    refine ⟨112286669353423924131071365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149715559137898565508095153 112286669353423924131071365)
    ·
      refine ⟨21053750503766985774575881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112286669353423924131071365 21053750503766985774575881)
      ·
        refine ⟨15790312877825239330931911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21053750503766985774575881 15790312877825239330931911)
        ·
          refine ⟨23685469316737858996397867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15790312877825239330931911 23685469316737858996397867)
          ·
            refine ⟨35528203975106788494596801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23685469316737858996397867 35528203975106788494596801)
            ·
              refine ⟨26646152981330091370947601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35528203975106788494596801 26646152981330091370947601)
              ·
                refine ⟨19984614735997568528210701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26646152981330091370947601 19984614735997568528210701)
                ·
                  refine ⟨7494230525999088198079013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19984614735997568528210701 7494230525999088198079013)
                  ·
                    refine ⟨1405168223624829037139815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7494230525999088198079013 1405168223624829037139815)
                    ·
                      rfl

theorem cell22_4104833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_4104833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104833 prefixEnd_4104833 := by exact prefixLift 4104833
  have htrace : WordTrace (prefixWord ++ tailWord_4104833) baseStart_4104833 baseEnd_4104833 := by
    simpa [prefixWord, tailWord_4104833, baseEnd_4104833] using wordTrace_append hprefix tailTrace_4104833
  have hstable : (prefixWord ++ tailWord_4104833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104833).length < 2 ^ (prefixWord ++ tailWord_4104833).sum := by decide
  have hdescent : baseEnd_4104833 < baseStart_4104833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104850 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4104850 : Nat := 118140960795 + 4104850 * 2 ^ 59
def prefixEnd_4104850 : Nat := 4983230072969 + 3 ^ 40 * 4104850 * 2
def baseEnd_4104850 : Nat := 1405174043072246659464763

theorem tailTrace_4104850 : CollatzResearch.WordTrace tailWord_4104850 prefixEnd_4104850 1405174043072246659464763 := by
  unfold tailWord_4104850
  simp only [CollatzResearch.WordTrace]
  refine ⟨37429044794709244352866001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99810786119224651607642669 37429044794709244352866001)
  ·
    refine ⟨28071783596031933264649501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37429044794709244352866001 28071783596031933264649501)
    ·
      refine ⟨10526918848511974974243563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28071783596031933264649501 10526918848511974974243563)
      ·
        refine ⟨15790378272767962461365345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10526918848511974974243563 15790378272767962461365345)
        ·
          refine ⟨11842783704575971846024009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15790378272767962461365345 11842783704575971846024009)
          ·
            refine ⟨8882087778431978884518007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11842783704575971846024009 8882087778431978884518007)
            ·
              refine ⟨13323131667647968326777011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8882087778431978884518007 13323131667647968326777011)
              ·
                refine ⟨19984697501471952490165517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13323131667647968326777011 19984697501471952490165517)
                ·
                  refine ⟨7494261563051982183812069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19984697501471952490165517 7494261563051982183812069)
                  ·
                    refine ⟨1405174043072246659464763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7494261563051982183812069 1405174043072246659464763)
                    ·
                      rfl

theorem cell22_4104850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4104850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104850 prefixEnd_4104850 := by exact prefixLift 4104850
  have htrace : WordTrace (prefixWord ++ tailWord_4104850) baseStart_4104850 baseEnd_4104850 := by
    simpa [prefixWord, tailWord_4104850, baseEnd_4104850] using wordTrace_append hprefix tailTrace_4104850
  have hstable : (prefixWord ++ tailWord_4104850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104850).length < 2 ^ (prefixWord ++ tailWord_4104850).sum := by decide
  have hdescent : baseEnd_4104850 < baseStart_4104850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104891 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 4, 7]
def baseStart_4104891 : Nat := 118140960795 + 4104891 * 2 ^ 59
def prefixEnd_4104891 : Nat := 4983230072969 + 3 ^ 40 * 4104891 * 2
def baseEnd_4104891 : Nat := 1405188078210136219189637

theorem tailTrace_4104891 : CollatzResearch.WordTrace tailWord_4104891 prefixEnd_4104891 1405188078210136219189637 := by
  unfold tailWord_4104891
  simp only [CollatzResearch.WordTrace]
  refine ⟨149717674571688441413706527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99811783047792294275804351 149717674571688441413706527)
  ·
    refine ⟨224576511857532662120559791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149717674571688441413706527 224576511857532662120559791)
    ·
      refine ⟨336864767786298993180839687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224576511857532662120559791 336864767786298993180839687)
      ·
        refine ⟨505297151679448489771259531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336864767786298993180839687 505297151679448489771259531)
        ·
          refine ⟨757945727519172734656889297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505297151679448489771259531 757945727519172734656889297)
          ·
            refine ⟨568459295639379550992666973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 757945727519172734656889297 568459295639379550992666973)
            ·
              refine ⟨213172235864767331622250115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568459295639379550992666973 213172235864767331622250115)
              ·
                refine ⟨319758353797150997433375173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213172235864767331622250115 319758353797150997433375173)
                ·
                  refine ⟨59954691336965812018757845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 319758353797150997433375173 59954691336965812018757845)
                  ·
                    refine ⟨1405188078210136219189637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59954691336965812018757845 1405188078210136219189637)
                    ·
                      rfl

theorem cell22_4104891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_4104891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104891 prefixEnd_4104891 := by exact prefixLift 4104891
  have htrace : WordTrace (prefixWord ++ tailWord_4104891) baseStart_4104891 baseEnd_4104891 := by
    simpa [prefixWord, tailWord_4104891, baseEnd_4104891] using wordTrace_append hprefix tailTrace_4104891
  have hstable : (prefixWord ++ tailWord_4104891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104891).length < 2 ^ (prefixWord ++ tailWord_4104891).sum := by decide
  have hdescent : baseEnd_4104891 < baseStart_4104891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104893 : List Nat := [1, 4, 1, 2, 1, 3, 3, 7]
def baseStart_4104893 : Nat := 118140960795 + 4104893 * 2 ^ 59
def prefixEnd_4104893 : Nat := 4983230072969 + 3 ^ 40 * 4104893 * 2
def baseEnd_4104893 : Nat := 156132084761223208959959

theorem tailTrace_4104893 : CollatzResearch.WordTrace tailWord_4104893 prefixEnd_4104893 156132084761223208959959 := by
  unfold tailWord_4104893
  simp only [CollatzResearch.WordTrace]
  refine ⟨149717747517681195755279333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99811831678454130503519555 149717747517681195755279333)
  ·
    refine ⟨28072077659565224204114875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149717747517681195755279333 28072077659565224204114875)
    ·
      refine ⟨42108116489347836306172313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28072077659565224204114875 42108116489347836306172313)
      ·
        refine ⟨31581087367010877229629235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42108116489347836306172313 31581087367010877229629235)
        ·
          refine ⟨47371631050516315844443853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31581087367010877229629235 47371631050516315844443853)
          ·
            refine ⟨17764361643943618441666445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47371631050516315844443853 17764361643943618441666445)
            ·
              refine ⟨6661635616478856915624917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17764361643943618441666445 6661635616478856915624917)
              ·
                refine ⟨156132084761223208959959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6661635616478856915624917 156132084761223208959959)
                ·
                  rfl

theorem cell22_4104893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 7].length) (baseStart_4104893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104893 prefixEnd_4104893 := by exact prefixLift 4104893
  have htrace : WordTrace (prefixWord ++ tailWord_4104893) baseStart_4104893 baseEnd_4104893 := by
    simpa [prefixWord, tailWord_4104893, baseEnd_4104893] using wordTrace_append hprefix tailTrace_4104893
  have hstable : (prefixWord ++ tailWord_4104893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104893).length < 2 ^ (prefixWord ++ tailWord_4104893).sum := by decide
  have hdescent : baseEnd_4104893 < baseStart_4104893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104910 : List Nat := [4, 1, 1, 1, 3, 3, 3, 6]
def baseStart_4104910 : Nat := 118140960795 + 4104910 * 2 ^ 59
def prefixEnd_4104910 : Nat := 4983230072969 + 3 ^ 40 * 4104910 * 2
def baseEnd_4104910 : Nat := 156132731366491833662731

theorem tailTrace_4104910 : CollatzResearch.WordTrace tailWord_4104910 prefixEnd_4104910 156132731366491833662731 := by
  unfold tailWord_4104910
  simp only [CollatzResearch.WordTrace]
  refine ⟨18714795944827450957331023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99812245039079738439098789 18714795944827450957331023)
  ·
    refine ⟨28072193917241176435996535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18714795944827450957331023 28072193917241176435996535)
    ·
      refine ⟨42108290875861764653994803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28072193917241176435996535 42108290875861764653994803)
      ·
        refine ⟨63162436313792646980992205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42108290875861764653994803 63162436313792646980992205)
        ·
          refine ⟨23685913617672242617872077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63162436313792646980992205 23685913617672242617872077)
          ·
            refine ⟨8882217606627090981702029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23685913617672242617872077 8882217606627090981702029)
            ·
              refine ⟨3330831602485159118138261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8882217606627090981702029 3330831602485159118138261)
              ·
                refine ⟨156132731366491833662731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3330831602485159118138261 156132731366491833662731)
                ·
                  rfl

theorem cell22_4104910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_4104910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104910 prefixEnd_4104910 := by exact prefixLift 4104910
  have htrace : WordTrace (prefixWord ++ tailWord_4104910) baseStart_4104910 baseEnd_4104910 := by
    simpa [prefixWord, tailWord_4104910, baseEnd_4104910] using wordTrace_append hprefix tailTrace_4104910
  have hstable : (prefixWord ++ tailWord_4104910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104910).length < 2 ^ (prefixWord ++ tailWord_4104910).sum := by decide
  have hdescent : baseEnd_4104910 < baseStart_4104910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104942 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 3, 3]
def baseStart_4104942 : Nat := 118140960795 + 4104942 * 2 ^ 59
def prefixEnd_4104942 : Nat := 4983230072969 + 3 ^ 40 * 4104942 * 2
def baseEnd_4104942 : Nat := 1405205536552389086164481

theorem tailTrace_4104942 : CollatzResearch.WordTrace tailWord_4104942 prefixEnd_4104942 1405205536552389086164481 := by
  unfold tailWord_4104942
  simp only [CollatzResearch.WordTrace]
  refine ⟨18714941836812959640476635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99813023129669118082542053 18714941836812959640476635)
  ·
    refine ⟨28072412755219439460714953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18714941836812959640476635 28072412755219439460714953)
    ·
      refine ⟨21054309566414579595536215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28072412755219439460714953 21054309566414579595536215)
      ·
        refine ⟨31581464349621869393304323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21054309566414579595536215 31581464349621869393304323)
        ·
          refine ⟨47372196524432804089956485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31581464349621869393304323 47372196524432804089956485)
          ·
            refine ⟨8882286848331150766866841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47372196524432804089956485 8882286848331150766866841)
            ·
              refine ⟨6661715136248363075150131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8882286848331150766866841 6661715136248363075150131)
              ·
                refine ⟨9992572704372544612725197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6661715136248363075150131 9992572704372544612725197)
                ·
                  refine ⟨3747214764139704229771949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9992572704372544612725197 3747214764139704229771949)
                  ·
                    refine ⟨1405205536552389086164481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3747214764139704229771949 1405205536552389086164481)
                    ·
                      rfl

theorem cell22_4104942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_4104942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104942 prefixEnd_4104942 := by exact prefixLift 4104942
  have htrace : WordTrace (prefixWord ++ tailWord_4104942) baseStart_4104942 baseEnd_4104942 := by
    simpa [prefixWord, tailWord_4104942, baseEnd_4104942] using wordTrace_append hprefix tailTrace_4104942
  have hstable : (prefixWord ++ tailWord_4104942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104942).length < 2 ^ (prefixWord ++ tailWord_4104942).sum := by decide
  have hdescent : baseEnd_4104942 < baseStart_4104942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4104948 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_4104948 : Nat := 118140960795 + 4104948 * 2 ^ 59
def prefixEnd_4104948 : Nat := 4983230072969 + 3 ^ 40 * 4104948 * 2
def baseEnd_4104948 : Nat := 1405207590475007070514463

theorem tailTrace_4104948 : CollatzResearch.WordTrace tailWord_4104948 prefixEnd_4104948 1405207590475007070514463 := by
  unfold tailWord_4104948
  simp only [CollatzResearch.WordTrace]
  refine ⟨74859876766240970074265749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99813169021654626765687665 74859876766240970074265749)
  ·
    refine ⟨3509056723417545472231207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74859876766240970074265749 3509056723417545472231207)
    ·
      refine ⟨5263585085126318208346811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3509056723417545472231207 5263585085126318208346811)
      ·
        refine ⟨7895377627689477312520217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5263585085126318208346811 7895377627689477312520217)
        ·
          refine ⟨5921533220767107984390163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7895377627689477312520217 5921533220767107984390163)
          ·
            refine ⟨8882299831150661976585245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5921533220767107984390163 8882299831150661976585245)
            ·
              refine ⟨3330862436681498241219467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8882299831150661976585245 3330862436681498241219467)
              ·
                refine ⟨4996293655022247361829201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3330862436681498241219467 4996293655022247361829201)
                ·
                  refine ⟨3747220241266685521371901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4996293655022247361829201 3747220241266685521371901)
                  ·
                    refine ⟨1405207590475007070514463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3747220241266685521371901 1405207590475007070514463)
                    ·
                      rfl

theorem cell22_4104948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_4104948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4104948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4104948 prefixEnd_4104948 := by exact prefixLift 4104948
  have htrace : WordTrace (prefixWord ++ tailWord_4104948) baseStart_4104948 baseEnd_4104948 := by
    simpa [prefixWord, tailWord_4104948, baseEnd_4104948] using wordTrace_append hprefix tailTrace_4104948
  have hstable : (prefixWord ++ tailWord_4104948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4104948).length < 2 ^ (prefixWord ++ tailWord_4104948).sum := by decide
  have hdescent : baseEnd_4104948 < baseStart_4104948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4104948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105077 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 5, 3]
def baseStart_4105077 : Nat := 118140960795 + 4105077 * 2 ^ 59
def prefixEnd_4105077 : Nat := 4983230072969 + 3 ^ 40 * 4105077 * 2
def baseEnd_4105077 : Nat := 1405251749811293734039067

theorem tailTrace_4105077 : CollatzResearch.WordTrace tailWord_4105077 prefixEnd_4105077 1405251749811293734039067 := by
  unfold tailWord_4105077
  simp only [CollatzResearch.WordTrace]
  refine ⟨149724458549014595179977485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99816305699343063453318323 149724458549014595179977485)
  ·
    refine ⟨56146671955880473192491557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149724458549014595179977485 56146671955880473192491557)
    ·
      refine ⟨10527500991727588723592167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56146671955880473192491557 10527500991727588723592167)
      ·
        refine ⟨15791251487591383085388251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10527500991727588723592167 15791251487591383085388251)
        ·
          refine ⟨23686877231387074628082377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15791251487591383085388251 23686877231387074628082377)
          ·
            refine ⟨17765157923540305971061783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23686877231387074628082377 17765157923540305971061783)
            ·
              refine ⟨26647736885310458956592675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17765157923540305971061783 26647736885310458956592675)
              ·
                refine ⟨39971605327965688434889013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26647736885310458956592675 39971605327965688434889013)
                ·
                  refine ⟨3747337999496783290770845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39971605327965688434889013 3747337999496783290770845)
                  ·
                    refine ⟨1405251749811293734039067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3747337999496783290770845 1405251749811293734039067)
                    ·
                      rfl

theorem cell22_4105077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_4105077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105077 prefixEnd_4105077 := by exact prefixLift 4105077
  have htrace : WordTrace (prefixWord ++ tailWord_4105077) baseStart_4105077 baseEnd_4105077 := by
    simpa [prefixWord, tailWord_4105077, baseEnd_4105077] using wordTrace_append hprefix tailTrace_4105077
  have hstable : (prefixWord ++ tailWord_4105077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105077).length < 2 ^ (prefixWord ++ tailWord_4105077).sum := by decide
  have hdescent : baseEnd_4105077 < baseStart_4105077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105120 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 5, 4]
def baseStart_4105120 : Nat := 118140960795 + 4105120 * 2 ^ 59
def prefixEnd_4105120 : Nat := 4983230072969 + 3 ^ 40 * 4105120 * 2
def baseEnd_4105120 : Nat := 1405266469590055955213935

theorem tailTrace_4105120 : CollatzResearch.WordTrace tailWord_4105120 prefixEnd_4105120 1405266469590055955213935 := by
  unfold tailWord_4105120
  simp only [CollatzResearch.WordTrace]
  refine ⟨74863013443929406761896407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99817351258572542349195209 74863013443929406761896407)
  ·
    refine ⟨112294520165894110142844611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74863013443929406761896407 112294520165894110142844611)
    ·
      refine ⟨168441780248841165214266917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112294520165894110142844611 168441780248841165214266917)
      ·
        refine ⟨31582833796657718477675047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 168441780248841165214266917 31582833796657718477675047)
        ·
          refine ⟨47374250694986577716512571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31582833796657718477675047 47374250694986577716512571)
          ·
            refine ⟨71061376042479866574768857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47374250694986577716512571 71061376042479866574768857)
            ·
              refine ⟨53296032031859899931076643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71061376042479866574768857 53296032031859899931076643)
              ·
                refine ⟨79944048047789849896614965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53296032031859899931076643 79944048047789849896614965)
                ·
                  refine ⟨7494754504480298427807653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79944048047789849896614965 7494754504480298427807653)
                  ·
                    refine ⟨1405266469590055955213935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7494754504480298427807653 1405266469590055955213935)
                    ·
                      rfl

theorem cell22_4105120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 5, 4].length) (baseStart_4105120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105120 prefixEnd_4105120 := by exact prefixLift 4105120
  have htrace : WordTrace (prefixWord ++ tailWord_4105120) baseStart_4105120 baseEnd_4105120 := by
    simpa [prefixWord, tailWord_4105120, baseEnd_4105120] using wordTrace_append hprefix tailTrace_4105120
  have hstable : (prefixWord ++ tailWord_4105120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105120).length < 2 ^ (prefixWord ++ tailWord_4105120).sum := by decide
  have hdescent : baseEnd_4105120 < baseStart_4105120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105122 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_4105122 : Nat := 118140960795 + 4105122 * 2 ^ 59
def prefixEnd_4105122 : Nat := 4983230072969 + 3 ^ 40 * 4105122 * 2
def baseEnd_4105122 : Nat := 1405267154230928616663929

theorem tailTrace_4105122 : CollatzResearch.WordTrace tailWord_4105122 prefixEnd_4105122 1405267154230928616663929 := by
  unfold tailWord_4105122
  simp only [CollatzResearch.WordTrace]
  refine ⟨37431524958462891966341405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99817399889234378576910413 37431524958462891966341405)
  ·
    refine ⟨14036821859423584487378027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37431524958462891966341405 14036821859423584487378027)
    ·
      refine ⟨21055232789135376731067041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14036821859423584487378027 21055232789135376731067041)
      ·
        refine ⟨15791424591851532548300281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21055232789135376731067041 15791424591851532548300281)
        ·
          refine ⟨11843568443888649411225211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15791424591851532548300281 11843568443888649411225211)
          ·
            refine ⟨17765352665832974116837817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11843568443888649411225211 17765352665832974116837817)
            ·
              refine ⟨13324014499374730587628363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17765352665832974116837817 13324014499374730587628363)
              ·
                refine ⟨19986021749062095881442545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13324014499374730587628363 19986021749062095881442545)
                ·
                  refine ⟨14989516311796571911081909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19986021749062095881442545 14989516311796571911081909)
                  ·
                    refine ⟨1405267154230928616663929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14989516311796571911081909 1405267154230928616663929)
                    ·
                      rfl

theorem cell22_4105122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_4105122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105122 prefixEnd_4105122 := by exact prefixLift 4105122
  have htrace : WordTrace (prefixWord ++ tailWord_4105122) baseStart_4105122 baseEnd_4105122 := by
    simpa [prefixWord, tailWord_4105122, baseEnd_4105122] using wordTrace_append hprefix tailTrace_4105122
  have hstable : (prefixWord ++ tailWord_4105122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105122).length < 2 ^ (prefixWord ++ tailWord_4105122).sum := by decide
  have hdescent : baseEnd_4105122 < baseStart_4105122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105167 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 4, 3]
def baseStart_4105167 : Nat := 118140960795 + 4105167 * 2 ^ 59
def prefixEnd_4105167 : Nat := 4983230072969 + 3 ^ 40 * 4105167 * 2
def baseEnd_4105167 : Nat := 1405282558650563499288791

theorem tailTrace_4105167 : CollatzResearch.WordTrace tailWord_4105167 prefixEnd_4105167 1405282558650563499288791 := by
  unfold tailWord_4105167
  simp only [CollatzResearch.WordTrace]
  refine ⟨149727741118688540550753755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99818494079125693700502503 149727741118688540550753755)
  ·
    refine ⟨224591611678032810826130633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149727741118688540550753755 224591611678032810826130633)
    ·
      refine ⟨168443708758524608119597975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224591611678032810826130633 168443708758524608119597975)
      ·
        refine ⟨252665563137786912179396963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168443708758524608119597975 252665563137786912179396963)
        ·
          refine ⟨378998344706680368269095445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252665563137786912179396963 378998344706680368269095445)
          ·
            refine ⟨17765547408125642262613849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 378998344706680368269095445 17765547408125642262613849)
            ·
              refine ⟨13324160556094231696960387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17765547408125642262613849 13324160556094231696960387)
              ·
                refine ⟨19986240834141347545440581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13324160556094231696960387 19986240834141347545440581)
                ·
                  refine ⟨3747420156401502664770109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19986240834141347545440581 3747420156401502664770109)
                  ·
                    refine ⟨1405282558650563499288791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3747420156401502664770109 1405282558650563499288791)
                    ·
                      rfl

theorem cell22_4105167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 3].length) (baseStart_4105167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105167 prefixEnd_4105167 := by exact prefixLift 4105167
  have htrace : WordTrace (prefixWord ++ tailWord_4105167) baseStart_4105167 baseEnd_4105167 := by
    simpa [prefixWord, tailWord_4105167, baseEnd_4105167] using wordTrace_append hprefix tailTrace_4105167
  have hstable : (prefixWord ++ tailWord_4105167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105167).length < 2 ^ (prefixWord ++ tailWord_4105167).sum := by decide
  have hdescent : baseEnd_4105167 < baseStart_4105167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105169 : List Nat := [1, 2, 2, 1, 2, 1, 7, 2, 4]
def baseStart_4105169 : Nat := 118140960795 + 4105169 * 2 ^ 59
def prefixEnd_4105169 : Nat := 4983230072969 + 3 ^ 40 * 4105169 * 2
def baseEnd_4105169 : Nat := 468427747763812053579595

theorem tailTrace_4105169 : CollatzResearch.WordTrace tailWord_4105169 prefixEnd_4105169 468427747763812053579595 := by
  unfold tailWord_4105169
  simp only [CollatzResearch.WordTrace]
  refine ⟨149727814064681294892326561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99818542709787529928217707 149727814064681294892326561)
  ·
    refine ⟨112295860548510971169244921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149727814064681294892326561 112295860548510971169244921)
    ·
      refine ⟨84221895411383228376933691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112295860548510971169244921 84221895411383228376933691)
      ·
        refine ⟨126332843117074842565400537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84221895411383228376933691 126332843117074842565400537)
        ·
          refine ⟨94749632337806131924050403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126332843117074842565400537 94749632337806131924050403)
          ·
            refine ⟨142124448506709197886075605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94749632337806131924050403 142124448506709197886075605)
            ·
              refine ⟨3331041761875996825454897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 142124448506709197886075605 3331041761875996825454897)
              ·
                refine ⟨2498281321406997619091173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3331041761875996825454897 2498281321406997619091173)
                ·
                  refine ⟨468427747763812053579595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2498281321406997619091173 468427747763812053579595)
                  ·
                    rfl

theorem cell22_4105169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 4].length) (baseStart_4105169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105169 prefixEnd_4105169 := by exact prefixLift 4105169
  have htrace : WordTrace (prefixWord ++ tailWord_4105169) baseStart_4105169 baseEnd_4105169 := by
    simpa [prefixWord, tailWord_4105169, baseEnd_4105169] using wordTrace_append hprefix tailTrace_4105169
  have hstable : (prefixWord ++ tailWord_4105169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105169).length < 2 ^ (prefixWord ++ tailWord_4105169).sum := by decide
  have hdescent : baseEnd_4105169 < baseStart_4105169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105210 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_4105210 : Nat := 118140960795 + 4105210 * 2 ^ 59
def prefixEnd_4105210 : Nat := 4983230072969 + 3 ^ 40 * 4105210 * 2
def baseEnd_4105210 : Nat := 1405297278429325720463659

theorem tailTrace_4105210 : CollatzResearch.WordTrace tailWord_4105210 prefixEnd_4105210 1405297278429325720463659 := by
  unfold tailWord_4105210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37432327364383189723642271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99819539638355172596379389 37432327364383189723642271)
  ·
    refine ⟨56148491046574784585463407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37432327364383189723642271 56148491046574784585463407)
    ·
      refine ⟨84222736569862176878195111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56148491046574784585463407 84222736569862176878195111)
      ·
        refine ⟨126334104854793265317292667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84222736569862176878195111 126334104854793265317292667)
        ·
          refine ⟨189501157282189897975939001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126334104854793265317292667 189501157282189897975939001)
          ·
            refine ⟨142125867961642423481954251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189501157282189897975939001 142125867961642423481954251)
            ·
              refine ⟨213188801942463635222931377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142125867961642423481954251 213188801942463635222931377)
              ·
                refine ⟨159891601456847726417198533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213188801942463635222931377 159891601456847726417198533)
                ·
                  refine ⟨29979675273158948703224725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159891601456847726417198533 29979675273158948703224725)
                  ·
                    refine ⟨1405297278429325720463659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29979675273158948703224725 1405297278429325720463659)
                    ·
                      rfl

theorem cell22_4105210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_4105210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105210 prefixEnd_4105210 := by exact prefixLift 4105210
  have htrace : WordTrace (prefixWord ++ tailWord_4105210) baseStart_4105210 baseEnd_4105210 := by
    simpa [prefixWord, tailWord_4105210, baseEnd_4105210] using wordTrace_append hprefix tailTrace_4105210
  have hstable : (prefixWord ++ tailWord_4105210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105210).length < 2 ^ (prefixWord ++ tailWord_4105210).sum := by decide
  have hdescent : baseEnd_4105210 < baseStart_4105210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105214 : List Nat := [4, 2, 2, 2, 3, 9]
def baseStart_4105214 : Nat := 118140960795 + 4105214 * 2 ^ 59
def prefixEnd_4105214 : Nat := 4983230072969 + 3 ^ 40 * 4105214 * 2
def baseEnd_4105214 : Nat := 17349366021124333868687

theorem tailTrace_4105214 : CollatzResearch.WordTrace tailWord_4105214 prefixEnd_4105214 17349366021124333868687 := by
  unfold tailWord_4105214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18716181918689783447214337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99819636899678845051809797 18716181918689783447214337)
  ·
    refine ⟨14037136439017337585410753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18716181918689783447214337 14037136439017337585410753)
    ·
      refine ⟨10527852329263003189058065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14037136439017337585410753 10527852329263003189058065)
      ·
        refine ⟨7895889246947252391793549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10527852329263003189058065 7895889246947252391793549)
        ·
          refine ⟨2960958467605219646922581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7895889246947252391793549 2960958467605219646922581)
          ·
            refine ⟨17349366021124333868687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2960958467605219646922581 17349366021124333868687)
            ·
              rfl

theorem cell22_4105214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 9].length) (baseStart_4105214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105214 prefixEnd_4105214 := by exact prefixLift 4105214
  have htrace : WordTrace (prefixWord ++ tailWord_4105214) baseStart_4105214 baseEnd_4105214 := by
    simpa [prefixWord, tailWord_4105214, baseEnd_4105214] using wordTrace_append hprefix tailTrace_4105214
  have hstable : (prefixWord ++ tailWord_4105214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105214).length < 2 ^ (prefixWord ++ tailWord_4105214).sum := by decide
  have hdescent : baseEnd_4105214 < baseStart_4105214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105225 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 7]
def baseStart_4105225 : Nat := 118140960795 + 4105225 * 2 ^ 59
def prefixEnd_4105225 : Nat := 4983230072969 + 3 ^ 40 * 4105225 * 2
def baseEnd_4105225 : Nat := 468434137745290227112871

theorem tailTrace_4105225 : CollatzResearch.WordTrace tailWord_4105225 prefixEnd_4105225 468434137745290227112871 := by
  unfold tailWord_4105225
  simp only [CollatzResearch.WordTrace]
  refine ⟨149729856552478416456365129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99819904368318944304243419 149729856552478416456365129)
  ·
    refine ⟨112297392414358812342273847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149729856552478416456365129 112297392414358812342273847)
    ·
      refine ⟨168446088621538218513410771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112297392414358812342273847 168446088621538218513410771)
      ·
        refine ⟨252669132932307327770116157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168446088621538218513410771 252669132932307327770116157)
        ·
          refine ⟨94750924849615247913793559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252669132932307327770116157 94750924849615247913793559)
          ·
            refine ⟨142126387274422871870690339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94750924849615247913793559 142126387274422871870690339)
            ·
              refine ⟨213189580911634307806035509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142126387274422871870690339 213189580911634307806035509)
              ·
                refine ⟨19986523210465716356815829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213189580911634307806035509 19986523210465716356815829)
                ·
                  refine ⟨468434137745290227112871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19986523210465716356815829 468434137745290227112871)
                  ·
                    rfl

theorem cell22_4105225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_4105225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105225 prefixEnd_4105225 := by exact prefixLift 4105225
  have htrace : WordTrace (prefixWord ++ tailWord_4105225) baseStart_4105225 baseEnd_4105225 := by
    simpa [prefixWord, tailWord_4105225, baseEnd_4105225] using wordTrace_append hprefix tailTrace_4105225
  have hstable : (prefixWord ++ tailWord_4105225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105225).length < 2 ^ (prefixWord ++ tailWord_4105225).sum := by decide
  have hdescent : baseEnd_4105225 < baseStart_4105225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105242 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_4105242 : Nat := 118140960795 + 4105242 * 2 ^ 59
def prefixEnd_4105242 : Nat := 4983230072969 + 3 ^ 40 * 4105242 * 2
def baseEnd_4105242 : Nat := 468436077561096101221187

theorem tailTrace_4105242 : CollatzResearch.WordTrace tailWord_4105242 prefixEnd_4105242 468436077561096101221187 := by
  unfold tailWord_4105242
  simp only [CollatzResearch.WordTrace]
  refine ⟨37432619148354207089933495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99820317728944552239822653 37432619148354207089933495)
  ·
    refine ⟨56148928722531310634900243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37432619148354207089933495 56148928722531310634900243)
    ·
      refine ⟨84223393083796965952350365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56148928722531310634900243 84223393083796965952350365)
      ·
        refine ⟨31583772406423862232131387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84223393083796965952350365 31583772406423862232131387)
        ·
          refine ⟨47375658609635793348197081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31583772406423862232131387 47375658609635793348197081)
          ·
            refine ⟨35531743957226845011147811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47375658609635793348197081 35531743957226845011147811)
            ·
              refine ⟨53297615935840267516721717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35531743957226845011147811 53297615935840267516721717)
              ·
                refine ⟨4996651493985025079692661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53297615935840267516721717 4996651493985025079692661)
                ·
                  refine ⟨468436077561096101221187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4996651493985025079692661 468436077561096101221187)
                  ·
                    rfl

theorem cell22_4105242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_4105242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105242 prefixEnd_4105242 := by exact prefixLift 4105242
  have htrace : WordTrace (prefixWord ++ tailWord_4105242) baseStart_4105242 baseEnd_4105242 := by
    simpa [prefixWord, tailWord_4105242, baseEnd_4105242] using wordTrace_append hprefix tailTrace_4105242
  have hstable : (prefixWord ++ tailWord_4105242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105242).length < 2 ^ (prefixWord ++ tailWord_4105242).sum := by decide
  have hdescent : baseEnd_4105242 < baseStart_4105242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105287 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 6]
def baseStart_4105287 : Nat := 118140960795 + 4105287 * 2 ^ 59
def prefixEnd_4105287 : Nat := 4983230072969 + 3 ^ 40 * 4105287 * 2
def baseEnd_4105287 : Nat := 468441212367641062096141

theorem tailTrace_4105287 : CollatzResearch.WordTrace tailWord_4105287 prefixEnd_4105287 468441212367641062096141 := by
  unfold tailWord_4105287
  simp only [CollatzResearch.WordTrace]
  refine ⟨149732117878253801045122115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99821411918835867363414743 149732117878253801045122115)
  ·
    refine ⟨224598176817380701567683173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149732117878253801045122115 224598176817380701567683173)
    ·
      refine ⟨42112158153258881543940595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 224598176817380701567683173 42112158153258881543940595)
      ·
        refine ⟨63168237229888322315910893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42112158153258881543940595 63168237229888322315910893)
        ·
          refine ⟨23688088961208120868466585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63168237229888322315910893 23688088961208120868466585)
          ·
            refine ⟨17766066720906090651349939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23688088961208120868466585 17766066720906090651349939)
            ·
              refine ⟨26649100081359135977024909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17766066720906090651349939 26649100081359135977024909)
              ·
                refine ⟨9993412530509675991384341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26649100081359135977024909 9993412530509675991384341)
                ·
                  refine ⟨468441212367641062096141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9993412530509675991384341 468441212367641062096141)
                  ·
                    rfl

theorem cell22_4105287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 6].length) (baseStart_4105287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105287 prefixEnd_4105287 := by exact prefixLift 4105287
  have htrace : WordTrace (prefixWord ++ tailWord_4105287) baseStart_4105287 baseEnd_4105287 := by
    simpa [prefixWord, tailWord_4105287, baseEnd_4105287] using wordTrace_append hprefix tailTrace_4105287
  have hstable : (prefixWord ++ tailWord_4105287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105287).length < 2 ^ (prefixWord ++ tailWord_4105287).sum := by decide
  have hdescent : baseEnd_4105287 < baseStart_4105287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105317 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_4105317 : Nat := 118140960795 + 4105317 * 2 ^ 59
def prefixEnd_4105317 : Nat := 4983230072969 + 3 ^ 40 * 4105317 * 2
def baseEnd_4105317 : Nat := 1405333906716013108038331

theorem tailTrace_4105317 : CollatzResearch.WordTrace tailWord_4105317 prefixEnd_4105317 1405333906716013108038331 := by
  unfold tailWord_4105317
  simp only [CollatzResearch.WordTrace]
  refine ⟨149733212068145116168714205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99822141378763410779142803 149733212068145116168714205)
  ·
    refine ⟨56149954525554418563267827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149733212068145116168714205 56149954525554418563267827)
    ·
      refine ⟨84224931788331627844901741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56149954525554418563267827 84224931788331627844901741)
      ·
        refine ⟨31584349420624360441838153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84224931788331627844901741 31584349420624360441838153)
        ·
          refine ⟨23688262065468270331378615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31584349420624360441838153 23688262065468270331378615)
          ·
            refine ⟨35532393098202405497067923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23688262065468270331378615 35532393098202405497067923)
            ·
              refine ⟨53298589647303608245601885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35532393098202405497067923 53298589647303608245601885)
              ·
                refine ⟨19986971117738853092100707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53298589647303608245601885 19986971117738853092100707)
                ·
                  refine ⟨29980456676608279638151061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19986971117738853092100707 29980456676608279638151061)
                  ·
                    refine ⟨1405333906716013108038331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29980456676608279638151061 1405333906716013108038331)
                    ·
                      rfl

theorem cell22_4105317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_4105317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105317 prefixEnd_4105317 := by exact prefixLift 4105317
  have htrace : WordTrace (prefixWord ++ tailWord_4105317) baseStart_4105317 baseEnd_4105317 := by
    simpa [prefixWord, tailWord_4105317, baseEnd_4105317] using wordTrace_append hprefix tailTrace_4105317
  have hstable : (prefixWord ++ tailWord_4105317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105317).length < 2 ^ (prefixWord ++ tailWord_4105317).sum := by decide
  have hdescent : baseEnd_4105317 < baseStart_4105317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105319 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 4, 3]
def baseStart_4105319 : Nat := 118140960795 + 4105319 * 2 ^ 59
def prefixEnd_4105319 : Nat := 4983230072969 + 3 ^ 40 * 4105319 * 2
def baseEnd_4105319 : Nat := 1405334591356885769488325

theorem tailTrace_4105319 : CollatzResearch.WordTrace tailWord_4105319 prefixEnd_4105319 1405334591356885769488325 := by
  unfold tailWord_4105319
  simp only [CollatzResearch.WordTrace]
  refine ⟨149733285014137870510287011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99822190009425247006858007 149733285014137870510287011)
  ·
    refine ⟨224599927521206805765430517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149733285014137870510287011 224599927521206805765430517)
    ·
      refine ⟨21056243205113138040509111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224599927521206805765430517 21056243205113138040509111)
      ·
        refine ⟨31584364807669707060763667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21056243205113138040509111 31584364807669707060763667)
        ·
          refine ⟨47376547211504560591145501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31584364807669707060763667 47376547211504560591145501)
          ·
            refine ⟨17766205204314210221679563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47376547211504560591145501 17766205204314210221679563)
            ·
              refine ⟨26649307806471315332519345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17766205204314210221679563 26649307806471315332519345)
              ·
                refine ⟨19986980854853486499389509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26649307806471315332519345 19986980854853486499389509)
                ·
                  refine ⟨3747558910285028718635533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19986980854853486499389509 3747558910285028718635533)
                  ·
                    refine ⟨1405334591356885769488325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3747558910285028718635533 1405334591356885769488325)
                    ·
                      rfl

theorem cell22_4105319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_4105319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105319 prefixEnd_4105319 := by exact prefixLift 4105319
  have htrace : WordTrace (prefixWord ++ tailWord_4105319) baseStart_4105319 baseEnd_4105319 := by
    simpa [prefixWord, tailWord_4105319, baseEnd_4105319] using wordTrace_append hprefix tailTrace_4105319
  have hstable : (prefixWord ++ tailWord_4105319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105319).length < 2 ^ (prefixWord ++ tailWord_4105319).sum := by decide
  have hdescent : baseEnd_4105319 < baseStart_4105319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105321 : List Nat := [1, 2, 1, 1, 1, 8, 1, 3, 4]
def baseStart_4105321 : Nat := 118140960795 + 4105321 * 2 ^ 59
def prefixEnd_4105321 : Nat := 4983230072969 + 3 ^ 40 * 4105321 * 2
def baseEnd_4105321 : Nat := 468445091999252810312773

theorem tailTrace_4105321 : CollatzResearch.WordTrace tailWord_4105321 prefixEnd_4105321 468445091999252810312773 := by
  unfold tailWord_4105321
  simp only [CollatzResearch.WordTrace]
  refine ⟨149733357960130624851859817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99822238640087083234573211 149733357960130624851859817)
  ·
    refine ⟨112300018470097968638894863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149733357960130624851859817 112300018470097968638894863)
    ·
      refine ⟨168450027705146952958342295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112300018470097968638894863 168450027705146952958342295)
      ·
        refine ⟨252675041557720429437513443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168450027705146952958342295 252675041557720429437513443)
        ·
          refine ⟨379012562336580644156270165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252675041557720429437513443 379012562336580644156270165)
          ·
            refine ⟨4441553464881804423706291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 379012562336580644156270165 4441553464881804423706291)
            ·
              refine ⟨6662330197322706635559437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441553464881804423706291 6662330197322706635559437)
              ·
                refine ⟨2498373823996014988334789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6662330197322706635559437 2498373823996014988334789)
                ·
                  refine ⟨468445091999252810312773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2498373823996014988334789 468445091999252810312773)
                  ·
                    rfl

theorem cell22_4105321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 4].length) (baseStart_4105321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105321 prefixEnd_4105321 := by exact prefixLift 4105321
  have htrace : WordTrace (prefixWord ++ tailWord_4105321) baseStart_4105321 baseEnd_4105321 := by
    simpa [prefixWord, tailWord_4105321, baseEnd_4105321] using wordTrace_append hprefix tailTrace_4105321
  have hstable : (prefixWord ++ tailWord_4105321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105321).length < 2 ^ (prefixWord ++ tailWord_4105321).sum := by decide
  have hdescent : baseEnd_4105321 < baseStart_4105321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105349 : List Nat := [1, 3, 1, 1, 6, 1, 2, 7]
def baseStart_4105349 : Nat := 118140960795 + 4105349 * 2 ^ 59
def prefixEnd_4105349 : Nat := 4983230072969 + 3 ^ 40 * 4105349 * 2
def baseEnd_4105349 : Nat := 156149428996663965693137

theorem tailTrace_4105349 : CollatzResearch.WordTrace tailWord_4105349 prefixEnd_4105349 156149428996663965693137 := by
  unfold tailWord_4105349
  simp only [CollatzResearch.WordTrace]
  refine ⟨149734379204029185633879101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99822919469352790422586067 149734379204029185633879101)
  ·
    refine ⟨56150392201510944612704663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149734379204029185633879101 56150392201510944612704663)
    ·
      refine ⟨84225588302266416919056995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56150392201510944612704663 84225588302266416919056995)
      ·
        refine ⟨126338382453399625378585493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84225588302266416919056995 126338382453399625378585493)
        ·
          refine ⟨5922111677503107439621195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126338382453399625378585493 5922111677503107439621195)
          ·
            refine ⟨8883167516254661159431793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5922111677503107439621195 8883167516254661159431793)
            ·
              refine ⟨6662375637190995869573845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8883167516254661159431793 6662375637190995869573845)
              ·
                refine ⟨156149428996663965693137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6662375637190995869573845 156149428996663965693137)
                ·
                  rfl

theorem cell22_4105349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 7].length) (baseStart_4105349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105349 prefixEnd_4105349 := by exact prefixLift 4105349
  have htrace : WordTrace (prefixWord ++ tailWord_4105349) baseStart_4105349 baseEnd_4105349 := by
    simpa [prefixWord, tailWord_4105349, baseEnd_4105349] using wordTrace_append hprefix tailTrace_4105349
  have hstable : (prefixWord ++ tailWord_4105349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105349).length < 2 ^ (prefixWord ++ tailWord_4105349).sum := by decide
  have hdescent : baseEnd_4105349 < baseStart_4105349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105353 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 2, 3]
def baseStart_4105353 : Nat := 118140960795 + 4105353 * 2 ^ 59
def prefixEnd_4105353 : Nat := 4983230072969 + 3 ^ 40 * 4105353 * 2
def baseEnd_4105353 : Nat := 1405346230251721014138221

theorem tailTrace_4105353 : CollatzResearch.WordTrace tailWord_4105353 prefixEnd_4105353 1405346230251721014138221 := by
  unfold tailWord_4105353
  simp only [CollatzResearch.WordTrace]
  refine ⟨149734525096014694317024713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99823016730676462878016475 149734525096014694317024713)
  ·
    refine ⟨112300893822011020737768535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149734525096014694317024713 112300893822011020737768535)
    ·
      refine ⟨168451340733016531106652803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112300893822011020737768535 168451340733016531106652803)
      ·
        refine ⟨252677011099524796659979205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168451340733016531106652803 252677011099524796659979205)
        ·
          refine ⟨47376939581160899373746101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252677011099524796659979205 47376939581160899373746101)
          ·
            refine ⟨4441588085733834316288697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47376939581160899373746101 4441588085733834316288697)
            ·
              refine ⟨3331191064300375737216523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4441588085733834316288697 3331191064300375737216523)
              ·
                refine ⟨4996786596450563605824785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331191064300375737216523 4996786596450563605824785)
                ·
                  refine ⟨3747589947337922704368589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4996786596450563605824785 3747589947337922704368589)
                  ·
                    refine ⟨1405346230251721014138221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3747589947337922704368589 1405346230251721014138221)
                    ·
                      rfl

theorem cell22_4105353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 2, 3].length) (baseStart_4105353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105353 prefixEnd_4105353 := by exact prefixLift 4105353
  have htrace : WordTrace (prefixWord ++ tailWord_4105353) baseStart_4105353 baseEnd_4105353 := by
    simpa [prefixWord, tailWord_4105353, baseEnd_4105353] using wordTrace_append hprefix tailTrace_4105353
  have hstable : (prefixWord ++ tailWord_4105353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105353).length < 2 ^ (prefixWord ++ tailWord_4105353).sum := by decide
  have hdescent : baseEnd_4105353 < baseStart_4105353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105392 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 4, 5]
def baseStart_4105392 : Nat := 118140960795 + 4105392 * 2 ^ 59
def prefixEnd_4105392 : Nat := 4983230072969 + 3 ^ 40 * 4105392 * 2
def baseEnd_4105392 : Nat := 1405359580748737912413101

theorem tailTrace_4105392 : CollatzResearch.WordTrace tailWord_4105392 prefixEnd_4105392 1405359580748737912413101 := by
  unfold tailWord_4105392
  simp only [CollatzResearch.WordTrace]
  refine ⟨74867973771436701988847215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99823965028582269318462953 74867973771436701988847215)
  ·
    refine ⟨112301960657155052983270823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74867973771436701988847215 112301960657155052983270823)
    ·
      refine ⟨168452940985732579474906235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112301960657155052983270823 168452940985732579474906235)
      ·
        refine ⟨252679411478598869212359353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168452940985732579474906235 252679411478598869212359353)
        ·
          refine ⟨189509558608949151909269515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252679411478598869212359353 189509558608949151909269515)
          ·
            refine ⟨284264337913423727863904273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189509558608949151909269515 284264337913423727863904273)
            ·
              refine ⟨213198253435067795897928205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284264337913423727863904273 213198253435067795897928205)
              ·
                refine ⟨79949345038150423461723077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213198253435067795897928205 79949345038150423461723077)
                ·
                  refine ⟨14990502194653204399073077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79949345038150423461723077 14990502194653204399073077)
                  ·
                    refine ⟨1405359580748737912413101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14990502194653204399073077 1405359580748737912413101)
                    ·
                      rfl

theorem cell22_4105392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_4105392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105392 prefixEnd_4105392 := by exact prefixLift 4105392
  have htrace : WordTrace (prefixWord ++ tailWord_4105392) baseStart_4105392 baseEnd_4105392 := by
    simpa [prefixWord, tailWord_4105392, baseEnd_4105392] using wordTrace_append hprefix tailTrace_4105392
  have hstable : (prefixWord ++ tailWord_4105392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105392).length < 2 ^ (prefixWord ++ tailWord_4105392).sum := by decide
  have hdescent : baseEnd_4105392 < baseStart_4105392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105394 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_4105394 : Nat := 118140960795 + 4105394 * 2 ^ 59
def prefixEnd_4105394 : Nat := 4983230072969 + 3 ^ 40 * 4105394 * 2
def baseEnd_4105394 : Nat := 468453421796536857954365

theorem tailTrace_4105394 : CollatzResearch.WordTrace tailWord_4105394 prefixEnd_4105394 468453421796536857954365 := by
  unfold tailWord_4105394
  simp only [CollatzResearch.WordTrace]
  refine ⟨37434005122216539579816809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99824013659244105546178157 37434005122216539579816809)
  ·
    refine ⟨28075503841662404684862607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37434005122216539579816809 28075503841662404684862607)
    ·
      refine ⟨42113255762493607027293911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28075503841662404684862607 42113255762493607027293911)
      ·
        refine ⟨63169883643740410540940867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42113255762493607027293911 63169883643740410540940867)
        ·
          refine ⟨94754825465610615811411301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63169883643740410540940867 94754825465610615811411301)
          ·
            refine ⟨17766529774801990464639619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94754825465610615811411301 17766529774801990464639619)
            ·
              refine ⟨26649794662202985696959429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17766529774801990464639619 26649794662202985696959429)
              ·
                refine ⟨4996836499163059818179893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26649794662202985696959429 4996836499163059818179893)
                ·
                  refine ⟨468453421796536857954365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4996836499163059818179893 468453421796536857954365)
                  ·
                    rfl

theorem cell22_4105394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_4105394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105394 prefixEnd_4105394 := by exact prefixLift 4105394
  have htrace : WordTrace (prefixWord ++ tailWord_4105394) baseStart_4105394 baseEnd_4105394 := by
    simpa [prefixWord, tailWord_4105394, baseEnd_4105394] using wordTrace_append hprefix tailTrace_4105394
  have hstable : (prefixWord ++ tailWord_4105394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105394).length < 2 ^ (prefixWord ++ tailWord_4105394).sum := by decide
  have hdescent : baseEnd_4105394 < baseStart_4105394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105441 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 1, 4]
def baseStart_4105441 : Nat := 118140960795 + 4105441 * 2 ^ 59
def prefixEnd_4105441 : Nat := 4983230072969 + 3 ^ 40 * 4105441 * 2
def baseEnd_4105441 : Nat := 1405376354450118117937951

theorem tailTrace_4105441 : CollatzResearch.WordTrace tailWord_4105441 prefixEnd_4105441 1405376354450118117937951 := by
  unfold tailWord_4105441
  simp only [CollatzResearch.WordTrace]
  refine ⟨149737734719695885346228177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99825156479797256897485451 149737734719695885346228177)
  ·
    refine ⟨112303301039771914009671133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149737734719695885346228177 112303301039771914009671133)
    ·
      refine ⟨42113737889914467753626675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112303301039771914009671133 42113737889914467753626675)
      ·
        refine ⟨63170606834871701630440013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42113737889914467753626675 63170606834871701630440013)
        ·
          refine ⟨23688977563076888111415005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63170606834871701630440013 23688977563076888111415005)
          ·
            refine ⟨8883366586153833041780627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23688977563076888111415005 8883366586153833041780627)
            ·
              refine ⟨13325049879230749562670941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883366586153833041780627 13325049879230749562670941)
              ·
                refine ⟨4996893704711531086001603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13325049879230749562670941 4996893704711531086001603)
                ·
                  refine ⟨7495340557067296629002405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4996893704711531086001603 7495340557067296629002405)
                  ·
                    refine ⟨1405376354450118117937951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7495340557067296629002405 1405376354450118117937951)
                    ·
                      rfl

theorem cell22_4105441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_4105441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105441 prefixEnd_4105441 := by exact prefixLift 4105441
  have htrace : WordTrace (prefixWord ++ tailWord_4105441) baseStart_4105441 baseEnd_4105441 := by
    simpa [prefixWord, tailWord_4105441, baseEnd_4105441] using wordTrace_append hprefix tailTrace_4105441
  have hstable : (prefixWord ++ tailWord_4105441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105441).length < 2 ^ (prefixWord ++ tailWord_4105441).sum := by decide
  have hdescent : baseEnd_4105441 < baseStart_4105441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105454 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_4105454 : Nat := 118140960795 + 4105454 * 2 ^ 59
def prefixEnd_4105454 : Nat := 4983230072969 + 3 ^ 40 * 4105454 * 2
def baseEnd_4105454 : Nat := 1405380804615790417362911

theorem tailTrace_4105454 : CollatzResearch.WordTrace tailWord_4105454 prefixEnd_4105454 1405380804615790417362911 := by
  unfold tailWord_4105454
  simp only [CollatzResearch.WordTrace]
  refine ⟨18717276108581098570806427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99825472579099192377634277 18717276108581098570806427)
  ·
    refine ⟨28075914162871647856209641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18717276108581098570806427 28075914162871647856209641)
    ·
      refine ⟨21056935622153735892157231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28075914162871647856209641 21056935622153735892157231)
      ·
        refine ⟨31585403433230603838235847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21056935622153735892157231 31585403433230603838235847)
        ·
          refine ⟨47378105149845905757353771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31585403433230603838235847 47378105149845905757353771)
          ·
            refine ⟨71067157724768858636030657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47378105149845905757353771 71067157724768858636030657)
            ·
              refine ⟨53300368293576643977022993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71067157724768858636030657 53300368293576643977022993)
              ·
                refine ⟨39975276220182482982767245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53300368293576643977022993 39975276220182482982767245)
                ·
                  refine ⟨14990728582568431118537717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39975276220182482982767245 14990728582568431118537717)
                  ·
                    refine ⟨1405380804615790417362911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14990728582568431118537717 1405380804615790417362911)
                    ·
                      rfl

theorem cell22_4105454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_4105454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105454 prefixEnd_4105454 := by exact prefixLift 4105454
  have htrace : WordTrace (prefixWord ++ tailWord_4105454) baseStart_4105454 baseEnd_4105454 := by
    simpa [prefixWord, tailWord_4105454, baseEnd_4105454] using wordTrace_append hprefix tailTrace_4105454
  have hstable : (prefixWord ++ tailWord_4105454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105454).length < 2 ^ (prefixWord ++ tailWord_4105454).sum := by decide
  have hdescent : baseEnd_4105454 < baseStart_4105454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105471 : List Nat := [1, 1, 2, 2, 1, 7, 1, 1, 1, 5]
def baseStart_4105471 : Nat := 118140960795 + 4105471 * 2 ^ 59
def prefixEnd_4105471 : Nat := 4983230072969 + 3 ^ 40 * 4105471 * 2
def baseEnd_4105471 : Nat := 1405386624063208039687859

theorem tailTrace_4105471 : CollatzResearch.WordTrace tailWord_4105471 prefixEnd_4105471 1405386624063208039687859 := by
  unfold tailWord_4105471
  simp only [CollatzResearch.WordTrace]
  refine ⟨149738828909587200469820267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99825885939724800313213511 149738828909587200469820267)
  ·
    refine ⟨224608243364380800704730401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149738828909587200469820267 224608243364380800704730401)
    ·
      refine ⟨168456182523285600528547801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224608243364380800704730401 168456182523285600528547801)
      ·
        refine ⟨126342136892464200396410851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168456182523285600528547801 126342136892464200396410851)
        ·
          refine ⟨189513205338696300594616277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126342136892464200396410851 189513205338696300594616277)
          ·
            refine ⟨4441715750125694545186319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 189513205338696300594616277 4441715750125694545186319)
            ·
              refine ⟨6662573625188541817779479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4441715750125694545186319 6662573625188541817779479)
              ·
                refine ⟨9993860437782812726669219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6662573625188541817779479 9993860437782812726669219)
                ·
                  refine ⟨14990790656674219090003829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9993860437782812726669219 14990790656674219090003829)
                  ·
                    refine ⟨1405386624063208039687859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14990790656674219090003829 1405386624063208039687859)
                    ·
                      rfl

theorem cell22_4105471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 5].length) (baseStart_4105471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105471 prefixEnd_4105471 := by exact prefixLift 4105471
  have htrace : WordTrace (prefixWord ++ tailWord_4105471) baseStart_4105471 baseEnd_4105471 := by
    simpa [prefixWord, tailWord_4105471, baseEnd_4105471] using wordTrace_append hprefix tailTrace_4105471
  have hstable : (prefixWord ++ tailWord_4105471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105471).length < 2 ^ (prefixWord ++ tailWord_4105471).sum := by decide
  have hdescent : baseEnd_4105471 < baseStart_4105471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105484 : List Nat := [2, 2, 1, 2, 2, 4, 1, 8]
def baseStart_4105484 : Nat := 118140960795 + 4105484 * 2 ^ 59
def prefixEnd_4105484 : Nat := 4983230072969 + 3 ^ 40 * 4105484 * 2
def baseEnd_4105484 : Nat := 156154563803208926568091

theorem tailTrace_4105484 : CollatzResearch.WordTrace tailWord_4105484 prefixEnd_4105484 156154563803208926568091 := by
  unfold tailWord_4105484
  simp only [CollatzResearch.WordTrace]
  refine ⟨74869651529270051845021753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99826202039026735793362337 74869651529270051845021753)
  ·
    refine ⟨56152238646952538883766315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74869651529270051845021753 56152238646952538883766315)
    ·
      refine ⟨84228357970428808325649473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56152238646952538883766315 84228357970428808325649473)
      ·
        refine ⟨63171268477821606244237105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84228357970428808325649473 63171268477821606244237105)
        ·
          refine ⟨47378451358366204683177829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63171268477821606244237105 47378451358366204683177829)
          ·
            refine ⟨8883459629693663378095843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47378451358366204683177829 8883459629693663378095843)
            ·
              refine ⟨13325189444540495067143765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883459629693663378095843 13325189444540495067143765)
              ·
                refine ⟨156154563803208926568091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13325189444540495067143765 156154563803208926568091)
                ·
                  rfl

theorem cell22_4105484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 8].length) (baseStart_4105484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105484 prefixEnd_4105484 := by exact prefixLift 4105484
  have htrace : WordTrace (prefixWord ++ tailWord_4105484) baseStart_4105484 baseEnd_4105484 := by
    simpa [prefixWord, tailWord_4105484, baseEnd_4105484] using wordTrace_append hprefix tailTrace_4105484
  have hstable : (prefixWord ++ tailWord_4105484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105484).length < 2 ^ (prefixWord ++ tailWord_4105484).sum := by decide
  have hdescent : baseEnd_4105484 < baseStart_4105484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105501 : List Nat := [1, 4, 2, 3, 1, 3, 8]
def baseStart_4105501 : Nat := 118140960795 + 4105501 * 2 ^ 59
def prefixEnd_4105501 : Nat := 4983230072969 + 3 ^ 40 * 4105501 * 2
def baseEnd_4105501 : Nat := 52051736802825850423621

theorem tailTrace_4105501 : CollatzResearch.WordTrace tailWord_4105501 prefixEnd_4105501 52051736802825850423621 := by
  unfold tailWord_4105501
  simp only [CollatzResearch.WordTrace]
  refine ⟨149739923099478515593412357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99826615399652343728941571 149739923099478515593412357)
  ·
    refine ⟨28076235581152221673764817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149739923099478515593412357 28076235581152221673764817)
    ·
      refine ⟨21057176685864166255323613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28076235581152221673764817 21057176685864166255323613)
      ·
        refine ⟨7896441257199062345746355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21057176685864166255323613 7896441257199062345746355)
        ·
          refine ⟨11844661885798593518619533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7896441257199062345746355 11844661885798593518619533)
          ·
            refine ⟨4441748207174472569482325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11844661885798593518619533 4441748207174472569482325)
            ·
              refine ⟨52051736802825850423621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4441748207174472569482325 52051736802825850423621)
              ·
                rfl

theorem cell22_4105501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 8].length) (baseStart_4105501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105501 prefixEnd_4105501 := by exact prefixLift 4105501
  have htrace : WordTrace (prefixWord ++ tailWord_4105501) baseStart_4105501 baseEnd_4105501 := by
    simpa [prefixWord, tailWord_4105501, baseEnd_4105501] using wordTrace_append hprefix tailTrace_4105501
  have hstable : (prefixWord ++ tailWord_4105501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105501).length < 2 ^ (prefixWord ++ tailWord_4105501).sum := by decide
  have hdescent : baseEnd_4105501 < baseStart_4105501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105544 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 4, 5]
def baseStart_4105544 : Nat := 118140960795 + 4105544 * 2 ^ 59
def prefixEnd_4105544 : Nat := 4983230072969 + 3 ^ 40 * 4105544 * 2
def baseEnd_4105544 : Nat := 1405411613455060182612635

theorem tailTrace_4105544 : CollatzResearch.WordTrace tailWord_4105544 prefixEnd_4105544 1405411613455060182612635 := by
  unfold tailWord_4105544
  simp only [CollatzResearch.WordTrace]
  refine ⟨74870745719161366968613843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99827660958881822624818457 74870745719161366968613843)
  ·
    refine ⟨112306118578742050452920765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74870745719161366968613843 112306118578742050452920765)
    ·
      refine ⟨42114794467028268919845287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112306118578742050452920765 42114794467028268919845287)
      ·
        refine ⟨63172191700542403379767931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42114794467028268919845287 63172191700542403379767931)
        ·
          refine ⟨94758287550813605069651897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63172191700542403379767931 94758287550813605069651897)
          ·
            refine ⟨71068715663110203802238923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94758287550813605069651897 71068715663110203802238923)
            ·
              refine ⟨106603073494665305703358385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71068715663110203802238923 106603073494665305703358385)
              ·
                refine ⟨79952305120998979277518789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106603073494665305703358385 79952305120998979277518789)
                ·
                  refine ⟨14991057210187308614534773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79952305120998979277518789 14991057210187308614534773)
                  ·
                    refine ⟨1405411613455060182612635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14991057210187308614534773 1405411613455060182612635)
                    ·
                      rfl

theorem cell22_4105544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_4105544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105544 prefixEnd_4105544 := by exact prefixLift 4105544
  have htrace : WordTrace (prefixWord ++ tailWord_4105544) baseStart_4105544 baseEnd_4105544 := by
    simpa [prefixWord, tailWord_4105544, baseEnd_4105544] using wordTrace_append hprefix tailTrace_4105544
  have hstable : (prefixWord ++ tailWord_4105544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105544).length < 2 ^ (prefixWord ++ tailWord_4105544).sum := by decide
  have hdescent : baseEnd_4105544 < baseStart_4105544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105558 : List Nat := [5, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_4105558 : Nat := 118140960795 + 4105558 * 2 ^ 59
def prefixEnd_4105558 : Nat := 4983230072969 + 3 ^ 40 * 4105558 * 2
def baseEnd_4105558 : Nat := 468472135313722937587531

theorem tailTrace_4105558 : CollatzResearch.WordTrace tailWord_4105558 prefixEnd_4105558 468472135313722937587531 := by
  unfold tailWord_4105558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9358875128767000895514833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99828001373514676218824885 9358875128767000895514833)
  ·
    refine ⟨7019156346575250671636125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9358875128767000895514833 7019156346575250671636125)
    ·
      refine ⟨2632183629965719001863547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7019156346575250671636125 2632183629965719001863547)
      ·
        refine ⟨3948275444948578502795321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632183629965719001863547 3948275444948578502795321)
        ·
          refine ⟨2961206583711433877096491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3948275444948578502795321 2961206583711433877096491)
          ·
            refine ⟨4441809875567150815644737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961206583711433877096491 4441809875567150815644737)
            ·
              refine ⟨3331357406675363111733553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4441809875567150815644737 3331357406675363111733553)
              ·
                refine ⟨2498518055006522333800165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3331357406675363111733553 2498518055006522333800165)
                ·
                  refine ⟨468472135313722937587531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2498518055006522333800165 468472135313722937587531)
                  ·
                    rfl

theorem cell22_4105558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_4105558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105558 prefixEnd_4105558 := by exact prefixLift 4105558
  have htrace : WordTrace (prefixWord ++ tailWord_4105558) baseStart_4105558 baseEnd_4105558 := by
    simpa [prefixWord, tailWord_4105558, baseEnd_4105558] using wordTrace_append hprefix tailTrace_4105558
  have hstable : (prefixWord ++ tailWord_4105558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105558).length < 2 ^ (prefixWord ++ tailWord_4105558).sum := by decide
  have hdescent : baseEnd_4105558 < baseStart_4105558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105578 : List Nat := [3, 1, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_4105578 : Nat := 118140960795 + 4105578 * 2 ^ 59
def prefixEnd_4105578 : Nat := 4983230072969 + 3 ^ 40 * 4105578 * 2
def baseEnd_4105578 : Nat := 1405423252349895427262531

theorem tailTrace_4105578 : CollatzResearch.WordTrace tailWord_4105578 prefixEnd_4105578 1405423252349895427262531 := by
  unfold tailWord_4105578
  simp only [CollatzResearch.WordTrace]
  refine ⟨37435682880049889435991347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99828487680133038495976925 37435682880049889435991347)
  ·
    refine ⟨56153524320074834153987021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37435682880049889435991347 56153524320074834153987021)
    ·
      refine ⟨21057571620028062807745133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56153524320074834153987021 21057571620028062807745133)
      ·
        refine ⟨7896589357510523552904425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21057571620028062807745133 7896589357510523552904425)
        ·
          refine ⟨5922442018132892664678319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7896589357510523552904425 5922442018132892664678319)
          ·
            refine ⟨8883663027199338997017479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5922442018132892664678319 8883663027199338997017479)
            ·
              refine ⟨13325494540799008495526219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883663027199338997017479 13325494540799008495526219)
              ·
                refine ⟨19988241811198512743289329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13325494540799008495526219 19988241811198512743289329)
                ·
                  refine ⟨14991181358398884557466997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19988241811198512743289329 14991181358398884557466997)
                  ·
                    refine ⟨1405423252349895427262531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14991181358398884557466997 1405423252349895427262531)
                    ·
                      rfl

theorem cell22_4105578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_4105578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105578 prefixEnd_4105578 := by exact prefixLift 4105578
  have htrace : WordTrace (prefixWord ++ tailWord_4105578) baseStart_4105578 baseEnd_4105578 := by
    simpa [prefixWord, tailWord_4105578, baseEnd_4105578] using wordTrace_append hprefix tailTrace_4105578
  have hstable : (prefixWord ++ tailWord_4105578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105578).length < 2 ^ (prefixWord ++ tailWord_4105578).sum := by decide
  have hdescent : baseEnd_4105578 < baseStart_4105578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105608 : List Nat := [2, 1, 3, 3, 1, 2, 1, 5, 4]
def baseStart_4105608 : Nat := 118140960795 + 4105608 * 2 ^ 59
def prefixEnd_4105608 : Nat := 4983230072969 + 3 ^ 40 * 4105608 * 2
def baseEnd_4105608 : Nat := 468477840654328449670813

theorem tailTrace_4105608 : CollatzResearch.WordTrace tailWord_4105608 prefixEnd_4105608 468477840654328449670813 := by
  unfold tailWord_4105608
  simp only [CollatzResearch.WordTrace]
  refine ⟨74871912855045436433778739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99829217140060581911704985 74871912855045436433778739)
  ·
    refine ⟨112307869282568154650668109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74871912855045436433778739 112307869282568154650668109)
    ·
      refine ⟨42115450980963057994000541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112307869282568154650668109 42115450980963057994000541)
      ·
        refine ⟨15793294117861146747750203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42115450980963057994000541 15793294117861146747750203)
        ·
          refine ⟨23689941176791720121625305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15793294117861146747750203 23689941176791720121625305)
          ·
            refine ⟨17767455882593790091218979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23689941176791720121625305 17767455882593790091218979)
            ·
              refine ⟨26651183823890685136828469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17767455882593790091218979 26651183823890685136828469)
              ·
                refine ⟨2498548483489751731577669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26651183823890685136828469 2498548483489751731577669)
                ·
                  refine ⟨468477840654328449670813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2498548483489751731577669 468477840654328449670813)
                  ·
                    rfl

theorem cell22_4105608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 5, 4].length) (baseStart_4105608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105608 prefixEnd_4105608 := by exact prefixLift 4105608
  have htrace : WordTrace (prefixWord ++ tailWord_4105608) baseStart_4105608 baseEnd_4105608 := by
    simpa [prefixWord, tailWord_4105608, baseEnd_4105608] using wordTrace_append hprefix tailTrace_4105608
  have hstable : (prefixWord ++ tailWord_4105608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105608).length < 2 ^ (prefixWord ++ tailWord_4105608).sum := by decide
  have hdescent : baseEnd_4105608 < baseStart_4105608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105621 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_4105621 : Nat := 118140960795 + 4105621 * 2 ^ 59
def prefixEnd_4105621 : Nat := 4983230072969 + 3 ^ 40 * 4105621 * 2
def baseEnd_4105621 : Nat := 1405437972128657648437399

theorem tailTrace_4105621 : CollatzResearch.WordTrace tailWord_4105621 prefixEnd_4105621 1405437972128657648437399 := by
  unfold tailWord_4105621
  simp only [CollatzResearch.WordTrace]
  refine ⟨149744299859043776087780717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99829533239362517391853811 149744299859043776087780717)
  ·
    refine ⟨56154112447141416032917769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149744299859043776087780717 56154112447141416032917769)
    ·
      refine ⟨42115584335356062024688327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56154112447141416032917769 42115584335356062024688327)
      ·
        refine ⟨63173376503034093037032491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42115584335356062024688327 63173376503034093037032491)
        ·
          refine ⟨94760064754551139555548737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63173376503034093037032491 94760064754551139555548737)
          ·
            refine ⟨71070048565913354666661553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94760064754551139555548737 71070048565913354666661553)
            ·
              refine ⟨53302536424435015999996165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71070048565913354666661553 53302536424435015999996165)
              ·
                refine ⟨9994225579581565499999281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53302536424435015999996165 9994225579581565499999281)
                ·
                  refine ⟨7495669184686174124999461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9994225579581565499999281 7495669184686174124999461)
                  ·
                    refine ⟨1405437972128657648437399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7495669184686174124999461 1405437972128657648437399)
                    ·
                      rfl

theorem cell22_4105621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_4105621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105621 prefixEnd_4105621 := by exact prefixLift 4105621
  have htrace : WordTrace (prefixWord ++ tailWord_4105621) baseStart_4105621 baseEnd_4105621 := by
    simpa [prefixWord, tailWord_4105621, baseEnd_4105621] using wordTrace_append hprefix tailTrace_4105621
  have hstable : (prefixWord ++ tailWord_4105621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105621).length < 2 ^ (prefixWord ++ tailWord_4105621).sum := by decide
  have hdescent : baseEnd_4105621 < baseStart_4105621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105653 : List Nat := [1, 3, 3, 2, 2, 1, 4, 6]
def baseStart_4105653 : Nat := 118140960795 + 4105653 * 2 ^ 59
def prefixEnd_4105653 : Nat := 4983230072969 + 3 ^ 40 * 4105653 * 2
def baseEnd_4105653 : Nat := 156160991820291136848589

theorem tailTrace_4105653 : CollatzResearch.WordTrace tailWord_4105653 prefixEnd_4105653 156160991820291136848589 := by
  unfold tailWord_4105653
  simp only [CollatzResearch.WordTrace]
  refine ⟨149745466994927845552945613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99830311329951897035297075 149745466994927845552945613)
  ·
    refine ⟨56154550123097942082354605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149745466994927845552945613 56154550123097942082354605)
    ·
      refine ⟨21057956296161728280882977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56154550123097942082354605 21057956296161728280882977)
      ·
        refine ⟨15793467222121296210662233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21057956296161728280882977 15793467222121296210662233)
        ·
          refine ⟨11845100416590972157996675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15793467222121296210662233 11845100416590972157996675)
          ·
            refine ⟨17767650624886458236995013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11845100416590972157996675 17767650624886458236995013)
            ·
              refine ⟨3331434492166210919436565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17767650624886458236995013 3331434492166210919436565)
              ·
                refine ⟨156160991820291136848589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3331434492166210919436565 156160991820291136848589)
                ·
                  rfl

theorem cell22_4105653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 6].length) (baseStart_4105653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105653 prefixEnd_4105653 := by exact prefixLift 4105653
  have htrace : WordTrace (prefixWord ++ tailWord_4105653) baseStart_4105653 baseEnd_4105653 := by
    simpa [prefixWord, tailWord_4105653, baseEnd_4105653] using wordTrace_append hprefix tailTrace_4105653
  have hstable : (prefixWord ++ tailWord_4105653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105653).length < 2 ^ (prefixWord ++ tailWord_4105653).sum := by decide
  have hdescent : baseEnd_4105653 < baseStart_4105653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105788 : List Nat := [2, 2, 2, 2, 4, 1, 9]
def baseStart_4105788 : Nat := 118140960795 + 4105788 * 2 ^ 59
def prefixEnd_4105788 : Nat := 4983230072969 + 3 ^ 40 * 4105788 * 2
def baseEnd_4105788 : Nat := 52055375542278699241181

theorem tailTrace_4105788 : CollatzResearch.WordTrace tailWord_4105788 prefixEnd_4105788 52055375542278699241181 := by
  unfold tailWord_4105788
  simp only [CollatzResearch.WordTrace]
  refine ⟨74875195424719381804555009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99833593899625842406073345 74875195424719381804555009)
  ·
    refine ⟨56156396568539536353416257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74875195424719381804555009 56156396568539536353416257)
    ·
      refine ⟨42117297426404652265062193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56156396568539536353416257 42117297426404652265062193)
      ·
        refine ⟨31587973069803489198796645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42117297426404652265062193 31587973069803489198796645)
        ·
          refine ⟨5922744950588154224774371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31587973069803489198796645 5922744950588154224774371)
          ·
            refine ⟨8884117425882231337161557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5922744950588154224774371 8884117425882231337161557)
            ·
              refine ⟨52055375542278699241181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8884117425882231337161557 52055375542278699241181)
              ·
                rfl

theorem cell22_4105788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 9].length) (baseStart_4105788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105788 prefixEnd_4105788 := by exact prefixLift 4105788
  have htrace : WordTrace (prefixWord ++ tailWord_4105788) baseStart_4105788 baseEnd_4105788 := by
    simpa [prefixWord, tailWord_4105788, baseEnd_4105788] using wordTrace_append hprefix tailTrace_4105788
  have hstable : (prefixWord ++ tailWord_4105788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105788).length < 2 ^ (prefixWord ++ tailWord_4105788).sum := by decide
  have hdescent : baseEnd_4105788 < baseStart_4105788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105801 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_4105801 : Nat := 118140960795 + 4105801 * 2 ^ 59
def prefixEnd_4105801 : Nat := 4983230072969 + 3 ^ 40 * 4105801 * 2
def baseEnd_4105801 : Nat := 1405499589807197178936847

theorem tailTrace_4105801 : CollatzResearch.WordTrace tailWord_4105801 prefixEnd_4105801 1405499589807197178936847 := by
  unfold tailWord_4105801
  simp only [CollatzResearch.WordTrace]
  refine ⟨149750864998391666829333257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99833909998927777886222171 149750864998391666829333257)
  ·
    refine ⟨112313148748793750121999943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149750864998391666829333257 112313148748793750121999943)
    ·
      refine ⟨168469723123190625182999915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112313148748793750121999943 168469723123190625182999915)
      ·
        refine ⟨252704584684785937774499873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168469723123190625182999915 252704584684785937774499873)
        ·
          refine ⟨189528438513589453330874905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252704584684785937774499873 189528438513589453330874905)
          ·
            refine ⟨142146328885192089998156179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189528438513589453330874905 142146328885192089998156179)
            ·
              refine ⟨213219493327788134997234269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142146328885192089998156179 213219493327788134997234269)
              ·
                refine ⟨79957309997920550623962851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 213219493327788134997234269 79957309997920550623962851)
                ·
                  refine ⟨119935964996880825935944277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79957309997920550623962851 119935964996880825935944277)
                  ·
                    refine ⟨1405499589807197178936847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119935964996880825935944277 1405499589807197178936847)
                    ·
                      rfl

theorem cell22_4105801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_4105801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105801 prefixEnd_4105801 := by exact prefixLift 4105801
  have htrace : WordTrace (prefixWord ++ tailWord_4105801) baseStart_4105801 baseEnd_4105801 := by
    simpa [prefixWord, tailWord_4105801, baseEnd_4105801] using wordTrace_append hprefix tailTrace_4105801
  have hstable : (prefixWord ++ tailWord_4105801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105801).length < 2 ^ (prefixWord ++ tailWord_4105801).sum := by decide
  have hdescent : baseEnd_4105801 < baseStart_4105801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105880 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 3, 4]
def baseStart_4105880 : Nat := 118140960795 + 4105880 * 2 ^ 59
def prefixEnd_4105880 : Nat := 4983230072969 + 3 ^ 40 * 4105880 * 2
def baseEnd_4105880 : Nat := 1405526633121667306211605

theorem tailTrace_4105880 : CollatzResearch.WordTrace tailWord_4105880 prefixEnd_4105880 1405526633121667306211605 := by
  unfold tailWord_4105880
  simp only [CollatzResearch.WordTrace]
  refine ⟨74876873182552731660729547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99835830910070308880972729 74876873182552731660729547)
  ·
    refine ⟨112315309773829097491094321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74876873182552731660729547 112315309773829097491094321)
    ·
      refine ⟨84236482330371823118320741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112315309773829097491094321 84236482330371823118320741)
      ·
        refine ⟨15794340436944716834685139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84236482330371823118320741 15794340436944716834685139)
        ·
          refine ⟨23691510655417075252027709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15794340436944716834685139 23691510655417075252027709)
          ·
            refine ⟨8884316495781403219510391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23691510655417075252027709 8884316495781403219510391)
            ·
              refine ⟨13326474743672104829265587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8884316495781403219510391 13326474743672104829265587)
              ·
                refine ⟨19989712115508157243898381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13326474743672104829265587 19989712115508157243898381)
                ·
                  refine ⟨7496142043315558966461893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19989712115508157243898381 7496142043315558966461893)
                  ·
                    refine ⟨1405526633121667306211605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7496142043315558966461893 1405526633121667306211605)
                    ·
                      rfl

theorem cell22_4105880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_4105880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105880 prefixEnd_4105880 := by exact prefixLift 4105880
  have htrace : WordTrace (prefixWord ++ tailWord_4105880) baseStart_4105880 baseEnd_4105880 := by
    simpa [prefixWord, tailWord_4105880, baseEnd_4105880] using wordTrace_append hprefix tailTrace_4105880
  have hstable : (prefixWord ++ tailWord_4105880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105880).length < 2 ^ (prefixWord ++ tailWord_4105880).sum := by decide
  have hdescent : baseEnd_4105880 < baseStart_4105880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105893 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_4105893 : Nat := 118140960795 + 4105893 * 2 ^ 59
def prefixEnd_4105893 : Nat := 4983230072969 + 3 ^ 40 * 4105893 * 2
def baseEnd_4105893 : Nat := 1405531083287339605636565

theorem tailTrace_4105893 : CollatzResearch.WordTrace tailWord_4105893 prefixEnd_4105893 1405531083287339605636565 := by
  unfold tailWord_4105893
  simp only [CollatzResearch.WordTrace]
  refine ⟨149754220514058366541682333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99836147009372244361121555 149754220514058366541682333)
  ·
    refine ⟨56157832692771887453130875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149754220514058366541682333 56157832692771887453130875)
    ·
      refine ⟨84236749039157831179696313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56157832692771887453130875 84236749039157831179696313)
      ·
        refine ⟨63177561779368373384772235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84236749039157831179696313 63177561779368373384772235)
        ·
          refine ⟨94766342669052560077158353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63177561779368373384772235 94766342669052560077158353)
          ·
            refine ⟨71074757001789420057868765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94766342669052560077158353 71074757001789420057868765)
            ·
              refine ⟨26653033875671032521700787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71074757001789420057868765 26653033875671032521700787)
              ·
                refine ⟨39979550813506548782551181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26653033875671032521700787 39979550813506548782551181)
                ·
                  refine ⟨14992331555064955793456693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39979550813506548782551181 14992331555064955793456693)
                  ·
                    refine ⟨1405531083287339605636565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14992331555064955793456693 1405531083287339605636565)
                    ·
                      rfl

theorem cell22_4105893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_4105893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105893 prefixEnd_4105893 := by exact prefixLift 4105893
  have htrace : WordTrace (prefixWord ++ tailWord_4105893) baseStart_4105893 baseEnd_4105893 := by
    simpa [prefixWord, tailWord_4105893, baseEnd_4105893] using wordTrace_append hprefix tailTrace_4105893
  have hstable : (prefixWord ++ tailWord_4105893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105893).length < 2 ^ (prefixWord ++ tailWord_4105893).sum := by decide
  have hdescent : baseEnd_4105893 < baseStart_4105893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105948 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 1, 4]
def baseStart_4105948 : Nat := 118140960795 + 4105948 * 2 ^ 59
def prefixEnd_4105948 : Nat := 4983230072969 + 3 ^ 40 * 4105948 * 2
def baseEnd_4105948 : Nat := 1405549910911337795511397

theorem tailTrace_4105948 : CollatzResearch.WordTrace tailWord_4105948 prefixEnd_4105948 1405549910911337795511397 := by
  unfold tailWord_4105948
  simp only [CollatzResearch.WordTrace]
  refine ⟨74878113264429555467467249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99837484352572740623289665 74878113264429555467467249)
  ·
    refine ⟨56158584948322166600600437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74878113264429555467467249 56158584948322166600600437)
    ·
      refine ⟨5264867338905203118806291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56158584948322166600600437 5264867338905203118806291)
      ·
        refine ⟨7897301008357804678209437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5264867338905203118806291 7897301008357804678209437)
        ·
          refine ⟨2961487878134176754328539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7897301008357804678209437 2961487878134176754328539)
          ·
            refine ⟨4442231817201265131492809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961487878134176754328539 4442231817201265131492809)
            ·
              refine ⟨3331673862900948848619607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4442231817201265131492809 3331673862900948848619607)
              ·
                refine ⟨4997510794351423272929411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331673862900948848619607 4997510794351423272929411)
                ·
                  refine ⟨7496266191527134909394117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997510794351423272929411 7496266191527134909394117)
                  ·
                    refine ⟨1405549910911337795511397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7496266191527134909394117 1405549910911337795511397)
                    ·
                      rfl

theorem cell22_4105948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_4105948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105948 prefixEnd_4105948 := by exact prefixLift 4105948
  have htrace : WordTrace (prefixWord ++ tailWord_4105948) baseStart_4105948 baseEnd_4105948 := by
    simpa [prefixWord, tailWord_4105948, baseEnd_4105948] using wordTrace_append hprefix tailTrace_4105948
  have hstable : (prefixWord ++ tailWord_4105948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105948).length < 2 ^ (prefixWord ++ tailWord_4105948).sum := by decide
  have hdescent : baseEnd_4105948 < baseStart_4105948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105985 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 5]
def baseStart_4105985 : Nat := 118140960795 + 4105985 * 2 ^ 59
def prefixEnd_4105985 : Nat := 4983230072969 + 3 ^ 40 * 4105985 * 2
def baseEnd_4105985 : Nat := 468520858922494010778761

theorem tailTrace_4105985 : CollatzResearch.WordTrace tailWord_4105985 prefixEnd_4105985 468520858922494010778761 := by
  unfold tailWord_4105985
  simp only [CollatzResearch.WordTrace]
  refine ⟨149757576029725066254031409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99838384019816710836020939 149757576029725066254031409)
  ·
    refine ⟨112318182022293799690523557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149757576029725066254031409 112318182022293799690523557)
    ·
      refine ⟨21059659129180087441973167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112318182022293799690523557 21059659129180087441973167)
      ·
        refine ⟨31589488693770131162959751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21059659129180087441973167 31589488693770131162959751)
        ·
          refine ⟨47384233040655196744439627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31589488693770131162959751 47384233040655196744439627)
          ·
            refine ⟨71076349560982795116659441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47384233040655196744439627 71076349560982795116659441)
            ·
              refine ⟨53307262170737096337494581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71076349560982795116659441 53307262170737096337494581)
              ·
                refine ⟨4997555828506602781640117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53307262170737096337494581 4997555828506602781640117)
                ·
                  refine ⟨468520858922494010778761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4997555828506602781640117 468520858922494010778761)
                  ·
                    rfl

theorem cell22_4105985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_4105985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105985 prefixEnd_4105985 := by exact prefixLift 4105985
  have htrace : WordTrace (prefixWord ++ tailWord_4105985) baseStart_4105985 baseEnd_4105985 := by
    simpa [prefixWord, tailWord_4105985, baseEnd_4105985] using wordTrace_append hprefix tailTrace_4105985
  have hstable : (prefixWord ++ tailWord_4105985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105985).length < 2 ^ (prefixWord ++ tailWord_4105985).sum := by decide
  have hdescent : baseEnd_4105985 < baseStart_4105985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4105997 : List Nat := [1, 7, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4105997 : Nat := 118140960795 + 4105997 * 2 ^ 59
def prefixEnd_4105997 : Nat := 4983230072969 + 3 ^ 40 * 4105997 * 2
def baseEnd_4105997 : Nat := 468522228204239333678749

theorem tailTrace_4105997 : CollatzResearch.WordTrace tailWord_4105997 prefixEnd_4105997 468522228204239333678749 := by
  unfold tailWord_4105997
  simp only [CollatzResearch.WordTrace]
  refine ⟨149758013705681592303468245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99838675803787728202312163 149758013705681592303468245)
  ·
    refine ⟨3509953446226912319612537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 149758013705681592303468245 3509953446226912319612537)
    ·
      refine ⟨2632465084670184239709403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3509953446226912319612537 2632465084670184239709403)
      ·
        refine ⟨3948697627005276359564105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2632465084670184239709403 3948697627005276359564105)
        ·
          refine ⟨2961523220253957269673079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3948697627005276359564105 2961523220253957269673079)
          ·
            refine ⟨4442284830380935904509619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961523220253957269673079 4442284830380935904509619)
            ·
              refine ⟨6663427245571403856764429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442284830380935904509619 6663427245571403856764429)
              ·
                refine ⟨2498785217089276446286661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6663427245571403856764429 2498785217089276446286661)
                ·
                  refine ⟨468522228204239333678749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2498785217089276446286661 468522228204239333678749)
                  ·
                    rfl

theorem cell22_4105997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4105997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4105997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4105997 prefixEnd_4105997 := by exact prefixLift 4105997
  have htrace : WordTrace (prefixWord ++ tailWord_4105997) baseStart_4105997 baseEnd_4105997 := by
    simpa [prefixWord, tailWord_4105997, baseEnd_4105997] using wordTrace_append hprefix tailTrace_4105997
  have hstable : (prefixWord ++ tailWord_4105997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4105997).length < 2 ^ (prefixWord ++ tailWord_4105997).sum := by decide
  have hdescent : baseEnd_4105997 < baseStart_4105997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4105997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106002 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_4106002 : Nat := 118140960795 + 4106002 * 2 ^ 59
def prefixEnd_4106002 : Nat := 4983230072969 + 3 ^ 40 * 4106002 * 2
def baseEnd_4106002 : Nat := 468522798738299884887077

theorem tailTrace_4106002 : CollatzResearch.WordTrace tailWord_4106002 prefixEnd_4106002 468522798738299884887077 := by
  unfold tailWord_4106002
  simp only [CollatzResearch.WordTrace]
  refine ⟨37439549017665869539350065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99838797380442318771600173 37439549017665869539350065)
  ·
    refine ⟨28079661763249402154512549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37439549017665869539350065 28079661763249402154512549)
    ·
      refine ⟨5264936580609262903971103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28079661763249402154512549 5264936580609262903971103)
      ·
        refine ⟨7897404870913894355956655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5264936580609262903971103 7897404870913894355956655)
        ·
          refine ⟨11846107306370841533934983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7897404870913894355956655 11846107306370841533934983)
          ·
            refine ⟨17769160959556262300902475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11846107306370841533934983 17769160959556262300902475)
            ·
              refine ⟨26653741439334393451353713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17769160959556262300902475 26653741439334393451353713)
              ·
                refine ⟨19990306079500795088515285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26653741439334393451353713 19990306079500795088515285)
                ·
                  refine ⟨468522798738299884887077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19990306079500795088515285 468522798738299884887077)
                  ·
                    rfl

theorem cell22_4106002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_4106002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106002 prefixEnd_4106002 := by exact prefixLift 4106002
  have htrace : WordTrace (prefixWord ++ tailWord_4106002) baseStart_4106002 baseEnd_4106002 := by
    simpa [prefixWord, tailWord_4106002, baseEnd_4106002] using wordTrace_append hprefix tailTrace_4106002
  have hstable : (prefixWord ++ tailWord_4106002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106002).length < 2 ^ (prefixWord ++ tailWord_4106002).sum := by decide
  have hdescent : baseEnd_4106002 < baseStart_4106002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106036 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 5]
def baseStart_4106036 : Nat := 118140960795 + 4106036 * 2 ^ 59
def prefixEnd_4106036 : Nat := 4983230072969 + 3 ^ 40 * 4106036 * 2
def baseEnd_4106036 : Nat := 468526678369911633103709

theorem tailTrace_4106036 : CollatzResearch.WordTrace tailWord_4106036 prefixEnd_4106036 468526678369911633103709 := by
  unfold tailWord_4106036
  simp only [CollatzResearch.WordTrace]
  refine ⟨74879718076270150982068981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99839624101693534642758641 74879718076270150982068981)
  ·
    refine ⟨7019973569650326654568967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74879718076270150982068981 7019973569650326654568967)
    ·
      refine ⟨10529960354475489981853451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7019973569650326654568967 10529960354475489981853451)
      ·
        refine ⟨15794940531713234972780177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10529960354475489981853451 15794940531713234972780177)
        ·
          refine ⟨11846205398784926229585133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15794940531713234972780177 11846205398784926229585133)
          ·
            refine ⟨4442327024544347336094425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11846205398784926229585133 4442327024544347336094425)
            ·
              refine ⟨3331745268408260502070819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4442327024544347336094425 3331745268408260502070819)
              ·
                refine ⟨4997617902612390753106229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3331745268408260502070819 4997617902612390753106229)
                ·
                  refine ⟨468526678369911633103709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4997617902612390753106229 468526678369911633103709)
                  ·
                    rfl

theorem cell22_4106036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_4106036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106036 prefixEnd_4106036 := by exact prefixLift 4106036
  have htrace : WordTrace (prefixWord ++ tailWord_4106036) baseStart_4106036 baseEnd_4106036 := by
    simpa [prefixWord, tailWord_4106036, baseEnd_4106036] using wordTrace_append hprefix tailTrace_4106036
  have hstable : (prefixWord ++ tailWord_4106036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106036).length < 2 ^ (prefixWord ++ tailWord_4106036).sum := by decide
  have hdescent : baseEnd_4106036 < baseStart_4106036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106079 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 2, 3]
def baseStart_4106079 : Nat := 118140960795 + 4106079 * 2 ^ 59
def prefixEnd_4106079 : Nat := 4983230072969 + 3 ^ 40 * 4106079 * 2
def baseEnd_4106079 : Nat := 1405594754888497120485995

theorem tailTrace_4106079 : CollatzResearch.WordTrace tailWord_4106079 prefixEnd_4106079 1405594754888497120485995 := by
  unfold tailWord_4106079
  simp only [CollatzResearch.WordTrace]
  refine ⟨149761004491384520307953291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99840669660923013538635527 149761004491384520307953291)
  ·
    refine ⟨224641506737076780461929937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149761004491384520307953291 224641506737076780461929937)
    ·
      refine ⟨168481130052807585346447453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224641506737076780461929937 168481130052807585346447453)
      ·
        refine ⟨63180423769802844504917795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168481130052807585346447453 63180423769802844504917795)
        ·
          refine ⟨94770635654704266757376693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63180423769802844504917795 94770635654704266757376693)
          ·
            refine ⟨8884747092628525008504065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94770635654704266757376693 8884747092628525008504065)
            ·
              refine ⟨6663560319471393756378049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8884747092628525008504065 6663560319471393756378049)
              ·
                refine ⟨4997670239603545317283537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6663560319471393756378049 4997670239603545317283537)
                ·
                  refine ⟨3748252679702658987962653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4997670239603545317283537 3748252679702658987962653)
                  ·
                    refine ⟨1405594754888497120485995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3748252679702658987962653 1405594754888497120485995)
                    ·
                      rfl

theorem cell22_4106079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 3].length) (baseStart_4106079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106079 prefixEnd_4106079 := by exact prefixLift 4106079
  have htrace : WordTrace (prefixWord ++ tailWord_4106079) baseStart_4106079 baseEnd_4106079 := by
    simpa [prefixWord, tailWord_4106079, baseEnd_4106079] using wordTrace_append hprefix tailTrace_4106079
  have hstable : (prefixWord ++ tailWord_4106079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106079).length < 2 ^ (prefixWord ++ tailWord_4106079).sum := by decide
  have hdescent : baseEnd_4106079 < baseStart_4106079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106092 : List Nat := [2, 2, 1, 1, 4, 4, 1, 7]
def baseStart_4106092 : Nat := 118140960795 + 4106092 * 2 ^ 59
def prefixEnd_4106092 : Nat := 4983230072969 + 3 ^ 40 * 4106092 * 2
def baseEnd_4106092 : Nat := 156177689450463268878995

theorem tailTrace_4106092 : CollatzResearch.WordTrace tailWord_4106092 prefixEnd_4106092 156177689450463268878995 := by
  unfold tailWord_4106092
  simp only [CollatzResearch.WordTrace]
  refine ⟨74880739320168711764088265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99840985760224949018784353 74880739320168711764088265)
  ·
    refine ⟨56160554490126533823066199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74880739320168711764088265 56160554490126533823066199)
    ·
      refine ⟨84240831735189800734599299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56160554490126533823066199 84240831735189800734599299)
      ·
        refine ⟨126361247602784701101898949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84240831735189800734599299 126361247602784701101898949)
        ·
          refine ⟨23692733925522131456606053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126361247602784701101898949 23692733925522131456606053)
          ·
            refine ⟨4442387611035399648113635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23692733925522131456606053 4442387611035399648113635)
            ·
              refine ⟨6663581416553099472170453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442387611035399648113635 6663581416553099472170453)
              ·
                refine ⟨156177689450463268878995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6663581416553099472170453 156177689450463268878995)
                ·
                  rfl

theorem cell22_4106092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 7].length) (baseStart_4106092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106092 prefixEnd_4106092 := by exact prefixLift 4106092
  have htrace : WordTrace (prefixWord ++ tailWord_4106092) baseStart_4106092 baseEnd_4106092 := by
    simpa [prefixWord, tailWord_4106092, baseEnd_4106092] using wordTrace_append hprefix tailTrace_4106092
  have hstable : (prefixWord ++ tailWord_4106092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106092).length < 2 ^ (prefixWord ++ tailWord_4106092).sum := by decide
  have hdescent : baseEnd_4106092 < baseStart_4106092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106105 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_4106105 : Nat := 118140960795 + 4106105 * 2 ^ 59
def prefixEnd_4106105 : Nat := 4983230072969 + 3 ^ 40 * 4106105 * 2
def baseEnd_4106105 : Nat := 1405603655219841719335915

theorem tailTrace_4106105 : CollatzResearch.WordTrace tailWord_4106105 prefixEnd_4106105 1405603655219841719335915 := by
  unfold tailWord_4106105
  simp only [CollatzResearch.WordTrace]
  refine ⟨149761952789290326748399769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99841301859526884498933179 149761952789290326748399769)
  ·
    refine ⟨112321464591967745061299827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149761952789290326748399769 112321464591967745061299827)
    ·
      refine ⟨168482196887951617591949741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112321464591967745061299827 168482196887951617591949741)
      ·
        refine ⟨63180823832981856596981153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168482196887951617591949741 63180823832981856596981153)
        ·
          refine ⟨47385617874736392447735865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63180823832981856596981153 47385617874736392447735865)
          ·
            refine ⟨35539213406052294335801899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47385617874736392447735865 35539213406052294335801899)
            ·
              refine ⟨53308820109078441503702849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35539213406052294335801899 53308820109078441503702849)
              ·
                refine ⟨39981615081808831127777137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53308820109078441503702849 39981615081808831127777137)
                ·
                  refine ⟨29986211311356623345832853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39981615081808831127777137 29986211311356623345832853)
                  ·
                    refine ⟨1405603655219841719335915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29986211311356623345832853 1405603655219841719335915)
                    ·
                      rfl

theorem cell22_4106105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_4106105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106105 prefixEnd_4106105 := by exact prefixLift 4106105
  have htrace : WordTrace (prefixWord ++ tailWord_4106105) baseStart_4106105 baseEnd_4106105 := by
    simpa [prefixWord, tailWord_4106105, baseEnd_4106105] using wordTrace_append hprefix tailTrace_4106105
  have hstable : (prefixWord ++ tailWord_4106105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106105).length < 2 ^ (prefixWord ++ tailWord_4106105).sum := by decide
  have hdescent : baseEnd_4106105 < baseStart_4106105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106137 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 5]
def baseStart_4106137 : Nat := 118140960795 + 4106137 * 2 ^ 59
def prefixEnd_4106137 : Nat := 4983230072969 + 3 ^ 40 * 4106137 * 2
def baseEnd_4106137 : Nat := 468538203157934767511939

theorem tailTrace_4106137 : CollatzResearch.WordTrace tailWord_4106137 prefixEnd_4106137 468538203157934767511939 := by
  unfold tailWord_4106137
  simp only [CollatzResearch.WordTrace]
  refine ⟨149763119925174396213564665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99842079950116264142376443 149763119925174396213564665)
  ·
    refine ⟨112322339943880797160173499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149763119925174396213564665 112322339943880797160173499)
    ·
      refine ⟨168483509915821195740260249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112322339943880797160173499 168483509915821195740260249)
      ·
        refine ⟨126362632436865896805195187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168483509915821195740260249 126362632436865896805195187)
        ·
          refine ⟨189543948655298845207792781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126362632436865896805195187 189543948655298845207792781)
          ·
            refine ⟨71078980745737066952922293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189543948655298845207792781 71078980745737066952922293)
            ·
              refine ⟨6663654444912850026836465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71078980745737066952922293 6663654444912850026836465)
              ·
                refine ⟨4997740833684637520127349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6663654444912850026836465 4997740833684637520127349)
                ·
                  refine ⟨468538203157934767511939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4997740833684637520127349 468538203157934767511939)
                  ·
                    rfl

theorem cell22_4106137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_4106137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106137 prefixEnd_4106137 := by exact prefixLift 4106137
  have htrace : WordTrace (prefixWord ++ tailWord_4106137) baseStart_4106137 baseEnd_4106137 := by
    simpa [prefixWord, tailWord_4106137, baseEnd_4106137] using wordTrace_append hprefix tailTrace_4106137
  have hstable : (prefixWord ++ tailWord_4106137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106137).length < 2 ^ (prefixWord ++ tailWord_4106137).sum := by decide
  have hdescent : baseEnd_4106137 < baseStart_4106137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106141 : List Nat := [1, 4, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_4106141 : Nat := 118140960795 + 4106141 * 2 ^ 59
def prefixEnd_4106141 : Nat := 4983230072969 + 3 ^ 40 * 4106141 * 2
def baseEnd_4106141 : Nat := 1405615978755549625435805

theorem tailTrace_4106141 : CollatzResearch.WordTrace tailWord_4106141 prefixEnd_4106141 1405615978755549625435805 := by
  unfold tailWord_4106141
  simp only [CollatzResearch.WordTrace]
  refine ⟨149763265817159904896710277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99842177211439936597806851 149763265817159904896710277)
  ·
    refine ⟨28080612340717482168133177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149763265817159904896710277 28080612340717482168133177)
    ·
      refine ⟨21060459255538111626099883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28080612340717482168133177 21060459255538111626099883)
      ·
        refine ⟨31590688883307167439149825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21060459255538111626099883 31590688883307167439149825)
        ·
          refine ⟨23693016662480375579362369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31590688883307167439149825 23693016662480375579362369)
          ·
            refine ⟨17769762496860281684521777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23693016662480375579362369 17769762496860281684521777)
            ·
              refine ⟨13327321872645211263391333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17769762496860281684521777 13327321872645211263391333)
              ·
                refine ⟨2498872851120977111885875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13327321872645211263391333 2498872851120977111885875)
                ·
                  refine ⟨3748309276681465667828813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498872851120977111885875 3748309276681465667828813)
                  ·
                    refine ⟨1405615978755549625435805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3748309276681465667828813 1405615978755549625435805)
                    ·
                      rfl

theorem cell22_4106141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_4106141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106141 prefixEnd_4106141 := by exact prefixLift 4106141
  have htrace : WordTrace (prefixWord ++ tailWord_4106141) baseStart_4106141 baseEnd_4106141 := by
    simpa [prefixWord, tailWord_4106141, baseEnd_4106141] using wordTrace_append hprefix tailTrace_4106141
  have hstable : (prefixWord ++ tailWord_4106141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106141).length < 2 ^ (prefixWord ++ tailWord_4106141).sum := by decide
  have hdescent : baseEnd_4106141 < baseStart_4106141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106184 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 1, 4]
def baseStart_4106184 : Nat := 118140960795 + 4106184 * 2 ^ 59
def prefixEnd_4106184 : Nat := 4983230072969 + 3 ^ 40 * 4106184 * 2
def baseEnd_4106184 : Nat := 1405630698534311846610673

theorem tailTrace_4106184 : CollatzResearch.WordTrace tailWord_4106184 prefixEnd_4106184 1405630698534311846610673 := by
  unfold tailWord_4106184
  simp only [CollatzResearch.WordTrace]
  refine ⟨74882417078002061620262803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99843222770669415493683737 74882417078002061620262803)
  ·
    refine ⟨112323625617003092430394205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74882417078002061620262803 112323625617003092430394205)
    ·
      refine ⟨42121359606376159661397827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112323625617003092430394205 42121359606376159661397827)
      ·
        refine ⟨63182039409564239492096741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42121359606376159661397827 63182039409564239492096741)
        ·
          refine ⟨11846632389293294904768139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63182039409564239492096741 11846632389293294904768139)
          ·
            refine ⟨17769948583939942357152209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11846632389293294904768139 17769948583939942357152209)
            ·
              refine ⟨13327461437954956767864157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17769948583939942357152209 13327461437954956767864157)
              ·
                refine ⟨4997798039233108787949059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13327461437954956767864157 4997798039233108787949059)
                ·
                  refine ⟨7496697058849663181923589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997798039233108787949059 7496697058849663181923589)
                  ·
                    refine ⟨1405630698534311846610673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7496697058849663181923589 1405630698534311846610673)
                    ·
                      rfl

theorem cell22_4106184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_4106184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106184 prefixEnd_4106184 := by exact prefixLift 4106184
  have htrace : WordTrace (prefixWord ++ tailWord_4106184) baseStart_4106184 baseEnd_4106184 := by
    simpa [prefixWord, tailWord_4106184, baseEnd_4106184] using wordTrace_append hprefix tailTrace_4106184
  have hstable : (prefixWord ++ tailWord_4106184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106184).length < 2 ^ (prefixWord ++ tailWord_4106184).sum := by decide
  have hdescent : baseEnd_4106184 < baseStart_4106184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106195 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 1, 12]
def baseStart_4106195 : Nat := 118140960795 + 4106195 * 2 ^ 59
def prefixEnd_4106195 : Nat := 4983230072969 + 3 ^ 40 * 4106195 * 2
def baseEnd_4106195 : Nat := 1405634464059111484585639

theorem tailTrace_4106195 : CollatzResearch.WordTrace tailWord_4106195 prefixEnd_4106195 1405634464059111484585639 := by
  unfold tailWord_4106195
  simp only [CollatzResearch.WordTrace]
  refine ⟨149765235358964272119176039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99843490239309514746117359 149765235358964272119176039)
  ·
    refine ⟨224647853038446408178764059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149765235358964272119176039 224647853038446408178764059)
    ·
      refine ⟨336971779557669612268146089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224647853038446408178764059 336971779557669612268146089)
      ·
        refine ⟨252728834668252209201109567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336971779557669612268146089 252728834668252209201109567)
        ·
          refine ⟨379093252002378313801664351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252728834668252209201109567 379093252002378313801664351)
          ·
            refine ⟨568639878003567470702496527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379093252002378313801664351 568639878003567470702496527)
            ·
              refine ⟨852959817005351206053744791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568639878003567470702496527 852959817005351206053744791)
              ·
                refine ⟨1279439725508026809080617187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852959817005351206053744791 1279439725508026809080617187)
                ·
                  refine ⟨1919159588262040213620925781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279439725508026809080617187 1919159588262040213620925781)
                  ·
                    refine ⟨1405634464059111484585639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1919159588262040213620925781 1405634464059111484585639)
                    ·
                      rfl

theorem cell22_4106195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_4106195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106195 prefixEnd_4106195 := by exact prefixLift 4106195
  have htrace : WordTrace (prefixWord ++ tailWord_4106195) baseStart_4106195 baseEnd_4106195 := by
    simpa [prefixWord, tailWord_4106195, baseEnd_4106195] using wordTrace_append hprefix tailTrace_4106195
  have hstable : (prefixWord ++ tailWord_4106195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106195).length < 2 ^ (prefixWord ++ tailWord_4106195).sum := by decide
  have hdescent : baseEnd_4106195 < baseStart_4106195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106212 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_4106212 : Nat := 118140960795 + 4106212 * 2 ^ 59
def prefixEnd_4106212 : Nat := 4983230072969 + 3 ^ 40 * 4106212 * 2
def baseEnd_4106212 : Nat := 1405640283506529106910587

theorem tailTrace_4106212 : CollatzResearch.WordTrace tailWord_4106212 prefixEnd_4106212 1405640283506529106910587 := by
  unfold tailWord_4106212
  simp only [CollatzResearch.WordTrace]
  refine ⟨74882927699951342011272445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99843903599935122681696593 74882927699951342011272445)
  ·
    refine ⟨28081097887481753254227167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74882927699951342011272445 28081097887481753254227167)
    ·
      refine ⟨42121646831222629881340751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28081097887481753254227167 42121646831222629881340751)
      ·
        refine ⟨63182470246833944822011127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42121646831222629881340751 63182470246833944822011127)
        ·
          refine ⟨94773705370250917233016691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63182470246833944822011127 94773705370250917233016691)
          ·
            refine ⟨142160558055376375849525037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94773705370250917233016691 142160558055376375849525037)
            ·
              refine ⟨53310209270766140943571889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142160558055376375849525037 53310209270766140943571889)
              ·
                refine ⟨39982656953074605707678917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53310209270766140943571889 39982656953074605707678917)
                ·
                  refine ⟨7496748178701488570189797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39982656953074605707678917 7496748178701488570189797)
                  ·
                    refine ⟨1405640283506529106910587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7496748178701488570189797 1405640283506529106910587)
                    ·
                      rfl

theorem cell22_4106212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_4106212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106212 prefixEnd_4106212 := by exact prefixLift 4106212
  have htrace : WordTrace (prefixWord ++ tailWord_4106212) baseStart_4106212 baseEnd_4106212 := by
    simpa [prefixWord, tailWord_4106212, baseEnd_4106212] using wordTrace_append hprefix tailTrace_4106212
  have hstable : (prefixWord ++ tailWord_4106212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106212).length < 2 ^ (prefixWord ++ tailWord_4106212).sum := by decide
  have hdescent : baseEnd_4106212 < baseStart_4106212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106244 : List Nat := [2, 3, 2, 4, 1, 10]
def baseStart_4106244 : Nat := 118140960795 + 4106244 * 2 ^ 59
def prefixEnd_4106244 : Nat := 4983230072969 + 3 ^ 40 * 4106244 * 2
def baseEnd_4106244 : Nat := 17353718984697428272969

theorem tailTrace_4106244 : CollatzResearch.WordTrace tailWord_4106244 prefixEnd_4106244 17353718984697428272969 := by
  unfold tailWord_4106244
  simp only [CollatzResearch.WordTrace]
  refine ⟨74883511267893376743854893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99844681690524502325139857 74883511267893376743854893)
  ·
    refine ⟨28081316725460016278945585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74883511267893376743854893 28081316725460016278945585)
    ·
      refine ⟨21060987544095012209209189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28081316725460016278945585 21060987544095012209209189)
      ·
        refine ⟨3948935164517814789226723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21060987544095012209209189 3948935164517814789226723)
        ·
          refine ⟨5923402746776722183840085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3948935164517814789226723 5923402746776722183840085)
          ·
            refine ⟨17353718984697428272969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5923402746776722183840085 17353718984697428272969)
            ·
              rfl

theorem cell22_4106244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 10].length) (baseStart_4106244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106244 prefixEnd_4106244 := by exact prefixLift 4106244
  have htrace : WordTrace (prefixWord ++ tailWord_4106244) baseStart_4106244 baseEnd_4106244 := by
    simpa [prefixWord, tailWord_4106244, baseEnd_4106244] using wordTrace_append hprefix tailTrace_4106244
  have hstable : (prefixWord ++ tailWord_4106244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106244).length < 2 ^ (prefixWord ++ tailWord_4106244).sum := by decide
  have hdescent : baseEnd_4106244 < baseStart_4106244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106250 : List Nat := [3, 1, 2, 2, 5, 1, 2, 2, 4]
def baseStart_4106250 : Nat := 118140960795 + 4106250 * 2 ^ 59
def prefixEnd_4106250 : Nat := 4983230072969 + 3 ^ 40 * 4106250 * 2
def baseEnd_4106250 : Nat := 468551097227703224820157

theorem tailTrace_4106250 : CollatzResearch.WordTrace tailWord_4106250 prefixEnd_4106250 468551097227703224820157 := by
  unfold tailWord_4106250
  simp only [CollatzResearch.WordTrace]
  refine ⟨37441810343441254128107051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99844827582510011008285469 37441810343441254128107051)
  ·
    refine ⟨56162715515161881192160577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37441810343441254128107051 56162715515161881192160577)
    ·
      refine ⟨42122036636371410894120433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56162715515161881192160577 42122036636371410894120433)
      ·
        refine ⟨31591527477278558170590325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42122036636371410894120433 31591527477278558170590325)
        ·
          refine ⟨2961705700994864828492843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31591527477278558170590325 2961705700994864828492843)
          ·
            refine ⟨4442558551492297242739265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961705700994864828492843 4442558551492297242739265)
            ·
              refine ⟨3331918913619222932054449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4442558551492297242739265 3331918913619222932054449)
              ·
                refine ⟨2498939185214417199040837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3331918913619222932054449 2498939185214417199040837)
                ·
                  refine ⟨468551097227703224820157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2498939185214417199040837 468551097227703224820157)
                  ·
                    rfl

theorem cell22_4106250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_4106250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106250 prefixEnd_4106250 := by exact prefixLift 4106250
  have htrace : WordTrace (prefixWord ++ tailWord_4106250) baseStart_4106250 baseEnd_4106250 := by
    simpa [prefixWord, tailWord_4106250, baseEnd_4106250] using wordTrace_append hprefix tailTrace_4106250
  have hstable : (prefixWord ++ tailWord_4106250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106250).length < 2 ^ (prefixWord ++ tailWord_4106250).sum := by decide
  have hdescent : baseEnd_4106250 < baseStart_4106250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106261 : List Nat := [1, 3, 2, 1, 6, 1, 1, 7]
def baseStart_4106261 : Nat := 118140960795 + 4106261 * 2 ^ 59
def prefixEnd_4106261 : Nat := 4983230072969 + 3 ^ 40 * 4106261 * 2
def baseEnd_4106261 : Nat := 156184117467545479159493

theorem tailTrace_4106261 : CollatzResearch.WordTrace tailWord_4106261 prefixEnd_4106261 156184117467545479159493 := by
  unfold tailWord_4106261
  simp only [CollatzResearch.WordTrace]
  refine ⟨149767642576725165391078637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99845095051150110260719091 149767642576725165391078637)
  ·
    refine ⟨56162865966271937021654489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149767642576725165391078637 56162865966271937021654489)
    ·
      refine ⟨42122149474703952766240867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56162865966271937021654489 42122149474703952766240867)
      ·
        refine ⟨63183224212055929149361301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42122149474703952766240867 63183224212055929149361301)
        ·
          refine ⟨2961713634940121678876311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63183224212055929149361301 2961713634940121678876311)
          ·
            refine ⟨4442570452410182518314467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961713634940121678876311 4442570452410182518314467)
            ·
              refine ⟨6663855678615273777471701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442570452410182518314467 6663855678615273777471701)
              ·
                refine ⟨156184117467545479159493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6663855678615273777471701 156184117467545479159493)
                ·
                  rfl

theorem cell22_4106261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 7].length) (baseStart_4106261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106261 prefixEnd_4106261 := by exact prefixLift 4106261
  have htrace : WordTrace (prefixWord ++ tailWord_4106261) baseStart_4106261 baseEnd_4106261 := by
    simpa [prefixWord, tailWord_4106261, baseEnd_4106261] using wordTrace_append hprefix tailTrace_4106261
  have hstable : (prefixWord ++ tailWord_4106261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106261).length < 2 ^ (prefixWord ++ tailWord_4106261).sum := by decide
  have hdescent : baseEnd_4106261 < baseStart_4106261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106280 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 2, 4]
def baseStart_4106280 : Nat := 118140960795 + 4106280 * 2 ^ 59
def prefixEnd_4106280 : Nat := 4983230072969 + 3 ^ 40 * 4106280 * 2
def baseEnd_4106280 : Nat := 1405663561296199596210379

theorem tailTrace_4106280 : CollatzResearch.WordTrace tailWord_4106280 prefixEnd_4106280 1405663561296199596210379 := by
  unfold tailWord_4106280
  simp only [CollatzResearch.WordTrace]
  refine ⟨74884167781828165818010147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99845557042437554424013529 74884167781828165818010147)
  ·
    refine ⟨112326251672742248727015221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74884167781828165818010147 112326251672742248727015221)
    ·
      refine ⟨10530586094319585818157677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112326251672742248727015221 10530586094319585818157677)
      ·
        refine ⟨3948969785369844681809129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10530586094319585818157677 3948969785369844681809129)
        ·
          refine ⟨2961727339027383511356847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3948969785369844681809129 2961727339027383511356847)
          ·
            refine ⟨4442591008541075267035271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2961727339027383511356847 4442591008541075267035271)
            ·
              refine ⟨6663886512811612900552907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4442591008541075267035271 6663886512811612900552907)
              ·
                refine ⟨9995829769217419350829361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6663886512811612900552907 9995829769217419350829361)
                ·
                  refine ⟨7496872326913064513122021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9995829769217419350829361 7496872326913064513122021)
                  ·
                    refine ⟨1405663561296199596210379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7496872326913064513122021 1405663561296199596210379)
                    ·
                      rfl

theorem cell22_4106280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_4106280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106280 prefixEnd_4106280 := by exact prefixLift 4106280
  have htrace : WordTrace (prefixWord ++ tailWord_4106280) baseStart_4106280 baseEnd_4106280 := by
    simpa [prefixWord, tailWord_4106280, baseEnd_4106280] using wordTrace_append hprefix tailTrace_4106280
  have hstable : (prefixWord ++ tailWord_4106280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106280).length < 2 ^ (prefixWord ++ tailWord_4106280).sum := by decide
  have hdescent : baseEnd_4106280 < baseStart_4106280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106310 : List Nat := [6, 1, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_4106310 : Nat := 118140960795 + 4106310 * 2 ^ 59
def prefixEnd_4106310 : Nat := 4983230072969 + 3 ^ 40 * 4106310 * 2
def baseEnd_4106310 : Nat := 1405673830909289517960287

theorem tailTrace_4106310 : CollatzResearch.WordTrace tailWord_4106310 prefixEnd_4106310 1405673830909289517960287 := by
  unfold tailWord_4106310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4680294679798363961237887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99846286502365097839741589 4680294679798363961237887)
  ·
    refine ⟨7020442019697545941856831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4680294679798363961237887 7020442019697545941856831)
    ·
      refine ⟨10530663029546318912785247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7020442019697545941856831 10530663029546318912785247)
      ·
        refine ⟨15795994544319478369177871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10530663029546318912785247 15795994544319478369177871)
        ·
          refine ⟨23693991816479217553766807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15795994544319478369177871 23693991816479217553766807)
          ·
            refine ⟨35540987724718826330650211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23693991816479217553766807 35540987724718826330650211)
            ·
              refine ⟨53311481587078239495975317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35540987724718826330650211 53311481587078239495975317)
              ·
                refine ⟨2498975699394292476373843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53311481587078239495975317 2498975699394292476373843)
                ·
                  refine ⟨3748463549091438714560765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2498975699394292476373843 3748463549091438714560765)
                  ·
                    refine ⟨1405673830909289517960287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3748463549091438714560765 1405673830909289517960287)
                    ·
                      rfl

theorem cell22_4106310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_4106310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106310 prefixEnd_4106310 := by exact prefixLift 4106310
  have htrace : WordTrace (prefixWord ++ tailWord_4106310) baseStart_4106310 baseEnd_4106310 := by
    simpa [prefixWord, tailWord_4106310, baseEnd_4106310] using wordTrace_append hprefix tailTrace_4106310
  have hstable : (prefixWord ++ tailWord_4106310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106310).length < 2 ^ (prefixWord ++ tailWord_4106310).sum := by decide
  have hdescent : baseEnd_4106310 < baseStart_4106310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106336 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 1, 4]
def baseStart_4106336 : Nat := 118140960795 + 4106336 * 2 ^ 59
def prefixEnd_4106336 : Nat := 4983230072969 + 3 ^ 40 * 4106336 * 2
def baseEnd_4106336 : Nat := 1405682731240634116810207

theorem tailTrace_4106336 : CollatzResearch.WordTrace tailWord_4106336 prefixEnd_4106336 1405682731240634116810207 := by
  unfold tailWord_4106336
  simp only [CollatzResearch.WordTrace]
  refine ⟨74885189025726726600029431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99846918700968968800039241 74885189025726726600029431)
  ·
    refine ⟨112327783538590089900044147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74885189025726726600029431 112327783538590089900044147)
    ·
      refine ⟨168491675307885134850066221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112327783538590089900044147 168491675307885134850066221)
      ·
        refine ⟨63184378240456925568774833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168491675307885134850066221 63184378240456925568774833)
        ·
          refine ⟨47388283680342694176581125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63184378240456925568774833 47388283680342694176581125)
          ·
            refine ⟨8885303190064255158108961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47388283680342694176581125 8885303190064255158108961)
            ·
              refine ⟨6663977392548191368581721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8885303190064255158108961 6663977392548191368581721)
              ·
                refine ⟨4997983044411143526436291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6663977392548191368581721 4997983044411143526436291)
                ·
                  refine ⟨7496974566616715289654437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4997983044411143526436291 7496974566616715289654437)
                  ·
                    refine ⟨1405682731240634116810207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7496974566616715289654437 1405682731240634116810207)
                    ·
                      rfl

theorem cell22_4106336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 1, 4].length) (baseStart_4106336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106336 prefixEnd_4106336 := by exact prefixLift 4106336
  have htrace : WordTrace (prefixWord ++ tailWord_4106336) baseStart_4106336 baseEnd_4106336 := by
    simpa [prefixWord, tailWord_4106336, baseEnd_4106336] using wordTrace_append hprefix tailTrace_4106336
  have hstable : (prefixWord ++ tailWord_4106336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106336).length < 2 ^ (prefixWord ++ tailWord_4106336).sum := by decide
  have hdescent : baseEnd_4106336 < baseStart_4106336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106349 : List Nat := [1, 5, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_4106349 : Nat := 118140960795 + 4106349 * 2 ^ 59
def prefixEnd_4106349 : Nat := 4983230072969 + 3 ^ 40 * 4106349 * 2
def baseEnd_4106349 : Nat := 1405687181406306416235167

theorem tailTrace_4106349 : CollatzResearch.WordTrace tailWord_4106349 prefixEnd_4106349 1405687181406306416235167 := by
  unfold tailWord_4106349
  simp only [CollatzResearch.WordTrace]
  refine ⟨149770852200406356420282101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99847234800270904280188067 149770852200406356420282101)
  ·
    refine ⟨14041017393788095914401447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149770852200406356420282101 14041017393788095914401447)
    ·
      refine ⟨21061526090682143871602171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14041017393788095914401447 21061526090682143871602171)
      ·
        refine ⟨31592289136023215807403257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21061526090682143871602171 31592289136023215807403257)
        ·
          refine ⟨23694216852017411855552443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31592289136023215807403257 23694216852017411855552443)
          ·
            refine ⟨35541325278026117783328665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23694216852017411855552443 35541325278026117783328665)
            ·
              refine ⟨26655993958519588337496499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35541325278026117783328665 26655993958519588337496499)
              ·
                refine ⟨39983990937779382506244749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26655993958519588337496499 39983990937779382506244749)
                ·
                  refine ⟨14993996601667268439841781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39983990937779382506244749 14993996601667268439841781)
                  ·
                    refine ⟨1405687181406306416235167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14993996601667268439841781 1405687181406306416235167)
                    ·
                      rfl

theorem cell22_4106349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_4106349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106349 prefixEnd_4106349 := by exact prefixLift 4106349
  have htrace : WordTrace (prefixWord ++ tailWord_4106349) baseStart_4106349 baseEnd_4106349 := by
    simpa [prefixWord, tailWord_4106349, baseEnd_4106349] using wordTrace_append hprefix tailTrace_4106349
  have hstable : (prefixWord ++ tailWord_4106349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106349).length < 2 ^ (prefixWord ++ tailWord_4106349).sum := by decide
  have hdescent : baseEnd_4106349 < baseStart_4106349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106351 : List Nat := [1, 1, 2, 1, 3, 4, 3, 3, 4]
def baseStart_4106351 : Nat := 118140960795 + 4106351 * 2 ^ 59
def prefixEnd_4106351 : Nat := 4983230072969 + 3 ^ 40 * 4106351 * 2
def baseEnd_4106351 : Nat := 468562622015726359228387

theorem tailTrace_4106351 : CollatzResearch.WordTrace tailWord_4106351 prefixEnd_4106351 468562622015726359228387 := by
  unfold tailWord_4106351
  simp only [CollatzResearch.WordTrace]
  refine ⟨149770925146399110761854907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99847283430932740507903271 149770925146399110761854907)
  ·
    refine ⟨224656387719598666142782361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149770925146399110761854907 224656387719598666142782361)
    ·
      refine ⟨168492290789698999607086771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224656387719598666142782361 168492290789698999607086771)
      ·
        refine ⟨252738436184548499410630157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168492290789698999607086771 252738436184548499410630157)
        ·
          refine ⟨94776913569205687278986309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252738436184548499410630157 94776913569205687278986309)
          ·
            refine ⟨17770671294226066364809933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94776913569205687278986309 17770671294226066364809933)
            ·
              refine ⟨6664001735334774886803725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17770671294226066364809933 6664001735334774886803725)
              ·
                refine ⟨2499000650750540582551397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6664001735334774886803725 2499000650750540582551397)
                ·
                  refine ⟨468562622015726359228387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2499000650750540582551397 468562622015726359228387)
                  ·
                    rfl

theorem cell22_4106351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 4].length) (baseStart_4106351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106351 prefixEnd_4106351 := by exact prefixLift 4106351
  have htrace : WordTrace (prefixWord ++ tailWord_4106351) baseStart_4106351 baseEnd_4106351 := by
    simpa [prefixWord, tailWord_4106351, baseEnd_4106351] using wordTrace_append hprefix tailTrace_4106351
  have hstable : (prefixWord ++ tailWord_4106351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106351).length < 2 ^ (prefixWord ++ tailWord_4106351).sum := by decide
  have hdescent : baseEnd_4106351 < baseStart_4106351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106364 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_4106364 : Nat := 118140960795 + 4106364 * 2 ^ 59
def prefixEnd_4106364 : Nat := 4983230072969 + 3 ^ 40 * 4106364 * 2
def baseEnd_4106364 : Nat := 1405692316212851377110121

theorem tailTrace_4106364 : CollatzResearch.WordTrace tailWord_4106364 prefixEnd_4106364 1405692316212851377110121 := by
  unfold tailWord_4106364
  simp only [CollatzResearch.WordTrace]
  refine ⟨74885699647676006991039073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99847599530234675988052097 74885699647676006991039073)
  ·
    refine ⟨56164274735757005243279305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74885699647676006991039073 56164274735757005243279305)
    ·
      refine ⟨42123206051817753932459479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56164274735757005243279305 42123206051817753932459479)
      ·
        refine ⟨63184809077726630898689219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42123206051817753932459479 63184809077726630898689219)
        ·
          refine ⟨94777213616589946348033829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63184809077726630898689219 94777213616589946348033829)
          ·
            refine ⟨17770727553110614940256343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94777213616589946348033829 17770727553110614940256343)
            ·
              refine ⟨26656091329665922410384515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17770727553110614940256343 26656091329665922410384515)
              ·
                refine ⟨39984136994498883615576773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26656091329665922410384515 39984136994498883615576773)
                ·
                  refine ⟨7497025686468540677920645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39984136994498883615576773 7497025686468540677920645)
                  ·
                    refine ⟨1405692316212851377110121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7497025686468540677920645 1405692316212851377110121)
                    ·
                      rfl

theorem cell22_4106364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_4106364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106364 prefixEnd_4106364 := by exact prefixLift 4106364
  have htrace : WordTrace (prefixWord ++ tailWord_4106364) baseStart_4106364 baseEnd_4106364 := by
    simpa [prefixWord, tailWord_4106364, baseEnd_4106364] using wordTrace_append hprefix tailTrace_4106364
  have hstable : (prefixWord ++ tailWord_4106364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106364).length < 2 ^ (prefixWord ++ tailWord_4106364).sum := by decide
  have hdescent : baseEnd_4106364 < baseStart_4106364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106486 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_4106486 : Nat := 118140960795 + 4106486 * 2 ^ 59
def prefixEnd_4106486 : Nat := 4983230072969 + 3 ^ 40 * 4106486 * 2
def baseEnd_4106486 : Nat := 468578026435361241853249

theorem tailTrace_4106486 : CollatzResearch.WordTrace tailWord_4106486 prefixEnd_4106486 468578026435361241853249 := by
  unfold tailWord_4106486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9360990562556876801126207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99850566000606685878679541 9360990562556876801126207)
  ·
    refine ⟨14041485843835315201689311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9360990562556876801126207 14041485843835315201689311)
    ·
      refine ⟨21062228765752972802533967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14041485843835315201689311 21062228765752972802533967)
      ·
        refine ⟨31593343148629459203800951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21062228765752972802533967 31593343148629459203800951)
        ·
          refine ⟨47390014722944188805701427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31593343148629459203800951 47390014722944188805701427)
          ·
            refine ⟨71085022084416283208552141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47390014722944188805701427 71085022084416283208552141)
            ·
              refine ⟨26656883281656106203207053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71085022084416283208552141 26656883281656106203207053)
              ·
                refine ⟨9996331230621039826202645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26656883281656106203207053 9996331230621039826202645)
                ·
                  refine ⟨468578026435361241853249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9996331230621039826202645 468578026435361241853249)
                  ·
                    rfl

theorem cell22_4106486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_4106486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106486 prefixEnd_4106486 := by exact prefixLift 4106486
  have htrace : WordTrace (prefixWord ++ tailWord_4106486) baseStart_4106486 baseEnd_4106486 := by
    simpa [prefixWord, tailWord_4106486, baseEnd_4106486] using wordTrace_append hprefix tailTrace_4106486
  have hstable : (prefixWord ++ tailWord_4106486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106486).length < 2 ^ (prefixWord ++ tailWord_4106486).sum := by decide
  have hdescent : baseEnd_4106486 < baseStart_4106486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106499 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 3, 6]
def baseStart_4106499 : Nat := 118140960795 + 4106499 * 2 ^ 59
def prefixEnd_4106499 : Nat := 4983230072969 + 3 ^ 40 * 4106499 * 2
def baseEnd_4106499 : Nat := 1405738529471756024984707

theorem tailTrace_4106499 : CollatzResearch.WordTrace tailWord_4106499 prefixEnd_4106499 1405738529471756024984707 := by
  unfold tailWord_4106499
  simp only [CollatzResearch.WordTrace]
  refine ⟨149776323149862932038242551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99850882099908621358828367 149776323149862932038242551)
  ·
    refine ⟨224664484724794398057363827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149776323149862932038242551 224664484724794398057363827)
    ·
      refine ⟨336996727087191597086045741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224664484724794398057363827 336996727087191597086045741)
      ·
        refine ⟨126373772657696848907267153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 336996727087191597086045741 126373772657696848907267153)
        ·
          refine ⟨94780329493272636680450365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126373772657696848907267153 94780329493272636680450365)
          ·
            refine ⟨35542623559977238755168887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94780329493272636680450365 35542623559977238755168887)
            ·
              refine ⟨53313935339965858132753331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35542623559977238755168887 53313935339965858132753331)
              ·
                refine ⟨79970903009948787199129997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53313935339965858132753331 79970903009948787199129997)
                ·
                  refine ⟨29989088628730795199673749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79970903009948787199129997 29989088628730795199673749)
                  ·
                    refine ⟨1405738529471756024984707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29989088628730795199673749 1405738529471756024984707)
                    ·
                      rfl

theorem cell22_4106499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_4106499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106499 prefixEnd_4106499 := by exact prefixLift 4106499
  have htrace : WordTrace (prefixWord ++ tailWord_4106499) baseStart_4106499 baseEnd_4106499 := by
    simpa [prefixWord, tailWord_4106499, baseEnd_4106499] using wordTrace_append hprefix tailTrace_4106499
  have hstable : (prefixWord ++ tailWord_4106499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106499).length < 2 ^ (prefixWord ++ tailWord_4106499).sum := by decide
  have hdescent : baseEnd_4106499 < baseStart_4106499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106533 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_4106533 : Nat := 118140960795 + 4106533 * 2 ^ 59
def prefixEnd_4106533 : Nat := 4983230072969 + 3 ^ 40 * 4106533 * 2
def baseEnd_4106533 : Nat := 1405750168366591269634603

theorem tailTrace_4106533 : CollatzResearch.WordTrace tailWord_4106533 prefixEnd_4106533 1405750168366591269634603 := by
  unfold tailWord_4106533
  simp only [CollatzResearch.WordTrace]
  refine ⟨149777563231739755844980253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99851708821159837229986835 149777563231739755844980253)
  ·
    refine ⟨56166586211902408441867595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149777563231739755844980253 56166586211902408441867595)
    ·
      refine ⟨84249879317853612662801393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56166586211902408441867595 84249879317853612662801393)
      ·
        refine ⟨63187409488390209497101045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84249879317853612662801393 63187409488390209497101045)
        ·
          refine ⟨5923819639536582140353223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63187409488390209497101045 5923819639536582140353223)
          ·
            refine ⟨8885729459304873210529835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5923819639536582140353223 8885729459304873210529835)
            ·
              refine ⟨13328594188957309815794753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8885729459304873210529835 13328594188957309815794753)
              ·
                refine ⟨9996445641717982361846065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13328594188957309815794753 9996445641717982361846065)
                ·
                  refine ⟨7497334231288486771384549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9996445641717982361846065 7497334231288486771384549)
                  ·
                    refine ⟨1405750168366591269634603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7497334231288486771384549 1405750168366591269634603)
                    ·
                      rfl

theorem cell22_4106533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_4106533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106533 prefixEnd_4106533 := by exact prefixLift 4106533
  have htrace : WordTrace (prefixWord ++ tailWord_4106533) baseStart_4106533 baseEnd_4106533 := by
    simpa [prefixWord, tailWord_4106533, baseEnd_4106533] using wordTrace_append hprefix tailTrace_4106533
  have hstable : (prefixWord ++ tailWord_4106533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106533).length < 2 ^ (prefixWord ++ tailWord_4106533).sum := by decide
  have hdescent : baseEnd_4106533 < baseStart_4106533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106548 : List Nat := [2, 5, 1, 1, 1, 3, 2, 7]
def baseStart_4106548 : Nat := 118140960795 + 4106548 * 2 ^ 59
def prefixEnd_4106548 : Nat := 4983230072969 + 3 ^ 40 * 4106548 * 2
def baseEnd_4106548 : Nat := 156195033685904025612173

theorem tailTrace_4106548 : CollatzResearch.WordTrace tailWord_4106548 prefixEnd_4106548 156195033685904025612173 := by
  unfold tailWord_4106548
  simp only [CollatzResearch.WordTrace]
  refine ⟨74889055163342706703388149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99852073551123608937850865 74889055163342706703388149)
  ·
    refine ⟨7020848921563378753442639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74889055163342706703388149 7020848921563378753442639)
    ·
      refine ⟨10531273382345068130163959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7020848921563378753442639 10531273382345068130163959)
      ·
        refine ⟨15796910073517602195245939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10531273382345068130163959 15796910073517602195245939)
        ·
          refine ⟨23695365110276403292868909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15796910073517602195245939 23695365110276403292868909)
          ·
            refine ⟨8885761916353651234825841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23695365110276403292868909 8885761916353651234825841)
            ·
              refine ⟨6664321437265238426119381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8885761916353651234825841 6664321437265238426119381)
              ·
                refine ⟨156195033685904025612173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6664321437265238426119381 156195033685904025612173)
                ·
                  rfl

theorem cell22_4106548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 7].length) (baseStart_4106548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106548 prefixEnd_4106548 := by exact prefixLift 4106548
  have htrace : WordTrace (prefixWord ++ tailWord_4106548) baseStart_4106548 baseEnd_4106548 := by
    simpa [prefixWord, tailWord_4106548, baseEnd_4106548] using wordTrace_append hprefix tailTrace_4106548
  have hstable : (prefixWord ++ tailWord_4106548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106548).length < 2 ^ (prefixWord ++ tailWord_4106548).sum := by decide
  have hdescent : baseEnd_4106548 < baseStart_4106548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106597 : List Nat := [1, 3, 1, 3, 1, 3, 4, 2, 1, 3]
def baseStart_4106597 : Nat := 118140960795 + 4106597 * 2 ^ 59
def prefixEnd_4106597 : Nat := 4983230072969 + 3 ^ 40 * 4106597 * 2
def baseEnd_4106597 : Nat := 1405772076874516436034407

theorem tailTrace_4106597 : CollatzResearch.WordTrace tailWord_4106597 prefixEnd_4106597 1405772076874516436034407 := by
  unfold tailWord_4106597
  simp only [CollatzResearch.WordTrace]
  refine ⟨149779897503507894775310045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99853265002338596516873363 149779897503507894775310045)
  ·
    refine ⟨56167461563815460540741267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149779897503507894775310045 56167461563815460540741267)
    ·
      refine ⟨84251192345723190811111901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56167461563815460540741267 84251192345723190811111901)
      ·
        refine ⟨31594197129646196554166963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84251192345723190811111901 31594197129646196554166963)
        ·
          refine ⟨47391295694469294831250445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31594197129646196554166963 47391295694469294831250445)
          ·
            refine ⟨17771735885425985561718917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47391295694469294831250445 17771735885425985561718917)
            ·
              refine ⟨3332200478517372292822297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17771735885425985561718917 3332200478517372292822297)
              ·
                refine ⟨2499150358888029219616723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3332200478517372292822297 2499150358888029219616723)
                ·
                  refine ⟨3748725538332043829425085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499150358888029219616723 3748725538332043829425085)
                  ·
                    refine ⟨1405772076874516436034407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3748725538332043829425085 1405772076874516436034407)
                    ·
                      rfl

theorem cell22_4106597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_4106597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106597 prefixEnd_4106597 := by exact prefixLift 4106597
  have htrace : WordTrace (prefixWord ++ tailWord_4106597) baseStart_4106597 baseEnd_4106597 := by
    simpa [prefixWord, tailWord_4106597, baseEnd_4106597] using wordTrace_append hprefix tailTrace_4106597
  have hstable : (prefixWord ++ tailWord_4106597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106597).length < 2 ^ (prefixWord ++ tailWord_4106597).sum := by decide
  have hdescent : baseEnd_4106597 < baseStart_4106597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106621 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 8]
def baseStart_4106621 : Nat := 118140960795 + 4106621 * 2 ^ 59
def prefixEnd_4106621 : Nat := 4983230072969 + 3 ^ 40 * 4106621 * 2
def baseEnd_4106621 : Nat := 468593430854996124478111

theorem tailTrace_4106621 : CollatzResearch.WordTrace tailWord_4106621 prefixEnd_4106621 468593430854996124478111 := by
  unfold tailWord_4106621
  simp only [CollatzResearch.WordTrace]
  refine ⟨149780772855420946874183717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99853848570280631249455811 149780772855420946874183717)
  ·
    refine ⟨28083894910391427538909447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149780772855420946874183717 28083894910391427538909447)
    ·
      refine ⟨42125842365587141308364171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28083894910391427538909447 42125842365587141308364171)
      ·
        refine ⟨63188763548380711962546257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42125842365587141308364171 63188763548380711962546257)
        ·
          refine ⟨47391572661285533971909693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63188763548380711962546257 47391572661285533971909693)
          ·
            refine ⟨17771839747982075239466135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47391572661285533971909693 17771839747982075239466135)
            ·
              refine ⟨26657759621973112859199203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17771839747982075239466135 26657759621973112859199203)
              ·
                refine ⟨39986639432959669288798805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26657759621973112859199203 39986639432959669288798805)
                ·
                  refine ⟨468593430854996124478111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39986639432959669288798805 468593430854996124478111)
                  ·
                    rfl

theorem cell22_4106621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_4106621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106621 prefixEnd_4106621 := by exact prefixLift 4106621
  have htrace : WordTrace (prefixWord ++ tailWord_4106621) baseStart_4106621 baseEnd_4106621 := by
    simpa [prefixWord, tailWord_4106621, baseEnd_4106621] using wordTrace_append hprefix tailTrace_4106621
  have hstable : (prefixWord ++ tailWord_4106621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106621).length < 2 ^ (prefixWord ++ tailWord_4106621).sum := by decide
  have hdescent : baseEnd_4106621 < baseStart_4106621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106700 : List Nat := [2, 2, 1, 4, 4, 1, 8]
def baseStart_4106700 : Nat := 118140960795 + 4106700 * 2 ^ 59
def prefixEnd_4106700 : Nat := 4983230072969 + 3 ^ 40 * 4106700 * 2
def baseEnd_4106700 : Nat := 52066938365905870396633

theorem tailTrace_4106700 : CollatzResearch.WordTrace tailWord_4106700 prefixEnd_4106700 52066938365905870396633 := by
  unfold tailWord_4106700
  simp only [CollatzResearch.WordTrace]
  refine ⟨74891827111067371683154777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99855769481423162244206369 74891827111067371683154777)
  ·
    refine ⟨56168870333300528762366083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74891827111067371683154777 56168870333300528762366083)
    ·
      refine ⟨84253305499950793143549125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56168870333300528762366083 84253305499950793143549125)
      ·
        refine ⟨15797494781240773714415461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84253305499950793143549125 15797494781240773714415461)
        ·
          refine ⟨2962030271482645071452899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15797494781240773714415461 2962030271482645071452899)
          ·
            refine ⟨4443045407223967607179349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962030271482645071452899 4443045407223967607179349)
            ·
              refine ⟨52066938365905870396633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4443045407223967607179349 52066938365905870396633)
              ·
                rfl

theorem cell22_4106700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 8].length) (baseStart_4106700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106700 prefixEnd_4106700 := by exact prefixLift 4106700
  have htrace : WordTrace (prefixWord ++ tailWord_4106700) baseStart_4106700 baseEnd_4106700 := by
    simpa [prefixWord, tailWord_4106700, baseEnd_4106700] using wordTrace_append hprefix tailTrace_4106700
  have hstable : (prefixWord ++ tailWord_4106700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106700).length < 2 ^ (prefixWord ++ tailWord_4106700).sum := by decide
  have hdescent : baseEnd_4106700 < baseStart_4106700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106766 : List Nat := [4, 1, 1, 2, 3, 3, 2, 2, 1, 3]
def baseStart_4106766 : Nat := 118140960795 + 4106766 * 2 ^ 59
def prefixEnd_4106766 : Nat := 4983230072969 + 3 ^ 40 * 4106766 * 2
def baseEnd_4106766 : Nat := 1405829929028256328558889

theorem tailTrace_4106766 : CollatzResearch.WordTrace tailWord_4106766 prefixEnd_4106766 1405829929028256328558889 := by
  unfold tailWord_4106766
  simp only [CollatzResearch.WordTrace]
  refine ⟨18723257679986954579776519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99857374293263757758808101 18723257679986954579776519)
  ·
    refine ⟨28084886519980431869664779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18723257679986954579776519 28084886519980431869664779)
    ·
      refine ⟨42127329779970647804497169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28084886519980431869664779 42127329779970647804497169)
      ·
        refine ⟨31595497334977985853372877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42127329779970647804497169 31595497334977985853372877)
        ·
          refine ⟨11848311500616744695014829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31595497334977985853372877 11848311500616744695014829)
          ·
            refine ⟨4443116812731279260630561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11848311500616744695014829 4443116812731279260630561)
            ·
              refine ⟨3332337609548459445472921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443116812731279260630561 3332337609548459445472921)
              ·
                refine ⟨2499253207161344584104691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3332337609548459445472921 2499253207161344584104691)
                ·
                  refine ⟨3748879810742016876157037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499253207161344584104691 3748879810742016876157037)
                  ·
                    refine ⟨1405829929028256328558889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3748879810742016876157037 1405829929028256328558889)
                    ·
                      rfl

theorem cell22_4106766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_4106766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106766 prefixEnd_4106766 := by exact prefixLift 4106766
  have htrace : WordTrace (prefixWord ++ tailWord_4106766) baseStart_4106766 baseEnd_4106766 := by
    simpa [prefixWord, tailWord_4106766, baseEnd_4106766] using wordTrace_append hprefix tailTrace_4106766
  have hstable : (prefixWord ++ tailWord_4106766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106766).length < 2 ^ (prefixWord ++ tailWord_4106766).sum := by decide
  have hdescent : baseEnd_4106766 < baseStart_4106766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106773 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 6]
def baseStart_4106773 : Nat := 118140960795 + 4106773 * 2 ^ 59
def prefixEnd_4106773 : Nat := 4983230072969 + 3 ^ 40 * 4106773 * 2
def baseEnd_4106773 : Nat := 468610775090436881211289

theorem tailTrace_4106773 : CollatzResearch.WordTrace tailWord_4106773 prefixEnd_4106773 468610775090436881211289 := by
  unfold tailWord_4106773
  simp only [CollatzResearch.WordTrace]
  refine ⟨149786316750870276833716973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99857544500580184555811315 149786316750870276833716973)
  ·
    refine ⟨56169868781576353812643865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149786316750870276833716973 56169868781576353812643865)
    ·
      refine ⟨42127401586182265359482899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56169868781576353812643865 42127401586182265359482899)
      ·
        refine ⟨63191102379273398039224349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42127401586182265359482899 63191102379273398039224349)
        ·
          refine ⟨23696663392227524264709131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63191102379273398039224349 23696663392227524264709131)
          ·
            refine ⟨35544995088341286397063697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23696663392227524264709131 35544995088341286397063697)
            ·
              refine ⟨26658746316255964797797773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35544995088341286397063697 26658746316255964797797773)
              ·
                refine ⟨9997029868595986799174165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26658746316255964797797773 9997029868595986799174165)
                ·
                  refine ⟨468610775090436881211289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9997029868595986799174165 468610775090436881211289)
                  ·
                    rfl

theorem cell22_4106773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_4106773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106773 prefixEnd_4106773 := by exact prefixLift 4106773
  have htrace : WordTrace (prefixWord ++ tailWord_4106773) baseStart_4106773 baseEnd_4106773 := by
    simpa [prefixWord, tailWord_4106773, baseEnd_4106773] using wordTrace_append hprefix tailTrace_4106773
  have hstable : (prefixWord ++ tailWord_4106773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106773).length < 2 ^ (prefixWord ++ tailWord_4106773).sum := by decide
  have hdescent : baseEnd_4106773 < baseStart_4106773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106803 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 1, 6]
def baseStart_4106803 : Nat := 118140960795 + 4106803 * 2 ^ 59
def prefixEnd_4106803 : Nat := 4983230072969 + 3 ^ 40 * 4106803 * 2
def baseEnd_4106803 : Nat := 1405842594884400565383775

theorem tailTrace_4106803 : CollatzResearch.WordTrace tailWord_4106803 prefixEnd_4106803 1405842594884400565383775 := by
  unfold tailWord_4106803
  simp only [CollatzResearch.WordTrace]
  refine ⟨149787410940761591957309063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99858273960507727971539375 149787410940761591957309063)
  ·
    refine ⟨224681116411142387935963595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149787410940761591957309063 224681116411142387935963595)
    ·
      refine ⟨337021674616713581903945393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224681116411142387935963595 337021674616713581903945393)
      ·
        refine ⟨252766255962535186427959045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337021674616713581903945393 252766255962535186427959045)
        ·
          refine ⟨47393672992975347455242321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 252766255962535186427959045 47393672992975347455242321)
          ·
            refine ⟨35545254744731510591431741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47393672992975347455242321 35545254744731510591431741)
            ·
              refine ⟨13329470529274316471786903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35545254744731510591431741 13329470529274316471786903)
              ·
                refine ⟨19994205793911474707680355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13329470529274316471786903 19994205793911474707680355)
                ·
                  refine ⟨29991308690867212061520533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19994205793911474707680355 29991308690867212061520533)
                  ·
                    refine ⟨1405842594884400565383775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29991308690867212061520533 1405842594884400565383775)
                    ·
                      rfl

theorem cell22_4106803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 6].length) (baseStart_4106803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106803 prefixEnd_4106803 := by exact prefixLift 4106803
  have htrace : WordTrace (prefixWord ++ tailWord_4106803) baseStart_4106803 baseEnd_4106803 := by
    simpa [prefixWord, tailWord_4106803, baseEnd_4106803] using wordTrace_append hprefix tailTrace_4106803
  have hstable : (prefixWord ++ tailWord_4106803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106803).length < 2 ^ (prefixWord ++ tailWord_4106803).sum := by decide
  have hdescent : baseEnd_4106803 < baseStart_4106803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106805 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 4, 3]
def baseStart_4106805 : Nat := 118140960795 + 4106805 * 2 ^ 59
def prefixEnd_4106805 : Nat := 4983230072969 + 3 ^ 40 * 4106805 * 2
def baseEnd_4106805 : Nat := 1405843279525273226833769

theorem tailTrace_4106805 : CollatzResearch.WordTrace tailWord_4106805 prefixEnd_4106805 1405843279525273226833769 := by
  unfold tailWord_4106805
  simp only [CollatzResearch.WordTrace]
  refine ⟨149787483886754346298881869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99858322591169564199254579 149787483886754346298881869)
  ·
    refine ⟨56170306457532879862080701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149787483886754346298881869 56170306457532879862080701)
    ·
      refine ⟨21063864921574829948280263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56170306457532879862080701 21063864921574829948280263)
      ·
        refine ⟨31595797382362244922420395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21063864921574829948280263 31595797382362244922420395)
        ·
          refine ⟨47393696073543367383630593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31595797382362244922420395 47393696073543367383630593)
          ·
            refine ⟨35545272055157525537722945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47393696073543367383630593 35545272055157525537722945)
            ·
              refine ⟨26658954041368144153292209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35545272055157525537722945 26658954041368144153292209)
              ·
                refine ⟨19994215531026108114969157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26658954041368144153292209 19994215531026108114969157)
                ·
                  refine ⟨3748915412067395271556717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19994215531026108114969157 3748915412067395271556717)
                  ·
                    refine ⟨1405843279525273226833769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3748915412067395271556717 1405843279525273226833769)
                    ·
                      rfl

theorem cell22_4106805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_4106805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106805 prefixEnd_4106805 := by exact prefixLift 4106805
  have htrace : WordTrace (prefixWord ++ tailWord_4106805) baseStart_4106805 baseEnd_4106805 := by
    simpa [prefixWord, tailWord_4106805, baseEnd_4106805] using wordTrace_append hprefix tailTrace_4106805
  have hstable : (prefixWord ++ tailWord_4106805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106805).length < 2 ^ (prefixWord ++ tailWord_4106805).sum := by decide
  have hdescent : baseEnd_4106805 < baseStart_4106805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106848 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_4106848 : Nat := 118140960795 + 4106848 * 2 ^ 59
def prefixEnd_4106848 : Nat := 4983230072969 + 3 ^ 40 * 4106848 * 2
def baseEnd_4106848 : Nat := 1405857999304035448008637

theorem tailTrace_4106848 : CollatzResearch.WordTrace tailWord_4106848 prefixEnd_4106848 1405857999304035448008637 := by
  unfold tailWord_4106848
  simp only [CollatzResearch.WordTrace]
  refine ⟨74894526112799282321348599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99859368150399043095131465 74894526112799282321348599)
  ·
    refine ⟨112341789169198923482022899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74894526112799282321348599 112341789169198923482022899)
    ·
      refine ⟨168512683753798385223034349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112341789169198923482022899 168512683753798385223034349)
      ·
        refine ⟨63192256407674394458637881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168512683753798385223034349 63192256407674394458637881)
        ·
          refine ⟨47394192305755795843978411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63192256407674394458637881 47394192305755795843978411)
          ·
            refine ⟨71091288458633693765967617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47394192305755795843978411 71091288458633693765967617)
            ·
              refine ⟨53318466343975270324475713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71091288458633693765967617 53318466343975270324475713)
              ·
                refine ⟨39988849757981452743356785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53318466343975270324475713 39988849757981452743356785)
                ·
                  refine ⟨29991637318486089557517589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39988849757981452743356785 29991637318486089557517589)
                  ·
                    refine ⟨1405857999304035448008637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29991637318486089557517589 1405857999304035448008637)
                    ·
                      rfl

theorem cell22_4106848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_4106848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106848 prefixEnd_4106848 := by exact prefixLift 4106848
  have htrace : WordTrace (prefixWord ++ tailWord_4106848) baseStart_4106848 baseEnd_4106848 := by
    simpa [prefixWord, tailWord_4106848, baseEnd_4106848] using wordTrace_append hprefix tailTrace_4106848
  have hstable : (prefixWord ++ tailWord_4106848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106848).length < 2 ^ (prefixWord ++ tailWord_4106848).sum := by decide
  have hdescent : baseEnd_4106848 < baseStart_4106848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106863 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 7]
def baseStart_4106863 : Nat := 118140960795 + 4106863 * 2 ^ 59
def prefixEnd_4106863 : Nat := 4983230072969 + 3 ^ 40 * 4106863 * 2
def baseEnd_4106863 : Nat := 468621044703526802961197

theorem tailTrace_4106863 : CollatzResearch.WordTrace tailWord_4106863 prefixEnd_4106863 468621044703526802961197 := by
  unfold tailWord_4106863
  simp only [CollatzResearch.WordTrace]
  refine ⟨149789599320544222204493243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99859732880362814802995495 149789599320544222204493243)
  ·
    refine ⟨224684398980816333306739865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149789599320544222204493243 224684398980816333306739865)
    ·
      refine ⟨168513299235612249980054899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224684398980816333306739865 168513299235612249980054899)
      ·
        refine ⟨252769948853418374970082349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168513299235612249980054899 252769948853418374970082349)
        ·
          refine ⟨94788730820031890613780881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 252769948853418374970082349 94788730820031890613780881)
          ·
            refine ⟨71091548115023917960335661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94788730820031890613780881 71091548115023917960335661)
            ·
              refine ⟨26659330543133969235125873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71091548115023917960335661 26659330543133969235125873)
              ·
                refine ⟨19994497907350476926344405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26659330543133969235125873 19994497907350476926344405)
                ·
                  refine ⟨468621044703526802961197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19994497907350476926344405 468621044703526802961197)
                  ·
                    rfl

theorem cell22_4106863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 7].length) (baseStart_4106863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106863 prefixEnd_4106863 := by exact prefixLift 4106863
  have htrace : WordTrace (prefixWord ++ tailWord_4106863) baseStart_4106863 baseEnd_4106863 := by
    simpa [prefixWord, tailWord_4106863, baseEnd_4106863] using wordTrace_append hprefix tailTrace_4106863
  have hstable : (prefixWord ++ tailWord_4106863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106863).length < 2 ^ (prefixWord ++ tailWord_4106863).sum := by decide
  have hdescent : baseEnd_4106863 < baseStart_4106863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106867 : List Nat := [1, 1, 1, 2, 2, 1, 1, 9, 1, 3]
def baseStart_4106867 : Nat := 118140960795 + 4106867 * 2 ^ 59
def prefixEnd_4106867 : Nat := 4983230072969 + 3 ^ 40 * 4106867 * 2
def baseEnd_4106867 : Nat := 1405864503392325731783579

theorem tailTrace_4106867 : CollatzResearch.WordTrace tailWord_4106867 prefixEnd_4106867 1405864503392325731783579 := by
  unfold tailWord_4106867
  simp only [CollatzResearch.WordTrace]
  refine ⟨149789745212529730887638855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99859830141686487258425903 149789745212529730887638855)
  ·
    refine ⟨224684617818794596331458283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149789745212529730887638855 224684617818794596331458283)
    ·
      refine ⟨337026926728191894497187425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224684617818794596331458283 337026926728191894497187425)
      ·
        refine ⟨252770195046143920872890569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337026926728191894497187425 252770195046143920872890569)
        ·
          refine ⟨189577646284607940654667927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252770195046143920872890569 189577646284607940654667927)
          ·
            refine ⟨284366469426911910982001891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189577646284607940654667927 284366469426911910982001891)
            ·
              refine ⟨426549704140367866473002837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284366469426911910982001891 426549704140367866473002837)
              ·
                refine ⟨2499314672697467967615251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 426549704140367866473002837 2499314672697467967615251)
                ·
                  refine ⟨3748972009046201951422877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499314672697467967615251 3748972009046201951422877)
                  ·
                    refine ⟨1405864503392325731783579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3748972009046201951422877 1405864503392325731783579)
                    ·
                      rfl

theorem cell22_4106867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 1, 3].length) (baseStart_4106867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106867 prefixEnd_4106867 := by exact prefixLift 4106867
  have htrace : WordTrace (prefixWord ++ tailWord_4106867) baseStart_4106867 baseEnd_4106867 := by
    simpa [prefixWord, tailWord_4106867, baseEnd_4106867] using wordTrace_append hprefix tailTrace_4106867
  have hstable : (prefixWord ++ tailWord_4106867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106867).length < 2 ^ (prefixWord ++ tailWord_4106867).sum := by decide
  have hdescent : baseEnd_4106867 < baseStart_4106867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106884 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_4106884 : Nat := 118140960795 + 4106884 * 2 ^ 59
def prefixEnd_4106884 : Nat := 4983230072969 + 3 ^ 40 * 4106884 * 2
def baseEnd_4106884 : Nat := 1405870322839743354108527

theorem tailTrace_4106884 : CollatzResearch.WordTrace tailWord_4106884 prefixEnd_4106884 1405870322839743354108527 := by
  unfold tailWord_4106884
  simp only [CollatzResearch.WordTrace]
  refine ⟨74895182626734071395503853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99860243502312095194005137 74895182626734071395503853)
  ·
    refine ⟨28085693485025276773313945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74895182626734071395503853 28085693485025276773313945)
    ·
      refine ⟨21064270113768957579985459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28085693485025276773313945 21064270113768957579985459)
      ·
        refine ⟨31596405170653436369978189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21064270113768957579985459 31596405170653436369978189)
        ·
          refine ⟨11848651938995038638741821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31596405170653436369978189 11848651938995038638741821)
          ·
            refine ⟨4443244477123139489528183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11848651938995038638741821 4443244477123139489528183)
            ·
              refine ⟨6664866715684709234292275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443244477123139489528183 6664866715684709234292275)
              ·
                refine ⟨9997300073527063851438413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6664866715684709234292275 9997300073527063851438413)
                ·
                  refine ⟨3748987527572648944289405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9997300073527063851438413 3748987527572648944289405)
                  ·
                    refine ⟨1405870322839743354108527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3748987527572648944289405 1405870322839743354108527)
                    ·
                      rfl

theorem cell22_4106884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_4106884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106884 prefixEnd_4106884 := by exact prefixLift 4106884
  have htrace : WordTrace (prefixWord ++ tailWord_4106884) baseStart_4106884 baseEnd_4106884 := by
    simpa [prefixWord, tailWord_4106884, baseEnd_4106884] using wordTrace_append hprefix tailTrace_4106884
  have hstable : (prefixWord ++ tailWord_4106884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106884).length < 2 ^ (prefixWord ++ tailWord_4106884).sum := by decide
  have hdescent : baseEnd_4106884 < baseStart_4106884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4106940 : List Nat := [2, 2, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_4106940 : Nat := 118140960795 + 4106940 * 2 ^ 59
def prefixEnd_4106940 : Nat := 4983230072969 + 3 ^ 40 * 4106940 * 2
def baseEnd_4106940 : Nat := 1405889492784177874708355

theorem tailTrace_4106940 : CollatzResearch.WordTrace tailWord_4106940 prefixEnd_4106940 1405889492784177874708355 := by
  unfold tailWord_4106940
  simp only [CollatzResearch.WordTrace]
  refine ⟨74896203870632632177523137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99861605160843509570030849 74896203870632632177523137)
  ·
    refine ⟨56172152902974474133142353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74896203870632632177523137 56172152902974474133142353)
    ·
      refine ⟨42129114677230855599856765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56172152902974474133142353 42129114677230855599856765)
      ·
        refine ⟨15798418003961570849946287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42129114677230855599856765 15798418003961570849946287)
        ·
          refine ⟨23697627005942356274919431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15798418003961570849946287 23697627005942356274919431)
          ·
            refine ⟨35546440508913534412379147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23697627005942356274919431 35546440508913534412379147)
            ·
              refine ⟨53319660763370301618568721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35546440508913534412379147 53319660763370301618568721)
              ·
                refine ⟨39989745572527726213926541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53319660763370301618568721 39989745572527726213926541)
                ·
                  refine ⟨14996154589697897330222453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39989745572527726213926541 14996154589697897330222453)
                  ·
                    refine ⟨1405889492784177874708355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14996154589697897330222453 1405889492784177874708355)
                    ·
                      rfl

theorem cell22_4106940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_4106940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4106940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4106940 prefixEnd_4106940 := by exact prefixLift 4106940
  have htrace : WordTrace (prefixWord ++ tailWord_4106940) baseStart_4106940 baseEnd_4106940 := by
    simpa [prefixWord, tailWord_4106940, baseEnd_4106940] using wordTrace_append hprefix tailTrace_4106940
  have hstable : (prefixWord ++ tailWord_4106940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4106940).length < 2 ^ (prefixWord ++ tailWord_4106940).sum := by decide
  have hdescent : baseEnd_4106940 < baseStart_4106940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4106940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107002 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 3, 3]
def baseStart_4107002 : Nat := 118140960795 + 4107002 * 2 ^ 59
def prefixEnd_4107002 : Nat := 4983230072969 + 3 ^ 40 * 4107002 * 2
def baseEnd_4107002 : Nat := 1405910716651230379658165

theorem tailTrace_4107002 : CollatzResearch.WordTrace tailWord_4107002 prefixEnd_4107002 1405910716651230379658165 := by
  unfold tailWord_4107002
  simp only [CollatzResearch.WordTrace]
  refine ⟨37448667266760162235950815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99863112711360432629202173 37448667266760162235950815)
  ·
    refine ⟨56173000900140243353926223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37448667266760162235950815 56173000900140243353926223)
    ·
      refine ⟨84259501350210365030889335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56173000900140243353926223 84259501350210365030889335)
      ·
        refine ⟨126389252025315547546334003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84259501350210365030889335 126389252025315547546334003)
        ·
          refine ⟨189583878037973321319501005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126389252025315547546334003 189583878037973321319501005)
          ·
            refine ⟨71093954264239995494812877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189583878037973321319501005 71093954264239995494812877)
            ·
              refine ⟨26660232849089998310554829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71093954264239995494812877 26660232849089998310554829)
              ·
                refine ⟨9997587318408749366458061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26660232849089998310554829 9997587318408749366458061)
                ·
                  refine ⟨3749095244403281012421773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9997587318408749366458061 3749095244403281012421773)
                  ·
                    refine ⟨1405910716651230379658165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3749095244403281012421773 1405910716651230379658165)
                    ·
                      rfl

theorem cell22_4107002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_4107002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107002 prefixEnd_4107002 := by exact prefixLift 4107002
  have htrace : WordTrace (prefixWord ++ tailWord_4107002) baseStart_4107002 baseEnd_4107002 := by
    simpa [prefixWord, tailWord_4107002, baseEnd_4107002] using wordTrace_append hprefix tailTrace_4107002
  have hstable : (prefixWord ++ tailWord_4107002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107002).length < 2 ^ (prefixWord ++ tailWord_4107002).sum := by decide
  have hdescent : baseEnd_4107002 < baseStart_4107002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107036 : List Nat := [2, 2, 3, 1, 1, 3, 3, 3, 1, 3]
def baseStart_4107036 : Nat := 118140960795 + 4107036 * 2 ^ 59
def prefixEnd_4107036 : Nat := 4983230072969 + 3 ^ 40 * 4107036 * 2
def baseEnd_4107036 : Nat := 1405922355546065624308061

theorem tailTrace_4107036 : CollatzResearch.WordTrace tailWord_4107036 prefixEnd_4107036 1405922355546065624308061 := by
  unfold tailWord_4107036
  simp only [CollatzResearch.WordTrace]
  refine ⟨74897954574458736375270481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99863939432611648500360641 74897954574458736375270481)
  ·
    refine ⟨56173465930844052281452861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74897954574458736375270481 56173465930844052281452861)
    ·
      refine ⟨21065049724066519605544823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56173465930844052281452861 21065049724066519605544823)
      ·
        refine ⟨31597574586099779408317235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21065049724066519605544823 31597574586099779408317235)
        ·
          refine ⟨47396361879149669112475853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31597574586099779408317235 47396361879149669112475853)
          ·
            refine ⟨17773635704681125917178445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47396361879149669112475853 17773635704681125917178445)
            ·
              refine ⟨6665113389255422218941917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17773635704681125917178445 6665113389255422218941917)
              ·
                refine ⟨2499417520970783332103219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6665113389255422218941917 2499417520970783332103219)
                ·
                  refine ⟨3749126281456174998154829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499417520970783332103219 3749126281456174998154829)
                  ·
                    refine ⟨1405922355546065624308061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3749126281456174998154829 1405922355546065624308061)
                    ·
                      rfl

theorem cell22_4107036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_4107036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107036 prefixEnd_4107036 := by exact prefixLift 4107036
  have htrace : WordTrace (prefixWord ++ tailWord_4107036) baseStart_4107036 baseEnd_4107036 := by
    simpa [prefixWord, tailWord_4107036, baseEnd_4107036] using wordTrace_append hprefix tailTrace_4107036
  have hstable : (prefixWord ++ tailWord_4107036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107036).length < 2 ^ (prefixWord ++ tailWord_4107036).sum := by decide
  have hdescent : baseEnd_4107036 < baseStart_4107036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107066 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 5]
def baseStart_4107066 : Nat := 118140960795 + 4107066 * 2 ^ 59
def prefixEnd_4107066 : Nat := 4983230072969 + 3 ^ 40 * 4107066 * 2
def baseEnd_4107066 : Nat := 468644208386385182019323

theorem tailTrace_4107066 : CollatzResearch.WordTrace tailWord_4107066 prefixEnd_4107066 468644208386385182019323 := by
  unfold tailWord_4107066
  simp only [CollatzResearch.WordTrace]
  refine ⟨37449250834702196968533263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99864668892539191916088701 37449250834702196968533263)
  ·
    refine ⟨56173876252053295452799895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37449250834702196968533263 56173876252053295452799895)
    ·
      refine ⟨84260814378079943179199843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56173876252053295452799895 84260814378079943179199843)
      ·
        refine ⟨126391221567119914768799765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84260814378079943179199843 126391221567119914768799765)
        ·
          refine ⟨5924588510958746004787489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 126391221567119914768799765 5924588510958746004787489)
          ·
            refine ⟨4443441383219059503590617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5924588510958746004787489 4443441383219059503590617)
            ·
              refine ⟨3332581037414294627692963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443441383219059503590617 3332581037414294627692963)
              ·
                refine ⟨4998871556121441941539445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332581037414294627692963 4998871556121441941539445)
                ·
                  refine ⟨468644208386385182019323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4998871556121441941539445 468644208386385182019323)
                  ·
                    rfl

theorem cell22_4107066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_4107066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107066 prefixEnd_4107066 := by exact prefixLift 4107066
  have htrace : WordTrace (prefixWord ++ tailWord_4107066) baseStart_4107066 baseEnd_4107066 := by
    simpa [prefixWord, tailWord_4107066, baseEnd_4107066] using wordTrace_append hprefix tailTrace_4107066
  have hstable : (prefixWord ++ tailWord_4107066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107066).length < 2 ^ (prefixWord ++ tailWord_4107066).sum := by decide
  have hdescent : baseEnd_4107066 < baseStart_4107066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107109 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 2, 3]
def baseStart_4107109 : Nat := 118140960795 + 4107109 * 2 ^ 59
def prefixEnd_4107109 : Nat := 4983230072969 + 3 ^ 40 * 4107109 * 2
def baseEnd_4107109 : Nat := 1405947344937917767232837

theorem tailTrace_4107109 : CollatzResearch.WordTrace tailWord_4107109 prefixEnd_4107109 1405947344937917767232837 := by
  unfold tailWord_4107109
  simp only [CollatzResearch.WordTrace]
  refine ⟨149798571677653006217948381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99865714451768670811965587 149798571677653006217948381)
  ·
    refine ⟨56174464379119877331730643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149798571677653006217948381 56174464379119877331730643)
    ·
      refine ⟨84261696568679815997595965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56174464379119877331730643 84261696568679815997595965)
      ·
        refine ⟨31598136213254930999098487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84261696568679815997595965 31598136213254930999098487)
        ·
          refine ⟨47397204319882396498647731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31598136213254930999098487 47397204319882396498647731)
          ·
            refine ⟨71095806479823594747971597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47397204319882396498647731 71095806479823594747971597)
            ·
              refine ⟨26660927429933848030489349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71095806479823594747971597 26660927429933848030489349)
              ·
                refine ⟨4998923893112596505716753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26660927429933848030489349 4998923893112596505716753)
                ·
                  refine ⟨3749192919834447379287565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4998923893112596505716753 3749192919834447379287565)
                  ·
                    refine ⟨1405947344937917767232837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3749192919834447379287565 1405947344937917767232837)
                    ·
                      rfl

theorem cell22_4107109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_4107109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107109 prefixEnd_4107109 := by exact prefixLift 4107109
  have htrace : WordTrace (prefixWord ++ tailWord_4107109) baseStart_4107109 baseEnd_4107109 := by
    simpa [prefixWord, tailWord_4107109, baseEnd_4107109] using wordTrace_append hprefix tailTrace_4107109
  have hstable : (prefixWord ++ tailWord_4107109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107109).length < 2 ^ (prefixWord ++ tailWord_4107109).sum := by decide
  have hdescent : baseEnd_4107109 < baseStart_4107109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107111 : List Nat := [1, 1, 5, 1, 2, 2, 4, 2, 4]
def baseStart_4107111 : Nat := 118140960795 + 4107111 * 2 ^ 59
def prefixEnd_4107111 : Nat := 4983230072969 + 3 ^ 40 * 4107111 * 2
def baseEnd_4107111 : Nat := 468649343192930142894277

theorem tailTrace_4107111 : CollatzResearch.WordTrace tailWord_4107111 prefixEnd_4107111 468649343192930142894277 := by
  unfold tailWord_4107111
  simp only [CollatzResearch.WordTrace]
  refine ⟨149798644623645760559521187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99865763082430507039680791 149798644623645760559521187)
  ·
    refine ⟨224697966935468640839281781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149798644623645760559521187 224697966935468640839281781)
    ·
      refine ⟨21065434400200185078682667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 224697966935468640839281781 21065434400200185078682667)
      ·
        refine ⟨31598151600300277618024001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21065434400200185078682667 31598151600300277618024001)
        ·
          refine ⟨23698613700225208213518001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31598151600300277618024001 23698613700225208213518001)
          ·
            refine ⟨17773960275168906160138501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23698613700225208213518001 17773960275168906160138501)
            ·
              refine ⟨3332617551594169905025969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17773960275168906160138501 3332617551594169905025969)
              ·
                refine ⟨2499463163695627428769477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3332617551594169905025969 2499463163695627428769477)
                ·
                  refine ⟨468649343192930142894277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2499463163695627428769477 468649343192930142894277)
                  ·
                    rfl

theorem cell22_4107111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 2, 4].length) (baseStart_4107111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107111 prefixEnd_4107111 := by exact prefixLift 4107111
  have htrace : WordTrace (prefixWord ++ tailWord_4107111) baseStart_4107111 baseEnd_4107111 := by
    simpa [prefixWord, tailWord_4107111, baseEnd_4107111] using wordTrace_append hprefix tailTrace_4107111
  have hstable : (prefixWord ++ tailWord_4107111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107111).length < 2 ^ (prefixWord ++ tailWord_4107111).sum := by decide
  have hdescent : baseEnd_4107111 < baseStart_4107111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107122 : List Nat := [3, 2, 1, 2, 1, 1, 5, 7]
def baseStart_4107122 : Nat := 118140960795 + 4107122 * 2 ^ 59
def prefixEnd_4107122 : Nat := 4983230072969 + 3 ^ 40 * 4107122 * 2
def baseEnd_4107122 : Nat := 156216866122621118517533

theorem tailTrace_4107122 : CollatzResearch.WordTrace tailWord_4107122 prefixEnd_4107122 156216866122621118517533 := by
  unfold tailWord_4107122
  simp only [CollatzResearch.WordTrace]
  refine ⟨37449761456651477359542905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99866030551070606292114413 37449761456651477359542905)
  ·
    refine ⟨28087321092488608019657179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37449761456651477359542905 28087321092488608019657179)
    ·
      refine ⟨42130981638732912029485769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28087321092488608019657179 42130981638732912029485769)
      ·
        refine ⟨31598236229049684022114327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42130981638732912029485769 31598236229049684022114327)
        ·
          refine ⟨47397354343574526033171491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31598236229049684022114327 47397354343574526033171491)
          ·
            refine ⟨71096031515361789049757237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47397354343574526033171491 71096031515361789049757237)
            ·
              refine ⟨6665252954565167723414741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71096031515361789049757237 6665252954565167723414741)
              ·
                refine ⟨156216866122621118517533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6665252954565167723414741 156216866122621118517533)
                ·
                  rfl

theorem cell22_4107122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_4107122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107122 prefixEnd_4107122 := by exact prefixLift 4107122
  have htrace : WordTrace (prefixWord ++ tailWord_4107122) baseStart_4107122 baseEnd_4107122 := by
    simpa [prefixWord, tailWord_4107122, baseEnd_4107122] using wordTrace_append hprefix tailTrace_4107122
  have hstable : (prefixWord ++ tailWord_4107122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107122).length < 2 ^ (prefixWord ++ tailWord_4107122).sum := by decide
  have hdescent : baseEnd_4107122 < baseStart_4107122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107126 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_4107126 : Nat := 118140960795 + 4107126 * 2 ^ 59
def prefixEnd_4107126 : Nat := 4983230072969 + 3 ^ 40 * 4107126 * 2
def baseEnd_4107126 : Nat := 1405953164385335389557785

theorem tailTrace_4107126 : CollatzResearch.WordTrace tailWord_4107126 prefixEnd_4107126 1405953164385335389557785 := by
  unfold tailWord_4107126
  simp only [CollatzResearch.WordTrace]
  refine ⟨9362449482411963632582327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99866127812394278747544821 9362449482411963632582327)
  ·
    refine ⟨14043674223617945448873491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9362449482411963632582327 14043674223617945448873491)
    ·
      refine ⟨21065511335426918173310237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14043674223617945448873491 21065511335426918173310237)
      ·
        refine ⟨7899566750785094314991339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21065511335426918173310237 7899566750785094314991339)
        ·
          refine ⟨11849350126177641472487009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7899566750785094314991339 11849350126177641472487009)
          ·
            refine ⟨8887012594633231104365257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11849350126177641472487009 8887012594633231104365257)
            ·
              refine ⟨6665259445974923328273943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8887012594633231104365257 6665259445974923328273943)
              ·
                refine ⟨9997889168962384992410915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6665259445974923328273943 9997889168962384992410915)
                ·
                  refine ⟨14996833753443577488616373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9997889168962384992410915 14996833753443577488616373)
                  ·
                    refine ⟨1405953164385335389557785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14996833753443577488616373 1405953164385335389557785)
                    ·
                      rfl

theorem cell22_4107126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_4107126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107126 prefixEnd_4107126 := by exact prefixLift 4107126
  have htrace : WordTrace (prefixWord ++ tailWord_4107126) baseStart_4107126 baseEnd_4107126 := by
    simpa [prefixWord, tailWord_4107126, baseEnd_4107126] using wordTrace_append hprefix tailTrace_4107126
  have hstable : (prefixWord ++ tailWord_4107126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107126).length < 2 ^ (prefixWord ++ tailWord_4107126).sum := by decide
  have hdescent : baseEnd_4107126 < baseStart_4107126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107171 : List Nat := [1, 1, 1, 4, 1, 2, 4, 4, 1, 3]
def baseStart_4107171 : Nat := 118140960795 + 4107171 * 2 ^ 59
def prefixEnd_4107171 : Nat := 4983230072969 + 3 ^ 40 * 4107171 * 2
def baseEnd_4107171 : Nat := 1405968568804970272182647

theorem tailTrace_4107171 : CollatzResearch.WordTrace tailWord_4107171 prefixEnd_4107171 1405968568804970272182647 := by
  unfold tailWord_4107171
  simp only [CollatzResearch.WordTrace]
  refine ⟨149800833003428390806705367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99867222002285593871136911 149800833003428390806705367)
  ·
    refine ⟨224701249505142586210058051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149800833003428390806705367 224701249505142586210058051)
    ·
      refine ⟨337051874257713879315087077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224701249505142586210058051 337051874257713879315087077)
      ·
        refine ⟨63197226423321352371578827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 337051874257713879315087077 63197226423321352371578827)
        ·
          refine ⟨94795839634982028557368241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63197226423321352371578827 94795839634982028557368241)
          ·
            refine ⟨71096879726236521418026181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94795839634982028557368241 71096879726236521418026181)
            ·
              refine ⟨13330664948669347765879909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71096879726236521418026181 13330664948669347765879909)
              ·
                refine ⟨2499499677875502706102483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13330664948669347765879909 2499499677875502706102483)
                ·
                  refine ⟨3749249516813254059153725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499499677875502706102483 3749249516813254059153725)
                  ·
                    refine ⟨1405968568804970272182647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3749249516813254059153725 1405968568804970272182647)
                    ·
                      rfl

theorem cell22_4107171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 1, 3].length) (baseStart_4107171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107171 prefixEnd_4107171 := by exact prefixLift 4107171
  have htrace : WordTrace (prefixWord ++ tailWord_4107171) baseStart_4107171 baseEnd_4107171 := by
    simpa [prefixWord, tailWord_4107171, baseEnd_4107171] using wordTrace_append hprefix tailTrace_4107171
  have hstable : (prefixWord ++ tailWord_4107171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107171).length < 2 ^ (prefixWord ++ tailWord_4107171).sum := by decide
  have hdescent : baseEnd_4107171 < baseStart_4107171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107188 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4107188 : Nat := 118140960795 + 4107188 * 2 ^ 59
def prefixEnd_4107188 : Nat := 4983230072969 + 3 ^ 40 * 4107188 * 2
def baseEnd_4107188 : Nat := 1405974388252387894507595

theorem tailTrace_4107188 : CollatzResearch.WordTrace tailWord_4107188 prefixEnd_4107188 1405974388252387894507595 := by
  unfold tailWord_4107188
  simp only [CollatzResearch.WordTrace]
  refine ⟨74900726522183401355037109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99867635362911201806716145 74900726522183401355037109)
  ·
    refine ⟨7021943111454693877034729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74900726522183401355037109 7021943111454693877034729)
    ·
      refine ⟨5266457333591020407776047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7021943111454693877034729 5266457333591020407776047)
      ·
        refine ⟨7899686000386530611664071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5266457333591020407776047 7899686000386530611664071)
        ·
          refine ⟨11849529000579795917496107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7899686000386530611664071 11849529000579795917496107)
          ·
            refine ⟨17774293500869693876244161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11849529000579795917496107 17774293500869693876244161)
            ·
              refine ⟨13330720125652270407183121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17774293500869693876244161 13330720125652270407183121)
              ·
                refine ⟨9998040094239202805387341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13330720125652270407183121 9998040094239202805387341)
                ·
                  refine ⟨3749265035339701052020253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9998040094239202805387341 3749265035339701052020253)
                  ·
                    refine ⟨1405974388252387894507595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3749265035339701052020253 1405974388252387894507595)
                    ·
                      rfl

theorem cell22_4107188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4107188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107188 prefixEnd_4107188 := by exact prefixLift 4107188
  have htrace : WordTrace (prefixWord ++ tailWord_4107188) baseStart_4107188 baseEnd_4107188 := by
    simpa [prefixWord, tailWord_4107188, baseEnd_4107188] using wordTrace_append hprefix tailTrace_4107188
  have hstable : (prefixWord ++ tailWord_4107188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107188).length < 2 ^ (prefixWord ++ tailWord_4107188).sum := by decide
  have hdescent : baseEnd_4107188 < baseStart_4107188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107222 : List Nat := [5, 2, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_4107222 : Nat := 118140960795 + 4107222 * 2 ^ 59
def prefixEnd_4107222 : Nat := 4983230072969 + 3 ^ 40 * 4107222 * 2
def baseEnd_4107222 : Nat := 1405986027147223139157491

theorem tailTrace_4107222 : CollatzResearch.WordTrace tailWord_4107222 prefixEnd_4107222 1405986027147223139157491 := by
  unfold tailWord_4107222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9362668320390226657300745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99868462084162417677874613 9362668320390226657300745)
  ·
    refine ⟨7022001240292669992975559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9362668320390226657300745 7022001240292669992975559)
    ·
      refine ⟨10533001860439004989463339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7022001240292669992975559 10533001860439004989463339)
      ·
        refine ⟨15799502790658507484195009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10533001860439004989463339 15799502790658507484195009)
        ·
          refine ⟨11849627092993880613146257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15799502790658507484195009 11849627092993880613146257)
          ·
            refine ⟨8887220319745410459859693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11849627092993880613146257 8887220319745410459859693)
            ·
              refine ⟨3332707619904528922447385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8887220319745410459859693 3332707619904528922447385)
              ·
                refine ⟨2499530714928396691835539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3332707619904528922447385 2499530714928396691835539)
                ·
                  refine ⟨3749296072392595037753309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2499530714928396691835539 3749296072392595037753309)
                  ·
                    refine ⟨1405986027147223139157491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3749296072392595037753309 1405986027147223139157491)
                    ·
                      rfl

theorem cell22_4107222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_4107222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107222 prefixEnd_4107222 := by exact prefixLift 4107222
  have htrace : WordTrace (prefixWord ++ tailWord_4107222) baseStart_4107222 baseEnd_4107222 := by
    simpa [prefixWord, tailWord_4107222, baseEnd_4107222] using wordTrace_append hprefix tailTrace_4107222
  have hstable : (prefixWord ++ tailWord_4107222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107222).length < 2 ^ (prefixWord ++ tailWord_4107222).sum := by decide
  have hdescent : baseEnd_4107222 < baseStart_4107222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107257 : List Nat := [1, 2, 1, 3, 1, 3, 1, 10]
def baseStart_4107257 : Nat := 118140960795 + 4107257 * 2 ^ 59
def prefixEnd_4107257 : Nat := 4983230072969 + 3 ^ 40 * 4107257 * 2
def baseEnd_4107257 : Nat := 156222000929166079392487

theorem tailTrace_4107257 : CollatzResearch.WordTrace tailWord_4107257 prefixEnd_4107257 156222000929166079392487 := by
  unfold tailWord_4107257
  simp only [CollatzResearch.WordTrace]
  refine ⟨149803969681116827494336025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99869313120744551662890683 149803969681116827494336025)
  ·
    refine ⟨112352977260837620620752019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149803969681116827494336025 112352977260837620620752019)
    ·
      refine ⟨168529465891256430931128029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112352977260837620620752019 168529465891256430931128029)
      ·
        refine ⟨63198549709221161599173011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168529465891256430931128029 63198549709221161599173011)
        ·
          refine ⟨94797824563831742398759517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63198549709221161599173011 94797824563831742398759517)
          ·
            refine ⟨35549184211436903399534819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94797824563831742398759517 35549184211436903399534819)
            ·
              refine ⟨53323776317155355099302229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35549184211436903399534819 53323776317155355099302229)
              ·
                refine ⟨156222000929166079392487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53323776317155355099302229 156222000929166079392487)
                ·
                  rfl

theorem cell22_4107257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 10].length) (baseStart_4107257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107257 prefixEnd_4107257 := by exact prefixLift 4107257
  have htrace : WordTrace (prefixWord ++ tailWord_4107257) baseStart_4107257 baseEnd_4107257 := by
    simpa [prefixWord, tailWord_4107257, baseEnd_4107257] using wordTrace_append hprefix tailTrace_4107257
  have hstable : (prefixWord ++ tailWord_4107257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107257).length < 2 ^ (prefixWord ++ tailWord_4107257).sum := by decide
  have hdescent : baseEnd_4107257 < baseStart_4107257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107278 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_4107278 : Nat := 118140960795 + 4107278 * 2 ^ 59
def prefixEnd_4107278 : Nat := 4983230072969 + 3 ^ 40 * 4107278 * 2
def baseEnd_4107278 : Nat := 1406005197091657659757319

theorem tailTrace_4107278 : CollatzResearch.WordTrace tailWord_4107278 prefixEnd_4107278 1406005197091657659757319 := by
  unfold tailWord_4107278
  simp only [CollatzResearch.WordTrace]
  refine ⟨18725591951755093510106311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99869823742693832053900325 18725591951755093510106311)
  ·
    refine ⟨28088387927632640265159467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18725591951755093510106311 28088387927632640265159467)
    ·
      refine ⟨42132581891448960397739201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28088387927632640265159467 42132581891448960397739201)
      ·
        refine ⟨31599436418586720298304401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42132581891448960397739201 31599436418586720298304401)
        ·
          refine ⟨23699577313940040223728301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31599436418586720298304401 23699577313940040223728301)
          ·
            refine ⟨8887341492727515083898113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23699577313940040223728301 8887341492727515083898113)
            ·
              refine ⟨6665506119545636312923585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8887341492727515083898113 6665506119545636312923585)
              ·
                refine ⟨4999129589659227234692689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6665506119545636312923585 4999129589659227234692689)
                ·
                  refine ⟨3749347192244420426019517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4999129589659227234692689 3749347192244420426019517)
                  ·
                    refine ⟨1406005197091657659757319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3749347192244420426019517 1406005197091657659757319)
                    ·
                      rfl

theorem cell22_4107278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_4107278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107278 prefixEnd_4107278 := by exact prefixLift 4107278
  have htrace : WordTrace (prefixWord ++ tailWord_4107278) baseStart_4107278 baseEnd_4107278 := by
    simpa [prefixWord, tailWord_4107278, baseEnd_4107278] using wordTrace_append hprefix tailTrace_4107278
  have hstable : (prefixWord ++ tailWord_4107278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107278).length < 2 ^ (prefixWord ++ tailWord_4107278).sum := by decide
  have hdescent : baseEnd_4107278 < baseStart_4107278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107428 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_4107428 : Nat := 118140960795 + 4107428 * 2 ^ 59
def prefixEnd_4107428 : Nat := 4983230072969 + 3 ^ 40 * 4107428 * 2
def baseEnd_4107428 : Nat := 1406056545157107268506859

theorem tailTrace_4107428 : CollatzResearch.WordTrace tailWord_4107428 prefixEnd_4107428 1406056545157107268506859 := by
  unfold tailWord_4107428
  simp only [CollatzResearch.WordTrace]
  refine ⟨74905103281748661849405469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99873471042331549132540625 74905103281748661849405469)
  ·
    refine ⟨28089413730655748193527051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74905103281748661849405469 28089413730655748193527051)
    ·
      refine ⟨42134120595983622290290577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28089413730655748193527051 42134120595983622290290577)
      ·
        refine ⟨31600590446987716717717933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42134120595983622290290577 31600590446987716717717933)
        ·
          refine ⟨11850221417620393769144225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31600590446987716717717933 11850221417620393769144225)
          ·
            refine ⟨8887666063215295326858169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11850221417620393769144225 8887666063215295326858169)
            ·
              refine ⟨6665749547411471495143627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8887666063215295326858169 6665749547411471495143627)
              ·
                refine ⟨9998624321117207242715441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6665749547411471495143627 9998624321117207242715441)
                ·
                  refine ⟨7498968240837905432036581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9998624321117207242715441 7498968240837905432036581)
                  ·
                    refine ⟨1406056545157107268506859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7498968240837905432036581 1406056545157107268506859)
                    ·
                      rfl

theorem cell22_4107428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_4107428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107428 prefixEnd_4107428 := by exact prefixLift 4107428
  have htrace : WordTrace (prefixWord ++ tailWord_4107428) baseStart_4107428 baseEnd_4107428 := by
    simpa [prefixWord, tailWord_4107428, baseEnd_4107428] using wordTrace_append hprefix tailTrace_4107428
  have hstable : (prefixWord ++ tailWord_4107428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107428).length < 2 ^ (prefixWord ++ tailWord_4107428).sum := by decide
  have hdescent : baseEnd_4107428 < baseStart_4107428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107460 : List Nat := [2, 3, 3, 1, 4, 1, 1, 7]
def baseStart_4107460 : Nat := 118140960795 + 4107460 * 2 ^ 59
def prefixEnd_4107460 : Nat := 4983230072969 + 3 ^ 40 * 4107460 * 2
def baseEnd_4107460 : Nat := 156229722156785539078529

theorem tailTrace_4107460 : CollatzResearch.WordTrace tailWord_4107460 prefixEnd_4107460 156229722156785539078529 := by
  unfold tailWord_4107460
  simp only [CollatzResearch.WordTrace]
  refine ⟨74905686849690696581987917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99874249132920928775983889 74905686849690696581987917)
  ·
    refine ⟨28089632568634011218245469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74905686849690696581987917 28089632568634011218245469)
    ·
      refine ⟨10533612213237754206842051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28089632568634011218245469 10533612213237754206842051)
      ·
        refine ⟨15800418319856631310263077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10533612213237754206842051 15800418319856631310263077)
        ·
          refine ⟨2962578434973118370674327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15800418319856631310263077 2962578434973118370674327)
          ·
            refine ⟨4443867652459677556011491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962578434973118370674327 4443867652459677556011491)
            ·
              refine ⟨6665801478689516334017237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4443867652459677556011491 6665801478689516334017237)
              ·
                refine ⟨156229722156785539078529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6665801478689516334017237 156229722156785539078529)
                ·
                  rfl

theorem cell22_4107460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 7].length) (baseStart_4107460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107460 prefixEnd_4107460 := by exact prefixLift 4107460
  have htrace : WordTrace (prefixWord ++ tailWord_4107460) baseStart_4107460 baseEnd_4107460 := by
    simpa [prefixWord, tailWord_4107460, baseEnd_4107460] using wordTrace_append hprefix tailTrace_4107460
  have hstable : (prefixWord ++ tailWord_4107460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107460).length < 2 ^ (prefixWord ++ tailWord_4107460).sum := by decide
  have hdescent : baseEnd_4107460 < baseStart_4107460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107522 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 5]
def baseStart_4107522 : Nat := 118140960795 + 4107522 * 2 ^ 59
def prefixEnd_4107522 : Nat := 4983230072969 + 3 ^ 40 * 4107522 * 2
def baseEnd_4107522 : Nat := 468696241092707452218857

theorem tailTrace_4107522 : CollatzResearch.WordTrace tailWord_4107522 prefixEnd_4107522 468696241092707452218857 := by
  unfold tailWord_4107522
  simp only [CollatzResearch.WordTrace]
  refine ⟨37453408756289194438183205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99875756683437851835155213 37453408756289194438183205)
  ·
    refine ⟨7022514141804223957159351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37453408756289194438183205 7022514141804223957159351)
    ·
      refine ⟨10533771212706335935739027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7022514141804223957159351 10533771212706335935739027)
      ·
        refine ⟨15800656819059503903608541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10533771212706335935739027 15800656819059503903608541)
        ·
          refine ⟨5925246307147313963853203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15800656819059503903608541 5925246307147313963853203)
          ·
            refine ⟨8887869460720970945779805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5925246307147313963853203 8887869460720970945779805)
            ·
              refine ⟨3332951047770364104667427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8887869460720970945779805 3332951047770364104667427)
              ·
                refine ⟨4999426571655546157001141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332951047770364104667427 4999426571655546157001141)
                ·
                  refine ⟨468696241092707452218857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4999426571655546157001141 468696241092707452218857)
                  ·
                    rfl

theorem cell22_4107522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_4107522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107522 prefixEnd_4107522 := by exact prefixLift 4107522
  have htrace : WordTrace (prefixWord ++ tailWord_4107522) baseStart_4107522 baseEnd_4107522 := by
    simpa [prefixWord, tailWord_4107522, baseEnd_4107522] using wordTrace_append hprefix tailTrace_4107522
  have hstable : (prefixWord ++ tailWord_4107522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107522).length < 2 ^ (prefixWord ++ tailWord_4107522).sum := by decide
  have hdescent : baseEnd_4107522 < baseStart_4107522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107548 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 4, 3]
def baseStart_4107548 : Nat := 118140960795 + 4107548 * 2 ^ 59
def prefixEnd_4107548 : Nat := 4983230072969 + 3 ^ 40 * 4107548 * 2
def baseEnd_4107548 : Nat := 1406097623609466955506491

theorem tailTrace_4107548 : CollatzResearch.WordTrace tailWord_4107548 prefixEnd_4107548 1406097623609466955506491 := by
  unfold tailWord_4107548
  simp only [CollatzResearch.WordTrace]
  refine ⟨74907291661531292096589649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99876388882041722795452865 74907291661531292096589649)
  ·
    refine ⟨56180468746148469072442237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74907291661531292096589649 56180468746148469072442237)
    ·
      refine ⟨21067675779805675902165839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56180468746148469072442237 21067675779805675902165839)
      ·
        refine ⟨31601513669708513853248759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21067675779805675902165839 31601513669708513853248759)
        ·
          refine ⟨47402270504562770779873139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31601513669708513853248759 47402270504562770779873139)
          ·
            refine ⟨71103405756844156169809709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47402270504562770779873139 71103405756844156169809709)
            ·
              refine ⟨26663777158816558563678641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71103405756844156169809709 26663777158816558563678641)
              ·
                refine ⟨19997832869112418922758981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26663777158816558563678641 19997832869112418922758981)
                ·
                  refine ⟨3749593662958578548017309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19997832869112418922758981 3749593662958578548017309)
                  ·
                    refine ⟨1406097623609466955506491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3749593662958578548017309 1406097623609466955506491)
                    ·
                      rfl

theorem cell22_4107548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_4107548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107548 prefixEnd_4107548 := by exact prefixLift 4107548
  have htrace : WordTrace (prefixWord ++ tailWord_4107548) baseStart_4107548 baseEnd_4107548 := by
    simpa [prefixWord, tailWord_4107548, baseEnd_4107548] using wordTrace_append hprefix tailTrace_4107548
  have hstable : (prefixWord ++ tailWord_4107548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107548).length < 2 ^ (prefixWord ++ tailWord_4107548).sum := by decide
  have hdescent : baseEnd_4107548 < baseStart_4107548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107593 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 3, 3]
def baseStart_4107593 : Nat := 118140960795 + 4107593 * 2 ^ 59
def prefixEnd_4107593 : Nat := 4983230072969 + 3 ^ 40 * 4107593 * 2
def baseEnd_4107593 : Nat := 1406113028029101838131353

theorem tailTrace_4107593 : CollatzResearch.WordTrace tailWord_4107593 prefixEnd_4107593 1406113028029101838131353 := by
  unfold tailWord_4107593
  simp only [CollatzResearch.WordTrace]
  refine ⟨149816224607899556878567433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99877483071933037919044955 149816224607899556878567433)
  ·
    refine ⟨112362168455924667658925575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149816224607899556878567433 112362168455924667658925575)
    ·
      refine ⟨168543252683887001488388363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112362168455924667658925575 168543252683887001488388363)
      ·
        refine ⟨252814879025830502232582545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168543252683887001488388363 252814879025830502232582545)
        ·
          refine ⟨189611159269372876674436909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252814879025830502232582545 189611159269372876674436909)
          ·
            refine ⟨71104184726014828752913841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189611159269372876674436909 71104184726014828752913841)
            ·
              refine ⟨53328138544511121564685381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71104184726014828752913841 53328138544511121564685381)
              ·
                refine ⟨9999025977095835293378509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53328138544511121564685381 9999025977095835293378509)
                ·
                  refine ⟨3749634741410938235016941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9999025977095835293378509 3749634741410938235016941)
                  ·
                    refine ⟨1406113028029101838131353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3749634741410938235016941 1406113028029101838131353)
                    ·
                      rfl

theorem cell22_4107593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 3].length) (baseStart_4107593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107593 prefixEnd_4107593 := by exact prefixLift 4107593
  have htrace : WordTrace (prefixWord ++ tailWord_4107593) baseStart_4107593 baseEnd_4107593 := by
    simpa [prefixWord, tailWord_4107593, baseEnd_4107593] using wordTrace_append hprefix tailTrace_4107593
  have hstable : (prefixWord ++ tailWord_4107593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107593).length < 2 ^ (prefixWord ++ tailWord_4107593).sum := by decide
  have hdescent : baseEnd_4107593 < baseStart_4107593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107653 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_4107653 : Nat := 118140960795 + 4107653 * 2 ^ 59
def prefixEnd_4107653 : Nat := 4983230072969 + 3 ^ 40 * 4107653 * 2
def baseEnd_4107653 : Nat := 1406133567255281681631169

theorem tailTrace_4107653 : CollatzResearch.WordTrace tailWord_4107653 prefixEnd_4107653 1406133567255281681631169 := by
  unfold tailWord_4107653
  simp only [CollatzResearch.WordTrace]
  refine ⟨149818412987682187125751613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99878941991788124750501075 149818412987682187125751613)
  ·
    refine ⟨56181904870380820172156855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149818412987682187125751613 56181904870380820172156855)
    ·
      refine ⟨84272857305571230258235283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56181904870380820172156855 84272857305571230258235283)
      ·
        refine ⟨126409285958356845387352925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84272857305571230258235283 126409285958356845387352925)
        ·
          refine ⟨47403482234383817020257347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126409285958356845387352925 47403482234383817020257347)
          ·
            refine ⟨71105223351575725530386021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47403482234383817020257347 71105223351575725530386021)
            ·
              refine ⟨13332229378420448536947379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71105223351575725530386021 13332229378420448536947379)
              ·
                refine ⟨19998344067630672805421069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13332229378420448536947379 19998344067630672805421069)
                ·
                  refine ⟨7499379025361502302032901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19998344067630672805421069 7499379025361502302032901)
                  ·
                    refine ⟨1406133567255281681631169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7499379025361502302032901 1406133567255281681631169)
                    ·
                      rfl

theorem cell22_4107653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_4107653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107653 prefixEnd_4107653 := by exact prefixLift 4107653
  have htrace : WordTrace (prefixWord ++ tailWord_4107653) baseStart_4107653 baseEnd_4107653 := by
    simpa [prefixWord, tailWord_4107653, baseEnd_4107653] using wordTrace_append hprefix tailTrace_4107653
  have hstable : (prefixWord ++ tailWord_4107653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107653).length < 2 ^ (prefixWord ++ tailWord_4107653).sum := by decide
  have hdescent : baseEnd_4107653 < baseStart_4107653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107698 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_4107698 : Nat := 118140960795 + 4107698 * 2 ^ 59
def prefixEnd_4107698 : Nat := 4983230072969 + 3 ^ 40 * 4107698 * 2
def baseEnd_4107698 : Nat := 1406148971674916564256031

theorem tailTrace_4107698 : CollatzResearch.WordTrace tailWord_4107698 prefixEnd_4107698 1406148971674916564256031 := by
  unfold tailWord_4107698
  simp only [CollatzResearch.WordTrace]
  refine ⟨37455013568129789952784937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99880036181679439874093165 37455013568129789952784937)
  ·
    refine ⟨28091260176097342464588703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37455013568129789952784937 28091260176097342464588703)
    ·
      refine ⟨42136890264146013696883055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28091260176097342464588703 42136890264146013696883055)
      ·
        refine ⟨63205335396219020545324583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42136890264146013696883055 63205335396219020545324583)
        ·
          refine ⟨94808003094328530817986875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63205335396219020545324583 94808003094328530817986875)
          ·
            refine ⟨142212004641492796226980313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94808003094328530817986875 142212004641492796226980313)
            ·
              refine ⟨106659003481119597170235235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142212004641492796226980313 106659003481119597170235235)
              ·
                refine ⟨159988505221679395755352853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106659003481119597170235235 159988505221679395755352853)
                ·
                  refine ⟨7499461182266221676032165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159988505221679395755352853 7499461182266221676032165)
                  ·
                    refine ⟨1406148971674916564256031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7499461182266221676032165 1406148971674916564256031)
                    ·
                      rfl

theorem cell22_4107698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_4107698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107698 prefixEnd_4107698 := by exact prefixLift 4107698
  have htrace : WordTrace (prefixWord ++ tailWord_4107698) baseStart_4107698 baseEnd_4107698 := by
    simpa [prefixWord, tailWord_4107698, baseEnd_4107698] using wordTrace_append hprefix tailTrace_4107698
  have hstable : (prefixWord ++ tailWord_4107698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107698).length < 2 ^ (prefixWord ++ tailWord_4107698).sum := by decide
  have hdescent : baseEnd_4107698 < baseStart_4107698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107732 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_4107732 : Nat := 118140960795 + 4107732 * 2 ^ 59
def prefixEnd_4107732 : Nat := 4983230072969 + 3 ^ 40 * 4107732 * 2
def baseEnd_4107732 : Nat := 1406160610569751808905927

theorem tailTrace_4107732 : CollatzResearch.WordTrace tailWord_4107732 prefixEnd_4107732 1406160610569751808905927 := by
  unfold tailWord_4107732
  simp only [CollatzResearch.WordTrace]
  refine ⟨74910647177197991808938725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99880862902930655745251633 74910647177197991808938725)
  ·
    refine ⟨14045746345724623464176011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74910647177197991808938725 14045746345724623464176011)
    ·
      refine ⟨21068619518586935196264017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14045746345724623464176011 21068619518586935196264017)
      ·
        refine ⟨15801464638940201397198013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21068619518586935196264017 15801464638940201397198013)
        ·
          refine ⟨5925549239602575523949255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15801464638940201397198013 5925549239602575523949255)
          ·
            refine ⟨8888323859403863285923883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5925549239602575523949255 8888323859403863285923883)
            ·
              refine ⟨13332485789105794928885825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8888323859403863285923883 13332485789105794928885825)
              ·
                refine ⟨9999364341829346196664369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13332485789105794928885825 9999364341829346196664369)
                ·
                  refine ⟨7499523256372009647498277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9999364341829346196664369 7499523256372009647498277)
                  ·
                    refine ⟨1406160610569751808905927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7499523256372009647498277 1406160610569751808905927)
                    ·
                      rfl

theorem cell22_4107732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_4107732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107732 prefixEnd_4107732 := by exact prefixLift 4107732
  have htrace : WordTrace (prefixWord ++ tailWord_4107732) baseStart_4107732 baseEnd_4107732 := by
    simpa [prefixWord, tailWord_4107732, baseEnd_4107732] using wordTrace_append hprefix tailTrace_4107732
  have hstable : (prefixWord ++ tailWord_4107732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107732).length < 2 ^ (prefixWord ++ tailWord_4107732).sum := by decide
  have hdescent : baseEnd_4107732 < baseStart_4107732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107743 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 2, 6]
def baseStart_4107743 : Nat := 118140960795 + 4107743 * 2 ^ 59
def prefixEnd_4107743 : Nat := 4983230072969 + 3 ^ 40 * 4107743 * 2
def baseEnd_4107743 : Nat := 1406164376094551446880893

theorem tailTrace_4107743 : CollatzResearch.WordTrace tailWord_4107743 prefixEnd_4107743 1406164376094551446880893 := by
  unfold tailWord_4107743
  simp only [CollatzResearch.WordTrace]
  refine ⟨149821695557356132496527883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99881130371570754997685255 149821695557356132496527883)
  ·
    refine ⟨224732543336034198744791825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149821695557356132496527883 224732543336034198744791825)
    ·
      refine ⟨168549407502025649058593869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224732543336034198744791825 168549407502025649058593869)
      ·
        refine ⟨63206027813259618396972701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168549407502025649058593869 63206027813259618396972701)
        ·
          refine ⟨23702260429972356898864763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63206027813259618396972701 23702260429972356898864763)
          ·
            refine ⟨35553390644958535348297145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23702260429972356898864763 35553390644958535348297145)
            ·
              refine ⟨26665042983718901511222859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35553390644958535348297145 26665042983718901511222859)
              ·
                refine ⟨39997564475578352266834289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26665042983718901511222859 39997564475578352266834289)
                ·
                  refine ⟨29998173356683764200125717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39997564475578352266834289 29998173356683764200125717)
                  ·
                    refine ⟨1406164376094551446880893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29998173356683764200125717 1406164376094551446880893)
                    ·
                      rfl

theorem cell22_4107743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_4107743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107743 prefixEnd_4107743 := by exact prefixLift 4107743
  have htrace : WordTrace (prefixWord ++ tailWord_4107743) baseStart_4107743 baseEnd_4107743 := by
    simpa [prefixWord, tailWord_4107743, baseEnd_4107743] using wordTrace_append hprefix tailTrace_4107743
  have hstable : (prefixWord ++ tailWord_4107743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107743).length < 2 ^ (prefixWord ++ tailWord_4107743).sum := by decide
  have hdescent : baseEnd_4107743 < baseStart_4107743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107805 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_4107805 : Nat := 118140960795 + 4107805 * 2 ^ 59
def prefixEnd_4107805 : Nat := 4983230072969 + 3 ^ 40 * 4107805 * 2
def baseEnd_4107805 : Nat := 1406185599961603951830703

theorem tailTrace_4107805 : CollatzResearch.WordTrace tailWord_4107805 prefixEnd_4107805 1406185599961603951830703 := by
  unfold tailWord_4107805
  simp only [CollatzResearch.WordTrace]
  refine ⟨149823956883131517085284869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99882637922087678056856579 149823956883131517085284869)
  ·
    refine ⟨28091991915587159453490913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149823956883131517085284869 28091991915587159453490913)
    ·
      refine ⟨21068993936690369590118185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28091991915587159453490913 21068993936690369590118185)
      ·
        refine ⟨15801745452517777192588639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21068993936690369590118185 15801745452517777192588639)
        ·
          refine ⟨23702618178776665788882959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15801745452517777192588639 23702618178776665788882959)
          ·
            refine ⟨35553927268164998683324439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23702618178776665788882959 35553927268164998683324439)
            ·
              refine ⟨53330890902247498024986659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35553927268164998683324439 53330890902247498024986659)
              ·
                refine ⟨79996336353371247037479989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53330890902247498024986659 79996336353371247037479989)
                ·
                  refine ⟨7499656533128554409763749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79996336353371247037479989 7499656533128554409763749)
                  ·
                    refine ⟨1406185599961603951830703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7499656533128554409763749 1406185599961603951830703)
                    ·
                      rfl

theorem cell22_4107805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_4107805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107805 prefixEnd_4107805 := by exact prefixLift 4107805
  have htrace : WordTrace (prefixWord ++ tailWord_4107805) baseStart_4107805 baseEnd_4107805 := by
    simpa [prefixWord, tailWord_4107805, baseEnd_4107805] using wordTrace_append hprefix tailTrace_4107805
  have hstable : (prefixWord ++ tailWord_4107805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107805).length < 2 ^ (prefixWord ++ tailWord_4107805).sum := by decide
  have hdescent : baseEnd_4107805 < baseStart_4107805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107822 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_4107822 : Nat := 118140960795 + 4107822 * 2 ^ 59
def prefixEnd_4107822 : Nat := 4983230072969 + 3 ^ 40 * 4107822 * 2
def baseEnd_4107822 : Nat := 1406191419409021574155651

theorem tailTrace_4107822 : CollatzResearch.WordTrace tailWord_4107822 prefixEnd_4107822 1406191419409021574155651 := by
  unfold tailWord_4107822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18728072115508741123581715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99883051282713285992435813 18728072115508741123581715)
  ·
    refine ⟨28092108173263111685372573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18728072115508741123581715 28092108173263111685372573)
    ·
      refine ⟨10534540564973666882014715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28092108173263111685372573 10534540564973666882014715)
      ·
        refine ⟨15801810847460500323022073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10534540564973666882014715 15801810847460500323022073)
        ·
          refine ⟨11851358135595375242266555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15801810847460500323022073 11851358135595375242266555)
          ·
            refine ⟨17777037203393062863399833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11851358135595375242266555 17777037203393062863399833)
            ·
              refine ⟨13332777902544797147549875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17777037203393062863399833 13332777902544797147549875)
              ·
                refine ⟨19999166853817195721324813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13332777902544797147549875 19999166853817195721324813)
                ·
                  refine ⟨7499687570181448395496805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19999166853817195721324813 7499687570181448395496805)
                  ·
                    refine ⟨1406191419409021574155651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7499687570181448395496805 1406191419409021574155651)
                    ·
                      rfl

theorem cell22_4107822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_4107822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107822 prefixEnd_4107822 := by exact prefixLift 4107822
  have htrace : WordTrace (prefixWord ++ tailWord_4107822) baseStart_4107822 baseEnd_4107822 := by
    simpa [prefixWord, tailWord_4107822, baseEnd_4107822] using wordTrace_append hprefix tailTrace_4107822
  have hstable : (prefixWord ++ tailWord_4107822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107822).length < 2 ^ (prefixWord ++ tailWord_4107822).sum := by decide
  have hdescent : baseEnd_4107822 < baseStart_4107822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4107839 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 1, 4]
def baseStart_4107839 : Nat := 118140960795 + 4107839 * 2 ^ 59
def prefixEnd_4107839 : Nat := 4983230072969 + 3 ^ 40 * 4107839 * 2
def baseEnd_4107839 : Nat := 1406197238856439196480599

theorem tailTrace_4107839 : CollatzResearch.WordTrace tailWord_4107839 prefixEnd_4107839 1406197238856439196480599 := by
  unfold tailWord_4107839
  simp only [CollatzResearch.WordTrace]
  refine ⟨149825196965008340892022571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99883464643338893928015047 149825196965008340892022571)
  ·
    refine ⟨224737795447512511338033857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149825196965008340892022571 224737795447512511338033857)
    ·
      refine ⟨168553346585634383503525393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224737795447512511338033857 168553346585634383503525393)
      ·
        refine ⟨126415009939225787627644045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168553346585634383503525393 126415009939225787627644045)
        ·
          refine ⟨47405628727209670360366517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126415009939225787627644045 47405628727209670360366517)
          ·
            refine ⟨4444277693175906596284361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47405628727209670360366517 4444277693175906596284361)
            ·
              refine ⟨3333208269881929947213271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4444277693175906596284361 3333208269881929947213271)
              ·
                refine ⟨4999812404822894920819907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3333208269881929947213271 4999812404822894920819907)
                ·
                  refine ⟨7499718607234342381229861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4999812404822894920819907 7499718607234342381229861)
                  ·
                    refine ⟨1406197238856439196480599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7499718607234342381229861 1406197238856439196480599)
                    ·
                      rfl

theorem cell22_4107839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 1, 4].length) (baseStart_4107839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4107839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4107839 prefixEnd_4107839 := by exact prefixLift 4107839
  have htrace : WordTrace (prefixWord ++ tailWord_4107839) baseStart_4107839 baseEnd_4107839 := by
    simpa [prefixWord, tailWord_4107839, baseEnd_4107839] using wordTrace_append hprefix tailTrace_4107839
  have hstable : (prefixWord ++ tailWord_4107839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4107839).length < 2 ^ (prefixWord ++ tailWord_4107839).sum := by decide
  have hdescent : baseEnd_4107839 < baseStart_4107839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4107839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
