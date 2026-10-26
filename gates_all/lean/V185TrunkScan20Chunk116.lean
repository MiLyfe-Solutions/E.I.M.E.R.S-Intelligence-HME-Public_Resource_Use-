import V185TrunkScan20Chunk115

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_705678 : List Nat := [4, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_705678 : Nat := 118140960795 + 705678 * 2 ^ 59
def prefixEnd_705678 : Nat := 4983230072969 + 3 ^ 40 * 705678 * 2
def baseEnd_705678 : Nat := 322090667825418013581913

theorem tailTrace_705678 : CollatzResearch.WordTrace tailWord_705678 prefixEnd_705678 322090667825418013581913 := by
  unfold tailWord_705678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3217273892182075131550711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17158794091637734034937125 3217273892182075131550711)
  ·
    refine ⟨4825910838273112697326067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3217273892182075131550711 4825910838273112697326067)
    ·
      refine ⟨7238866257409669045989101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4825910838273112697326067 7238866257409669045989101)
      ·
        refine ⟨2714574846528625892245913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7238866257409669045989101 2714574846528625892245913)
        ·
          refine ⟨2035931134896469419184435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2714574846528625892245913 2035931134896469419184435)
          ·
            refine ⟨3053896702344704128776653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035931134896469419184435 3053896702344704128776653)
            ·
              refine ⟨1145211263379264048291245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3053896702344704128776653 1145211263379264048291245)
              ·
                refine ⟨429454223767224018109217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1145211263379264048291245 429454223767224018109217)
                ·
                  refine ⟨322090667825418013581913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429454223767224018109217 322090667825418013581913)
                  ·
                    rfl

theorem cell20_705678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_705678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705678 prefixEnd_705678 := by exact prefixLift 705678
  have htrace : WordTrace (prefixWord ++ tailWord_705678) baseStart_705678 baseEnd_705678 := by
    simpa [prefixWord, tailWord_705678, baseEnd_705678] using wordTrace_append hprefix tailTrace_705678
  have hstable : (prefixWord ++ tailWord_705678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705678).length < 2 ^ (prefixWord ++ tailWord_705678).sum := by decide
  have hdescent : baseEnd_705678 < baseStart_705678 := by decide
  rcases family_descends (prefixWord ++ tailWord_705678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705695 : List Nat := [1, 1, 2, 6, 2, 1, 3, 2, 2]
def baseStart_705695 : Nat := 118140960795 + 705695 * 2 ^ 59
def prefixEnd_705695 : Nat := 4983230072969 + 3 ^ 40 * 705695 * 2
def baseEnd_705695 : Nat := 322098427088641510015177

theorem tailTrace_705695 : CollatzResearch.WordTrace tailWord_705695 prefixEnd_705695 322098427088641510015177 := by
  unfold tailWord_705695
  simp only [CollatzResearch.WordTrace]
  refine ⟨25738811178395012955774539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17159207452263341970516359 25738811178395012955774539)
  ·
    refine ⟨38608216767592519433661809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25738811178395012955774539 38608216767592519433661809)
    ·
      refine ⟨28956162575694389575246357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38608216767592519433661809 28956162575694389575246357)
      ·
        refine ⟨1357320120735674511339673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28956162575694389575246357 1357320120735674511339673)
        ·
          refine ⟨1017990090551755883504755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1357320120735674511339673 1017990090551755883504755)
          ·
            refine ⟨1526985135827633825257133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017990090551755883504755 1526985135827633825257133)
            ·
              refine ⟨572619425935362684471425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1526985135827633825257133 572619425935362684471425)
              ·
                refine ⟨429464569451522013353569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572619425935362684471425 429464569451522013353569)
                ·
                  refine ⟨322098427088641510015177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429464569451522013353569 322098427088641510015177)
                  ·
                    rfl

theorem cell20_705695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 2].length) (baseStart_705695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705695 prefixEnd_705695 := by exact prefixLift 705695
  have htrace : WordTrace (prefixWord ++ tailWord_705695) baseStart_705695 baseEnd_705695 := by
    simpa [prefixWord, tailWord_705695, baseEnd_705695] using wordTrace_append hprefix tailTrace_705695
  have hstable : (prefixWord ++ tailWord_705695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705695).length < 2 ^ (prefixWord ++ tailWord_705695).sum := by decide
  have hdescent : baseEnd_705695 < baseStart_705695 := by decide
  rcases family_descends (prefixWord ++ tailWord_705695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705696 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_705696 : Nat := 118140960795 + 705696 * 2 ^ 59
def prefixEnd_705696 : Nat := 4983230072969 + 3 ^ 40 * 705696 * 2
def baseEnd_705696 : Nat := 322098883515889950981839

theorem tailTrace_705696 : CollatzResearch.WordTrace tailWord_705696 prefixEnd_705696 322098883515889950981839 := by
  unfold tailWord_705696
  simp only [CollatzResearch.WordTrace]
  refine ⟨12869423825695695063280471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17159231767594260084373961 12869423825695695063280471)
  ·
    refine ⟨19304135738543542594920707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12869423825695695063280471 19304135738543542594920707)
    ·
      refine ⟨28956203607815313892381061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19304135738543542594920707 28956203607815313892381061)
      ·
        refine ⟨5429288176465371354821449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28956203607815313892381061 5429288176465371354821449)
        ·
          refine ⟨4071966132349028516116087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5429288176465371354821449 4071966132349028516116087)
          ·
            refine ⟨6107949198523542774174131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4071966132349028516116087 6107949198523542774174131)
            ·
              refine ⟨9161923797785314161261197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6107949198523542774174131 9161923797785314161261197)
              ·
                refine ⟨3435721424169492810472949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9161923797785314161261197 3435721424169492810472949)
                ·
                  refine ⟨322098883515889950981839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3435721424169492810472949 322098883515889950981839)
                  ·
                    rfl

theorem cell20_705696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_705696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705696 prefixEnd_705696 := by exact prefixLift 705696
  have htrace : WordTrace (prefixWord ++ tailWord_705696) baseStart_705696 baseEnd_705696 := by
    simpa [prefixWord, tailWord_705696, baseEnd_705696] using wordTrace_append hprefix tailTrace_705696
  have hstable : (prefixWord ++ tailWord_705696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705696).length < 2 ^ (prefixWord ++ tailWord_705696).sum := by decide
  have hdescent : baseEnd_705696 < baseStart_705696 := by decide
  rcases family_descends (prefixWord ++ tailWord_705696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705706 : List Nat := [3, 1, 5, 1, 1, 1, 1, 7]
def baseStart_705706 : Nat := 118140960795 + 705706 * 2 ^ 59
def prefixEnd_705706 : Nat := 4983230072969 + 3 ^ 40 * 705706 * 2
def baseEnd_705706 : Nat := 107367815929458120216155

theorem tailTrace_705706 : CollatzResearch.WordTrace tailWord_705706 prefixEnd_705706 107367815929458120216155 := by
  unfold tailWord_705706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6434803095338790458606243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17159474920903441222949981 6434803095338790458606243)
  ·
    refine ⟨9652204643008185687909365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6434803095338790458606243 9652204643008185687909365)
    ·
      refine ⟨904894185282017408241503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9652204643008185687909365 904894185282017408241503)
      ·
        refine ⟨1357341277923026112362255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904894185282017408241503 1357341277923026112362255)
        ·
          refine ⟨2036011916884539168543383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357341277923026112362255 2036011916884539168543383)
          ·
            refine ⟨3054017875326808752815075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036011916884539168543383 3054017875326808752815075)
            ·
              refine ⟨4581026812990213129222613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3054017875326808752815075 4581026812990213129222613)
              ·
                refine ⟨107367815929458120216155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4581026812990213129222613 107367815929458120216155)
                ·
                  rfl

theorem cell20_705706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_705706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705706 prefixEnd_705706 := by exact prefixLift 705706
  have htrace : WordTrace (prefixWord ++ tailWord_705706) baseStart_705706 baseEnd_705706 := by
    simpa [prefixWord, tailWord_705706, baseEnd_705706] using wordTrace_append hprefix tailTrace_705706
  have hstable : (prefixWord ++ tailWord_705706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705706).length < 2 ^ (prefixWord ++ tailWord_705706).sum := by decide
  have hdescent : baseEnd_705706 < baseStart_705706 := by decide
  rcases family_descends (prefixWord ++ tailWord_705706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705779 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 6]
def baseStart_705779 : Nat := 118140960795 + 705779 * 2 ^ 59
def prefixEnd_705779 : Nat := 4983230072969 + 3 ^ 40 * 705779 * 2
def baseEnd_705779 : Nat := 322136766977510551214833

theorem tailTrace_705779 : CollatzResearch.WordTrace tailWord_705779 prefixEnd_705779 322136766977510551214833 := by
  unfold tailWord_705779
  simp only [CollatzResearch.WordTrace]
  refine ⟨25741874910090695301832391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17161249940060463534554927 25741874910090695301832391)
  ·
    refine ⟨38612812365136042952748587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25741874910090695301832391 38612812365136042952748587)
    ·
      refine ⟨57919218547704064429122881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38612812365136042952748587 57919218547704064429122881)
      ·
        refine ⟨43439413910778048321842161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57919218547704064429122881 43439413910778048321842161)
        ·
          refine ⟨32579560433083536241381621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43439413910778048321842161 32579560433083536241381621)
          ·
            refine ⟨3054333790601581522629527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32579560433083536241381621 3054333790601581522629527)
            ·
              refine ⟨4581500685902372283944291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3054333790601581522629527 4581500685902372283944291)
              ·
                refine ⟨6872251028853558425916437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4581500685902372283944291 6872251028853558425916437)
                ·
                  refine ⟨322136766977510551214833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6872251028853558425916437 322136766977510551214833)
                  ·
                    rfl

theorem cell20_705779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_705779 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705779 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705779 prefixEnd_705779 := by exact prefixLift 705779
  have htrace : WordTrace (prefixWord ++ tailWord_705779) baseStart_705779 baseEnd_705779 := by
    simpa [prefixWord, tailWord_705779, baseEnd_705779] using wordTrace_append hprefix tailTrace_705779
  have hstable : (prefixWord ++ tailWord_705779).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705779).length < 2 ^ (prefixWord ++ tailWord_705779).sum := by decide
  have hdescent : baseEnd_705779 < baseStart_705779 := by decide
  rcases family_descends (prefixWord ++ tailWord_705779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705806 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_705806 : Nat := 118140960795 + 705806 * 2 ^ 59
def prefixEnd_705806 : Nat := 4983230072969 + 3 ^ 40 * 705806 * 2
def baseEnd_705806 : Nat := 322149090513218457314723

theorem tailTrace_705806 : CollatzResearch.WordTrace tailWord_705806 prefixEnd_705806 322149090513218457314723 := by
  unfold tailWord_705806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3217857460124109864133159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17161906453995252608710181 3217857460124109864133159)
  ·
    refine ⟨4826786190186164796199739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3217857460124109864133159 4826786190186164796199739)
    ·
      refine ⟨7240179285279247194299609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4826786190186164796199739 7240179285279247194299609)
      ·
        refine ⟨5430134463959435395724707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7240179285279247194299609 5430134463959435395724707)
        ·
          refine ⟨8145201695939153093587061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5430134463959435395724707 8145201695939153093587061)
          ·
            refine ⟨763612658994295602523787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8145201695939153093587061 763612658994295602523787)
            ·
              refine ⟨1145418988491443403785681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 763612658994295602523787 1145418988491443403785681)
              ·
                refine ⟨859064241368582552839261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145418988491443403785681 859064241368582552839261)
                ·
                  refine ⟨322149090513218457314723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859064241368582552839261 322149090513218457314723)
                  ·
                    rfl

theorem cell20_705806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_705806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705806 prefixEnd_705806 := by exact prefixLift 705806
  have htrace : WordTrace (prefixWord ++ tailWord_705806) baseStart_705806 baseEnd_705806 := by
    simpa [prefixWord, tailWord_705806, baseEnd_705806] using wordTrace_append hprefix tailTrace_705806
  have hstable : (prefixWord ++ tailWord_705806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705806).length < 2 ^ (prefixWord ++ tailWord_705806).sum := by decide
  have hdescent : baseEnd_705806 < baseStart_705806 := by decide
  rcases family_descends (prefixWord ++ tailWord_705806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705837 : List Nat := [1, 5, 3, 1, 1, 1, 4, 4]
def baseStart_705837 : Nat := 118140960795 + 705837 * 2 ^ 59
def prefixEnd_705837 : Nat := 4983230072969 + 3 ^ 40 * 705837 * 2
def baseEnd_705837 : Nat := 107387746585973375760421

theorem tailTrace_705837 : CollatzResearch.WordTrace tailWord_705837 prefixEnd_705837 107387746585973375760421 := by
  unfold tailWord_705837
  simp only [CollatzResearch.WordTrace]
  refine ⟨25743990343880571207443765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17162660229253714138295843 25743990343880571207443765)
  ·
    refine ⟨2413499094738803550697853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25743990343880571207443765 2413499094738803550697853)
    ·
      refine ⟨905062160527051331511695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2413499094738803550697853 905062160527051331511695)
      ·
        refine ⟨1357593240790576997267543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905062160527051331511695 1357593240790576997267543)
        ·
          refine ⟨2036389861185865495901315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357593240790576997267543 2036389861185865495901315)
          ·
            refine ⟨3054584791778798243851973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2036389861185865495901315 3054584791778798243851973)
            ·
              refine ⟨572734648458524670722245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3054584791778798243851973 572734648458524670722245)
              ·
                refine ⟨107387746585973375760421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 572734648458524670722245 107387746585973375760421)
                ·
                  rfl

theorem cell20_705837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 4].length) (baseStart_705837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705837 prefixEnd_705837 := by exact prefixLift 705837
  have htrace : WordTrace (prefixWord ++ tailWord_705837) baseStart_705837 baseEnd_705837 := by
    simpa [prefixWord, tailWord_705837, baseEnd_705837] using wordTrace_append hprefix tailTrace_705837
  have hstable : (prefixWord ++ tailWord_705837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705837).length < 2 ^ (prefixWord ++ tailWord_705837).sum := by decide
  have hdescent : baseEnd_705837 < baseStart_705837 := by decide
  rcases family_descends (prefixWord ++ tailWord_705837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705841 : List Nat := [1, 2, 2, 3, 3, 2, 1, 6]
def baseStart_705841 : Nat := 118140960795 + 705841 * 2 ^ 59
def prefixEnd_705841 : Nat := 4983230072969 + 3 ^ 40 * 705841 * 2
def baseEnd_705841 : Nat := 107388355155637963715971

theorem tailTrace_705841 : CollatzResearch.WordTrace tailWord_705841 prefixEnd_705841 107388355155637963715971 := by
  unfold tailWord_705841
  simp only [CollatzResearch.WordTrace]
  refine ⟨25744136235866079890589377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17162757490577386593726251 25744136235866079890589377)
  ·
    refine ⟨19308102176899559917942033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25744136235866079890589377 19308102176899559917942033)
    ·
      refine ⟨14481076632674669938456525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19308102176899559917942033 14481076632674669938456525)
      ·
        refine ⟨5430403737253001226921197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14481076632674669938456525 5430403737253001226921197)
        ·
          refine ⟨2036401401469875460095449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5430403737253001226921197 2036401401469875460095449)
          ·
            refine ⟨1527301051102406595071587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2036401401469875460095449 1527301051102406595071587)
            ·
              refine ⟨2290951576653609892607381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1527301051102406595071587 2290951576653609892607381)
              ·
                refine ⟨107388355155637963715971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2290951576653609892607381 107388355155637963715971)
                ·
                  rfl

theorem cell20_705841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_705841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705841 prefixEnd_705841 := by exact prefixLift 705841
  have htrace : WordTrace (prefixWord ++ tailWord_705841) baseStart_705841 baseEnd_705841 := by
    simpa [prefixWord, tailWord_705841, baseEnd_705841] using wordTrace_append hprefix tailTrace_705841
  have hstable : (prefixWord ++ tailWord_705841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705841).length < 2 ^ (prefixWord ++ tailWord_705841).sum := by decide
  have hdescent : baseEnd_705841 < baseStart_705841 := by decide
  rcases family_descends (prefixWord ++ tailWord_705841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705868 : List Nat := [2, 2, 1, 3, 2, 3, 3, 2, 2]
def baseStart_705868 : Nat := 118140960795 + 705868 * 2 ^ 59
def prefixEnd_705868 : Nat := 4983230072969 + 3 ^ 40 * 705868 * 2
def baseEnd_705868 : Nat := 322177389002621797247803

theorem tailTrace_705868 : CollatzResearch.WordTrace tailWord_705868 prefixEnd_705868 322177389002621797247803 := by
  unfold tailWord_705868
  simp only [CollatzResearch.WordTrace]
  refine ⟨12872560503384131750911129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17163414004512175667881505 12872560503384131750911129)
  ·
    refine ⟨9654420377538098813183347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12872560503384131750911129 9654420377538098813183347)
    ·
      refine ⟨14481630566307148219775021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9654420377538098813183347 14481630566307148219775021)
      ·
        refine ⟨5430611462365180582415633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14481630566307148219775021 5430611462365180582415633)
        ·
          refine ⟨4072958596773885436811725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5430611462365180582415633 4072958596773885436811725)
          ·
            refine ⟨1527359473790207038804397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4072958596773885436811725 1527359473790207038804397)
            ·
              refine ⟨572759802671327639551649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1527359473790207038804397 572759802671327639551649)
              ·
                refine ⟨429569852003495729663737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572759802671327639551649 429569852003495729663737)
                ·
                  refine ⟨322177389002621797247803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429569852003495729663737 322177389002621797247803)
                  ·
                    rfl

theorem cell20_705868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_705868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705868 prefixEnd_705868 := by exact prefixLift 705868
  have htrace : WordTrace (prefixWord ++ tailWord_705868) baseStart_705868 baseEnd_705868 := by
    simpa [prefixWord, tailWord_705868, baseEnd_705868] using wordTrace_append hprefix tailTrace_705868
  have hstable : (prefixWord ++ tailWord_705868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705868).length < 2 ^ (prefixWord ++ tailWord_705868).sum := by decide
  have hdescent : baseEnd_705868 < baseStart_705868 := by decide
  rcases family_descends (prefixWord ++ tailWord_705868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705879 : List Nat := [1, 1, 3, 2, 3, 3, 2, 5]
def baseStart_705879 : Nat := 118140960795 + 705879 * 2 ^ 59
def prefixEnd_705879 : Nat := 4983230072969 + 3 ^ 40 * 705879 * 2
def baseEnd_705879 : Nat := 107394136567451549293697

theorem tailTrace_705879 : CollatzResearch.WordTrace tailWord_705879 prefixEnd_705879 107394136567451549293697 := by
  unfold tailWord_705879
  simp only [CollatzResearch.WordTrace]
  refine ⟨25745522209728412380472691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17163681473152274920315127 25745522209728412380472691)
  ·
    refine ⟨38618283314592618570709037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25745522209728412380472691 38618283314592618570709037)
    ·
      refine ⟨14481856242972231964015889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38618283314592618570709037 14481856242972231964015889)
      ·
        refine ⟨10861392182229173973011917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14481856242972231964015889 10861392182229173973011917)
        ·
          refine ⟨4073022068335940239879469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10861392182229173973011917 4073022068335940239879469)
          ·
            refine ⟨1527383275625977589954801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4073022068335940239879469 1527383275625977589954801)
            ·
              refine ⟨1145537456719483192466101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1527383275625977589954801 1145537456719483192466101)
              ·
                refine ⟨107394136567451549293697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1145537456719483192466101 107394136567451549293697)
                ·
                  rfl

theorem cell20_705879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_705879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705879 prefixEnd_705879 := by exact prefixLift 705879
  have htrace : WordTrace (prefixWord ++ tailWord_705879) baseStart_705879 baseEnd_705879 := by
    simpa [prefixWord, tailWord_705879, baseEnd_705879] using wordTrace_append hprefix tailTrace_705879
  have hstable : (prefixWord ++ tailWord_705879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705879).length < 2 ^ (prefixWord ++ tailWord_705879).sum := by decide
  have hdescent : baseEnd_705879 < baseStart_705879 := by decide
  rcases family_descends (prefixWord ++ tailWord_705879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705893 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_705893 : Nat := 118140960795 + 705893 * 2 ^ 59
def prefixEnd_705893 : Nat := 4983230072969 + 3 ^ 40 * 705893 * 2
def baseEnd_705893 : Nat := 322188799683832821414367

theorem tailTrace_705893 : CollatzResearch.WordTrace tailWord_705893 prefixEnd_705893 322188799683832821414367 := by
  unfold tailWord_705893
  simp only [CollatzResearch.WordTrace]
  refine ⟨25746032831677692771482333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17164021887785128514321555 25746032831677692771482333)
  ·
    refine ⟨9654762311879134789305875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25746032831677692771482333 9654762311879134789305875)
    ·
      refine ⟨14482143467818702183958813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9654762311879134789305875 14482143467818702183958813)
      ·
        refine ⟨5430803800432013318984555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14482143467818702183958813 5430803800432013318984555)
        ·
          refine ⟨8146205700648019978476833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5430803800432013318984555 8146205700648019978476833)
          ·
            refine ⟨6109654275486014983857625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8146205700648019978476833 6109654275486014983857625)
            ·
              refine ⟨4582240706614511237893219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6109654275486014983857625 4582240706614511237893219)
              ·
                refine ⟨6873361059921766856839829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4582240706614511237893219 6873361059921766856839829)
                ·
                  refine ⟨322188799683832821414367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6873361059921766856839829 322188799683832821414367)
                  ·
                    rfl

theorem cell20_705893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_705893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705893 prefixEnd_705893 := by exact prefixLift 705893
  have htrace : WordTrace (prefixWord ++ tailWord_705893) baseStart_705893 baseEnd_705893 := by
    simpa [prefixWord, tailWord_705893, baseEnd_705893] using wordTrace_append hprefix tailTrace_705893
  have hstable : (prefixWord ++ tailWord_705893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705893).length < 2 ^ (prefixWord ++ tailWord_705893).sum := by decide
  have hdescent : baseEnd_705893 < baseStart_705893 := by decide
  rcases family_descends (prefixWord ++ tailWord_705893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705927 : List Nat := [1, 1, 4, 2, 2, 3, 1, 4, 2]
def baseStart_705927 : Nat := 118140960795 + 705927 * 2 ^ 59
def prefixEnd_705927 : Nat := 4983230072969 + 3 ^ 40 * 705927 * 2
def baseEnd_705927 : Nat := 322204318210279814280895

theorem tailTrace_705927 : CollatzResearch.WordTrace tailWord_705927 prefixEnd_705927 322204318210279814280895 := by
  unfold tailWord_705927
  simp only [CollatzResearch.WordTrace]
  refine ⟨25747272913554516578220035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17164848609036344385480023 25747272913554516578220035)
  ·
    refine ⟨38620909370331774867330053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25747272913554516578220035 38620909370331774867330053)
    ·
      refine ⟨7241420506937207787624385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38620909370331774867330053 7241420506937207787624385)
      ·
        refine ⟨5431065380202905840718289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7241420506937207787624385 5431065380202905840718289)
        ·
          refine ⟨4073299035152179380538717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5431065380202905840718289 4073299035152179380538717)
          ·
            refine ⟨1527487138182067267702019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4073299035152179380538717 1527487138182067267702019)
            ·
              refine ⟨2291230707273100901553029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1527487138182067267702019 2291230707273100901553029)
              ·
                refine ⟨429605757613706419041193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2291230707273100901553029 429605757613706419041193)
                ·
                  refine ⟨322204318210279814280895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429605757613706419041193 322204318210279814280895)
                  ·
                    rfl

theorem cell20_705927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 2].length) (baseStart_705927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705927 prefixEnd_705927 := by exact prefixLift 705927
  have htrace : WordTrace (prefixWord ++ tailWord_705927) baseStart_705927 baseEnd_705927 := by
    simpa [prefixWord, tailWord_705927, baseEnd_705927] using wordTrace_append hprefix tailTrace_705927
  have hstable : (prefixWord ++ tailWord_705927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705927).length < 2 ^ (prefixWord ++ tailWord_705927).sum := by decide
  have hdescent : baseEnd_705927 < baseStart_705927 := by decide
  rcases family_descends (prefixWord ++ tailWord_705927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705931 : List Nat := [1, 1, 1, 1, 4, 3, 2, 3, 4]
def baseStart_705931 : Nat := 118140960795 + 705931 * 2 ^ 59
def prefixEnd_705931 : Nat := 4983230072969 + 3 ^ 40 * 705931 * 2
def baseEnd_705931 : Nat := 322206143919273578147545

theorem tailTrace_705931 : CollatzResearch.WordTrace tailWord_705931 prefixEnd_705931 322206143919273578147545 := by
  unfold tailWord_705931
  simp only [CollatzResearch.WordTrace]
  refine ⟨25747418805540025261365647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17164945870360016840910431 25747418805540025261365647)
  ·
    refine ⟨38621128208310037892048471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25747418805540025261365647 38621128208310037892048471)
    ·
      refine ⟨57931692312465056838072707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38621128208310037892048471 57931692312465056838072707)
      ·
        refine ⟨86897538468697585257109061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57931692312465056838072707 86897538468697585257109061)
        ·
          refine ⟨16293288462880797235707949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86897538468697585257109061 16293288462880797235707949)
          ·
            refine ⟨6109983173580298963390481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16293288462880797235707949 6109983173580298963390481)
            ·
              refine ⟨4582487380185224222542861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6109983173580298963390481 4582487380185224222542861)
              ·
                refine ⟨1718432767569459083453573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4582487380185224222542861 1718432767569459083453573)
                ·
                  refine ⟨322206143919273578147545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1718432767569459083453573 322206143919273578147545)
                  ·
                    rfl

theorem cell20_705931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_705931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705931 prefixEnd_705931 := by exact prefixLift 705931
  have htrace : WordTrace (prefixWord ++ tailWord_705931) baseStart_705931 baseEnd_705931 := by
    simpa [prefixWord, tailWord_705931, baseEnd_705931] using wordTrace_append hprefix tailTrace_705931
  have hstable : (prefixWord ++ tailWord_705931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705931).length < 2 ^ (prefixWord ++ tailWord_705931).sum := by decide
  have hdescent : baseEnd_705931 < baseStart_705931 := by decide
  rcases family_descends (prefixWord ++ tailWord_705931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705955 : List Nat := [1, 1, 1, 4, 1, 3, 5, 4]
def baseStart_705955 : Nat := 118140960795 + 705955 * 2 ^ 59
def prefixEnd_705955 : Nat := 4983230072969 + 3 ^ 40 * 705955 * 2
def baseEnd_705955 : Nat := 107405699391078720449149

theorem tailTrace_705955 : CollatzResearch.WordTrace tailWord_705955 prefixEnd_705955 107405699391078720449149 := by
  unfold tailWord_705955
  simp only [CollatzResearch.WordTrace]
  refine ⟨25748294157453077360239319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17165529438302051573492879 25748294157453077360239319)
  ·
    refine ⟨38622441236179616040358979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25748294157453077360239319 38622441236179616040358979)
    ·
      refine ⟨57933661854269424060538469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38622441236179616040358979 57933661854269424060538469)
      ·
        refine ⟨10862561597675517011350963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57933661854269424060538469 10862561597675517011350963)
        ·
          refine ⟨16293842396513275517026445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10862561597675517011350963 16293842396513275517026445)
          ·
            refine ⟨6110190898692478318884917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16293842396513275517026445 6110190898692478318884917)
            ·
              refine ⟨572830396752419842395461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6110190898692478318884917 572830396752419842395461)
              ·
                refine ⟨107405699391078720449149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 572830396752419842395461 107405699391078720449149)
                ·
                  rfl

theorem cell20_705955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 4].length) (baseStart_705955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705955 prefixEnd_705955 := by exact prefixLift 705955
  have htrace : WordTrace (prefixWord ++ tailWord_705955) baseStart_705955 baseEnd_705955 := by
    simpa [prefixWord, tailWord_705955, baseEnd_705955] using wordTrace_append hprefix tailTrace_705955
  have hstable : (prefixWord ++ tailWord_705955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705955).length < 2 ^ (prefixWord ++ tailWord_705955).sum := by decide
  have hdescent : baseEnd_705955 < baseStart_705955 := by decide
  rcases family_descends (prefixWord ++ tailWord_705955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705969 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 6]
def baseStart_705969 : Nat := 118140960795 + 705969 * 2 ^ 59
def prefixEnd_705969 : Nat := 4983230072969 + 3 ^ 40 * 705969 * 2
def baseEnd_705969 : Nat := 322223488154714334880723

theorem tailTrace_705969 : CollatzResearch.WordTrace tailWord_705969 prefixEnd_705969 322223488154714334880723 := by
  unfold tailWord_705969
  simp only [CollatzResearch.WordTrace]
  refine ⟨25748804779402357751248961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17165869852934905167499307 25748804779402357751248961)
  ·
    refine ⟨19311603584551768313436721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25748804779402357751248961 19311603584551768313436721)
    ·
      refine ⟨14483702688413826235077541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19311603584551768313436721 14483702688413826235077541)
      ·
        refine ⟨2715694254077592419077039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14483702688413826235077541 2715694254077592419077039)
        ·
          refine ⟨4073541381116388628615559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2715694254077592419077039 4073541381116388628615559)
          ·
            refine ⟨6110312071674582942923339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4073541381116388628615559 6110312071674582942923339)
            ·
              refine ⟨9165468107511874414385009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6110312071674582942923339 9165468107511874414385009)
              ·
                refine ⟨6874101080633905810788757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9165468107511874414385009 6874101080633905810788757)
                ·
                  refine ⟨322223488154714334880723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6874101080633905810788757 322223488154714334880723)
                  ·
                    rfl

theorem cell20_705969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_705969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705969 prefixEnd_705969 := by exact prefixLift 705969
  have htrace : WordTrace (prefixWord ++ tailWord_705969) baseStart_705969 baseEnd_705969 := by
    simpa [prefixWord, tailWord_705969, baseEnd_705969] using wordTrace_append hprefix tailTrace_705969
  have hstable : (prefixWord ++ tailWord_705969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705969).length < 2 ^ (prefixWord ++ tailWord_705969).sum := by decide
  have hdescent : baseEnd_705969 < baseStart_705969 := by decide
  rcases family_descends (prefixWord ++ tailWord_705969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_705996 : List Nat := [2, 2, 1, 4, 2, 2, 3, 1, 3]
def baseStart_705996 : Nat := 118140960795 + 705996 * 2 ^ 59
def prefixEnd_705996 : Nat := 4983230072969 + 3 ^ 40 * 705996 * 2
def baseEnd_705996 : Nat := 322235811690422240980613

theorem tailTrace_705996 : CollatzResearch.WordTrace tailWord_705996 prefixEnd_705996 322235811690422240980613 := by
  unfold tailWord_705996
  simp only [CollatzResearch.WordTrace]
  refine ⟨12874894775152270681240921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17166526366869694241654561 12874894775152270681240921)
  ·
    refine ⟨9656171081364203010930691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12874894775152270681240921 9656171081364203010930691)
    ·
      refine ⟨14484256622046304516396037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9656171081364203010930691 14484256622046304516396037)
      ·
        refine ⟨2715798116633682096824257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14484256622046304516396037 2715798116633682096824257)
        ·
          refine ⟨2036848587475261572618193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2715798116633682096824257 2036848587475261572618193)
          ·
            refine ⟨1527636440606446179463645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2036848587475261572618193 1527636440606446179463645)
            ·
              refine ⟨572863665227417317298867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1527636440606446179463645 572863665227417317298867)
              ·
                refine ⟨859295497841125975948301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572863665227417317298867 859295497841125975948301)
                ·
                  refine ⟨322235811690422240980613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859295497841125975948301 322235811690422240980613)
                  ·
                    rfl

theorem cell20_705996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_705996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_705996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_705996 prefixEnd_705996 := by exact prefixLift 705996
  have htrace : WordTrace (prefixWord ++ tailWord_705996) baseStart_705996 baseEnd_705996 := by
    simpa [prefixWord, tailWord_705996, baseEnd_705996] using wordTrace_append hprefix tailTrace_705996
  have hstable : (prefixWord ++ tailWord_705996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_705996).length < 2 ^ (prefixWord ++ tailWord_705996).sum := by decide
  have hdescent : baseEnd_705996 < baseStart_705996 := by decide
  rcases family_descends (prefixWord ++ tailWord_705996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706010 : List Nat := [3, 1, 1, 2, 3, 4, 2, 4]
def baseStart_706010 : Nat := 118140960795 + 706010 * 2 ^ 59
def prefixEnd_706010 : Nat := 4983230072969 + 3 ^ 40 * 706010 * 2
def baseEnd_706010 : Nat := 107414067223966804837963

theorem tailTrace_706010 : CollatzResearch.WordTrace tailWord_706010 prefixEnd_706010 107414067223966804837963 := by
  unfold tailWord_706010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6437575043063455438372871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17166866781502547835660989 6437575043063455438372871)
  ·
    refine ⟨9656362564595183157559307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6437575043063455438372871 9656362564595183157559307)
    ·
      refine ⟨14484543846892774736338961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9656362564595183157559307 14484543846892774736338961)
      ·
        refine ⟨10863407885169581052254221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14484543846892774736338961 10863407885169581052254221)
        ·
          refine ⟨4073777956938592894595333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10863407885169581052254221 4073777956938592894595333)
          ·
            refine ⟨763833366925986167736625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4073777956938592894595333 763833366925986167736625)
            ·
              refine ⟨572875025194489625802469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763833366925986167736625 572875025194489625802469)
              ·
                refine ⟨107414067223966804837963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 572875025194489625802469 107414067223966804837963)
                ·
                  rfl

theorem cell20_706010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_706010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706010 prefixEnd_706010 := by exact prefixLift 706010
  have htrace : WordTrace (prefixWord ++ tailWord_706010) baseStart_706010 baseEnd_706010 := by
    simpa [prefixWord, tailWord_706010, baseEnd_706010] using wordTrace_append hprefix tailTrace_706010
  have hstable : (prefixWord ++ tailWord_706010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706010).length < 2 ^ (prefixWord ++ tailWord_706010).sum := by decide
  have hdescent : baseEnd_706010 < baseStart_706010 := by decide
  rcases family_descends (prefixWord ++ tailWord_706010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706037 : List Nat := [1, 3, 5, 1, 1, 2, 3, 2, 2]
def baseStart_706037 : Nat := 118140960795 + 706037 * 2 ^ 59
def prefixEnd_706037 : Nat := 4983230072969 + 3 ^ 40 * 706037 * 2
def baseEnd_706037 : Nat := 322254525207608320613779

theorem tailTrace_706037 : CollatzResearch.WordTrace tailWord_706037 prefixEnd_706037 322254525207608320613779 := by
  unfold tailWord_706037
  simp only [CollatzResearch.WordTrace]
  refine ⟨25751284943156005364724365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17167523295437336909816243 25751284943156005364724365)
  ·
    refine ⟨9656731853683502011771637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25751284943156005364724365 9656731853683502011771637)
    ·
      refine ⟨905318611282828313603591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9656731853683502011771637 905318611282828313603591)
      ·
        refine ⟨1357977916924242470405387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905318611282828313603591 1357977916924242470405387)
        ·
          refine ⟨2036966875386363705608081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357977916924242470405387 2036966875386363705608081)
          ·
            refine ⟨1527725156539772779206061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2036966875386363705608081 1527725156539772779206061)
            ·
              refine ⟨572896933702414792202273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1527725156539772779206061 572896933702414792202273)
              ·
                refine ⟨429672700276811094151705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572896933702414792202273 429672700276811094151705)
                ·
                  refine ⟨322254525207608320613779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429672700276811094151705 322254525207608320613779)
                  ·
                    rfl

theorem cell20_706037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_706037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706037 prefixEnd_706037 := by exact prefixLift 706037
  have htrace : WordTrace (prefixWord ++ tailWord_706037) baseStart_706037 baseEnd_706037 := by
    simpa [prefixWord, tailWord_706037, baseEnd_706037] using wordTrace_append hprefix tailTrace_706037
  have hstable : (prefixWord ++ tailWord_706037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706037).length < 2 ^ (prefixWord ++ tailWord_706037).sum := by decide
  have hdescent : baseEnd_706037 < baseStart_706037 := by decide
  rcases family_descends (prefixWord ++ tailWord_706037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706055 : List Nat := [1, 1, 4, 3, 2, 2, 1, 3, 3]
def baseStart_706055 : Nat := 118140960795 + 706055 * 2 ^ 59
def prefixEnd_706055 : Nat := 4983230072969 + 3 ^ 40 * 706055 * 2
def baseEnd_706055 : Nat := 322262740898080258013705

theorem tailTrace_706055 : CollatzResearch.WordTrace tailWord_706055 prefixEnd_706055 322262740898080258013705 := by
  unfold tailWord_706055
  simp only [CollatzResearch.WordTrace]
  refine ⟨25751941457090794438879619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17167960971393862959253079 25751941457090794438879619)
  ·
    refine ⟨38627912185636191658319429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25751941457090794438879619 38627912185636191658319429)
    ·
      refine ⟨7242733534806785935934893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38627912185636191658319429 7242733534806785935934893)
      ·
        refine ⟨2716025075552544725975585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7242733534806785935934893 2716025075552544725975585)
        ·
          refine ⟨2037018806664408544481689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2716025075552544725975585 2037018806664408544481689)
          ·
            refine ⟨1527764104998306408361267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2037018806664408544481689 1527764104998306408361267)
            ·
              refine ⟨2291646157497459612541901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1527764104998306408361267 2291646157497459612541901)
              ·
                refine ⟨859367309061547354703213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2291646157497459612541901 859367309061547354703213)
                ·
                  refine ⟨322262740898080258013705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859367309061547354703213 322262740898080258013705)
                  ·
                    rfl

theorem cell20_706055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 3].length) (baseStart_706055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706055 prefixEnd_706055 := by exact prefixLift 706055
  have htrace : WordTrace (prefixWord ++ tailWord_706055) baseStart_706055 baseEnd_706055 := by
    simpa [prefixWord, tailWord_706055, baseEnd_706055] using wordTrace_append hprefix tailTrace_706055
  have hstable : (prefixWord ++ tailWord_706055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706055).length < 2 ^ (prefixWord ++ tailWord_706055).sum := by decide
  have hdescent : baseEnd_706055 < baseStart_706055 := by decide
  rcases family_descends (prefixWord ++ tailWord_706055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706169 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 3]
def baseStart_706169 : Nat := 118140960795 + 706169 * 2 ^ 59
def prefixEnd_706169 : Nat := 4983230072969 + 3 ^ 40 * 706169 * 2
def baseEnd_706169 : Nat := 322314773604402528213239

theorem tailTrace_706169 : CollatzResearch.WordTrace tailWord_706169 prefixEnd_706169 322314773604402528213239 := by
  unfold tailWord_706169
  simp only [CollatzResearch.WordTrace]
  refine ⟨25756099378677791908529561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17170732919118527939019707 25756099378677791908529561)
  ·
    refine ⟨19317074534008343931397171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25756099378677791908529561 19317074534008343931397171)
    ·
      refine ⟨28975611801012515897095757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19317074534008343931397171 28975611801012515897095757)
      ·
        refine ⟨10865854425379693461410909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28975611801012515897095757 10865854425379693461410909)
        ·
          refine ⟨4074695409517385048029091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10865854425379693461410909 4074695409517385048029091)
          ·
            refine ⟨6112043114276077572043637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074695409517385048029091 6112043114276077572043637)
            ·
              refine ⟨573004041963382272379091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6112043114276077572043637 573004041963382272379091)
              ·
                refine ⟨859506062945073408568637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573004041963382272379091 859506062945073408568637)
                ·
                  refine ⟨322314773604402528213239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859506062945073408568637 322314773604402528213239)
                  ·
                    rfl

theorem cell20_706169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_706169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706169 prefixEnd_706169 := by exact prefixLift 706169
  have htrace : WordTrace (prefixWord ++ tailWord_706169) baseStart_706169 baseEnd_706169 := by
    simpa [prefixWord, tailWord_706169, baseEnd_706169] using wordTrace_append hprefix tailTrace_706169
  have hstable : (prefixWord ++ tailWord_706169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706169).length < 2 ^ (prefixWord ++ tailWord_706169).sum := by decide
  have hdescent : baseEnd_706169 < baseStart_706169 := by decide
  rcases family_descends (prefixWord ++ tailWord_706169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706183 : List Nat := [1, 1, 4, 2, 1, 3, 4, 4]
def baseStart_706183 : Nat := 118140960795 + 706183 * 2 ^ 59
def prefixEnd_706183 : Nat := 4983230072969 + 3 ^ 40 * 706183 * 2
def baseEnd_706183 : Nat := 107440387861960233915505

theorem tailTrace_706183 : CollatzResearch.WordTrace tailWord_706183 prefixEnd_706183 107440387861960233915505 := by
  unfold tailWord_706183
  simp only [CollatzResearch.WordTrace]
  refine ⟨25756610000627072299539203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17171073333751381533026135 25756610000627072299539203)
  ·
    refine ⟨38634915000940608449308805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25756610000627072299539203 38634915000940608449308805)
    ·
      refine ⟨7244046562676364084245401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38634915000940608449308805 7244046562676364084245401)
      ·
        refine ⟨5433034922007273063184051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7244046562676364084245401 5433034922007273063184051)
        ·
          refine ⟨8149552383010909594776077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5433034922007273063184051 8149552383010909594776077)
          ·
            refine ⟨3056082143629091098041029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8149552383010909594776077 3056082143629091098041029)
            ·
              refine ⟨573015401930454580882693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3056082143629091098041029 573015401930454580882693)
              ·
                refine ⟨107440387861960233915505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 573015401930454580882693 107440387861960233915505)
                ·
                  rfl

theorem cell20_706183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 4].length) (baseStart_706183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706183 prefixEnd_706183 := by exact prefixLift 706183
  have htrace : WordTrace (prefixWord ++ tailWord_706183) baseStart_706183 baseEnd_706183 := by
    simpa [prefixWord, tailWord_706183, baseEnd_706183] using wordTrace_append hprefix tailTrace_706183
  have hstable : (prefixWord ++ tailWord_706183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706183).length < 2 ^ (prefixWord ++ tailWord_706183).sum := by decide
  have hdescent : baseEnd_706183 < baseStart_706183 := by decide
  rcases family_descends (prefixWord ++ tailWord_706183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706190 : List Nat := [4, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_706190 : Nat := 118140960795 + 706190 * 2 ^ 59
def prefixEnd_706190 : Nat := 4983230072969 + 3 ^ 40 * 706190 * 2
def baseEnd_706190 : Nat := 322324358576619788513153

theorem tailTrace_706190 : CollatzResearch.WordTrace tailWord_706190 prefixEnd_706190 322324358576619788513153 := by
  unfold tailWord_706190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219608163950214061880503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17171243541067808330029349 3219608163950214061880503)
  ·
    refine ⟨4829412245925321092820755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3219608163950214061880503 4829412245925321092820755)
    ·
      refine ⟨7244118368887981639231133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4829412245925321092820755 7244118368887981639231133)
      ·
        refine ⟨2716544388332993114711675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7244118368887981639231133 2716544388332993114711675)
        ·
          refine ⟨4074816582499489672067513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716544388332993114711675 4074816582499489672067513)
          ·
            refine ⟨3056112436874617254050635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4074816582499489672067513 3056112436874617254050635)
            ·
              refine ⟨4584168655311925881075953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3056112436874617254050635 4584168655311925881075953)
              ·
                refine ⟨3438126491483944410806965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4584168655311925881075953 3438126491483944410806965)
                ·
                  refine ⟨322324358576619788513153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3438126491483944410806965 322324358576619788513153)
                  ·
                    rfl

theorem cell20_706190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_706190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706190 prefixEnd_706190 := by exact prefixLift 706190
  have htrace : WordTrace (prefixWord ++ tailWord_706190) baseStart_706190 baseEnd_706190 := by
    simpa [prefixWord, tailWord_706190, baseEnd_706190] using wordTrace_append hprefix tailTrace_706190
  have hstable : (prefixWord ++ tailWord_706190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706190).length < 2 ^ (prefixWord ++ tailWord_706190).sum := by decide
  have hdescent : baseEnd_706190 < baseStart_706190 := by decide
  rcases family_descends (prefixWord ++ tailWord_706190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706210 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_706210 : Nat := 118140960795 + 706210 * 2 ^ 59
def prefixEnd_706210 : Nat := 4983230072969 + 3 ^ 40 * 706210 * 2
def baseEnd_706210 : Nat := 322333487121588607846405

theorem tailTrace_706210 : CollatzResearch.WordTrace tailWord_706210 prefixEnd_706210 322333487121588607846405 := by
  unfold tailWord_706210
  simp only [CollatzResearch.WordTrace]
  refine ⟨6439398692882313977693021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17171729847686170607181389 6439398692882313977693021)
  ·
    refine ⟨2414774509830867741634883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6439398692882313977693021 2414774509830867741634883)
    ·
      refine ⟨3622161764746301612452325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414774509830867741634883 3622161764746301612452325)
      ·
        refine ⟨679155330889931552334811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3622161764746301612452325 679155330889931552334811)
        ·
          refine ⟨1018732996334897328502217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679155330889931552334811 1018732996334897328502217)
          ·
            refine ⟨764049747251172996376663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1018732996334897328502217 764049747251172996376663)
            ·
              refine ⟨1146074620876759494564995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764049747251172996376663 1146074620876759494564995)
              ·
                refine ⟨1719111931315139241847493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1146074620876759494564995 1719111931315139241847493)
                ·
                  refine ⟨322333487121588607846405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719111931315139241847493 322333487121588607846405)
                  ·
                    rfl

theorem cell20_706210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_706210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706210 prefixEnd_706210 := by exact prefixLift 706210
  have htrace : WordTrace (prefixWord ++ tailWord_706210) baseStart_706210 baseEnd_706210 := by
    simpa [prefixWord, tailWord_706210, baseEnd_706210] using wordTrace_append hprefix tailTrace_706210
  have hstable : (prefixWord ++ tailWord_706210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706210).length < 2 ^ (prefixWord ++ tailWord_706210).sum := by decide
  have hdescent : baseEnd_706210 < baseStart_706210 := by decide
  rcases family_descends (prefixWord ++ tailWord_706210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706211 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 5]
def baseStart_706211 : Nat := 118140960795 + 706211 * 2 ^ 59
def prefixEnd_706211 : Nat := 4983230072969 + 3 ^ 40 * 706211 * 2
def baseEnd_706211 : Nat := 322333943548837048813067

theorem tailTrace_706211 : CollatzResearch.WordTrace tailWord_706211 prefixEnd_706211 322333943548837048813067 := by
  unfold tailWord_706211
  simp only [CollatzResearch.WordTrace]
  refine ⟨25757631244525633081558487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17171754163017088721038991 25757631244525633081558487)
  ·
    refine ⟨38636446866788449622337731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25757631244525633081558487 38636446866788449622337731)
    ·
      refine ⟨57954670300182674433506597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38636446866788449622337731 57954670300182674433506597)
      ·
        refine ⟨10866500681284251456282487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57954670300182674433506597 10866500681284251456282487)
        ·
          refine ⟨16299751021926377184423731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10866500681284251456282487 16299751021926377184423731)
          ·
            refine ⟨24449626532889565776635597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16299751021926377184423731 24449626532889565776635597)
            ·
              refine ⟨9168609949833587166238349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24449626532889565776635597 9168609949833587166238349)
              ·
                refine ⟨3438228731187595187339381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9168609949833587166238349 3438228731187595187339381)
                ·
                  refine ⟨322333943548837048813067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3438228731187595187339381 322333943548837048813067)
                  ·
                    rfl

theorem cell20_706211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_706211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706211 prefixEnd_706211 := by exact prefixLift 706211
  have htrace : WordTrace (prefixWord ++ tailWord_706211) baseStart_706211 baseEnd_706211 := by
    simpa [prefixWord, tailWord_706211, baseEnd_706211] using wordTrace_append hprefix tailTrace_706211
  have hstable : (prefixWord ++ tailWord_706211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706211).length < 2 ^ (prefixWord ++ tailWord_706211).sum := by decide
  have hdescent : baseEnd_706211 < baseStart_706211 := by decide
  rcases family_descends (prefixWord ++ tailWord_706211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706221 : List Nat := [1, 5, 2, 1, 1, 1, 4, 5]
def baseStart_706221 : Nat := 118140960795 + 706221 * 2 ^ 59
def prefixEnd_706221 : Nat := 4983230072969 + 3 ^ 40 * 706221 * 2
def baseEnd_706221 : Nat := 107446169273773819493231

theorem tailTrace_706221 : CollatzResearch.WordTrace tailWord_706221 prefixEnd_706221 107446169273773819493231 := by
  unfold tailWord_706221
  simp only [CollatzResearch.WordTrace]
  refine ⟨25757995974489404789422517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17171997316326269859615011 25757995974489404789422517)
  ·
    refine ⟨2414812122608381699008361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25757995974489404789422517 2414812122608381699008361)
    ·
      refine ⟨1811109091956286274256271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2414812122608381699008361 1811109091956286274256271)
      ·
        refine ⟨2716663637934429411384407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1811109091956286274256271 2716663637934429411384407)
        ·
          refine ⟨4074995456901644117076611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716663637934429411384407 4074995456901644117076611)
          ·
            refine ⟨6112493185352466175614917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074995456901644117076611 6112493185352466175614917)
            ·
              refine ⟨1146092472253587407927797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6112493185352466175614917 1146092472253587407927797)
              ·
                refine ⟨107446169273773819493231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1146092472253587407927797 107446169273773819493231)
                ·
                  rfl

theorem cell20_706221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_706221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706221 prefixEnd_706221 := by exact prefixLift 706221
  have htrace : WordTrace (prefixWord ++ tailWord_706221) baseStart_706221 baseEnd_706221 := by
    simpa [prefixWord, tailWord_706221, baseEnd_706221] using wordTrace_append hprefix tailTrace_706221
  have hstable : (prefixWord ++ tailWord_706221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706221).length < 2 ^ (prefixWord ++ tailWord_706221).sum := by decide
  have hdescent : baseEnd_706221 < baseStart_706221 := by decide
  rcases family_descends (prefixWord ++ tailWord_706221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706256 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_706256 : Nat := 118140960795 + 706256 * 2 ^ 59
def prefixEnd_706256 : Nat := 4983230072969 + 3 ^ 40 * 706256 * 2
def baseEnd_706256 : Nat := 322354482775016892312883

theorem tailTrace_706256 : CollatzResearch.WordTrace tailWord_706256 prefixEnd_706256 322354482775016892312883 := by
  unfold tailWord_706256
  simp only [CollatzResearch.WordTrace]
  refine ⟨12879636264681302883473311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17172848352908403844631081 12879636264681302883473311)
  ·
    refine ⟨19319454397021954325209967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12879636264681302883473311 19319454397021954325209967)
    ·
      refine ⟨28979181595532931487814951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19319454397021954325209967 28979181595532931487814951)
      ·
        refine ⟨43468772393299397231722427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28979181595532931487814951 43468772393299397231722427)
        ·
          refine ⟨65203158589949095847583641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43468772393299397231722427 65203158589949095847583641)
          ·
            refine ⟨48902368942461821885687731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65203158589949095847583641 48902368942461821885687731)
            ·
              refine ⟨73353553413692732828531597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48902368942461821885687731 73353553413692732828531597)
              ·
                refine ⟨27507582530134774810699349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73353553413692732828531597 27507582530134774810699349)
                ·
                  refine ⟨322354482775016892312883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27507582530134774810699349 322354482775016892312883)
                  ·
                    rfl

theorem cell20_706256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_706256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706256 prefixEnd_706256 := by exact prefixLift 706256
  have htrace : WordTrace (prefixWord ++ tailWord_706256) baseStart_706256 baseEnd_706256 := by
    simpa [prefixWord, tailWord_706256, baseEnd_706256] using wordTrace_append hprefix tailTrace_706256
  have hstable : (prefixWord ++ tailWord_706256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706256).length < 2 ^ (prefixWord ++ tailWord_706256).sum := by decide
  have hdescent : baseEnd_706256 < baseStart_706256 := by decide
  rcases family_descends (prefixWord ++ tailWord_706256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706266 : List Nat := [3, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_706266 : Nat := 118140960795 + 706266 * 2 ^ 59
def prefixEnd_706266 : Nat := 4983230072969 + 3 ^ 40 * 706266 * 2
def baseEnd_706266 : Nat := 322359047047501301979509

theorem tailTrace_706266 : CollatzResearch.WordTrace tailWord_706266 prefixEnd_706266 322359047047501301979509 := by
  unfold tailWord_706266
  simp only [CollatzResearch.WordTrace]
  refine ⟨6439909314831594368702663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17173091506217584983207101 6439909314831594368702663)
  ·
    refine ⟨9659863972247391553053995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6439909314831594368702663 9659863972247391553053995)
    ·
      refine ⟨14489795958371087329580993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9659863972247391553053995 14489795958371087329580993)
      ·
        refine ⟨10867346968778315497185745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14489795958371087329580993 10867346968778315497185745)
        ·
          refine ⟨8150510226583736622889309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10867346968778315497185745 8150510226583736622889309)
          ·
            refine ⟨3056441334968901233583491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8150510226583736622889309 3056441334968901233583491)
            ·
              refine ⟨4584662002453351850375237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3056441334968901233583491 4584662002453351850375237)
              ·
                refine ⟨859624125460003471945357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4584662002453351850375237 859624125460003471945357)
                ·
                  refine ⟨322359047047501301979509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859624125460003471945357 322359047047501301979509)
                  ·
                    rfl

theorem cell20_706266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_706266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706266 prefixEnd_706266 := by exact prefixLift 706266
  have htrace : WordTrace (prefixWord ++ tailWord_706266) baseStart_706266 baseEnd_706266 := by
    simpa [prefixWord, tailWord_706266, baseEnd_706266] using wordTrace_append hprefix tailTrace_706266
  have hstable : (prefixWord ++ tailWord_706266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706266).length < 2 ^ (prefixWord ++ tailWord_706266).sum := by decide
  have hdescent : baseEnd_706266 < baseStart_706266 := by decide
  rcases family_descends (prefixWord ++ tailWord_706266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706328 : List Nat := [2, 1, 2, 3, 1, 1, 4, 4, 2]
def baseStart_706328 : Nat := 118140960795 + 706328 * 2 ^ 59
def prefixEnd_706328 : Nat := 4983230072969 + 3 ^ 40 * 706328 * 2
def baseEnd_706328 : Nat := 322387345536904641912589

theorem tailTrace_706328 : CollatzResearch.WordTrace tailWord_706328 prefixEnd_706328 322387345536904641912589 := by
  unfold tailWord_706328
  simp only [CollatzResearch.WordTrace]
  refine ⟨12880949292550881031783819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17174599056734508042378425 12880949292550881031783819)
  ·
    refine ⟨19321423938826321547675729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12880949292550881031783819 19321423938826321547675729)
    ·
      refine ⟨14491067954119741160756797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19321423938826321547675729 14491067954119741160756797)
      ·
        refine ⟨5434150482794902935283799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14491067954119741160756797 5434150482794902935283799)
        ·
          refine ⟨8151225724192354402925699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5434150482794902935283799 8151225724192354402925699)
          ·
            refine ⟨12226838586288531604388549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8151225724192354402925699 12226838586288531604388549)
            ·
              refine ⟨2292532234929099675822853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12226838586288531604388549 2292532234929099675822853)
              ·
                refine ⟨429849794049206189216785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2292532234929099675822853 429849794049206189216785)
                ·
                  refine ⟨322387345536904641912589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429849794049206189216785 322387345536904641912589)
                  ·
                    rfl

theorem cell20_706328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 2].length) (baseStart_706328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706328 prefixEnd_706328 := by exact prefixLift 706328
  have htrace : WordTrace (prefixWord ++ tailWord_706328) baseStart_706328 baseEnd_706328 := by
    simpa [prefixWord, tailWord_706328, baseEnd_706328] using wordTrace_append hprefix tailTrace_706328
  have hstable : (prefixWord ++ tailWord_706328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706328).length < 2 ^ (prefixWord ++ tailWord_706328).sum := by decide
  have hdescent : baseEnd_706328 < baseStart_706328 := by decide
  rcases family_descends (prefixWord ++ tailWord_706328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706334 : List Nat := [4, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_706334 : Nat := 118140960795 + 706334 * 2 ^ 59
def prefixEnd_706334 : Nat := 4983230072969 + 3 ^ 40 * 706334 * 2
def baseEnd_706334 : Nat := 322390084100395287712565

theorem tailTrace_706334 : CollatzResearch.WordTrace tailWord_706334 prefixEnd_706334 322390084100395287712565 := by
  unfold tailWord_706334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220264677885003136035757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17174744948720016725524037 3220264677885003136035757)
  ·
    refine ⟨1207599254206876176013409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3220264677885003136035757 1207599254206876176013409)
    ·
      refine ⟨905699440655157132010057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1207599254206876176013409 905699440655157132010057)
      ·
        refine ⟨679274580491367849007543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 905699440655157132010057 679274580491367849007543)
        ·
          refine ⟨1018911870737051773511315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679274580491367849007543 1018911870737051773511315)
          ·
            refine ⟨1528367806105577660266973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018911870737051773511315 1528367806105577660266973)
            ·
              refine ⟨573137927289591622600115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1528367806105577660266973 573137927289591622600115)
              ·
                refine ⟨859706890934387433900173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573137927289591622600115 859706890934387433900173)
                ·
                  refine ⟨322390084100395287712565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 859706890934387433900173 322390084100395287712565)
                  ·
                    rfl

theorem cell20_706334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_706334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706334 prefixEnd_706334 := by exact prefixLift 706334
  have htrace : WordTrace (prefixWord ++ tailWord_706334) baseStart_706334 baseEnd_706334 := by
    simpa [prefixWord, tailWord_706334, baseEnd_706334] using wordTrace_append hprefix tailTrace_706334
  have hstable : (prefixWord ++ tailWord_706334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706334).length < 2 ^ (prefixWord ++ tailWord_706334).sum := by decide
  have hdescent : baseEnd_706334 < baseStart_706334 := by decide
  rcases family_descends (prefixWord ++ tailWord_706334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706394 : List Nat := [3, 1, 1, 2, 1, 3, 4, 5]
def baseStart_706394 : Nat := 118140960795 + 706394 * 2 ^ 59
def prefixEnd_706394 : Nat := 4983230072969 + 3 ^ 40 * 706394 * 2
def baseEnd_706394 : Nat := 107472489911767248570773

theorem tailTrace_706394 : CollatzResearch.WordTrace tailWord_706394 prefixEnd_706394 107472489911767248570773 := by
  unfold tailWord_706394
  simp only [CollatzResearch.WordTrace]
  refine ⟨6441076450715663833867559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17176203868575103556980157 6441076450715663833867559)
  ·
    refine ⟨9661614676073495750801339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6441076450715663833867559 9661614676073495750801339)
    ·
      refine ⟨14492422014110243626202009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9661614676073495750801339 14492422014110243626202009)
      ·
        refine ⟨10869316510582682719651507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14492422014110243626202009 10869316510582682719651507)
        ·
          refine ⟨16303974765874024079477261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10869316510582682719651507 16303974765874024079477261)
          ·
            refine ⟨6113990537202759029803973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16303974765874024079477261 6113990537202759029803973)
            ·
              refine ⟨1146373225725517318088245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6113990537202759029803973 1146373225725517318088245)
              ·
                refine ⟨107472489911767248570773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1146373225725517318088245 107472489911767248570773)
                ·
                  rfl

theorem cell20_706394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_706394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706394 prefixEnd_706394 := by exact prefixLift 706394
  have htrace : WordTrace (prefixWord ++ tailWord_706394) baseStart_706394 baseEnd_706394 := by
    simpa [prefixWord, tailWord_706394, baseEnd_706394] using wordTrace_append hprefix tailTrace_706394
  have hstable : (prefixWord ++ tailWord_706394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706394).length < 2 ^ (prefixWord ++ tailWord_706394).sum := by decide
  have hdescent : baseEnd_706394 < baseStart_706394 := by decide
  rcases family_descends (prefixWord ++ tailWord_706394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706466 : List Nat := [3, 3, 1, 2, 3, 1, 3, 4]
def baseStart_706466 : Nat := 118140960795 + 706466 * 2 ^ 59
def prefixEnd_706466 : Nat := 4983230072969 + 3 ^ 40 * 706466 * 2
def baseEnd_706466 : Nat := 107483444165729831770675

theorem tailTrace_706466 : CollatzResearch.WordTrace tailWord_706466 prefixEnd_706466 107483444165729831770675 := by
  unfold tailWord_706466
  simp only [CollatzResearch.WordTrace]
  refine ⟨6441732964650452908022813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17177954572401207754727501 6441732964650452908022813)
  ·
    refine ⟨2415649861743919840508555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6441732964650452908022813 2415649861743919840508555)
    ·
      refine ⟨3623474792615879760762833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2415649861743919840508555 3623474792615879760762833)
      ·
        refine ⟨2717606094461909820572125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3623474792615879760762833 2717606094461909820572125)
        ·
          refine ⟨1019102285423216182714547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2717606094461909820572125 1019102285423216182714547)
          ·
            refine ⟨1528653428134824274071821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019102285423216182714547 1528653428134824274071821)
            ·
              refine ⟨573245035550559102776933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1528653428134824274071821 573245035550559102776933)
              ·
                refine ⟨107483444165729831770675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 573245035550559102776933 107483444165729831770675)
                ·
                  rfl

theorem cell20_706466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_706466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706466 prefixEnd_706466 := by exact prefixLift 706466
  have htrace : WordTrace (prefixWord ++ tailWord_706466) baseStart_706466 baseEnd_706466 := by
    simpa [prefixWord, tailWord_706466, baseEnd_706466] using wordTrace_append hprefix tailTrace_706466
  have hstable : (prefixWord ++ tailWord_706466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706466).length < 2 ^ (prefixWord ++ tailWord_706466).sum := by decide
  have hdescent : baseEnd_706466 < baseStart_706466 := by decide
  rcases family_descends (prefixWord ++ tailWord_706466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706494 : List Nat := [4, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_706494 : Nat := 118140960795 + 706494 * 2 ^ 59
def prefixEnd_706494 : Nat := 4983230072969 + 3 ^ 40 * 706494 * 2
def baseEnd_706494 : Nat := 322463112460145842378577

theorem tailTrace_706494 : CollatzResearch.WordTrace tailWord_706494 prefixEnd_706494 322463112460145842378577 := by
  unfold tailWord_706494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220994137812546551763817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17178635401666914942740357 3220994137812546551763817)
  ·
    refine ⟨2415745603359409913822863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3220994137812546551763817 2415745603359409913822863)
    ·
      refine ⟨3623618405039114870734295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2415745603359409913822863 3623618405039114870734295)
      ·
        refine ⟨5435427607558672306101443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3623618405039114870734295 5435427607558672306101443)
        ·
          refine ⟨8153141411338008459152165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5435427607558672306101443 8153141411338008459152165)
          ·
            refine ⟨1528714014625876586091031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8153141411338008459152165 1528714014625876586091031)
            ·
              refine ⟨2293071021938814879136547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528714014625876586091031 2293071021938814879136547)
              ·
                refine ⟨3439606532908222318704821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293071021938814879136547 3439606532908222318704821)
                ·
                  refine ⟨322463112460145842378577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3439606532908222318704821 322463112460145842378577)
                  ·
                    rfl

theorem cell20_706494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_706494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706494 prefixEnd_706494 := by exact prefixLift 706494
  have htrace : WordTrace (prefixWord ++ tailWord_706494) baseStart_706494 baseEnd_706494 := by
    simpa [prefixWord, tailWord_706494, baseEnd_706494] using wordTrace_append hprefix tailTrace_706494
  have hstable : (prefixWord ++ tailWord_706494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706494).length < 2 ^ (prefixWord ++ tailWord_706494).sum := by decide
  have hdescent : baseEnd_706494 < baseStart_706494 := by decide
  rcases family_descends (prefixWord ++ tailWord_706494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706525 : List Nat := [1, 4, 3, 1, 3, 1, 1, 6]
def baseStart_706525 : Nat := 118140960795 + 706525 * 2 ^ 59
def prefixEnd_706525 : Nat := 4983230072969 + 3 ^ 40 * 706525 * 2
def baseEnd_706525 : Nat := 107492420568282504115039

theorem tailTrace_706525 : CollatzResearch.WordTrace tailWord_706525 prefixEnd_706525 107492420568282504115039 := by
  unfold tailWord_706525
  simp only [CollatzResearch.WordTrace]
  refine ⟨25769083765388064708489029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17179389176925376472326019 25769083765388064708489029)
  ·
    refine ⟨4831703206010262132841693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25769083765388064708489029 4831703206010262132841693)
    ·
      refine ⟨1811888702253848299815635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4831703206010262132841693 1811888702253848299815635)
      ·
        refine ⟨2717833053380772449723453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1811888702253848299815635 2717833053380772449723453)
        ·
          refine ⟨1019187395017789668646295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2717833053380772449723453 1019187395017789668646295)
          ·
            refine ⟨1528781092526684502969443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019187395017789668646295 1528781092526684502969443)
            ·
              refine ⟨2293171638790026754454165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528781092526684502969443 2293171638790026754454165)
              ·
                refine ⟨107492420568282504115039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2293171638790026754454165 107492420568282504115039)
                ·
                  rfl

theorem cell20_706525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 6].length) (baseStart_706525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706525 prefixEnd_706525 := by exact prefixLift 706525
  have htrace : WordTrace (prefixWord ++ tailWord_706525) baseStart_706525 baseEnd_706525 := by
    simpa [prefixWord, tailWord_706525, baseEnd_706525] using wordTrace_append hprefix tailTrace_706525
  have hstable : (prefixWord ++ tailWord_706525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706525).length < 2 ^ (prefixWord ++ tailWord_706525).sum := by decide
  have hdescent : baseEnd_706525 < baseStart_706525 := by decide
  rcases family_descends (prefixWord ++ tailWord_706525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706553 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 5]
def baseStart_706553 : Nat := 118140960795 + 706553 * 2 ^ 59
def prefixEnd_706553 : Nat := 4983230072969 + 3 ^ 40 * 706553 * 2
def baseEnd_706553 : Nat := 322490041667803859411669

theorem tailTrace_706553 : CollatzResearch.WordTrace tailWord_706553 prefixEnd_706553 322490041667803859411669 := by
  unfold tailWord_706553
  simp only [CollatzResearch.WordTrace]
  refine ⟨25770105009286625490508313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17180070006191083660338875 25770105009286625490508313)
  ·
    refine ⟨19327578756964969117881235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25770105009286625490508313 19327578756964969117881235)
    ·
      refine ⟨28991368135447453676821853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19327578756964969117881235 28991368135447453676821853)
      ·
        refine ⟨10871763050792795128808195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28991368135447453676821853 10871763050792795128808195)
        ·
          refine ⟨16307644576189192693212293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10871763050792795128808195 16307644576189192693212293)
          ·
            refine ⟨3057683358035473629977305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16307644576189192693212293 3057683358035473629977305)
            ·
              refine ⟨2293262518526605222482979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3057683358035473629977305 2293262518526605222482979)
              ·
                refine ⟨3439893777789907833724469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293262518526605222482979 3439893777789907833724469)
                ·
                  refine ⟨322490041667803859411669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3439893777789907833724469 322490041667803859411669)
                  ·
                    rfl

theorem cell20_706553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_706553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706553 prefixEnd_706553 := by exact prefixLift 706553
  have htrace : WordTrace (prefixWord ++ tailWord_706553) baseStart_706553 baseEnd_706553 := by
    simpa [prefixWord, tailWord_706553, baseEnd_706553] using wordTrace_append hprefix tailTrace_706553
  have hstable : (prefixWord ++ tailWord_706553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706553).length < 2 ^ (prefixWord ++ tailWord_706553).sum := by decide
  have hdescent : baseEnd_706553 < baseStart_706553 := by decide
  rcases family_descends (prefixWord ++ tailWord_706553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706560 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_706560 : Nat := 118140960795 + 706560 * 2 ^ 59
def prefixEnd_706560 : Nat := 4983230072969 + 3 ^ 40 * 706560 * 2
def baseEnd_706560 : Nat := 322493236658542946178307

theorem tailTrace_706560 : CollatzResearch.WordTrace tailWord_706560 prefixEnd_706560 322493236658542946178307 := by
  unfold tailWord_706560
  simp only [CollatzResearch.WordTrace]
  refine ⟨12885180160130632843006567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17180240213507510457342089 12885180160130632843006567)
  ·
    refine ⟨19327770240195949264509851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12885180160130632843006567 19327770240195949264509851)
    ·
      refine ⟨28991655360293923896764777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19327770240195949264509851 28991655360293923896764777)
      ·
        refine ⟨21743741520220442922573583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28991655360293923896764777 21743741520220442922573583)
        ·
          refine ⟨32615612280330664383860375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21743741520220442922573583 32615612280330664383860375)
          ·
            refine ⟨48923418420495996575790563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32615612280330664383860375 48923418420495996575790563)
            ·
              refine ⟨73385127630743994863685845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48923418420495996575790563 73385127630743994863685845)
              ·
                refine ⟨1719963928845562379617637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73385127630743994863685845 1719963928845562379617637)
                ·
                  refine ⟨322493236658542946178307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719963928845562379617637 322493236658542946178307)
                  ·
                    rfl

theorem cell20_706560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_706560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706560 prefixEnd_706560 := by exact prefixLift 706560
  have htrace : WordTrace (prefixWord ++ tailWord_706560) baseStart_706560 baseEnd_706560 := by
    simpa [prefixWord, tailWord_706560, baseEnd_706560] using wordTrace_append hprefix tailTrace_706560
  have hstable : (prefixWord ++ tailWord_706560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706560).length < 2 ^ (prefixWord ++ tailWord_706560).sum := by decide
  have hdescent : baseEnd_706560 < baseStart_706560 := by decide
  rcases family_descends (prefixWord ++ tailWord_706560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706594 : List Nat := [3, 3, 1, 1, 1, 2, 2, 5, 2]
def baseStart_706594 : Nat := 118140960795 + 706594 * 2 ^ 59
def prefixEnd_706594 : Nat := 4983230072969 + 3 ^ 40 * 706594 * 2
def baseEnd_706594 : Nat := 322508755184989939044835

theorem tailTrace_706594 : CollatzResearch.WordTrace tailWord_706594 prefixEnd_706594 322508755184989939044835 := by
  unfold tailWord_706594
  simp only [CollatzResearch.WordTrace]
  refine ⟨6442900100534522373187709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17181066934758726328500557 6442900100534522373187709)
  ·
    refine ⟨2416087537700445889945391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6442900100534522373187709 2416087537700445889945391)
    ·
      refine ⟨3624131306550668834918087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416087537700445889945391 3624131306550668834918087)
      ·
        refine ⟨5436196959826003252377131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3624131306550668834918087 5436196959826003252377131)
        ·
          refine ⟨8154295439739004878565697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5436196959826003252377131 8154295439739004878565697)
          ·
            refine ⟨6115721579804253658924273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8154295439739004878565697 6115721579804253658924273)
            ·
              refine ⟨4586791184853190244193205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6115721579804253658924273 4586791184853190244193205)
              ·
                refine ⟨430011673579986585393113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4586791184853190244193205 430011673579986585393113)
                ·
                  refine ⟨322508755184989939044835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430011673579986585393113 322508755184989939044835)
                  ·
                    rfl

theorem cell20_706594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_706594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706594 prefixEnd_706594 := by exact prefixLift 706594
  have htrace : WordTrace (prefixWord ++ tailWord_706594) baseStart_706594 baseEnd_706594 := by
    simpa [prefixWord, tailWord_706594, baseEnd_706594] using wordTrace_append hprefix tailTrace_706594
  have hstable : (prefixWord ++ tailWord_706594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706594).length < 2 ^ (prefixWord ++ tailWord_706594).sum := by decide
  have hdescent : baseEnd_706594 < baseStart_706594 := by decide
  rcases family_descends (prefixWord ++ tailWord_706594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706605 : List Nat := [1, 5, 14]
def baseStart_706605 : Nat := 118140960795 + 706605 * 2 ^ 59
def prefixEnd_706605 : Nat := 4983230072969 + 3 ^ 40 * 706605 * 2
def baseEnd_706605 : Nat := 442405728236931124387

theorem tailTrace_706605 : CollatzResearch.WordTrace tailWord_706605 prefixEnd_706605 442405728236931124387 := by
  unfold tailWord_706605
  simp only [CollatzResearch.WordTrace]
  refine ⟨25772001605098238371401269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17181334403398825580934179 25772001605098238371401269)
  ·
    refine ⟨2416125150477959847318869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25772001605098238371401269 2416125150477959847318869)
    ·
      refine ⟨442405728236931124387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 2416125150477959847318869 442405728236931124387)
      ·
        rfl

theorem cell20_706605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 14].length) (baseStart_706605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706605 prefixEnd_706605 := by exact prefixLift 706605
  have htrace : WordTrace (prefixWord ++ tailWord_706605) baseStart_706605 baseEnd_706605 := by
    simpa [prefixWord, tailWord_706605, baseEnd_706605] using wordTrace_append hprefix tailTrace_706605
  have hstable : (prefixWord ++ tailWord_706605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706605).length < 2 ^ (prefixWord ++ tailWord_706605).sum := by decide
  have hdescent : baseEnd_706605 < baseStart_706605 := by decide
  rcases family_descends (prefixWord ++ tailWord_706605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706608 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 3]
def baseStart_706608 : Nat := 118140960795 + 706608 * 2 ^ 59
def prefixEnd_706608 : Nat := 4983230072969 + 3 ^ 40 * 706608 * 2
def baseEnd_706608 : Nat := 322515145166468112578111

theorem tailTrace_706608 : CollatzResearch.WordTrace tailWord_706608 prefixEnd_706608 322515145166468112578111 := by
  unfold tailWord_706608
  simp only [CollatzResearch.WordTrace]
  refine ⟨12886055512043684941880239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17181407349391579922506985 12886055512043684941880239)
  ·
    refine ⟨19329083268065527412820359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12886055512043684941880239 19329083268065527412820359)
    ·
      refine ⟨28993624902098291119230539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19329083268065527412820359 28993624902098291119230539)
      ·
        refine ⟨43490437353147436678845809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28993624902098291119230539 43490437353147436678845809)
        ·
          refine ⟨32617828014860577509134357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43490437353147436678845809 32617828014860577509134357)
          ·
            refine ⟨1528960688196589570740673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32617828014860577509134357 1528960688196589570740673)
            ·
              refine ⟨1146720516147442178055505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1528960688196589570740673 1146720516147442178055505)
              ·
                refine ⟨860040387110581633541629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146720516147442178055505 860040387110581633541629)
                ·
                  refine ⟨322515145166468112578111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860040387110581633541629 322515145166468112578111)
                  ·
                    rfl

theorem cell20_706608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_706608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706608 prefixEnd_706608 := by exact prefixLift 706608
  have htrace : WordTrace (prefixWord ++ tailWord_706608) baseStart_706608 baseEnd_706608 := by
    simpa [prefixWord, tailWord_706608, baseEnd_706608] using wordTrace_append hprefix tailTrace_706608
  have hstable : (prefixWord ++ tailWord_706608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706608).length < 2 ^ (prefixWord ++ tailWord_706608).sum := by decide
  have hdescent : baseEnd_706608 < baseStart_706608 := by decide
  rcases family_descends (prefixWord ++ tailWord_706608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706636 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_706636 : Nat := 118140960795 + 706636 * 2 ^ 59
def prefixEnd_706636 : Nat := 4983230072969 + 3 ^ 40 * 706636 * 2
def baseEnd_706636 : Nat := 322527925129424459644663

theorem tailTrace_706636 : CollatzResearch.WordTrace tailWord_706636 prefixEnd_706636 322527925129424459644663 := by
  unfold tailWord_706636
  simp only [CollatzResearch.WordTrace]
  refine ⟨12886566133992965332889881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17182088178657287110519841 12886566133992965332889881)
  ·
    refine ⟨9664924600494723999667411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12886566133992965332889881 9664924600494723999667411)
    ·
      refine ⟨14497386900742085999501117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9664924600494723999667411 14497386900742085999501117)
      ·
        refine ⟨5436520087778282249812919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14497386900742085999501117 5436520087778282249812919)
        ·
          refine ⟨8154780131667423374719379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5436520087778282249812919 8154780131667423374719379)
          ·
            refine ⟨12232170197501135062079069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8154780131667423374719379 12232170197501135062079069)
            ·
              refine ⟨4587063824062925648279651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12232170197501135062079069 4587063824062925648279651)
              ·
                refine ⟨6880595736094388472419477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4587063824062925648279651 6880595736094388472419477)
                ·
                  refine ⟨322527925129424459644663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6880595736094388472419477 322527925129424459644663)
                  ·
                    rfl

theorem cell20_706636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_706636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706636 prefixEnd_706636 := by exact prefixLift 706636
  have htrace : WordTrace (prefixWord ++ tailWord_706636) baseStart_706636 baseEnd_706636 := by
    simpa [prefixWord, tailWord_706636, baseEnd_706636] using wordTrace_append hprefix tailTrace_706636
  have hstable : (prefixWord ++ tailWord_706636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706636).length < 2 ^ (prefixWord ++ tailWord_706636).sum := by decide
  have hdescent : baseEnd_706636 < baseStart_706636 := by decide
  rcases family_descends (prefixWord ++ tailWord_706636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706670 : List Nat := [4, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_706670 : Nat := 118140960795 + 706670 * 2 ^ 59
def prefixEnd_706670 : Nat := 4983230072969 + 3 ^ 40 * 706670 * 2
def baseEnd_706670 : Nat := 322543443655871452511191

theorem tailTrace_706670 : CollatzResearch.WordTrace tailWord_706670 prefixEnd_706670 322543443655871452511191 := by
  unfold tailWord_706670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221796543732844309064683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17182914899908502981678309 3221796543732844309064683)
  ·
    refine ⟨4832694815599266463597025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3221796543732844309064683 4832694815599266463597025)
    ·
      refine ⟨3624521111699449847697769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4832694815599266463597025 3624521111699449847697769)
      ·
        refine ⟨2718390833774587385773327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3624521111699449847697769 2718390833774587385773327)
        ·
          refine ⟨4077586250661881078659991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718390833774587385773327 4077586250661881078659991)
          ·
            refine ⟨6116379375992821617989987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4077586250661881078659991 6116379375992821617989987)
            ·
              refine ⟨9174569063989232426984981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6116379375992821617989987 9174569063989232426984981)
              ·
                refine ⟨430057924874495270014921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9174569063989232426984981 430057924874495270014921)
                ·
                  refine ⟨322543443655871452511191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430057924874495270014921 322543443655871452511191)
                  ·
                    rfl

theorem cell20_706670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_706670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706670 prefixEnd_706670 := by exact prefixLift 706670
  have htrace : WordTrace (prefixWord ++ tailWord_706670) baseStart_706670 baseEnd_706670 := by
    simpa [prefixWord, tailWord_706670, baseEnd_706670] using wordTrace_append hprefix tailTrace_706670
  have hstable : (prefixWord ++ tailWord_706670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706670).length < 2 ^ (prefixWord ++ tailWord_706670).sum := by decide
  have hdescent : baseEnd_706670 < baseStart_706670 := by decide
  rcases family_descends (prefixWord ++ tailWord_706670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706698 : List Nat := [3, 1, 2, 3, 1, 3, 1, 6]
def baseStart_706698 : Nat := 118140960795 + 706698 * 2 ^ 59
def prefixEnd_706698 : Nat := 4983230072969 + 3 ^ 40 * 706698 * 2
def baseEnd_706698 : Nat := 107518741206275933192581

theorem tailTrace_706698 : CollatzResearch.WordTrace tailWord_706698 prefixEnd_706698 107518741206275933192581 := by
  unfold tailWord_706698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443848398440328813634187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17183595729174210169691165 6443848398440328813634187)
  ·
    refine ⟨9665772597660493220451281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6443848398440328813634187 9665772597660493220451281)
    ·
      refine ⟨7249329448245369915338461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9665772597660493220451281 7249329448245369915338461)
      ·
        refine ⟨2718498543092013718251923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7249329448245369915338461 2718498543092013718251923)
        ·
          refine ⟨4077747814638020577377885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2718498543092013718251923 4077747814638020577377885)
          ·
            refine ⟨1529155430489257716516707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4077747814638020577377885 1529155430489257716516707)
            ·
              refine ⟨2293733145733886574775061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529155430489257716516707 2293733145733886574775061)
              ·
                refine ⟨107518741206275933192581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2293733145733886574775061 107518741206275933192581)
                ·
                  rfl

theorem cell20_706698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_706698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706698 prefixEnd_706698 := by exact prefixLift 706698
  have htrace : WordTrace (prefixWord ++ tailWord_706698) baseStart_706698 baseEnd_706698 := by
    simpa [prefixWord, tailWord_706698, baseEnd_706698] using wordTrace_append hprefix tailTrace_706698
  have hstable : (prefixWord ++ tailWord_706698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706698).length < 2 ^ (prefixWord ++ tailWord_706698).sum := by decide
  have hdescent : baseEnd_706698 < baseStart_706698 := by decide
  rcases family_descends (prefixWord ++ tailWord_706698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706722 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_706722 : Nat := 118140960795 + 706722 * 2 ^ 59
def prefixEnd_706722 : Nat := 4983230072969 + 3 ^ 40 * 706722 * 2
def baseEnd_706722 : Nat := 322567177872790382777645

theorem tailTrace_706722 : CollatzResearch.WordTrace tailWord_706722 prefixEnd_706722 322567177872790382777645 := by
  unfold tailWord_706722
  simp only [CollatzResearch.WordTrace]
  refine ⟨6444067236418591838352605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17184179297116244902273613 6444067236418591838352605)
  ·
    refine ⟨2416525213656971939382227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6444067236418591838352605 2416525213656971939382227)
    ·
      refine ⟨3624787820485457909073341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416525213656971939382227 3624787820485457909073341)
      ·
        refine ⟨1359295432682046715902503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3624787820485457909073341 1359295432682046715902503)
        ·
          refine ⟨2038943149023070073853755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359295432682046715902503 2038943149023070073853755)
          ·
            refine ⟨3058414723534605110780633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038943149023070073853755 3058414723534605110780633)
            ·
              refine ⟨2293811042650953833085475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3058414723534605110780633 2293811042650953833085475)
              ·
                refine ⟨3440716563976430749628213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2293811042650953833085475 3440716563976430749628213)
                ·
                  refine ⟨322567177872790382777645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3440716563976430749628213 322567177872790382777645)
                  ·
                    rfl

theorem cell20_706722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_706722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706722 prefixEnd_706722 := by exact prefixLift 706722
  have htrace : WordTrace (prefixWord ++ tailWord_706722) baseStart_706722 baseEnd_706722 := by
    simpa [prefixWord, tailWord_706722, baseEnd_706722] using wordTrace_append hprefix tailTrace_706722
  have hstable : (prefixWord ++ tailWord_706722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706722).length < 2 ^ (prefixWord ++ tailWord_706722).sum := by decide
  have hdescent : baseEnd_706722 < baseStart_706722 := by decide
  rcases family_descends (prefixWord ++ tailWord_706722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706757 : List Nat := [1, 3, 1, 1, 1, 1, 6, 6]
def baseStart_706757 : Nat := 118140960795 + 706757 * 2 ^ 59
def prefixEnd_706757 : Nat := 4983230072969 + 3 ^ 40 * 706757 * 2
def baseEnd_706757 : Nat := 107527717608828605536945

theorem tailTrace_706757 : CollatzResearch.WordTrace tailWord_706757 prefixEnd_706757 107527717608828605536945 := by
  unfold tailWord_706757
  simp only [CollatzResearch.WordTrace]
  refine ⟨25777545500547568330934525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17185030333698378887289683 25777545500547568330934525)
  ·
    refine ⟨9666579562705338124100447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25777545500547568330934525 9666579562705338124100447)
    ·
      refine ⟨14499869344058007186150671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9666579562705338124100447 14499869344058007186150671)
      ·
        refine ⟨21749804016087010779226007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14499869344058007186150671 21749804016087010779226007)
        ·
          refine ⟨32624706024130516168839011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21749804016087010779226007 32624706024130516168839011)
          ·
            refine ⟨48937059036195774253258517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32624706024130516168839011 48937059036195774253258517)
            ·
              refine ⟨2293924642321676918121493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48937059036195774253258517 2293924642321676918121493)
              ·
                refine ⟨107527717608828605536945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2293924642321676918121493 107527717608828605536945)
                ·
                  rfl

theorem cell20_706757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_706757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706757 prefixEnd_706757 := by exact prefixLift 706757
  have htrace : WordTrace (prefixWord ++ tailWord_706757) baseStart_706757 baseEnd_706757 := by
    simpa [prefixWord, tailWord_706757, baseEnd_706757] using wordTrace_append hprefix tailTrace_706757
  have hstable : (prefixWord ++ tailWord_706757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706757).length < 2 ^ (prefixWord ++ tailWord_706757).sum := by decide
  have hdescent : baseEnd_706757 < baseStart_706757 := by decide
  rcases family_descends (prefixWord ++ tailWord_706757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706767 : List Nat := [1, 1, 2, 1, 1, 3, 4, 5, 2]
def baseStart_706767 : Nat := 118140960795 + 706767 * 2 ^ 59
def prefixEnd_706767 : Nat := 4983230072969 + 3 ^ 40 * 706767 * 2
def baseEnd_706767 : Nat := 322587717098970226277461

theorem tailTrace_706767 : CollatzResearch.WordTrace tailWord_706767 prefixEnd_706767 322587717098970226277461 := by
  unfold tailWord_706767
  simp only [CollatzResearch.WordTrace]
  refine ⟨25777910230511340038798555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17185273487007560025865703 25777910230511340038798555)
  ·
    refine ⟨38666865345767010058197833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25777910230511340038798555 38666865345767010058197833)
    ·
      refine ⟨29000149009325257543648375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38666865345767010058197833 29000149009325257543648375)
      ·
        refine ⟨43500223513987886315472563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29000149009325257543648375 43500223513987886315472563)
        ·
          refine ⟨65250335270981829473208845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43500223513987886315472563 65250335270981829473208845)
          ·
            refine ⟨24468875726618186052453317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65250335270981829473208845 24468875726618186052453317)
            ·
              refine ⟨4587914198740909884834997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24468875726618186052453317 4587914198740909884834997)
              ·
                refine ⟨430116956131960301703281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4587914198740909884834997 430116956131960301703281)
                ·
                  refine ⟨322587717098970226277461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430116956131960301703281 322587717098970226277461)
                  ·
                    rfl

theorem cell20_706767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 2].length) (baseStart_706767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706767 prefixEnd_706767 := by exact prefixLift 706767
  have htrace : WordTrace (prefixWord ++ tailWord_706767) baseStart_706767 baseEnd_706767 := by
    simpa [prefixWord, tailWord_706767, baseEnd_706767] using wordTrace_append hprefix tailTrace_706767
  have hstable : (prefixWord ++ tailWord_706767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706767).length < 2 ^ (prefixWord ++ tailWord_706767).sum := by decide
  have hdescent : baseEnd_706767 < baseStart_706767 := by decide
  rcases family_descends (prefixWord ++ tailWord_706767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706780 : List Nat := [2, 2, 5, 2, 1, 1, 1, 4, 2]
def baseStart_706780 : Nat := 118140960795 + 706780 * 2 ^ 59
def prefixEnd_706780 : Nat := 4983230072969 + 3 ^ 40 * 706780 * 2
def baseEnd_706780 : Nat := 322593650653199958844075

theorem tailTrace_706780 : CollatzResearch.WordTrace tailWord_706780 prefixEnd_706780 322593650653199958844075 := by
  unfold tailWord_706780
  simp only [CollatzResearch.WordTrace]
  refine ⟨12889192189732121629510897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17185589586309495506014529 12889192189732121629510897)
  ·
    refine ⟨9666894142299091222133173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12889192189732121629510897 9666894142299091222133173)
    ·
      refine ⟨906271325840539802074985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9666894142299091222133173 906271325840539802074985)
      ·
        refine ⟨679703494380404851556239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 906271325840539802074985 679703494380404851556239)
        ·
          refine ⟨1019555241570607277334359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679703494380404851556239 1019555241570607277334359)
          ·
            refine ⟨1529332862355910916001539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019555241570607277334359 1529332862355910916001539)
            ·
              refine ⟨2293999293533866374002309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529332862355910916001539 2293999293533866374002309)
              ·
                refine ⟨430124867537599945125433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2293999293533866374002309 430124867537599945125433)
                ·
                  refine ⟨322593650653199958844075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430124867537599945125433 322593650653199958844075)
                  ·
                    rfl

theorem cell20_706780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_706780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706780 prefixEnd_706780 := by exact prefixLift 706780
  have htrace : WordTrace (prefixWord ++ tailWord_706780) baseStart_706780 baseEnd_706780 := by
    simpa [prefixWord, tailWord_706780, baseEnd_706780] using wordTrace_append hprefix tailTrace_706780
  have hstable : (prefixWord ++ tailWord_706780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706780).length < 2 ^ (prefixWord ++ tailWord_706780).sum := by decide
  have hdescent : baseEnd_706780 < baseStart_706780 := by decide
  rcases family_descends (prefixWord ++ tailWord_706780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706788 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_706788 : Nat := 118140960795 + 706788 * 2 ^ 59
def prefixEnd_706788 : Nat := 4983230072969 + 3 ^ 40 * 706788 * 2
def baseEnd_706788 : Nat := 322597302071187486577375

theorem tailTrace_706788 : CollatzResearch.WordTrace tailWord_706788 prefixEnd_706788 322597302071187486577375 := by
  unfold tailWord_706788
  simp only [CollatzResearch.WordTrace]
  refine ⟨12889338081717630312656509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17185784108956840416875345 12889338081717630312656509)
  ·
    refine ⟨4833501780644111367246191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12889338081717630312656509 4833501780644111367246191)
    ·
      refine ⟨7250252670966167050869287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4833501780644111367246191 7250252670966167050869287)
      ·
        refine ⟨10875379006449250576303931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7250252670966167050869287 10875379006449250576303931)
        ·
          refine ⟨16313068509673875864455897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10875379006449250576303931 16313068509673875864455897)
          ·
            refine ⟨12234801382255406898341923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16313068509673875864455897 12234801382255406898341923)
            ·
              refine ⟨18352202073383110347512885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12234801382255406898341923 18352202073383110347512885)
              ·
                refine ⟨1720518944379666595079333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18352202073383110347512885 1720518944379666595079333)
                ·
                  refine ⟨322597302071187486577375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1720518944379666595079333 322597302071187486577375)
                  ·
                    rfl

theorem cell20_706788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_706788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706788 prefixEnd_706788 := by exact prefixLift 706788
  have htrace : WordTrace (prefixWord ++ tailWord_706788) baseStart_706788 baseEnd_706788 := by
    simpa [prefixWord, tailWord_706788, baseEnd_706788] using wordTrace_append hprefix tailTrace_706788
  have hstable : (prefixWord ++ tailWord_706788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706788).length < 2 ^ (prefixWord ++ tailWord_706788).sum := by decide
  have hdescent : baseEnd_706788 < baseStart_706788 := by decide
  rcases family_descends (prefixWord ++ tailWord_706788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706791 : List Nat := [1, 1, 5, 3, 1, 3, 1, 5]
def baseStart_706791 : Nat := 118140960795 + 706791 * 2 ^ 59
def prefixEnd_706791 : Nat := 4983230072969 + 3 ^ 40 * 706791 * 2
def baseEnd_706791 : Nat := 107532890450977603159121

theorem tailTrace_706791 : CollatzResearch.WordTrace tailWord_706791 prefixEnd_706791 107532890450977603159121 := by
  unfold tailWord_706791
  simp only [CollatzResearch.WordTrace]
  refine ⟨25778785582424392137672227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17185857054949594758448151 25778785582424392137672227)
  ·
    refine ⟨38668178373636588206508341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25778785582424392137672227 38668178373636588206508341)
    ·
      refine ⟨3625141722528430144360157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38668178373636588206508341 3625141722528430144360157)
      ·
        refine ⟨1359428145948161304135059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3625141722528430144360157 1359428145948161304135059)
        ·
          refine ⟨2039142218922241956202589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359428145948161304135059 2039142218922241956202589)
          ·
            refine ⟨764678332095840733575971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2039142218922241956202589 764678332095840733575971)
            ·
              refine ⟨1147017498143761100363957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764678332095840733575971 1147017498143761100363957)
              ·
                refine ⟨107532890450977603159121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1147017498143761100363957 107532890450977603159121)
                ·
                  rfl

theorem cell20_706791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 5].length) (baseStart_706791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706791 prefixEnd_706791 := by exact prefixLift 706791
  have htrace : WordTrace (prefixWord ++ tailWord_706791) baseStart_706791 baseEnd_706791 := by
    simpa [prefixWord, tailWord_706791, baseEnd_706791] using wordTrace_append hprefix tailTrace_706791
  have hstable : (prefixWord ++ tailWord_706791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706791).length < 2 ^ (prefixWord ++ tailWord_706791).sum := by decide
  have hdescent : baseEnd_706791 < baseStart_706791 := by decide
  rcases family_descends (prefixWord ++ tailWord_706791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706833 : List Nat := [1, 2, 2, 1, 1, 6, 7]
def baseStart_706833 : Nat := 118140960795 + 706833 * 2 ^ 59
def prefixEnd_706833 : Nat := 4983230072969 + 3 ^ 40 * 706833 * 2
def baseEnd_706833 : Nat := 35846426810818592230799

theorem tailTrace_706833 : CollatzResearch.WordTrace tailWord_706833 prefixEnd_706833 35846426810818592230799 := by
  unfold tailWord_706833
  simp only [CollatzResearch.WordTrace]
  refine ⟨25780317448272233310701153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17186878298848155540467435 25780317448272233310701153)
  ·
    refine ⟨19335238086204174983025865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25780317448272233310701153 19335238086204174983025865)
    ·
      refine ⟨14501428564653131237269399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19335238086204174983025865 14501428564653131237269399)
      ·
        refine ⟨21752142846979696855904099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14501428564653131237269399 21752142846979696855904099)
        ·
          refine ⟨32628214270469545283856149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21752142846979696855904099 32628214270469545283856149)
          ·
            refine ⟨1529447543928259935180757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32628214270469545283856149 1529447543928259935180757)
            ·
              refine ⟨35846426810818592230799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1529447543928259935180757 35846426810818592230799)
              ·
                rfl

theorem cell20_706833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 7].length) (baseStart_706833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706833 prefixEnd_706833 := by exact prefixLift 706833
  have htrace : WordTrace (prefixWord ++ tailWord_706833) baseStart_706833 baseEnd_706833 := by
    simpa [prefixWord, tailWord_706833, baseEnd_706833] using wordTrace_append hprefix tailTrace_706833
  have hstable : (prefixWord ++ tailWord_706833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706833).length < 2 ^ (prefixWord ++ tailWord_706833).sum := by decide
  have hdescent : baseEnd_706833 < baseStart_706833 := by decide
  rcases family_descends (prefixWord ++ tailWord_706833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706843 : List Nat := [1, 1, 1, 1, 1, 1, 8, 4, 2]
def baseStart_706843 : Nat := 118140960795 + 706843 * 2 ^ 59
def prefixEnd_706843 : Nat := 4983230072969 + 3 ^ 40 * 706843 * 2
def baseEnd_706843 : Nat := 322622405569851739743817

theorem tailTrace_706843 : CollatzResearch.WordTrace tailWord_706843 prefixEnd_706843 322622405569851739743817 := by
  unfold tailWord_706843
  simp only [CollatzResearch.WordTrace]
  refine ⟨25780682178236005018565183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17187121452157336679043455 25780682178236005018565183)
  ·
    refine ⟨38671023267354007527847775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25780682178236005018565183 38671023267354007527847775)
    ·
      refine ⟨58006534901031011291771663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38671023267354007527847775 58006534901031011291771663)
      ·
        refine ⟨87009802351546516937657495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58006534901031011291771663 87009802351546516937657495)
        ·
          refine ⟨130514703527319775406486243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87009802351546516937657495 130514703527319775406486243)
          ·
            refine ⟨195772055290979663109729365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130514703527319775406486243 195772055290979663109729365)
            ·
              refine ⟨2294203772941167927067141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 195772055290979663109729365 2294203772941167927067141)
              ·
                refine ⟨430163207426468986325089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2294203772941167927067141 430163207426468986325089)
                ·
                  refine ⟨322622405569851739743817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430163207426468986325089 322622405569851739743817)
                  ·
                    rfl

theorem cell20_706843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 2].length) (baseStart_706843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706843 prefixEnd_706843 := by exact prefixLift 706843
  have htrace : WordTrace (prefixWord ++ tailWord_706843) baseStart_706843 baseEnd_706843 := by
    simpa [prefixWord, tailWord_706843, baseEnd_706843] using wordTrace_append hprefix tailTrace_706843
  have hstable : (prefixWord ++ tailWord_706843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706843).length < 2 ^ (prefixWord ++ tailWord_706843).sum := by decide
  have hdescent : baseEnd_706843 < baseStart_706843 := by decide
  rcases family_descends (prefixWord ++ tailWord_706843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706853 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 3]
def baseStart_706853 : Nat := 118140960795 + 706853 * 2 ^ 59
def prefixEnd_706853 : Nat := 4983230072969 + 3 ^ 40 * 706853 * 2
def baseEnd_706853 : Nat := 322626969842336149410443

theorem tailTrace_706853 : CollatzResearch.WordTrace tailWord_706853 prefixEnd_706853 322626969842336149410443 := by
  unfold tailWord_706853
  simp only [CollatzResearch.WordTrace]
  refine ⟨25781046908199776726429213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17187364605466517817619475 25781046908199776726429213)
  ·
    refine ⟨9667892590574916272410955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25781046908199776726429213 9667892590574916272410955)
    ·
      refine ⟨14501838885862374408616433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9667892590574916272410955 14501838885862374408616433)
      ·
        refine ⟨10876379164396780806462325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14501838885862374408616433 10876379164396780806462325)
        ·
          refine ⟨1019660546662198200605843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10876379164396780806462325 1019660546662198200605843)
          ·
            refine ⟨1529490819993297300908765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019660546662198200605843 1529490819993297300908765)
            ·
              refine ⟨573559057497486487840787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1529490819993297300908765 573559057497486487840787)
              ·
                refine ⟨860338586246229731761181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573559057497486487840787 860338586246229731761181)
                ·
                  refine ⟨322626969842336149410443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860338586246229731761181 322626969842336149410443)
                  ·
                    rfl

theorem cell20_706853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_706853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706853 prefixEnd_706853 := by exact prefixLift 706853
  have htrace : WordTrace (prefixWord ++ tailWord_706853) baseStart_706853 baseEnd_706853 := by
    simpa [prefixWord, tailWord_706853, baseEnd_706853] using wordTrace_append hprefix tailTrace_706853
  have hstable : (prefixWord ++ tailWord_706853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706853).length < 2 ^ (prefixWord ++ tailWord_706853).sum := by decide
  have hdescent : baseEnd_706853 < baseStart_706853 := by decide
  rcases family_descends (prefixWord ++ tailWord_706853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706884 : List Nat := [2, 3, 4, 1, 3, 1, 6]
def baseStart_706884 : Nat := 118140960795 + 706884 * 2 ^ 59
def prefixEnd_706884 : Nat := 4983230072969 + 3 ^ 40 * 706884 * 2
def baseEnd_706884 : Nat := 35849013231893091041887

theorem tailTrace_706884 : CollatzResearch.WordTrace tailWord_706884 prefixEnd_706884 35849013231893091041887 := by
  unfold tailWord_706884
  simp only [CollatzResearch.WordTrace]
  refine ⟨12891088785543734510403853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17188118380724979347205137 12891088785543734510403853)
  ·
    refine ⟨4834158294578900441401445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12891088785543734510403853 4834158294578900441401445)
    ·
      refine ⟨906404680233543832762771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4834158294578900441401445 906404680233543832762771)
      ·
        refine ⟨1359607020350315749144157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906404680233543832762771 1359607020350315749144157)
        ·
          refine ⟨509852632631368405929059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1359607020350315749144157 509852632631368405929059)
          ·
            refine ⟨764778948947052608893589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509852632631368405929059 764778948947052608893589)
            ·
              refine ⟨35849013231893091041887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 764778948947052608893589 35849013231893091041887)
              ·
                rfl

theorem cell20_706884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 6].length) (baseStart_706884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706884 prefixEnd_706884 := by exact prefixLift 706884
  have htrace : WordTrace (prefixWord ++ tailWord_706884) baseStart_706884 baseEnd_706884 := by
    simpa [prefixWord, tailWord_706884, baseEnd_706884] using wordTrace_append hprefix tailTrace_706884
  have hstable : (prefixWord ++ tailWord_706884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706884).length < 2 ^ (prefixWord ++ tailWord_706884).sum := by decide
  have hdescent : baseEnd_706884 < baseStart_706884 := by decide
  rcases family_descends (prefixWord ++ tailWord_706884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706912 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 3]
def baseStart_706912 : Nat := 118140960795 + 706912 * 2 ^ 59
def prefixEnd_706912 : Nat := 4983230072969 + 3 ^ 40 * 706912 * 2
def baseEnd_706912 : Nat := 322653899049994166443535

theorem tailTrace_706912 : CollatzResearch.WordTrace tailWord_706912 prefixEnd_706912 322653899049994166443535 := by
  unfold tailWord_706912
  simp only [CollatzResearch.WordTrace]
  refine ⟨12891599407493014901413495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17188799209990686535217993 12891599407493014901413495)
  ·
    refine ⟨19337399111239522352120243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12891599407493014901413495 19337399111239522352120243)
    ·
      refine ⟨29006098666859283528180365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19337399111239522352120243 29006098666859283528180365)
      ·
        refine ⟨10877287000072231323067637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29006098666859283528180365 10877287000072231323067637)
        ·
          refine ⟨1019745656256771686537591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10877287000072231323067637 1019745656256771686537591)
          ·
            refine ⟨1529618484385157529806387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019745656256771686537591 1529618484385157529806387)
            ·
              refine ⟨2294427726577736294709581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529618484385157529806387 2294427726577736294709581)
              ·
                refine ⟨860410397466651110516093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2294427726577736294709581 860410397466651110516093)
                ·
                  refine ⟨322653899049994166443535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860410397466651110516093 322653899049994166443535)
                  ·
                    rfl

theorem cell20_706912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_706912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706912 prefixEnd_706912 := by exact prefixLift 706912
  have htrace : WordTrace (prefixWord ++ tailWord_706912) baseStart_706912 baseEnd_706912 := by
    simpa [prefixWord, tailWord_706912, baseEnd_706912] using wordTrace_append hprefix tailTrace_706912
  have hstable : (prefixWord ++ tailWord_706912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706912).length < 2 ^ (prefixWord ++ tailWord_706912).sum := by decide
  have hdescent : baseEnd_706912 < baseStart_706912 := by decide
  rcases family_descends (prefixWord ++ tailWord_706912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706946 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_706946 : Nat := 118140960795 + 706946 * 2 ^ 59
def prefixEnd_706946 : Nat := 4983230072969 + 3 ^ 40 * 706946 * 2
def baseEnd_706946 : Nat := 322669417576441159310063

theorem tailTrace_706946 : CollatzResearch.WordTrace tailWord_706946 prefixEnd_706946 322669417576441159310063 := by
  unfold tailWord_706946
  simp only [CollatzResearch.WordTrace]
  refine ⟨6446109724215713402391173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17189625931241902406376461 6446109724215713402391173)
  ·
    refine ⟨1208645573290446262948345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6446109724215713402391173 1208645573290446262948345)
    ·
      refine ⟨906484179967834697211259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1208645573290446262948345 906484179967834697211259)
      ·
        refine ⟨1359726269951752045816889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906484179967834697211259 1359726269951752045816889)
        ·
          refine ⟨1019794702463814034362667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1359726269951752045816889 1019794702463814034362667)
          ·
            refine ⟨1529692053695721051544001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019794702463814034362667 1529692053695721051544001)
            ·
              refine ⟨1147269040271790788658001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529692053695721051544001 1147269040271790788658001)
              ·
                refine ⟨860451780203843091493501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147269040271790788658001 860451780203843091493501)
                ·
                  refine ⟨322669417576441159310063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860451780203843091493501 322669417576441159310063)
                  ·
                    rfl

theorem cell20_706946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_706946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706946 prefixEnd_706946 := by exact prefixLift 706946
  have htrace : WordTrace (prefixWord ++ tailWord_706946) baseStart_706946 baseEnd_706946 := by
    simpa [prefixWord, tailWord_706946, baseEnd_706946] using wordTrace_append hprefix tailTrace_706946
  have hstable : (prefixWord ++ tailWord_706946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706946).length < 2 ^ (prefixWord ++ tailWord_706946).sum := by decide
  have hdescent : baseEnd_706946 < baseStart_706946 := by decide
  rcases family_descends (prefixWord ++ tailWord_706946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706947 : List Nat := [1, 1, 1, 3, 6, 8]
def baseStart_706947 : Nat := 118140960795 + 706947 * 2 ^ 59
def prefixEnd_706947 : Nat := 4983230072969 + 3 ^ 40 * 706947 * 2
def baseEnd_706947 : Nat := 11950736074210725936175

theorem tailTrace_706947 : CollatzResearch.WordTrace tailWord_706947 prefixEnd_706947 11950736074210725936175 := by
  unfold tailWord_706947
  simp only [CollatzResearch.WordTrace]
  refine ⟨25784475369859230780351095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17189650246572820520234063 25784475369859230780351095)
  ·
    refine ⟨38676713054788846170526643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25784475369859230780351095 38676713054788846170526643)
    ·
      refine ⟨58015069582183269255789965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38676713054788846170526643 58015069582183269255789965)
      ·
        refine ⟨21755651093318725970921237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58015069582183269255789965 21755651093318725970921237)
        ·
          refine ⟨1019796144999315279886933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21755651093318725970921237 1019796144999315279886933)
          ·
            refine ⟨11950736074210725936175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1019796144999315279886933 11950736074210725936175)
            ·
              rfl

theorem cell20_706947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 8].length) (baseStart_706947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706947 prefixEnd_706947 := by exact prefixLift 706947
  have htrace : WordTrace (prefixWord ++ tailWord_706947) baseStart_706947 baseEnd_706947 := by
    simpa [prefixWord, tailWord_706947, baseEnd_706947] using wordTrace_append hprefix tailTrace_706947
  have hstable : (prefixWord ++ tailWord_706947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706947).length < 2 ^ (prefixWord ++ tailWord_706947).sum := by decide
  have hdescent : baseEnd_706947 < baseStart_706947 := by decide
  rcases family_descends (prefixWord ++ tailWord_706947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706953 : List Nat := [1, 2, 1, 1, 6, 3, 2, 2, 2]
def baseStart_706953 : Nat := 118140960795 + 706953 * 2 ^ 59
def prefixEnd_706953 : Nat := 4983230072969 + 3 ^ 40 * 706953 * 2
def baseEnd_706953 : Nat := 322672612567180246076701

theorem tailTrace_706953 : CollatzResearch.WordTrace tailWord_706953 prefixEnd_706953 322672612567180246076701 := by
  unfold tailWord_706953
  simp only [CollatzResearch.WordTrace]
  refine ⟨25784694207837493805069513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17189796138558329203379675 25784694207837493805069513)
  ·
    refine ⟨19338520655878120353802135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25784694207837493805069513 19338520655878120353802135)
    ·
      refine ⟨29007780983817180530703203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19338520655878120353802135 29007780983817180530703203)
      ·
        refine ⟨43511671475725770796054805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29007780983817180530703203 43511671475725770796054805)
        ·
          refine ⟨2039609600424645506065069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43511671475725770796054805 2039609600424645506065069)
          ·
            refine ⟨764853600159242064774401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2039609600424645506065069 764853600159242064774401)
            ·
              refine ⟨573640200119431548580801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 764853600159242064774401 573640200119431548580801)
              ·
                refine ⟨430230150089573661435601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573640200119431548580801 430230150089573661435601)
                ·
                  refine ⟨322672612567180246076701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430230150089573661435601 322672612567180246076701)
                  ·
                    rfl

theorem cell20_706953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 2].length) (baseStart_706953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706953 prefixEnd_706953 := by exact prefixLift 706953
  have htrace : WordTrace (prefixWord ++ tailWord_706953) baseStart_706953 baseEnd_706953 := by
    simpa [prefixWord, tailWord_706953, baseEnd_706953] using wordTrace_append hprefix tailTrace_706953
  have hstable : (prefixWord ++ tailWord_706953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706953).length < 2 ^ (prefixWord ++ tailWord_706953).sum := by decide
  have hdescent : baseEnd_706953 < baseStart_706953 := by decide
  rcases family_descends (prefixWord ++ tailWord_706953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_706974 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_706974 : Nat := 118140960795 + 706974 * 2 ^ 59
def prefixEnd_706974 : Nat := 4983230072969 + 3 ^ 40 * 706974 * 2
def baseEnd_706974 : Nat := 322682197539397506376615

theorem tailTrace_706974 : CollatzResearch.WordTrace tailWord_706974 prefixEnd_706974 322682197539397506376615 := by
  unfold tailWord_706974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223182517595176798947997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17190306760507609594389317 3223182517595176798947997)
  ·
    refine ⟨1208693444098191299605499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3223182517595176798947997 1208693444098191299605499)
    ·
      refine ⟨1813040166147286949408249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1208693444098191299605499 1813040166147286949408249)
      ·
        refine ⟨1359780124610465212056187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1813040166147286949408249 1359780124610465212056187)
        ·
          refine ⟨2039670186915697818084281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359780124610465212056187 2039670186915697818084281)
          ·
            refine ⟨1529752640186773363563211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2039670186915697818084281 1529752640186773363563211)
            ·
              refine ⟨2294628960280160045344817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1529752640186773363563211 2294628960280160045344817)
              ·
                refine ⟨1720971720210120034008613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2294628960280160045344817 1720971720210120034008613)
                ·
                  refine ⟨322682197539397506376615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1720971720210120034008613 322682197539397506376615)
                  ·
                    rfl

theorem cell20_706974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_706974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_706974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_706974 prefixEnd_706974 := by exact prefixLift 706974
  have htrace : WordTrace (prefixWord ++ tailWord_706974) baseStart_706974 baseEnd_706974 := by
    simpa [prefixWord, tailWord_706974, baseEnd_706974] using wordTrace_append hprefix tailTrace_706974
  have hstable : (prefixWord ++ tailWord_706974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_706974).length < 2 ^ (prefixWord ++ tailWord_706974).sum := by decide
  have hdescent : baseEnd_706974 < baseStart_706974 := by decide
  rcases family_descends (prefixWord ++ tailWord_706974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707012 : List Nat := [2, 3, 3, 2, 2, 1, 2, 1, 4]
def baseStart_707012 : Nat := 118140960795 + 707012 * 2 ^ 59
def prefixEnd_707012 : Nat := 4983230072969 + 3 ^ 40 * 707012 * 2
def baseEnd_707012 : Nat := 322699541774838263109793

theorem tailTrace_707012 : CollatzResearch.WordTrace tailWord_707012 prefixEnd_707012 322699541774838263109793 := by
  unfold tailWord_707012
  simp only [CollatzResearch.WordTrace]
  refine ⟨12893423057311873440733645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17191230743082497920978193 12893423057311873440733645)
  ·
    refine ⟨4835033646491952540275117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12893423057311873440733645 4835033646491952540275117)
    ·
      refine ⟨1813137617434482202603169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4835033646491952540275117 1813137617434482202603169)
      ·
        refine ⟨1359853213075861651952377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1813137617434482202603169 1359853213075861651952377)
        ·
          refine ⟨1019889909806896238964283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1359853213075861651952377 1019889909806896238964283)
          ·
            refine ⟨1529834864710344358446425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1019889909806896238964283 1529834864710344358446425)
            ·
              refine ⟨1147376148532758268834819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1529834864710344358446425 1147376148532758268834819)
              ·
                refine ⟨1721064222799137403252229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1147376148532758268834819 1721064222799137403252229)
                ·
                  refine ⟨322699541774838263109793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721064222799137403252229 322699541774838263109793)
                  ·
                    rfl

theorem cell20_707012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_707012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707012 prefixEnd_707012 := by exact prefixLift 707012
  have htrace : WordTrace (prefixWord ++ tailWord_707012) baseStart_707012 baseEnd_707012 := by
    simpa [prefixWord, tailWord_707012, baseEnd_707012] using wordTrace_append hprefix tailTrace_707012
  have hstable : (prefixWord ++ tailWord_707012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707012).length < 2 ^ (prefixWord ++ tailWord_707012).sum := by decide
  have hdescent : baseEnd_707012 < baseStart_707012 := by decide
  rcases family_descends (prefixWord ++ tailWord_707012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707016 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_707016 : Nat := 118140960795 + 707016 * 2 ^ 59
def prefixEnd_707016 : Nat := 4983230072969 + 3 ^ 40 * 707016 * 2
def baseEnd_707016 : Nat := 322701367483832026976443

theorem tailTrace_707016 : CollatzResearch.WordTrace tailWord_707016 prefixEnd_707016 322701367483832026976443 := by
  unfold tailWord_707016
  simp only [CollatzResearch.WordTrace]
  refine ⟨12893496003304627782306451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17191328004406170376408601 12893496003304627782306451)
  ·
    refine ⟨19340244004956941673459677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12893496003304627782306451 19340244004956941673459677)
    ·
      refine ⟨7252591501858853127547379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19340244004956941673459677 7252591501858853127547379)
      ·
        refine ⟨10878887252788279691321069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7252591501858853127547379 10878887252788279691321069)
        ·
          refine ⟨4079582719795604884245401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10878887252788279691321069 4079582719795604884245401)
          ·
            refine ⟨3059687039846703663184051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4079582719795604884245401 3059687039846703663184051)
            ·
              refine ⟨4589530559770055494776077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3059687039846703663184051 4589530559770055494776077)
              ·
                refine ⟨1721073959913770810541029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4589530559770055494776077 1721073959913770810541029)
                ·
                  refine ⟨322701367483832026976443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1721073959913770810541029 322701367483832026976443)
                  ·
                    rfl

theorem cell20_707016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_707016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707016 prefixEnd_707016 := by exact prefixLift 707016
  have htrace : WordTrace (prefixWord ++ tailWord_707016) baseStart_707016 baseEnd_707016 := by
    simpa [prefixWord, tailWord_707016, baseEnd_707016] using wordTrace_append hprefix tailTrace_707016
  have hstable : (prefixWord ++ tailWord_707016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707016).length < 2 ^ (prefixWord ++ tailWord_707016).sum := by decide
  have hdescent : baseEnd_707016 < baseStart_707016 := by decide
  rcases family_descends (prefixWord ++ tailWord_707016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707050 : List Nat := [3, 1, 3, 1, 3, 1, 3, 3, 2]
def baseStart_707050 : Nat := 118140960795 + 707050 * 2 ^ 59
def prefixEnd_707050 : Nat := 4983230072969 + 3 ^ 40 * 707050 * 2
def baseEnd_707050 : Nat := 322716886010279019842971

theorem tailTrace_707050 : CollatzResearch.WordTrace tailWord_707050 prefixEnd_707050 322716886010279019842971 := by
  unfold tailWord_707050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6447058022121519842837651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17192154725657386247567069 6447058022121519842837651)
  ·
    refine ⟨9670587033182279764256477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6447058022121519842837651 9670587033182279764256477)
    ·
      refine ⟨3626470137443354911596179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9670587033182279764256477 3626470137443354911596179)
      ·
        refine ⟨5439705206165032367394269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3626470137443354911596179 5439705206165032367394269)
        ·
          refine ⟨2039889452311887137772851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5439705206165032367394269 2039889452311887137772851)
          ·
            refine ⟨3059834178467830706659277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2039889452311887137772851 3059834178467830706659277)
            ·
              refine ⟨1147437816925436514997229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3059834178467830706659277 1147437816925436514997229)
              ·
                refine ⟨430289181347038693123961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1147437816925436514997229 430289181347038693123961)
                ·
                  refine ⟨322716886010279019842971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430289181347038693123961 322716886010279019842971)
                  ·
                    rfl

theorem cell20_707050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_707050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707050 prefixEnd_707050 := by exact prefixLift 707050
  have htrace : WordTrace (prefixWord ++ tailWord_707050) baseStart_707050 baseEnd_707050 := by
    simpa [prefixWord, tailWord_707050, baseEnd_707050] using wordTrace_append hprefix tailTrace_707050
  have hstable : (prefixWord ++ tailWord_707050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707050).length < 2 ^ (prefixWord ++ tailWord_707050).sum := by decide
  have hdescent : baseEnd_707050 < baseStart_707050 := by decide
  rcases family_descends (prefixWord ++ tailWord_707050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707123 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 3]
def baseStart_707123 : Nat := 118140960795 + 707123 * 2 ^ 59
def prefixEnd_707123 : Nat := 4983230072969 + 3 ^ 40 * 707123 * 2
def baseEnd_707123 : Nat := 322750205199415210409339

theorem tailTrace_707123 : CollatzResearch.WordTrace tailWord_707123 prefixEnd_707123 322750205199415210409339 := by
  unfold tailWord_707123
  simp only [CollatzResearch.WordTrace]
  refine ⟨25790894617221612838758023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17193929744814408559172015 25790894617221612838758023)
  ·
    refine ⟨38686341925832419258137035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25790894617221612838758023 38686341925832419258137035)
    ·
      refine ⟨58029512888748628887205553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38686341925832419258137035 58029512888748628887205553)
      ·
        refine ⟨43522134666561471665404165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58029512888748628887205553 43522134666561471665404165)
        ·
          refine ⟨8160400249980275937263281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43522134666561471665404165 8160400249980275937263281)
          ·
            refine ⟨6120300187485206952947461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8160400249980275937263281 6120300187485206952947461)
            ·
              refine ⟨1147556285153476303677649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6120300187485206952947461 1147556285153476303677649)
              ·
                refine ⟨860667213865107227758237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1147556285153476303677649 860667213865107227758237)
                ·
                  refine ⟨322750205199415210409339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860667213865107227758237 322750205199415210409339)
                  ·
                    rfl

theorem cell20_707123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 3].length) (baseStart_707123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707123 prefixEnd_707123 := by exact prefixLift 707123
  have htrace : WordTrace (prefixWord ++ tailWord_707123) baseStart_707123 baseEnd_707123 := by
    simpa [prefixWord, tailWord_707123, baseEnd_707123] using wordTrace_append hprefix tailTrace_707123
  have hstable : (prefixWord ++ tailWord_707123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707123).length < 2 ^ (prefixWord ++ tailWord_707123).sum := by decide
  have hdescent : baseEnd_707123 < baseStart_707123 := by decide
  rcases family_descends (prefixWord ++ tailWord_707123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707151 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 6]
def baseStart_707151 : Nat := 118140960795 + 707151 * 2 ^ 59
def prefixEnd_707151 : Nat := 4983230072969 + 3 ^ 40 * 707151 * 2
def baseEnd_707151 : Nat := 322762985162371557475891

theorem tailTrace_707151 : CollatzResearch.WordTrace tailWord_707151 prefixEnd_707151 322762985162371557475891 := by
  unfold tailWord_707151
  simp only [CollatzResearch.WordTrace]
  refine ⟨25791915861120173620777307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17194610574080115747184871 25791915861120173620777307)
  ·
    refine ⟨38687873791680260431165961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25791915861120173620777307 38687873791680260431165961)
    ·
      refine ⟨29015905343760195323374471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38687873791680260431165961 29015905343760195323374471)
      ·
        refine ⟨43523858015640292985061707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29015905343760195323374471 43523858015640292985061707)
        ·
          refine ⟨65285787023460439477592561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43523858015640292985061707 65285787023460439477592561)
          ·
            refine ⟨48964340267595329608194421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65285787023460439477592561 48964340267595329608194421)
            ·
              refine ⟨4590406900087062150768227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48964340267595329608194421 4590406900087062150768227)
              ·
                refine ⟨6885610350130593226152341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590406900087062150768227 6885610350130593226152341)
                ·
                  refine ⟨322762985162371557475891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6885610350130593226152341 322762985162371557475891)
                  ·
                    rfl

theorem cell20_707151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_707151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707151 prefixEnd_707151 := by exact prefixLift 707151
  have htrace : WordTrace (prefixWord ++ tailWord_707151) baseStart_707151 baseEnd_707151 := by
    simpa [prefixWord, tailWord_707151, baseEnd_707151] using wordTrace_append hprefix tailTrace_707151
  have hstable : (prefixWord ++ tailWord_707151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707151).length < 2 ^ (prefixWord ++ tailWord_707151).sum := by decide
  have hdescent : baseEnd_707151 < baseStart_707151 := by decide
  rcases family_descends (prefixWord ++ tailWord_707151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707154 : List Nat := [3, 2, 2, 1, 2, 1, 5, 4]
def baseStart_707154 : Nat := 118140960795 + 707154 * 2 ^ 59
def prefixEnd_707154 : Nat := 4983230072969 + 3 ^ 40 * 707154 * 2
def baseEnd_707154 : Nat := 107588118148038960125293

theorem tailTrace_707154 : CollatzResearch.WordTrace tailWord_707154 prefixEnd_707154 107588118148038960125293 := by
  unfold tailWord_707154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6448006320027326283284129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17194683520072870088757677 6448006320027326283284129)
  ·
    refine ⟨4836004740020494712463097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6448006320027326283284129 4836004740020494712463097)
    ·
      refine ⟨3627003555015371034347323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4836004740020494712463097 3627003555015371034347323)
      ·
        refine ⟨5440505332523056551520985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3627003555015371034347323 5440505332523056551520985)
        ·
          refine ⟨4080378999392292413640739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5440505332523056551520985 4080378999392292413640739)
          ·
            refine ⟨6120568499088438620461109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4080378999392292413640739 6120568499088438620461109)
            ·
              refine ⟨573803296789541120668229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6120568499088438620461109 573803296789541120668229)
              ·
                refine ⟨107588118148038960125293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 573803296789541120668229 107588118148038960125293)
                ·
                  rfl

theorem cell20_707154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_707154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707154 prefixEnd_707154 := by exact prefixLift 707154
  have htrace : WordTrace (prefixWord ++ tailWord_707154) baseStart_707154 baseEnd_707154 := by
    simpa [prefixWord, tailWord_707154, baseEnd_707154] using wordTrace_append hprefix tailTrace_707154
  have hstable : (prefixWord ++ tailWord_707154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707154).length < 2 ^ (prefixWord ++ tailWord_707154).sum := by decide
  have hdescent : baseEnd_707154 < baseStart_707154 := by decide
  rcases family_descends (prefixWord ++ tailWord_707154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707251 : List Nat := [1, 1, 1, 2, 3, 5, 2, 5]
def baseStart_707251 : Nat := 118140960795 + 707251 * 2 ^ 59
def prefixEnd_707251 : Nat := 4983230072969 + 3 ^ 40 * 707251 * 2
def baseEnd_707251 : Nat := 107602875962405218047383

theorem tailTrace_707251 : CollatzResearch.WordTrace tailWord_707251 prefixEnd_707251 107602875962405218047383 := by
  unfold tailWord_707251
  simp only [CollatzResearch.WordTrace]
  refine ⟨25795563160757890699417607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17197042107171927132945071 25795563160757890699417607)
  ·
    refine ⟨38693344741136836049126411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25795563160757890699417607 38693344741136836049126411)
    ·
      refine ⟨58040017111705254073689617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38693344741136836049126411 58040017111705254073689617)
      ·
        refine ⟨43530012833778940555267213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58040017111705254073689617 43530012833778940555267213)
        ·
          refine ⟨16323754812667102708225205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43530012833778940555267213 16323754812667102708225205)
          ·
            refine ⟨1530352013687540878896113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16323754812667102708225205 1530352013687540878896113)
            ·
              refine ⟨1147764010265655659172085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530352013687540878896113 1147764010265655659172085)
              ·
                refine ⟨107602875962405218047383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1147764010265655659172085 107602875962405218047383)
                ·
                  rfl

theorem cell20_707251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_707251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707251 prefixEnd_707251 := by exact prefixLift 707251
  have htrace : WordTrace (prefixWord ++ tailWord_707251) baseStart_707251 baseEnd_707251 := by
    simpa [prefixWord, tailWord_707251, baseEnd_707251] using wordTrace_append hprefix tailTrace_707251
  have hstable : (prefixWord ++ tailWord_707251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707251).length < 2 ^ (prefixWord ++ tailWord_707251).sum := by decide
  have hdescent : baseEnd_707251 < baseStart_707251 := by decide
  rcases family_descends (prefixWord ++ tailWord_707251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707292 : List Nat := [2, 2, 5, 1, 1, 1, 1, 4, 3]
def baseStart_707292 : Nat := 118140960795 + 707292 * 2 ^ 59
def prefixEnd_707292 : Nat := 4983230072969 + 3 ^ 40 * 707292 * 2
def baseEnd_707292 : Nat := 322827341404401733775315

theorem tailTrace_707292 : CollatzResearch.WordTrace tailWord_707292 prefixEnd_707292 322827341404401733775315 := by
  unfold tailWord_707292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12898529276804677350830065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17198039035739569801106753 12898529276804677350830065)
  ·
    refine ⟨9673896957603508013122549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12898529276804677350830065 9673896957603508013122549)
    ·
      refine ⟨906927839775328876230239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9673896957603508013122549 906927839775328876230239)
      ·
        refine ⟨1360391759662993314345359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 906927839775328876230239 1360391759662993314345359)
        ·
          refine ⟨2040587639494489971518039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360391759662993314345359 2040587639494489971518039)
          ·
            refine ⟨3060881459241734957277059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040587639494489971518039 3060881459241734957277059)
            ·
              refine ⟨4591322188862602435915589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060881459241734957277059 4591322188862602435915589)
              ·
                refine ⟨860872910411737956734173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4591322188862602435915589 860872910411737956734173)
                ·
                  refine ⟨322827341404401733775315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860872910411737956734173 322827341404401733775315)
                  ·
                    rfl

theorem cell20_707292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_707292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707292 prefixEnd_707292 := by exact prefixLift 707292
  have htrace : WordTrace (prefixWord ++ tailWord_707292) baseStart_707292 baseEnd_707292 := by
    simpa [prefixWord, tailWord_707292, baseEnd_707292] using wordTrace_append hprefix tailTrace_707292
  have hstable : (prefixWord ++ tailWord_707292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707292).length < 2 ^ (prefixWord ++ tailWord_707292).sum := by decide
  have hdescent : baseEnd_707292 < baseStart_707292 := by decide
  rcases family_descends (prefixWord ++ tailWord_707292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707351 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 5]
def baseStart_707351 : Nat := 118140960795 + 707351 * 2 ^ 59
def prefixEnd_707351 : Nat := 4983230072969 + 3 ^ 40 * 707351 * 2
def baseEnd_707351 : Nat := 322854270612059750808407

theorem tailTrace_707351 : CollatzResearch.WordTrace tailWord_707351 prefixEnd_707351 322854270612059750808407 := by
  unfold tailWord_707351
  simp only [CollatzResearch.WordTrace]
  refine ⟨25799210460395607778057907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17199473640263738518705271 25799210460395607778057907)
  ·
    refine ⟨38698815690593411667086861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25799210460395607778057907 38698815690593411667086861)
    ·
      refine ⟨14512055883972529375157573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38698815690593411667086861 14512055883972529375157573)
      ·
        refine ⟨2721010478244849257842045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14512055883972529375157573 2721010478244849257842045)
        ·
          refine ⟨1020378929341818471690767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2721010478244849257842045 1020378929341818471690767)
          ·
            refine ⟨1530568394012727707536151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020378929341818471690767 1530568394012727707536151)
            ·
              refine ⟨2295852591019091561304227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1530568394012727707536151 2295852591019091561304227)
              ·
                refine ⟨3443778886528637341956341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2295852591019091561304227 3443778886528637341956341)
                ·
                  refine ⟨322854270612059750808407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3443778886528637341956341 322854270612059750808407)
                  ·
                    rfl

theorem cell20_707351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 5].length) (baseStart_707351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707351 prefixEnd_707351 := by exact prefixLift 707351
  have htrace : WordTrace (prefixWord ++ tailWord_707351) baseStart_707351 baseEnd_707351 := by
    simpa [prefixWord, tailWord_707351, baseEnd_707351] using wordTrace_append hprefix tailTrace_707351
  have hstable : (prefixWord ++ tailWord_707351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707351).length < 2 ^ (prefixWord ++ tailWord_707351).sum := by decide
  have hdescent : baseEnd_707351 < baseStart_707351 := by decide
  rcases family_descends (prefixWord ++ tailWord_707351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707368 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 3]
def baseStart_707368 : Nat := 118140960795 + 707368 * 2 ^ 59
def prefixEnd_707368 : Nat := 4983230072969 + 3 ^ 40 * 707368 * 2
def baseEnd_707368 : Nat := 322862029875283247241671

theorem tailTrace_707368 : CollatzResearch.WordTrace tailWord_707368 prefixEnd_707368 322862029875283247241671 := by
  unfold tailWord_707368
  simp only [CollatzResearch.WordTrace]
  refine ⟨12899915250667009840713379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17199887000889346454284505 12899915250667009840713379)
  ·
    refine ⟨19349872876000514761070069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12899915250667009840713379 19349872876000514761070069)
    ·
      refine ⟨1814050582125048258850319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19349872876000514761070069 1814050582125048258850319)
      ·
        refine ⟨2721075873187572388275479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814050582125048258850319 2721075873187572388275479)
        ·
          refine ⟨4081613809781358582413219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2721075873187572388275479 4081613809781358582413219)
          ·
            refine ⟨6122420714672037873619829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4081613809781358582413219 6122420714672037873619829)
            ·
              refine ⟨573976942000503550651859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6122420714672037873619829 573976942000503550651859)
              ·
                refine ⟨860965413000755325977789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573976942000503550651859 860965413000755325977789)
                ·
                  refine ⟨322862029875283247241671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 860965413000755325977789 322862029875283247241671)
                  ·
                    rfl

theorem cell20_707368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_707368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707368 prefixEnd_707368 := by exact prefixLift 707368
  have htrace : WordTrace (prefixWord ++ tailWord_707368) baseStart_707368 baseEnd_707368 := by
    simpa [prefixWord, tailWord_707368, baseEnd_707368] using wordTrace_append hprefix tailTrace_707368
  have hstable : (prefixWord ++ tailWord_707368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707368).length < 2 ^ (prefixWord ++ tailWord_707368).sum := by decide
  have hdescent : baseEnd_707368 < baseStart_707368 := by decide
  rcases family_descends (prefixWord ++ tailWord_707368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707410 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_707410 : Nat := 118140960795 + 707410 * 2 ^ 59
def prefixEnd_707410 : Nat := 4983230072969 + 3 ^ 40 * 707410 * 2
def baseEnd_707410 : Nat := 322881199819717767841499

theorem tailTrace_707410 : CollatzResearch.WordTrace tailWord_707410 prefixEnd_707410 322881199819717767841499 := by
  unfold tailWord_707410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6450340591795465213613921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17200908244787907236303789 6450340591795465213613921)
  ·
    refine ⟨4837755443846598910210441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6450340591795465213613921 4837755443846598910210441)
    ·
      refine ⟨3628316582884949182657831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4837755443846598910210441 3628316582884949182657831)
      ·
        refine ⟨5442474874327423773986747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3628316582884949182657831 5442474874327423773986747)
        ·
          refine ⟨8163712311491135660980121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5442474874327423773986747 8163712311491135660980121)
          ·
            refine ⟨6122784233618351745735091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8163712311491135660980121 6122784233618351745735091)
            ·
              refine ⟨9184176350427527618602637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6122784233618351745735091 9184176350427527618602637)
              ·
                refine ⟨3444066131410322856975989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9184176350427527618602637 3444066131410322856975989)
                ·
                  refine ⟨322881199819717767841499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3444066131410322856975989 322881199819717767841499)
                  ·
                    rfl

theorem cell20_707410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_707410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707410 prefixEnd_707410 := by exact prefixLift 707410
  have htrace : WordTrace (prefixWord ++ tailWord_707410) baseStart_707410 baseEnd_707410 := by
    simpa [prefixWord, tailWord_707410, baseEnd_707410] using wordTrace_append hprefix tailTrace_707410
  have hstable : (prefixWord ++ tailWord_707410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707410).length < 2 ^ (prefixWord ++ tailWord_707410).sum := by decide
  have hdescent : baseEnd_707410 < baseStart_707410 := by decide
  rcases family_descends (prefixWord ++ tailWord_707410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707420 : List Nat := [2, 2, 4, 2, 1, 2, 2, 5]
def baseStart_707420 : Nat := 118140960795 + 707420 * 2 ^ 59
def prefixEnd_707420 : Nat := 4983230072969 + 3 ^ 40 * 707420 * 2
def baseEnd_707420 : Nat := 107628588030734059169375

theorem tailTrace_707420 : CollatzResearch.WordTrace tailWord_707420 prefixEnd_707420 107628588030734059169375 := by
  unfold tailWord_707420
  simp only [CollatzResearch.WordTrace]
  refine ⟨12900863548572816281159857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17201151398097088374879809 12900863548572816281159857)
  ·
    refine ⟨9675647661429612210869893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12900863548572816281159857 9675647661429612210869893)
    ·
      refine ⟨1814183936518052289538105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9675647661429612210869893 1814183936518052289538105)
      ·
        refine ⟨1360637952388539217153579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1814183936518052289538105 1360637952388539217153579)
        ·
          refine ⟨2040956928582808825730369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360637952388539217153579 2040956928582808825730369)
          ·
            refine ⟨1530717696437106619297777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2040956928582808825730369 1530717696437106619297777)
            ·
              refine ⟨1148038272327829964473333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530717696437106619297777 1148038272327829964473333)
              ·
                refine ⟨107628588030734059169375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1148038272327829964473333 107628588030734059169375)
                ·
                  rfl

theorem cell20_707420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_707420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707420 prefixEnd_707420 := by exact prefixLift 707420
  have htrace : WordTrace (prefixWord ++ tailWord_707420) baseStart_707420 baseEnd_707420 := by
    simpa [prefixWord, tailWord_707420, baseEnd_707420] using wordTrace_append hprefix tailTrace_707420
  have hstable : (prefixWord ++ tailWord_707420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707420).length < 2 ^ (prefixWord ++ tailWord_707420).sum := by decide
  have hdescent : baseEnd_707420 < baseStart_707420 := by decide
  rcases family_descends (prefixWord ++ tailWord_707420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707427 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 3]
def baseStart_707427 : Nat := 118140960795 + 707427 * 2 ^ 59
def prefixEnd_707427 : Nat := 4983230072969 + 3 ^ 40 * 707427 * 2
def baseEnd_707427 : Nat := 322888959082941264274763

theorem tailTrace_707427 : CollatzResearch.WordTrace tailWord_707427 prefixEnd_707427 322888959082941264274763 := by
  unfold tailWord_707427
  simp only [CollatzResearch.WordTrace]
  refine ⟨25801982408120272757824535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17201321605413515171883023 25801982408120272757824535)
  ·
    refine ⟨38702973612180409136736803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25801982408120272757824535 38702973612180409136736803)
    ·
      refine ⟨58054460418270613705105205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38702973612180409136736803 58054460418270613705105205)
      ·
        refine ⟨5442605664212870034853613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58054460418270613705105205 5442605664212870034853613)
        ·
          refine ⟨2040977124079826263070105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5442605664212870034853613 2040977124079826263070105)
          ·
            refine ⟨1530732843059869697302579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2040977124079826263070105 1530732843059869697302579)
            ·
              refine ⟨2296099264589804545953869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1530732843059869697302579 2296099264589804545953869)
              ·
                refine ⟨861037224221176704732701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2296099264589804545953869 861037224221176704732701)
                ·
                  refine ⟨322888959082941264274763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861037224221176704732701 322888959082941264274763)
                  ·
                    rfl

theorem cell20_707427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 3].length) (baseStart_707427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707427 prefixEnd_707427 := by exact prefixLift 707427
  have htrace : WordTrace (prefixWord ++ tailWord_707427) baseStart_707427 baseEnd_707427 := by
    simpa [prefixWord, tailWord_707427, baseEnd_707427] using wordTrace_append hprefix tailTrace_707427
  have hstable : (prefixWord ++ tailWord_707427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707427).length < 2 ^ (prefixWord ++ tailWord_707427).sum := by decide
  have hdescent : baseEnd_707427 < baseStart_707427 := by decide
  rcases family_descends (prefixWord ++ tailWord_707427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707458 : List Nat := [3, 4, 2, 2, 9]
def baseStart_707458 : Nat := 118140960795 + 707458 * 2 ^ 59
def prefixEnd_707458 : Nat := 4983230072969 + 3 ^ 40 * 707458 * 2
def baseEnd_707458 : Nat := 3986458127501764620263

theorem tailTrace_707458 : CollatzResearch.WordTrace tailWord_707458 prefixEnd_707458 3986458127501764620263 := by
  unfold tailWord_707458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6450778267751991263050757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17202075380671976701468685 6450778267751991263050757)
  ·
    refine ⟨1209520925203498361822017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6450778267751991263050757 1209520925203498361822017)
    ·
      refine ⟨907140693902623771366513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1209520925203498361822017 907140693902623771366513)
      ·
        refine ⟨680355520426967828524885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 907140693902623771366513 680355520426967828524885)
        ·
          refine ⟨3986458127501764620263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 680355520426967828524885 3986458127501764620263)
          ·
            rfl

theorem cell20_707458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 9].length) (baseStart_707458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707458 prefixEnd_707458 := by exact prefixLift 707458
  have htrace : WordTrace (prefixWord ++ tailWord_707458) baseStart_707458 baseEnd_707458 := by
    simpa [prefixWord, tailWord_707458, baseEnd_707458] using wordTrace_append hprefix tailTrace_707458
  have hstable : (prefixWord ++ tailWord_707458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707458).length < 2 ^ (prefixWord ++ tailWord_707458).sum := by decide
  have hdescent : baseEnd_707458 < baseStart_707458 := by decide
  rcases family_descends (prefixWord ++ tailWord_707458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707465 : List Nat := [1, 2, 1, 1, 5, 3, 2, 2, 3]
def baseStart_707465 : Nat := 118140960795 + 707465 * 2 ^ 59
def prefixEnd_707465 : Nat := 4983230072969 + 3 ^ 40 * 707465 * 2
def baseEnd_707465 : Nat := 322906303318382021007941

theorem tailTrace_707465 : CollatzResearch.WordTrace tailWord_707465 prefixEnd_707465 322906303318382021007941 := by
  unfold tailWord_707465
  simp only [CollatzResearch.WordTrace]
  refine ⟨25803368381982605247707849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17202245587988403498471899 25803368381982605247707849)
  ·
    refine ⟨19352526286486953935780887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25803368381982605247707849 19352526286486953935780887)
    ·
      refine ⟨29028789429730430903671331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19352526286486953935780887 29028789429730430903671331)
      ·
        refine ⟨43543184144595646355506997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29028789429730430903671331 43543184144595646355506997)
        ·
          refine ⟨4082173513555841845828781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43543184144595646355506997 4082173513555841845828781)
          ·
            refine ⟨1530815067583440692185793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4082173513555841845828781 1530815067583440692185793)
            ·
              refine ⟨1148111300687580519139345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1530815067583440692185793 1148111300687580519139345)
              ·
                refine ⟨861083475515685389354509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148111300687580519139345 861083475515685389354509)
                ·
                  refine ⟨322906303318382021007941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861083475515685389354509 322906303318382021007941)
                  ·
                    rfl

theorem cell20_707465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_707465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707465 prefixEnd_707465 := by exact prefixLift 707465
  have htrace : WordTrace (prefixWord ++ tailWord_707465) baseStart_707465 baseEnd_707465 := by
    simpa [prefixWord, tailWord_707465, baseEnd_707465] using wordTrace_append hprefix tailTrace_707465
  have hstable : (prefixWord ++ tailWord_707465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707465).length < 2 ^ (prefixWord ++ tailWord_707465).sum := by decide
  have hdescent : baseEnd_707465 < baseStart_707465 := by decide
  rcases family_descends (prefixWord ++ tailWord_707465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707517 : List Nat := [1, 4, 1, 2, 4, 1, 7]
def baseStart_707517 : Nat := 118140960795 + 707517 * 2 ^ 59
def prefixEnd_707517 : Nat := 4983230072969 + 3 ^ 40 * 707517 * 2
def baseEnd_707517 : Nat := 35881115281700105697155

theorem tailTrace_707517 : CollatzResearch.WordTrace tailWord_707517 prefixEnd_707517 35881115281700105697155 := by
  unfold tailWord_707517
  simp only [CollatzResearch.WordTrace]
  refine ⟨25805264977794218128600805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17203509985196145419067203 25805264977794218128600805)
  ·
    refine ⟨4838487183336415899112651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25805264977794218128600805 4838487183336415899112651)
    ·
      refine ⟨7257730775004623848668977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4838487183336415899112651 7257730775004623848668977)
      ·
        refine ⟨5443298081253467886501733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7257730775004623848668977 5443298081253467886501733)
        ·
          refine ⟨1020618390235025228719075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5443298081253467886501733 1020618390235025228719075)
          ·
            refine ⟨1530927585352537843078613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020618390235025228719075 1530927585352537843078613)
            ·
              refine ⟨35881115281700105697155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1530927585352537843078613 35881115281700105697155)
              ·
                rfl

theorem cell20_707517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 7].length) (baseStart_707517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707517 prefixEnd_707517 := by exact prefixLift 707517
  have htrace : WordTrace (prefixWord ++ tailWord_707517) baseStart_707517 baseEnd_707517 := by
    simpa [prefixWord, tailWord_707517, baseEnd_707517] using wordTrace_append hprefix tailTrace_707517
  have hstable : (prefixWord ++ tailWord_707517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707517).length < 2 ^ (prefixWord ++ tailWord_707517).sum := by decide
  have hdescent : baseEnd_707517 < baseStart_707517 := by decide
  rcases family_descends (prefixWord ++ tailWord_707517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707531 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 4]
def baseStart_707531 : Nat := 118140960795 + 707531 * 2 ^ 59
def prefixEnd_707531 : Nat := 4983230072969 + 3 ^ 40 * 707531 * 2
def baseEnd_707531 : Nat := 322936427516779124807671

theorem tailTrace_707531 : CollatzResearch.WordTrace tailWord_707531 prefixEnd_707531 322936427516779124807671 := by
  unfold tailWord_707531
  simp only [CollatzResearch.WordTrace]
  refine ⟨25805775599743498519610447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17203850399828999013073631 25805775599743498519610447)
  ·
    refine ⟨38708663399615247779415671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25805775599743498519610447 38708663399615247779415671)
    ·
      refine ⟨58062995099422871669123507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38708663399615247779415671 58062995099422871669123507)
      ·
        refine ⟨87094492649134307503685261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58062995099422871669123507 87094492649134307503685261)
        ·
          refine ⟨32660434743425365313881973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87094492649134307503685261 32660434743425365313881973)
          ·
            refine ⟨3061915757196127998176435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32660434743425365313881973 3061915757196127998176435)
            ·
              refine ⟨4592873635794191997264653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061915757196127998176435 4592873635794191997264653)
              ·
                refine ⟨1722327613422821998974245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4592873635794191997264653 1722327613422821998974245)
                ·
                  refine ⟨322936427516779124807671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1722327613422821998974245 322936427516779124807671)
                  ·
                    rfl

theorem cell20_707531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_707531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707531 prefixEnd_707531 := by exact prefixLift 707531
  have htrace : WordTrace (prefixWord ++ tailWord_707531) baseStart_707531 baseEnd_707531 := by
    simpa [prefixWord, tailWord_707531, baseEnd_707531] using wordTrace_append hprefix tailTrace_707531
  have hstable : (prefixWord ++ tailWord_707531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707531).length < 2 ^ (prefixWord ++ tailWord_707531).sum := by decide
  have hdescent : baseEnd_707531 < baseStart_707531 := by decide
  rcases family_descends (prefixWord ++ tailWord_707531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707533 : List Nat := [1, 6, 3, 1, 1, 1, 3, 1, 3]
def baseStart_707533 : Nat := 118140960795 + 707533 * 2 ^ 59
def prefixEnd_707533 : Nat := 4983230072969 + 3 ^ 40 * 707533 * 2
def baseEnd_707533 : Nat := 322937340371276006740997

theorem tailTrace_707533 : CollatzResearch.WordTrace tailWord_707533 prefixEnd_707533 322937340371276006740997 := by
  unfold tailWord_707533
  simp only [CollatzResearch.WordTrace]
  refine ⟨25805848545736252861183253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17203899030490835240788835 25805848545736252861183253)
  ·
    refine ⟨1209649150581386852867965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25805848545736252861183253 1209649150581386852867965)
    ·
      refine ⟨453618431468020069825487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1209649150581386852867965 453618431468020069825487)
      ·
        refine ⟨680427647202030104738231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453618431468020069825487 680427647202030104738231)
        ·
          refine ⟨1020641470803045157107347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680427647202030104738231 1020641470803045157107347)
          ·
            refine ⟨1530962206204567735661021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1020641470803045157107347 1530962206204567735661021)
            ·
              refine ⟨574110827326712900872883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1530962206204567735661021 574110827326712900872883)
              ·
                refine ⟨861166240990069351309325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574110827326712900872883 861166240990069351309325)
                ·
                  refine ⟨322937340371276006740997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861166240990069351309325 322937340371276006740997)
                  ·
                    rfl

theorem cell20_707533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_707533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707533 prefixEnd_707533 := by exact prefixLift 707533
  have htrace : WordTrace (prefixWord ++ tailWord_707533) baseStart_707533 baseEnd_707533 := by
    simpa [prefixWord, tailWord_707533, baseEnd_707533] using wordTrace_append hprefix tailTrace_707533
  have hstable : (prefixWord ++ tailWord_707533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707533).length < 2 ^ (prefixWord ++ tailWord_707533).sum := by decide
  have hdescent : baseEnd_707533 < baseStart_707533 := by decide
  rcases family_descends (prefixWord ++ tailWord_707533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707551 : List Nat := [1, 1, 2, 3, 6, 1, 2, 4]
def baseStart_707551 : Nat := 118140960795 + 707551 * 2 ^ 59
def prefixEnd_707551 : Nat := 4983230072969 + 3 ^ 40 * 707551 * 2
def baseEnd_707551 : Nat := 107648518687249314713641

theorem tailTrace_707551 : CollatzResearch.WordTrace tailWord_707551 prefixEnd_707551 107648518687249314713641 := by
  unfold tailWord_707551
  simp only [CollatzResearch.WordTrace]
  refine ⟨25806505059671041935338507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17204336706447361290225671 25806505059671041935338507)
  ·
    refine ⟨38709757589506562903007761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25806505059671041935338507 38709757589506562903007761)
    ·
      refine ⟨29032318192129922177255821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38709757589506562903007761 29032318192129922177255821)
      ·
        refine ⟨10887119322048720816470933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29032318192129922177255821 10887119322048720816470933)
        ·
          refine ⟨510333718221033788272075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10887119322048720816470933 510333718221033788272075)
          ·
            refine ⟨765500577331550682408113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510333718221033788272075 765500577331550682408113)
            ·
              refine ⟨574125432998663011806085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765500577331550682408113 574125432998663011806085)
              ·
                refine ⟨107648518687249314713641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 574125432998663011806085 107648518687249314713641)
                ·
                  rfl

theorem cell20_707551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 4].length) (baseStart_707551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707551 prefixEnd_707551 := by exact prefixLift 707551
  have htrace : WordTrace (prefixWord ++ tailWord_707551) baseStart_707551 baseEnd_707551 := by
    simpa [prefixWord, tailWord_707551, baseEnd_707551] using wordTrace_append hprefix tailTrace_707551
  have hstable : (prefixWord ++ tailWord_707551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707551).length < 2 ^ (prefixWord ++ tailWord_707551).sum := by decide
  have hdescent : baseEnd_707551 < baseStart_707551 := by decide
  rcases family_descends (prefixWord ++ tailWord_707551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707562 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_707562 : Nat := 118140960795 + 707562 * 2 ^ 59
def prefixEnd_707562 : Nat := 4983230072969 + 3 ^ 40 * 707562 * 2
def baseEnd_707562 : Nat := 322950576761480794774211

theorem tailTrace_707562 : CollatzResearch.WordTrace tailWord_707562 prefixEnd_707562 322950576761480794774211 := by
  unfold tailWord_707562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6451726565657797703497235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17204604175087460542659293 6451726565657797703497235)
  ·
    refine ⟨9677589848486696555245853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6451726565657797703497235 9677589848486696555245853)
    ·
      refine ⟨3629096193182511208217195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9677589848486696555245853 3629096193182511208217195)
      ·
        refine ⟨5443644289773766812325793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3629096193182511208217195 5443644289773766812325793)
        ·
          refine ⟨4082733217330325109244345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5443644289773766812325793 4082733217330325109244345)
          ·
            refine ⟨3062049912997743831933259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4082733217330325109244345 3062049912997743831933259)
            ·
              refine ⟨4593074869496615747899889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3062049912997743831933259 4593074869496615747899889)
              ·
                refine ⟨3444806152122461810924917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4593074869496615747899889 3444806152122461810924917)
                ·
                  refine ⟨322950576761480794774211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3444806152122461810924917 322950576761480794774211)
                  ·
                    rfl

theorem cell20_707562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_707562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707562 prefixEnd_707562 := by exact prefixLift 707562
  have htrace : WordTrace (prefixWord ++ tailWord_707562) baseStart_707562 baseEnd_707562 := by
    simpa [prefixWord, tailWord_707562, baseEnd_707562] using wordTrace_append hprefix tailTrace_707562
  have hstable : (prefixWord ++ tailWord_707562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707562).length < 2 ^ (prefixWord ++ tailWord_707562).sum := by decide
  have hdescent : baseEnd_707562 < baseStart_707562 := by decide
  rcases family_descends (prefixWord ++ tailWord_707562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707582 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_707582 : Nat := 118140960795 + 707582 * 2 ^ 59
def prefixEnd_707582 : Nat := 4983230072969 + 3 ^ 40 * 707582 * 2
def baseEnd_707582 : Nat := 322959705306449614107463

theorem tailTrace_707582 : CollatzResearch.WordTrace tailWord_707582 prefixEnd_707582 322959705306449614107463 := by
  unfold tailWord_707582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225954465319841778714625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17205090481705822819811333 3225954465319841778714625)
  ·
    refine ⟨2419465848989881334035969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3225954465319841778714625 2419465848989881334035969)
    ·
      refine ⟨1814599386742411000526977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2419465848989881334035969 1814599386742411000526977)
      ·
        refine ⟨1360949540056808250395233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1814599386742411000526977 1360949540056808250395233)
        ·
          refine ⟨1020712155042606187796425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1360949540056808250395233 1020712155042606187796425)
          ·
            refine ⟨765534116281954640847319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1020712155042606187796425 765534116281954640847319)
            ·
              refine ⟨1148301174422931961270979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765534116281954640847319 1148301174422931961270979)
              ·
                refine ⟨1722451761634397941906469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148301174422931961270979 1722451761634397941906469)
                ·
                  refine ⟨322959705306449614107463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1722451761634397941906469 322959705306449614107463)
                  ·
                    rfl

theorem cell20_707582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_707582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707582 prefixEnd_707582 := by exact prefixLift 707582
  have htrace : WordTrace (prefixWord ++ tailWord_707582) baseStart_707582 baseEnd_707582 := by
    simpa [prefixWord, tailWord_707582, baseEnd_707582] using wordTrace_append hprefix tailTrace_707582
  have hstable : (prefixWord ++ tailWord_707582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707582).length < 2 ^ (prefixWord ++ tailWord_707582).sum := by decide
  have hdescent : baseEnd_707582 < baseStart_707582 := by decide
  rcases family_descends (prefixWord ++ tailWord_707582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707596 : List Nat := [2, 2, 1, 2, 3, 4, 2, 1, 3]
def baseStart_707596 : Nat := 118140960795 + 707596 * 2 ^ 59
def prefixEnd_707596 : Nat := 4983230072969 + 3 ^ 40 * 707596 * 2
def baseEnd_707596 : Nat := 322966095287927787640739

theorem tailTrace_707596 : CollatzResearch.WordTrace tailWord_707596 prefixEnd_707596 322966095287927787640739 := by
  unfold tailWord_707596
  simp only [CollatzResearch.WordTrace]
  refine ⟨12904073172254007310363321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17205430896338676413817761 12904073172254007310363321)
  ·
    refine ⟨9678054879190505482772491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12904073172254007310363321 9678054879190505482772491)
    ·
      refine ⟨14517082318785758224158737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9678054879190505482772491 14517082318785758224158737)
      ·
        refine ⟨10887811739089318668119053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14517082318785758224158737 10887811739089318668119053)
        ·
          refine ⟨4082929402158494500544645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10887811739089318668119053 4082929402158494500544645)
          ·
            refine ⟨765549262904717718852121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4082929402158494500544645 765549262904717718852121)
            ·
              refine ⟨574161947178538289139091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765549262904717718852121 574161947178538289139091)
              ·
                refine ⟨861242920767807433708637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574161947178538289139091 861242920767807433708637)
                ·
                  refine ⟨322966095287927787640739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861242920767807433708637 322966095287927787640739)
                  ·
                    rfl

theorem cell20_707596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_707596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707596 prefixEnd_707596 := by exact prefixLift 707596
  have htrace : WordTrace (prefixWord ++ tailWord_707596) baseStart_707596 baseEnd_707596 := by
    simpa [prefixWord, tailWord_707596, baseEnd_707596] using wordTrace_append hprefix tailTrace_707596
  have hstable : (prefixWord ++ tailWord_707596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707596).length < 2 ^ (prefixWord ++ tailWord_707596).sum := by decide
  have hdescent : baseEnd_707596 < baseStart_707596 := by decide
  rcases family_descends (prefixWord ++ tailWord_707596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707641 : List Nat := [1, 2, 1, 5, 2, 2, 1, 4, 2]
def baseStart_707641 : Nat := 118140960795 + 707641 * 2 ^ 59
def prefixEnd_707641 : Nat := 4983230072969 + 3 ^ 40 * 707641 * 2
def baseEnd_707641 : Nat := 322986634514107631140555

theorem tailTrace_707641 : CollatzResearch.WordTrace tailWord_707641 prefixEnd_707641 322986634514107631140555 := by
  unfold tailWord_707641
  simp only [CollatzResearch.WordTrace]
  refine ⟨25809787629344987306114777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17206525086229991537409851 25809787629344987306114777)
  ·
    refine ⟨19357340722008740479586083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25809787629344987306114777 19357340722008740479586083)
    ·
      refine ⟨29036011083013110719379125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19357340722008740479586083 29036011083013110719379125)
      ·
        refine ⟨2722126039032479129941793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29036011083013110719379125 2722126039032479129941793)
        ·
          refine ⟨2041594529274359347456345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2722126039032479129941793 2041594529274359347456345)
          ·
            refine ⟨1531195896955769510592259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2041594529274359347456345 1531195896955769510592259)
            ·
              refine ⟨2296793845433654265888389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531195896955769510592259 2296793845433654265888389)
              ·
                refine ⟨430648846018810174854073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2296793845433654265888389 430648846018810174854073)
                ·
                  refine ⟨322986634514107631140555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430648846018810174854073 322986634514107631140555)
                  ·
                    rfl

theorem cell20_707641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 2].length) (baseStart_707641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707641 prefixEnd_707641 := by exact prefixLift 707641
  have htrace : WordTrace (prefixWord ++ tailWord_707641) baseStart_707641 baseEnd_707641 := by
    simpa [prefixWord, tailWord_707641, baseEnd_707641] using wordTrace_append hprefix tailTrace_707641
  have hstable : (prefixWord ++ tailWord_707641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707641).length < 2 ^ (prefixWord ++ tailWord_707641).sum := by decide
  have hdescent : baseEnd_707641 < baseStart_707641 := by decide
  rcases family_descends (prefixWord ++ tailWord_707641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707669 : List Nat := [1, 3, 2, 2, 1, 2, 5, 4]
def baseStart_707669 : Nat := 118140960795 + 707669 * 2 ^ 59
def prefixEnd_707669 : Nat := 4983230072969 + 3 ^ 40 * 707669 * 2
def baseEnd_707669 : Nat := 107666471492354659402369

theorem tailTrace_707669 : CollatzResearch.WordTrace tailWord_707669 prefixEnd_707669 107666471492354659402369 := by
  unfold tailWord_707669
  simp only [CollatzResearch.WordTrace]
  refine ⟨25810808873243548088134061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17207205915495698725422707 25810808873243548088134061)
  ·
    refine ⟨9679053327466330533050273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25810808873243548088134061 9679053327466330533050273)
    ·
      refine ⟨7259289995599747899787705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9679053327466330533050273 7259289995599747899787705)
      ·
        refine ⟨5444467496699810924840779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7259289995599747899787705 5444467496699810924840779)
        ·
          refine ⟨8166701245049716387261169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5444467496699810924840779 8166701245049716387261169)
          ·
            refine ⟨6125025933787287290445877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8166701245049716387261169 6125025933787287290445877)
            ·
              refine ⟨574221181292558183479301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6125025933787287290445877 574221181292558183479301)
              ·
                refine ⟨107666471492354659402369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 574221181292558183479301 107666471492354659402369)
                ·
                  rfl

theorem cell20_707669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 4].length) (baseStart_707669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707669 prefixEnd_707669 := by exact prefixLift 707669
  have htrace : WordTrace (prefixWord ++ tailWord_707669) baseStart_707669 baseEnd_707669 := by
    simpa [prefixWord, tailWord_707669, baseEnd_707669] using wordTrace_append hprefix tailTrace_707669
  have hstable : (prefixWord ++ tailWord_707669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707669).length < 2 ^ (prefixWord ++ tailWord_707669).sum := by decide
  have hdescent : baseEnd_707669 < baseStart_707669 := by decide
  rcases family_descends (prefixWord ++ tailWord_707669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707676 : List Nat := [2, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_707676 : Nat := 118140960795 + 707676 * 2 ^ 59
def prefixEnd_707676 : Nat := 4983230072969 + 3 ^ 40 * 707676 * 2
def baseEnd_707676 : Nat := 323002609467803064973745

theorem tailTrace_707676 : CollatzResearch.WordTrace tailWord_707676 prefixEnd_707676 323002609467803064973745 := by
  unfold tailWord_707676
  simp only [CollatzResearch.WordTrace]
  refine ⟨12905532092109094141819441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17207376122812125522425921 12905532092109094141819441)
  ·
    refine ⟨9679149069081820606364581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12905532092109094141819441 9679149069081820606364581)
    ·
      refine ⟨1814840450452841363693359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9679149069081820606364581 1814840450452841363693359)
      ·
        refine ⟨2722260675679262045540039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814840450452841363693359 2722260675679262045540039)
        ·
          refine ⟨4083391013518893068310059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722260675679262045540039 4083391013518893068310059)
          ·
            refine ⟨6125086520278339602465089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4083391013518893068310059 6125086520278339602465089)
            ·
              refine ⟨4593814890208754701848817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6125086520278339602465089 4593814890208754701848817)
              ·
                refine ⟨3445361167656566026386613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4593814890208754701848817 3445361167656566026386613)
                ·
                  refine ⟨323002609467803064973745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3445361167656566026386613 323002609467803064973745)
                  ·
                    rfl

theorem cell20_707676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_707676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707676 prefixEnd_707676 := by exact prefixLift 707676
  have htrace : WordTrace (prefixWord ++ tailWord_707676) baseStart_707676 baseEnd_707676 := by
    simpa [prefixWord, tailWord_707676, baseEnd_707676] using wordTrace_append hprefix tailTrace_707676
  have hstable : (prefixWord ++ tailWord_707676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707676).length < 2 ^ (prefixWord ++ tailWord_707676).sum := by decide
  have hdescent : baseEnd_707676 < baseStart_707676 := by decide
  rcases family_descends (prefixWord ++ tailWord_707676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707693 : List Nat := [1, 5, 1, 1, 2, 2, 3, 2, 3]
def baseStart_707693 : Nat := 118140960795 + 707693 * 2 ^ 59
def prefixEnd_707693 : Nat := 4983230072969 + 3 ^ 40 * 707693 * 2
def baseEnd_707693 : Nat := 323010368731026561407009

theorem tailTrace_707693 : CollatzResearch.WordTrace tailWord_707693 prefixEnd_707693 323010368731026561407009 := by
  unfold tailWord_707693
  simp only [CollatzResearch.WordTrace]
  refine ⟨25811684225156600187007733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17207789483437733458005155 25811684225156600187007733)
  ·
    refine ⟨2419845396108431267531975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25811684225156600187007733 2419845396108431267531975)
    ·
      refine ⟨3629768094162646901297963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2419845396108431267531975 3629768094162646901297963)
      ·
        refine ⟨5444652141243970351946945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3629768094162646901297963 5444652141243970351946945)
        ·
          refine ⟨4083489105932977763960209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5444652141243970351946945 4083489105932977763960209)
          ·
            refine ⟨3062616829449733322970157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4083489105932977763960209 3062616829449733322970157)
            ·
              refine ⟨1148481311043649996113809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3062616829449733322970157 1148481311043649996113809)
              ·
                refine ⟨861360983282737497085357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148481311043649996113809 861360983282737497085357)
                ·
                  refine ⟨323010368731026561407009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861360983282737497085357 323010368731026561407009)
                  ·
                    rfl

theorem cell20_707693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_707693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707693 prefixEnd_707693 := by exact prefixLift 707693
  have htrace : WordTrace (prefixWord ++ tailWord_707693) baseStart_707693 baseEnd_707693 := by
    simpa [prefixWord, tailWord_707693, baseEnd_707693] using wordTrace_append hprefix tailTrace_707693
  have hstable : (prefixWord ++ tailWord_707693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707693).length < 2 ^ (prefixWord ++ tailWord_707693).sum := by decide
  have hdescent : baseEnd_707693 < baseStart_707693 := by decide
  rcases family_descends (prefixWord ++ tailWord_707693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707721 : List Nat := [1, 2, 1, 1, 4, 3, 2, 2, 4]
def baseStart_707721 : Nat := 118140960795 + 707721 * 2 ^ 59
def prefixEnd_707721 : Nat := 4983230072969 + 3 ^ 40 * 707721 * 2
def baseEnd_707721 : Nat := 323023148693982908473561

theorem tailTrace_707721 : CollatzResearch.WordTrace tailWord_707721 prefixEnd_707721 323023148693982908473561 := by
  unfold tailWord_707721
  simp only [CollatzResearch.WordTrace]
  refine ⟨25812705469055160969027017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17208470312703440646018011 25812705469055160969027017)
  ·
    refine ⟨19359529101791370726770263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25812705469055160969027017 19359529101791370726770263)
    ·
      refine ⟨29039293652687056090155395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19359529101791370726770263 29039293652687056090155395)
      ·
        refine ⟨43558940479030584135233093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29039293652687056090155395 43558940479030584135233093)
        ·
          refine ⟨8167301339818234525356205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43558940479030584135233093 8167301339818234525356205)
          ·
            refine ⟨3062738002431837947008577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8167301339818234525356205 3062738002431837947008577)
            ·
              refine ⟨2297053501823878460256433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3062738002431837947008577 2297053501823878460256433)
              ·
                refine ⟨1722790126367908845192325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2297053501823878460256433 1722790126367908845192325)
                ·
                  refine ⟨323023148693982908473561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1722790126367908845192325 323023148693982908473561)
                  ·
                    rfl

theorem cell20_707721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_707721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707721 prefixEnd_707721 := by exact prefixLift 707721
  have htrace : WordTrace (prefixWord ++ tailWord_707721) baseStart_707721 baseEnd_707721 := by
    simpa [prefixWord, tailWord_707721, baseEnd_707721] using wordTrace_append hprefix tailTrace_707721
  have hstable : (prefixWord ++ tailWord_707721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707721).length < 2 ^ (prefixWord ++ tailWord_707721).sum := by decide
  have hdescent : baseEnd_707721 < baseStart_707721 := by decide
  rcases family_descends (prefixWord ++ tailWord_707721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707759 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 4]
def baseStart_707759 : Nat := 118140960795 + 707759 * 2 ^ 59
def prefixEnd_707759 : Nat := 4983230072969 + 3 ^ 40 * 707759 * 2
def baseEnd_707759 : Nat := 323040492929423665206739

theorem tailTrace_707759 : CollatzResearch.WordTrace tailWord_707759 prefixEnd_707759 323040492929423665206739 := by
  unfold tailWord_707759
  simp only [CollatzResearch.WordTrace]
  refine ⟨25814091442917493458910331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17209394295278328972606887 25814091442917493458910331)
  ·
    refine ⟨38721137164376240188365497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25814091442917493458910331 38721137164376240188365497)
    ·
      refine ⟨29040852873282180141274123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38721137164376240188365497 29040852873282180141274123)
      ·
        refine ⟨43561279309923270211911185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29040852873282180141274123 43561279309923270211911185)
        ·
          refine ⟨32670959482442452658933389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43561279309923270211911185 32670959482442452658933389)
          ·
            refine ⟨12251609805915919747100021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32670959482442452658933389 12251609805915919747100021)
            ·
              refine ⟨1148588419304617476290627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12251609805915919747100021 1148588419304617476290627)
              ·
                refine ⟨1722882628956926214435941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148588419304617476290627 1722882628956926214435941)
                ·
                  refine ⟨323040492929423665206739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1722882628956926214435941 323040492929423665206739)
                  ·
                    rfl

theorem cell20_707759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_707759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707759 prefixEnd_707759 := by exact prefixLift 707759
  have htrace : WordTrace (prefixWord ++ tailWord_707759) baseStart_707759 baseEnd_707759 := by
    simpa [prefixWord, tailWord_707759, baseEnd_707759] using wordTrace_append hprefix tailTrace_707759
  have hstable : (prefixWord ++ tailWord_707759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707759).length < 2 ^ (prefixWord ++ tailWord_707759).sum := by decide
  have hdescent : baseEnd_707759 < baseStart_707759 := by decide
  rcases family_descends (prefixWord ++ tailWord_707759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707769 : List Nat := [1, 2, 1, 4, 1, 3, 4, 1, 3]
def baseStart_707769 : Nat := 118140960795 + 707769 * 2 ^ 59
def prefixEnd_707769 : Nat := 4983230072969 + 3 ^ 40 * 707769 * 2
def baseEnd_707769 : Nat := 323045057201908074873365

theorem tailTrace_707769 : CollatzResearch.WordTrace tailWord_707769 prefixEnd_707769 323045057201908074873365 := by
  unfold tailWord_707769
  simp only [CollatzResearch.WordTrace]
  refine ⟨25814456172881265166774361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17209637448587510111182907 25814456172881265166774361)
  ·
    refine ⟨19360842129660948875080771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25814456172881265166774361 19360842129660948875080771)
    ·
      refine ⟨29041263194491423312621157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19360842129660948875080771 29041263194491423312621157)
      ·
        refine ⟨5445236848967141871116467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29041263194491423312621157 5445236848967141871116467)
        ·
          refine ⟨8167855273450712806674701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5445236848967141871116467 8167855273450712806674701)
          ·
            refine ⟨3062945727544017302503013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8167855273450712806674701 3062945727544017302503013)
            ·
              refine ⟨574302323914503244219315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3062945727544017302503013 574302323914503244219315)
              ·
                refine ⟨861453485871754866328973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574302323914503244219315 861453485871754866328973)
                ·
                  refine ⟨323045057201908074873365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861453485871754866328973 323045057201908074873365)
                  ·
                    rfl

theorem cell20_707769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 3].length) (baseStart_707769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707769 prefixEnd_707769 := by exact prefixLift 707769
  have htrace : WordTrace (prefixWord ++ tailWord_707769) baseStart_707769 baseEnd_707769 := by
    simpa [prefixWord, tailWord_707769, baseEnd_707769] using wordTrace_append hprefix tailTrace_707769
  have hstable : (prefixWord ++ tailWord_707769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707769).length < 2 ^ (prefixWord ++ tailWord_707769).sum := by decide
  have hdescent : baseEnd_707769 < baseStart_707769 := by decide
  rcases family_descends (prefixWord ++ tailWord_707769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707804 : List Nat := [2, 2, 5, 11]
def baseStart_707804 : Nat := 118140960795 + 707804 * 2 ^ 59
def prefixEnd_707804 : Nat := 4983230072969 + 3 ^ 40 * 707804 * 2
def baseEnd_707804 : Nat := 1329469268130055591385

theorem tailTrace_707804 : CollatzResearch.WordTrace tailWord_707804 prefixEnd_707804 1329469268130055591385 := by
  unfold tailWord_707804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12907866363877233072149233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17210488485169644096198977 12907866363877233072149233)
  ·
    refine ⟨9680899772907924804111925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12907866363877233072149233 9680899772907924804111925)
    ·
      refine ⟨907584353710117950385493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9680899772907924804111925 907584353710117950385493)
      ·
        refine ⟨1329469268130055591385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 907584353710117950385493 1329469268130055591385)
        ·
          rfl

theorem cell20_707804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 11].length) (baseStart_707804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707804 prefixEnd_707804 := by exact prefixLift 707804
  have htrace : WordTrace (prefixWord ++ tailWord_707804) baseStart_707804 baseEnd_707804 := by
    simpa [prefixWord, tailWord_707804, baseEnd_707804] using wordTrace_append hprefix tailTrace_707804
  have hstable : (prefixWord ++ tailWord_707804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707804).length < 2 ^ (prefixWord ++ tailWord_707804).sum := by decide
  have hdescent : baseEnd_707804 < baseStart_707804 := by decide
  rcases family_descends (prefixWord ++ tailWord_707804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707821 : List Nat := [1, 5, 1, 2, 2, 1, 3, 5]
def baseStart_707821 : Nat := 118140960795 + 707821 * 2 ^ 59
def prefixEnd_707821 : Nat := 4983230072969 + 3 ^ 40 * 707821 * 2
def baseEnd_707821 : Nat := 107689597139609001713273

theorem tailTrace_707821 : CollatzResearch.WordTrace tailWord_707821 prefixEnd_707821 107689597139609001713273 := by
  unfold tailWord_707821
  simp only [CollatzResearch.WordTrace]
  refine ⟨25816352768692878047667317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17210901845795252031778211 25816352768692878047667317)
  ·
    refine ⟨2420283072064957316968811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25816352768692878047667317 2420283072064957316968811)
    ·
      refine ⟨3630424608097435975453217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2420283072064957316968811 3630424608097435975453217)
      ·
        refine ⟨2722818456073076981589913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3630424608097435975453217 2722818456073076981589913)
        ·
          refine ⟨2042113842054807736192435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2722818456073076981589913 2042113842054807736192435)
          ·
            refine ⟨3063170763082211604288653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042113842054807736192435 3063170763082211604288653)
            ·
              refine ⟨1148689036155829351608245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3063170763082211604288653 1148689036155829351608245)
              ·
                refine ⟨107689597139609001713273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1148689036155829351608245 107689597139609001713273)
                ·
                  rfl

theorem cell20_707821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_707821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707821 prefixEnd_707821 := by exact prefixLift 707821
  have htrace : WordTrace (prefixWord ++ tailWord_707821) baseStart_707821 baseEnd_707821 := by
    simpa [prefixWord, tailWord_707821, baseEnd_707821] using wordTrace_append hprefix tailTrace_707821
  have hstable : (prefixWord ++ tailWord_707821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707821).length < 2 ^ (prefixWord ++ tailWord_707821).sum := by decide
  have hdescent : baseEnd_707821 < baseStart_707821 := by decide
  rcases family_descends (prefixWord ++ tailWord_707821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707838 : List Nat := [4, 2, 2, 1, 1, 3, 3, 4]
def baseStart_707838 : Nat := 118140960795 + 707838 * 2 ^ 59
def prefixEnd_707838 : Nat := 4983230072969 + 3 ^ 40 * 707838 * 2
def baseEnd_707838 : Nat := 107692183560683500524361

theorem tailTrace_707838 : CollatzResearch.WordTrace tailWord_707838 prefixEnd_707838 107692183560683500524361 := by
  unfold tailWord_707838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227121601203911243879521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17211315206420859967357445 3227121601203911243879521)
  ·
    refine ⟨2420341200902933432909641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3227121601203911243879521 2420341200902933432909641)
    ·
      refine ⟨1815255900677200074682231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2420341200902933432909641 1815255900677200074682231)
      ·
        refine ⟨2722883851015800112023347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1815255900677200074682231 2722883851015800112023347)
        ·
          refine ⟨4084325776523700168035021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2722883851015800112023347 4084325776523700168035021)
          ·
            refine ⟨1531622166196387563013133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4084325776523700168035021 1531622166196387563013133)
            ·
              refine ⟨574358312323645336129925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1531622166196387563013133 574358312323645336129925)
              ·
                refine ⟨107692183560683500524361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 574358312323645336129925 107692183560683500524361)
                ·
                  rfl

theorem cell20_707838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_707838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707838 prefixEnd_707838 := by exact prefixLift 707838
  have htrace : WordTrace (prefixWord ++ tailWord_707838) baseStart_707838 baseEnd_707838 := by
    simpa [prefixWord, tailWord_707838, baseEnd_707838] using wordTrace_append hprefix tailTrace_707838
  have hstable : (prefixWord ++ tailWord_707838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707838).length < 2 ^ (prefixWord ++ tailWord_707838).sum := by decide
  have hdescent : baseEnd_707838 < baseStart_707838 := by decide
  rcases family_descends (prefixWord ++ tailWord_707838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707849 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 5]
def baseStart_707849 : Nat := 118140960795 + 707849 * 2 ^ 59
def prefixEnd_707849 : Nat := 4983230072969 + 3 ^ 40 * 707849 * 2
def baseEnd_707849 : Nat := 323081571381783352206371

theorem tailTrace_707849 : CollatzResearch.WordTrace tailWord_707849 prefixEnd_707849 323081571381783352206371 := by
  unfold tailWord_707849
  simp only [CollatzResearch.WordTrace]
  refine ⟨25817374012591438829686601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17211582675060959219791067 25817374012591438829686601)
  ·
    refine ⟨19363030509443579122264951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25817374012591438829686601 19363030509443579122264951)
    ·
      refine ⟨29044545764165368683397427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19363030509443579122264951 29044545764165368683397427)
      ·
        refine ⟨43566818646248053025096141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29044545764165368683397427 43566818646248053025096141)
        ·
          refine ⟨16337556992343019884411053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43566818646248053025096141 16337556992343019884411053)
          ·
            refine ⟨6126583872128632456654145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16337556992343019884411053 6126583872128632456654145)
            ·
              refine ⟨4594937904096474342490609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6126583872128632456654145 4594937904096474342490609)
              ·
                refine ⟨3446203428072355756867957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4594937904096474342490609 3446203428072355756867957)
                ·
                  refine ⟨323081571381783352206371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3446203428072355756867957 323081571381783352206371)
                  ·
                    rfl

theorem cell20_707849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_707849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707849 prefixEnd_707849 := by exact prefixLift 707849
  have htrace : WordTrace (prefixWord ++ tailWord_707849) baseStart_707849 baseEnd_707849 := by
    simpa [prefixWord, tailWord_707849, baseEnd_707849] using wordTrace_append hprefix tailTrace_707849
  have hstable : (prefixWord ++ tailWord_707849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707849).length < 2 ^ (prefixWord ++ tailWord_707849).sum := by decide
  have hdescent : baseEnd_707849 < baseStart_707849 := by decide
  rcases family_descends (prefixWord ++ tailWord_707849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707852 : List Nat := [2, 2, 1, 2, 2, 3, 1, 5, 2]
def baseStart_707852 : Nat := 118140960795 + 707852 * 2 ^ 59
def prefixEnd_707852 : Nat := 4983230072969 + 3 ^ 40 * 707852 * 2
def baseEnd_707852 : Nat := 323082940663528675106359

theorem tailTrace_707852 : CollatzResearch.WordTrace tailWord_707852 prefixEnd_707852 323082940663528675106359 := by
  unfold tailWord_707852
  simp only [CollatzResearch.WordTrace]
  refine ⟨12908741715790285171022905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17211655621053713561363873 12908741715790285171022905)
  ·
    refine ⟨9681556286842713878267179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12908741715790285171022905 9681556286842713878267179)
    ·
      refine ⟨14522334430264070817400769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9681556286842713878267179 14522334430264070817400769)
      ·
        refine ⟨10891750822698053113050577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14522334430264070817400769 10891750822698053113050577)
        ·
          refine ⟨8168813117023539834787933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10891750822698053113050577 8168813117023539834787933)
          ·
            refine ⟨3063304918883827438045475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8168813117023539834787933 3063304918883827438045475)
            ·
              refine ⟨4594957378325741157068213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3063304918883827438045475 4594957378325741157068213)
              ·
                refine ⟨430777254218038233475145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4594957378325741157068213 430777254218038233475145)
                ·
                  refine ⟨323082940663528675106359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430777254218038233475145 323082940663528675106359)
                  ·
                    rfl

theorem cell20_707852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_707852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707852 prefixEnd_707852 := by exact prefixLift 707852
  have htrace : WordTrace (prefixWord ++ tailWord_707852) baseStart_707852 baseEnd_707852 := by
    simpa [prefixWord, tailWord_707852, baseEnd_707852] using wordTrace_append hprefix tailTrace_707852
  have hstable : (prefixWord ++ tailWord_707852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707852).length < 2 ^ (prefixWord ++ tailWord_707852).sum := by decide
  have hdescent : baseEnd_707852 < baseStart_707852 := by decide
  rcases family_descends (prefixWord ++ tailWord_707852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707858 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 3]
def baseStart_707858 : Nat := 118140960795 + 707858 * 2 ^ 59
def prefixEnd_707858 : Nat := 4983230072969 + 3 ^ 40 * 707858 * 2
def baseEnd_707858 : Nat := 323085679227019320906335

theorem tailTrace_707858 : CollatzResearch.WordTrace tailWord_707858 prefixEnd_707858 323085679227019320906335 := by
  unfold tailWord_707858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6454425567389708341691057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17211801513039222244509485 6454425567389708341691057)
  ·
    refine ⟨4840819175542281256268293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6454425567389708341691057 4840819175542281256268293)
    ·
      refine ⟨907653595414177735550305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4840819175542281256268293 907653595414177735550305)
      ·
        refine ⟨680740196560633301662729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 907653595414177735550305 680740196560633301662729)
        ·
          refine ⟨510555147420474976247047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680740196560633301662729 510555147420474976247047)
          ·
            refine ⟨765832721130712464370571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510555147420474976247047 765832721130712464370571)
            ·
              refine ⟨1148749081696068696555857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765832721130712464370571 1148749081696068696555857)
              ·
                refine ⟨861561811272051522416893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148749081696068696555857 861561811272051522416893)
                ·
                  refine ⟨323085679227019320906335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861561811272051522416893 323085679227019320906335)
                  ·
                    rfl

theorem cell20_707858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_707858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707858 prefixEnd_707858 := by exact prefixLift 707858
  have htrace : WordTrace (prefixWord ++ tailWord_707858) baseStart_707858 baseEnd_707858 := by
    simpa [prefixWord, tailWord_707858, baseEnd_707858] using wordTrace_append hprefix tailTrace_707858
  have hstable : (prefixWord ++ tailWord_707858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707858).length < 2 ^ (prefixWord ++ tailWord_707858).sum := by decide
  have hdescent : baseEnd_707858 < baseStart_707858 := by decide
  rcases family_descends (prefixWord ++ tailWord_707858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707866 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_707866 : Nat := 118140960795 + 707866 * 2 ^ 59
def prefixEnd_707866 : Nat := 4983230072969 + 3 ^ 40 * 707866 * 2
def baseEnd_707866 : Nat := 323089330645006848639635

theorem tailTrace_707866 : CollatzResearch.WordTrace tailWord_707866 prefixEnd_707866 323089330645006848639635 := by
  unfold tailWord_707866
  simp only [CollatzResearch.WordTrace]
  refine ⟨6454498513382462683263863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17211996035686567155370301 6454498513382462683263863)
  ·
    refine ⟨9681747770073694024895795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6454498513382462683263863 9681747770073694024895795)
    ·
      refine ⟨14522621655110541037343693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9681747770073694024895795 14522621655110541037343693)
      ·
        refine ⟨5445983120666452889003885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14522621655110541037343693 5445983120666452889003885)
        ·
          refine ⟨2042243670249919833376457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5445983120666452889003885 2042243670249919833376457)
          ·
            refine ⟨1531682752687439875032343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2042243670249919833376457 1531682752687439875032343)
            ·
              refine ⟨2297524129031159812548515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531682752687439875032343 2297524129031159812548515)
              ·
                refine ⟨3446286193546739718822773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2297524129031159812548515 3446286193546739718822773)
                ·
                  refine ⟨323089330645006848639635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3446286193546739718822773 323089330645006848639635)
                  ·
                    rfl

theorem cell20_707866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_707866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707866 prefixEnd_707866 := by exact prefixLift 707866
  have htrace : WordTrace (prefixWord ++ tailWord_707866) baseStart_707866 baseEnd_707866 := by
    simpa [prefixWord, tailWord_707866, baseEnd_707866] using wordTrace_append hprefix tailTrace_707866
  have hstable : (prefixWord ++ tailWord_707866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707866).length < 2 ^ (prefixWord ++ tailWord_707866).sum := by decide
  have hdescent : baseEnd_707866 < baseStart_707866 := by decide
  rcases family_descends (prefixWord ++ tailWord_707866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707869 : List Nat := [1, 4, 2, 3, 1, 1, 2, 4, 2]
def baseStart_707869 : Nat := 118140960795 + 707869 * 2 ^ 59
def prefixEnd_707869 : Nat := 4983230072969 + 3 ^ 40 * 707869 * 2
def baseEnd_707869 : Nat := 323090699926752171539623

theorem tailTrace_707869 : CollatzResearch.WordTrace tailWord_707869 prefixEnd_707869 323090699926752171539623 := by
  unfold tailWord_707869
  simp only [CollatzResearch.WordTrace]
  refine ⟨25818103472518982245414661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17212068981679321496943107 25818103472518982245414661)
  ·
    refine ⟨4840894401097309171015249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25818103472518982245414661 4840894401097309171015249)
    ·
      refine ⟨3630670800822981878261437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4840894401097309171015249 3630670800822981878261437)
      ·
        refine ⟨1361501550308618204348039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3630670800822981878261437 1361501550308618204348039)
        ·
          refine ⟨2042252325462927306522059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361501550308618204348039 2042252325462927306522059)
          ·
            refine ⟨3063378488194390959783089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042252325462927306522059 3063378488194390959783089)
            ·
              refine ⟨2297533866145793219837317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3063378488194390959783089 2297533866145793219837317)
              ·
                refine ⟨430787599902336228719497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2297533866145793219837317 430787599902336228719497)
                ·
                  refine ⟨323090699926752171539623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430787599902336228719497 323090699926752171539623)
                  ·
                    rfl

theorem cell20_707869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_707869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707869 prefixEnd_707869 := by exact prefixLift 707869
  have htrace : WordTrace (prefixWord ++ tailWord_707869) baseStart_707869 baseEnd_707869 := by
    simpa [prefixWord, tailWord_707869, baseEnd_707869] using wordTrace_append hprefix tailTrace_707869
  have hstable : (prefixWord ++ tailWord_707869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707869).length < 2 ^ (prefixWord ++ tailWord_707869).sum := by decide
  have hdescent : baseEnd_707869 < baseStart_707869 := by decide
  rcases family_descends (prefixWord ++ tailWord_707869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707897 : List Nat := [1, 2, 1, 6, 2, 1, 1, 6]
def baseStart_707897 : Nat := 118140960795 + 707897 * 2 ^ 59
def prefixEnd_707897 : Nat := 4983230072969 + 3 ^ 40 * 707897 * 2
def baseEnd_707897 : Nat := 107701159963236172868725

theorem tailTrace_707897 : CollatzResearch.WordTrace tailWord_707897 prefixEnd_707897 107701159963236172868725 := by
  unfold tailWord_707897
  simp only [CollatzResearch.WordTrace]
  refine ⟨25819124716417543027433945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17212749810945028684955963 25819124716417543027433945)
  ·
    refine ⟨19364343537313157270575459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25819124716417543027433945 19364343537313157270575459)
    ·
      refine ⟨29046515305969735905863189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19364343537313157270575459 29046515305969735905863189)
      ·
        refine ⟨1361555404967331370587337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29046515305969735905863189 1361555404967331370587337)
        ·
          refine ⟨1021166553725498527940503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1361555404967331370587337 1021166553725498527940503)
          ·
            refine ⟨1531749830588247791910755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021166553725498527940503 1531749830588247791910755)
            ·
              refine ⟨2297624745882371687866133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1531749830588247791910755 2297624745882371687866133)
              ·
                refine ⟨107701159963236172868725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2297624745882371687866133 107701159963236172868725)
                ·
                  rfl

theorem cell20_707897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 6].length) (baseStart_707897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707897 prefixEnd_707897 := by exact prefixLift 707897
  have htrace : WordTrace (prefixWord ++ tailWord_707897) baseStart_707897 baseEnd_707897 := by
    simpa [prefixWord, tailWord_707897, baseEnd_707897] using wordTrace_append hprefix tailTrace_707897
  have hstable : (prefixWord ++ tailWord_707897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707897).length < 2 ^ (prefixWord ++ tailWord_707897).sum := by decide
  have hdescent : baseEnd_707897 < baseStart_707897 := by decide
  rcases family_descends (prefixWord ++ tailWord_707897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707910 : List Nat := [6, 1, 1, 3, 2, 1, 6]
def baseStart_707910 : Nat := 118140960795 + 707910 * 2 ^ 59
def prefixEnd_707910 : Nat := 4983230072969 + 3 ^ 40 * 707910 * 2
def baseEnd_707910 : Nat := 35901045938215361241421

theorem tailTrace_707910 : CollatzResearch.WordTrace tailWord_707910 prefixEnd_707910 35901045938215361241421 := by
  unfold tailWord_707910
  simp only [CollatzResearch.WordTrace]
  refine ⟨806862464542826445239287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17213065910246964165104789 806862464542826445239287)
  ·
    refine ⟨1210293696814239667858931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 806862464542826445239287 1210293696814239667858931)
    ·
      refine ⟨1815440545221359501788397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1210293696814239667858931 1815440545221359501788397)
      ·
        refine ⟨680790204458009813170649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1815440545221359501788397 680790204458009813170649)
        ·
          refine ⟨510592653343507359877987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 680790204458009813170649 510592653343507359877987)
          ·
            refine ⟨765888980015261039816981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510592653343507359877987 765888980015261039816981)
            ·
              refine ⟨35901045938215361241421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 765888980015261039816981 35901045938215361241421)
              ·
                rfl

theorem cell20_707910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 6].length) (baseStart_707910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707910 prefixEnd_707910 := by exact prefixLift 707910
  have htrace : WordTrace (prefixWord ++ tailWord_707910) baseStart_707910 baseEnd_707910 := by
    simpa [prefixWord, tailWord_707910, baseEnd_707910] using wordTrace_append hprefix tailTrace_707910
  have hstable : (prefixWord ++ tailWord_707910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707910).length < 2 ^ (prefixWord ++ tailWord_707910).sum := by decide
  have hdescent : baseEnd_707910 < baseStart_707910 := by decide
  rcases family_descends (prefixWord ++ tailWord_707910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707977 : List Nat := [1, 2, 1, 1, 15]
def baseStart_707977 : Nat := 118140960795 + 707977 * 2 ^ 59
def prefixEnd_707977 : Nat := 4983230072969 + 3 ^ 40 * 707977 * 2
def baseEnd_707977 : Nat := 3989382642834367851101

theorem tailTrace_707977 : CollatzResearch.WordTrace tailWord_707977 prefixEnd_707977 3989382642834367851101 := by
  unfold tailWord_707977
  simp only [CollatzResearch.WordTrace]
  refine ⟨25822042556127716690346185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17214695037418477793564123 25822042556127716690346185)
  ·
    refine ⟨19366531917095787517759639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25822042556127716690346185 19366531917095787517759639)
    ·
      refine ⟨29049797875643681276639459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19366531917095787517759639 29049797875643681276639459)
      ·
        refine ⟨43574696813465521914959189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29049797875643681276639459 43574696813465521914959189)
        ·
          refine ⟨3989382642834367851101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 43574696813465521914959189 3989382642834367851101)
          ·
            rfl

theorem cell20_707977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 15].length) (baseStart_707977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707977 prefixEnd_707977 := by exact prefixLift 707977
  have htrace : WordTrace (prefixWord ++ tailWord_707977) baseStart_707977 baseEnd_707977 := by
    simpa [prefixWord, tailWord_707977, baseEnd_707977] using wordTrace_append hprefix tailTrace_707977
  have hstable : (prefixWord ++ tailWord_707977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707977).length < 2 ^ (prefixWord ++ tailWord_707977).sum := by decide
  have hdescent : baseEnd_707977 < baseStart_707977 := by decide
  rcases family_descends (prefixWord ++ tailWord_707977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_707980 : List Nat := [2, 2, 1, 2, 1, 3, 4, 2, 3]
def baseStart_707980 : Nat := 118140960795 + 707980 * 2 ^ 59
def prefixEnd_707980 : Nat := 4983230072969 + 3 ^ 40 * 707980 * 2
def baseEnd_707980 : Nat := 323141363351329118839169

theorem tailTrace_707980 : CollatzResearch.WordTrace tailWord_707980 prefixEnd_707980 323141363351329118839169 := by
  unfold tailWord_707980
  simp only [CollatzResearch.WordTrace]
  refine ⟨12911075987558424101352697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17214767983411232135136929 12911075987558424101352697)
  ·
    refine ⟨9683306990668818076014523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12911075987558424101352697 9683306990668818076014523)
    ·
      refine ⟨14524960486003227114021785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9683306990668818076014523 14524960486003227114021785)
      ·
        refine ⟨10893720364502420335516339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14524960486003227114021785 10893720364502420335516339)
        ·
          refine ⟨16340580546753630503274509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10893720364502420335516339 16340580546753630503274509)
          ·
            refine ⟨6127717705032611438727941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16340580546753630503274509 6127717705032611438727941)
            ·
              refine ⟨1148947069693614644761489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6127717705032611438727941 1148947069693614644761489)
              ·
                refine ⟨861710302270210983571117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1148947069693614644761489 861710302270210983571117)
                ·
                  refine ⟨323141363351329118839169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861710302270210983571117 323141363351329118839169)
                  ·
                    rfl

theorem cell20_707980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_707980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_707980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_707980 prefixEnd_707980 := by exact prefixLift 707980
  have htrace : WordTrace (prefixWord ++ tailWord_707980) baseStart_707980 baseEnd_707980 := by
    simpa [prefixWord, tailWord_707980, baseEnd_707980] using wordTrace_append hprefix tailTrace_707980
  have hstable : (prefixWord ++ tailWord_707980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_707980).length < 2 ^ (prefixWord ++ tailWord_707980).sum := by decide
  have hdescent : baseEnd_707980 < baseStart_707980 := by decide
  rcases family_descends (prefixWord ++ tailWord_707980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708015 : List Nat := [1, 1, 2, 1, 2, 2, 1, 10]
def baseStart_708015 : Nat := 118140960795 + 708015 * 2 ^ 59
def prefixEnd_708015 : Nat := 4983230072969 + 3 ^ 40 * 708015 * 2
def baseEnd_708015 : Nat := 107719112768341517557453

theorem tailTrace_708015 : CollatzResearch.WordTrace tailWord_708015 prefixEnd_708015 107719112768341517557453 := by
  unfold tailWord_708015
  simp only [CollatzResearch.WordTrace]
  refine ⟨25823428529990049180229499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17215619019993366120152999 25823428529990049180229499)
  ·
    refine ⟨38735142794985073770344249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25823428529990049180229499 38735142794985073770344249)
    ·
      refine ⟨29051357096238805327758187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38735142794985073770344249 29051357096238805327758187)
      ·
        refine ⟨43577035644358207991637281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29051357096238805327758187 43577035644358207991637281)
        ·
          refine ⟨32682776733268655993727961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43577035644358207991637281 32682776733268655993727961)
          ·
            refine ⟨24512082549951491995295971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32682776733268655993727961 24512082549951491995295971)
            ·
              refine ⟨36768123824927237992943957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24512082549951491995295971 36768123824927237992943957)
              ·
                refine ⟨107719112768341517557453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36768123824927237992943957 107719112768341517557453)
                ·
                  rfl

theorem cell20_708015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_708015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708015 prefixEnd_708015 := by exact prefixLift 708015
  have htrace : WordTrace (prefixWord ++ tailWord_708015) baseStart_708015 baseEnd_708015 := by
    simpa [prefixWord, tailWord_708015, baseEnd_708015] using wordTrace_append hprefix tailTrace_708015
  have hstable : (prefixWord ++ tailWord_708015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708015).length < 2 ^ (prefixWord ++ tailWord_708015).sum := by decide
  have hdescent : baseEnd_708015 < baseStart_708015 := by decide
  rcases family_descends (prefixWord ++ tailWord_708015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708021 : List Nat := [1, 3, 3, 2, 2, 2, 2, 3, 2]
def baseStart_708021 : Nat := 118140960795 + 708021 * 2 ^ 59
def prefixEnd_708021 : Nat := 4983230072969 + 3 ^ 40 * 708021 * 2
def baseEnd_708021 : Nat := 323160076868515198472335

theorem tailTrace_708021 : CollatzResearch.WordTrace tailWord_708021 prefixEnd_708021 323160076868515198472335 := by
  unfold tailWord_708021
  simp only [CollatzResearch.WordTrace]
  refine ⟨25823647367968312204947917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17215764911978874803298611 25823647367968312204947917)
  ·
    refine ⟨9683867762988117076855469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25823647367968312204947917 9683867762988117076855469)
    ·
      refine ⟨3631450411120543903820801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9683867762988117076855469 3631450411120543903820801)
      ·
        refine ⟨2723587808340407927865601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3631450411120543903820801 2723587808340407927865601)
        ·
          refine ⟨2042690856255305945899201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2723587808340407927865601 2042690856255305945899201)
          ·
            refine ⟨1532018142191479459424401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2042690856255305945899201 1532018142191479459424401)
            ·
              refine ⟨1149013606643609594568301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532018142191479459424401 1149013606643609594568301)
              ·
                refine ⟨430880102491353597963113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1149013606643609594568301 430880102491353597963113)
                ·
                  refine ⟨323160076868515198472335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430880102491353597963113 323160076868515198472335)
                  ·
                    rfl

theorem cell20_708021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_708021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708021 prefixEnd_708021 := by exact prefixLift 708021
  have htrace : WordTrace (prefixWord ++ tailWord_708021) baseStart_708021 baseEnd_708021 := by
    simpa [prefixWord, tailWord_708021, baseEnd_708021] using wordTrace_append hprefix tailTrace_708021
  have hstable : (prefixWord ++ tailWord_708021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708021).length < 2 ^ (prefixWord ++ tailWord_708021).sum := by decide
  have hdescent : baseEnd_708021 < baseStart_708021 := by decide
  rcases family_descends (prefixWord ++ tailWord_708021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708039 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 5]
def baseStart_708039 : Nat := 118140960795 + 708039 * 2 ^ 59
def prefixEnd_708039 : Nat := 4983230072969 + 3 ^ 40 * 708039 * 2
def baseEnd_708039 : Nat := 323168292558987135872261

theorem tailTrace_708039 : CollatzResearch.WordTrace tailWord_708039 prefixEnd_708039 323168292558987135872261 := by
  unfold tailWord_708039
  simp only [CollatzResearch.WordTrace]
  refine ⟨25824303881903101279103171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17216202587935400852735447 25824303881903101279103171)
  ·
    refine ⟨38736455822854651918654757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25824303881903101279103171 38736455822854651918654757)
    ·
      refine ⟨7263085466785247234747767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38736455822854651918654757 7263085466785247234747767)
      ·
        refine ⟨10894628200177870852121651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7263085466785247234747767 10894628200177870852121651)
        ·
          refine ⟨16341942300266806278182477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10894628200177870852121651 16341942300266806278182477)
          ·
            refine ⟨6128228362600052354318429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16341942300266806278182477 6128228362600052354318429)
            ·
              refine ⟨2298085635975019632869411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6128228362600052354318429 2298085635975019632869411)
              ·
                refine ⟨3447128453962529449304117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2298085635975019632869411 3447128453962529449304117)
                ·
                  refine ⟨323168292558987135872261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3447128453962529449304117 323168292558987135872261)
                  ·
                    rfl

theorem cell20_708039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_708039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708039 prefixEnd_708039 := by exact prefixLift 708039
  have htrace : WordTrace (prefixWord ++ tailWord_708039) baseStart_708039 baseEnd_708039 := by
    simpa [prefixWord, tailWord_708039, baseEnd_708039] using wordTrace_append hprefix tailTrace_708039
  have hstable : (prefixWord ++ tailWord_708039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708039).length < 2 ^ (prefixWord ++ tailWord_708039).sum := by decide
  have hdescent : baseEnd_708039 < baseStart_708039 := by decide
  rcases family_descends (prefixWord ++ tailWord_708039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708042 : List Nat := [3, 1, 2, 1, 2, 3, 2, 4, 2]
def baseStart_708042 : Nat := 118140960795 + 708042 * 2 ^ 59
def prefixEnd_708042 : Nat := 4983230072969 + 3 ^ 40 * 708042 * 2
def baseEnd_708042 : Nat := 323169661840732458772249

theorem tailTrace_708042 : CollatzResearch.WordTrace tailWord_708042 prefixEnd_708042 323169661840732458772249 := by
  unfold tailWord_708042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6456103325223058197865595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17216275533928155194308253 6456103325223058197865595)
  ·
    refine ⟨9684154987834587296798393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6456103325223058197865595 9684154987834587296798393)
    ·
      refine ⟨7263116240875940472598795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9684154987834587296798393 7263116240875940472598795)
      ·
        refine ⟨10894674361313910708898193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7263116240875940472598795 10894674361313910708898193)
        ·
          refine ⟨8171005770985433031673645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10894674361313910708898193 8171005770985433031673645)
          ·
            refine ⟨3064127164119537386877617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8171005770985433031673645 3064127164119537386877617)
            ·
              refine ⟨2298095373089653040158213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3064127164119537386877617 2298095373089653040158213)
              ·
                refine ⟨430892882454309945029665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2298095373089653040158213 430892882454309945029665)
                ·
                  refine ⟨323169661840732458772249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430892882454309945029665 323169661840732458772249)
                  ·
                    rfl

theorem cell20_708042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_708042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708042 prefixEnd_708042 := by exact prefixLift 708042
  have htrace : WordTrace (prefixWord ++ tailWord_708042) baseStart_708042 baseEnd_708042 := by
    simpa [prefixWord, tailWord_708042, baseEnd_708042] using wordTrace_append hprefix tailTrace_708042
  have hstable : (prefixWord ++ tailWord_708042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708042).length < 2 ^ (prefixWord ++ tailWord_708042).sum := by decide
  have hdescent : baseEnd_708042 < baseStart_708042 := by decide
  rcases family_descends (prefixWord ++ tailWord_708042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708052 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 3]
def baseStart_708052 : Nat := 118140960795 + 708052 * 2 ^ 59
def prefixEnd_708052 : Nat := 4983230072969 + 3 ^ 40 * 708052 * 2
def baseEnd_708052 : Nat := 323174226113216868438875

theorem tailTrace_708052 : CollatzResearch.WordTrace tailWord_708052 prefixEnd_708052 323174226113216868438875 := by
  unfold tailWord_708052
  simp only [CollatzResearch.WordTrace]
  refine ⟨12912389015428002249663205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17216518687237336332884273 12912389015428002249663205)
  ·
    refine ⟨2421072940392750421811851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12912389015428002249663205 2421072940392750421811851)
    ·
      refine ⟨3631609410589125632717777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2421072940392750421811851 3631609410589125632717777)
      ·
        refine ⟨2723707057941844224538333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3631609410589125632717777 2723707057941844224538333)
        ·
          refine ⟨1021390146728191584201875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2723707057941844224538333 1021390146728191584201875)
          ·
            refine ⟨1532085220092287376302813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021390146728191584201875 1532085220092287376302813)
            ·
              refine ⟨574531957534607766113555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1532085220092287376302813 574531957534607766113555)
              ·
                refine ⟨861797936301911649170333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574531957534607766113555 861797936301911649170333)
                ·
                  refine ⟨323174226113216868438875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861797936301911649170333 323174226113216868438875)
                  ·
                    rfl

theorem cell20_708052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_708052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708052 prefixEnd_708052 := by exact prefixLift 708052
  have htrace : WordTrace (prefixWord ++ tailWord_708052) baseStart_708052 baseEnd_708052 := by
    simpa [prefixWord, tailWord_708052, baseEnd_708052] using wordTrace_append hprefix tailTrace_708052
  have hstable : (prefixWord ++ tailWord_708052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708052).length < 2 ^ (prefixWord ++ tailWord_708052).sum := by decide
  have hdescent : baseEnd_708052 < baseStart_708052 := by decide
  rcases family_descends (prefixWord ++ tailWord_708052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708080 : List Nat := [2, 1, 1, 1, 3, 4, 3, 3, 2]
def baseStart_708080 : Nat := 118140960795 + 708080 * 2 ^ 59
def prefixEnd_708080 : Nat := 4983230072969 + 3 ^ 40 * 708080 * 2
def baseEnd_708080 : Nat := 323187006076173215505427

theorem tailTrace_708080 : CollatzResearch.WordTrace tailWord_708080 prefixEnd_708080 323187006076173215505427 := by
  unfold tailWord_708080
  simp only [CollatzResearch.WordTrace]
  refine ⟨12912899637377282640672847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17217199516503043520897129 12912899637377282640672847)
  ·
    refine ⟨19369349456065923961009271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12912899637377282640672847 19369349456065923961009271)
    ·
      refine ⟨29054024184098885941513907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19369349456065923961009271 29054024184098885941513907)
      ·
        refine ⟨43581036276148328912270861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29054024184098885941513907 43581036276148328912270861)
        ·
          refine ⟨16342888603555623342101573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43581036276148328912270861 16342888603555623342101573)
          ·
            refine ⟨3064291613166679376644045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16342888603555623342101573 3064291613166679376644045)
            ·
              refine ⟨1149109354937504766241517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3064291613166679376644045 1149109354937504766241517)
              ·
                refine ⟨430916008101564287340569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1149109354937504766241517 430916008101564287340569)
                ·
                  refine ⟨323187006076173215505427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430916008101564287340569 323187006076173215505427)
                  ·
                    rfl

theorem cell20_708080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 2].length) (baseStart_708080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708080 prefixEnd_708080 := by exact prefixLift 708080
  have htrace : WordTrace (prefixWord ++ tailWord_708080) baseStart_708080 baseEnd_708080 := by
    simpa [prefixWord, tailWord_708080, baseEnd_708080] using wordTrace_append hprefix tailTrace_708080
  have hstable : (prefixWord ++ tailWord_708080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708080).length < 2 ^ (prefixWord ++ tailWord_708080).sum := by decide
  have hdescent : baseEnd_708080 < baseStart_708080 := by decide
  rcases family_descends (prefixWord ++ tailWord_708080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708097 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 4]
def baseStart_708097 : Nat := 118140960795 + 708097 * 2 ^ 59
def prefixEnd_708097 : Nat := 4983230072969 + 3 ^ 40 * 708097 * 2
def baseEnd_708097 : Nat := 323194765339396711938691

theorem tailTrace_708097 : CollatzResearch.WordTrace tailWord_708097 prefixEnd_708097 323194765339396711938691 := by
  unfold tailWord_708097
  simp only [CollatzResearch.WordTrace]
  refine ⟨25826419315692977184714545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17217612877128651456476363 25826419315692977184714545)
  ·
    refine ⟨19369814486769732888535909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25826419315692977184714545 19369814486769732888535909)
    ·
      refine ⟨3631840216269324916600483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19369814486769732888535909 3631840216269324916600483)
      ·
        refine ⟨5447760324403987374900725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3631840216269324916600483 5447760324403987374900725)
        ·
          refine ⟨510727530412873816396943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5447760324403987374900725 510727530412873816396943)
          ·
            refine ⟨766091295619310724595415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510727530412873816396943 766091295619310724595415)
            ·
              refine ⟨1149136943428966086893123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766091295619310724595415 1149136943428966086893123)
              ·
                refine ⟨1723705415143449130339685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1149136943428966086893123 1723705415143449130339685)
                ·
                  refine ⟨323194765339396711938691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1723705415143449130339685 323194765339396711938691)
                  ·
                    rfl

theorem cell20_708097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 4].length) (baseStart_708097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708097 prefixEnd_708097 := by exact prefixLift 708097
  have htrace : WordTrace (prefixWord ++ tailWord_708097) baseStart_708097 baseEnd_708097 := by
    simpa [prefixWord, tailWord_708097, baseEnd_708097] using wordTrace_append hprefix tailTrace_708097
  have hstable : (prefixWord ++ tailWord_708097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708097).length < 2 ^ (prefixWord ++ tailWord_708097).sum := by decide
  have hdescent : baseEnd_708097 < baseStart_708097 := by decide
  rcases family_descends (prefixWord ++ tailWord_708097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708122 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_708122 : Nat := 118140960795 + 708122 * 2 ^ 59
def prefixEnd_708122 : Nat := 4983230072969 + 3 ^ 40 * 708122 * 2
def baseEnd_708122 : Nat := 323206176020607736105255

theorem tailTrace_708122 : CollatzResearch.WordTrace tailWord_708122 prefixEnd_708122 323206176020607736105255 := by
  unfold tailWord_708122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6456832785150601613593655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17218220760401604302916413 6456832785150601613593655)
  ·
    refine ⟨9685249177725902420390483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6456832785150601613593655 9685249177725902420390483)
    ·
      refine ⟨14527873766588853630585725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9685249177725902420390483 14527873766588853630585725)
      ·
        refine ⟨5447952662470820111469647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14527873766588853630585725 5447952662470820111469647)
        ·
          refine ⟨8171928993706230167204471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5447952662470820111469647 8171928993706230167204471)
          ·
            refine ⟨12257893490559345250806707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8171928993706230167204471 12257893490559345250806707)
            ·
              refine ⟨18386840235839017876210061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12257893490559345250806707 18386840235839017876210061)
              ·
                refine ⟨6895065088439631703578773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18386840235839017876210061 6895065088439631703578773)
                ·
                  refine ⟨323206176020607736105255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6895065088439631703578773 323206176020607736105255)
                  ·
                    rfl

theorem cell20_708122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_708122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708122 prefixEnd_708122 := by exact prefixLift 708122
  have htrace : WordTrace (prefixWord ++ tailWord_708122) baseStart_708122 baseEnd_708122 := by
    simpa [prefixWord, tailWord_708122, baseEnd_708122] using wordTrace_append hprefix tailTrace_708122
  have hstable : (prefixWord ++ tailWord_708122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708122).length < 2 ^ (prefixWord ++ tailWord_708122).sum := by decide
  have hdescent : baseEnd_708122 < baseStart_708122 := by decide
  rcases family_descends (prefixWord ++ tailWord_708122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708160 : List Nat := [2, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_708160 : Nat := 118140960795 + 708160 * 2 ^ 59
def prefixEnd_708160 : Nat := 4983230072969 + 3 ^ 40 * 708160 * 2
def baseEnd_708160 : Nat := 323223520256048492838433

theorem tailTrace_708160 : CollatzResearch.WordTrace tailWord_708160 prefixEnd_708160 323223520256048492838433 := by
  unfold tailWord_708160
  simp only [CollatzResearch.WordTrace]
  refine ⟨12914358557232369472128967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17219144742976492629505289 12914358557232369472128967)
  ·
    refine ⟨19371537835848554208193451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12914358557232369472128967 19371537835848554208193451)
    ·
      refine ⟨29057306753772831312290177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19371537835848554208193451 29057306753772831312290177)
      ·
        refine ⟨21792980065329623484217633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29057306753772831312290177 21792980065329623484217633)
        ·
          refine ⟨16344735048997217613163225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21792980065329623484217633 16344735048997217613163225)
          ·
            refine ⟨12258551286747913209872419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16344735048997217613163225 12258551286747913209872419)
            ·
              refine ⟨18387826930121869814808629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12258551286747913209872419 18387826930121869814808629)
              ·
                refine ⟨1723858774698925295138309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18387826930121869814808629 1723858774698925295138309)
                ·
                  refine ⟨323223520256048492838433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1723858774698925295138309 323223520256048492838433)
                  ·
                    rfl

theorem cell20_708160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_708160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708160 prefixEnd_708160 := by exact prefixLift 708160
  have htrace : WordTrace (prefixWord ++ tailWord_708160) baseStart_708160 baseEnd_708160 := by
    simpa [prefixWord, tailWord_708160, baseEnd_708160] using wordTrace_append hprefix tailTrace_708160
  have hstable : (prefixWord ++ tailWord_708160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708160).length < 2 ^ (prefixWord ++ tailWord_708160).sum := by decide
  have hdescent : baseEnd_708160 < baseStart_708160 := by decide
  rcases family_descends (prefixWord ++ tailWord_708160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708208 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 3]
def baseStart_708208 : Nat := 118140960795 + 708208 * 2 ^ 59
def prefixEnd_708208 : Nat := 4983230072969 + 3 ^ 40 * 708208 * 2
def baseEnd_708208 : Nat := 323245428763973659238237

theorem tailTrace_708208 : CollatzResearch.WordTrace tailWord_708208 prefixEnd_708208 323245428763973659238237 := by
  unfold tailWord_708208
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915233909145421571002639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17220311878860562094670185 12915233909145421571002639)
  ·
    refine ⟨19372850863718132356503959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12915233909145421571002639 19372850863718132356503959)
    ·
      refine ⟨29059276295577198534755939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19372850863718132356503959 29059276295577198534755939)
      ·
        refine ⟨43588914443365797802133909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29059276295577198534755939 43588914443365797802133909)
        ·
          refine ⟨2043230364532771771975027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 43588914443365797802133909 2043230364532771771975027)
          ·
            refine ⟨3064845546799157657962541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043230364532771771975027 3064845546799157657962541)
            ·
              refine ⟨1149317080049684121735953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3064845546799157657962541 1149317080049684121735953)
              ·
                refine ⟨861987810037263091301965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149317080049684121735953 861987810037263091301965)
                ·
                  refine ⟨323245428763973659238237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861987810037263091301965 323245428763973659238237)
                  ·
                    rfl

theorem cell20_708208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_708208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708208 prefixEnd_708208 := by exact prefixLift 708208
  have htrace : WordTrace (prefixWord ++ tailWord_708208) baseStart_708208 baseEnd_708208 := by
    simpa [prefixWord, tailWord_708208, baseEnd_708208] using wordTrace_append hprefix tailTrace_708208
  have hstable : (prefixWord ++ tailWord_708208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708208).length < 2 ^ (prefixWord ++ tailWord_708208).sum := by decide
  have hdescent : baseEnd_708208 < baseStart_708208 := by decide
  rcases family_descends (prefixWord ++ tailWord_708208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708225 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 3]
def baseStart_708225 : Nat := 118140960795 + 708225 * 2 ^ 59
def prefixEnd_708225 : Nat := 4983230072969 + 3 ^ 40 * 708225 * 2
def baseEnd_708225 : Nat := 323253188027197155671501

theorem tailTrace_708225 : CollatzResearch.WordTrace tailWord_708225 prefixEnd_708225 323253188027197155671501 := by
  unfold tailWord_708225
  simp only [CollatzResearch.WordTrace]
  refine ⟨25831087859229255045374129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17220725239486170030249419 25831087859229255045374129)
  ·
    refine ⟨19373315894421941284030597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25831087859229255045374129 19373315894421941284030597)
    ·
      refine ⟨3632496730204113990755737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19373315894421941284030597 3632496730204113990755737)
      ·
        refine ⟨2724372547653085493066803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3632496730204113990755737 2724372547653085493066803)
        ·
          refine ⟨4086558821479628239600205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2724372547653085493066803 4086558821479628239600205)
          ·
            refine ⟨1532459558054860589850077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4086558821479628239600205 1532459558054860589850077)
            ·
              refine ⟨574672334270572721193779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1532459558054860589850077 574672334270572721193779)
              ·
                refine ⟨862008501405859081790669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574672334270572721193779 862008501405859081790669)
                ·
                  refine ⟨323253188027197155671501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862008501405859081790669 323253188027197155671501)
                  ·
                    rfl

theorem cell20_708225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_708225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708225 prefixEnd_708225 := by exact prefixLift 708225
  have htrace : WordTrace (prefixWord ++ tailWord_708225) baseStart_708225 baseEnd_708225 := by
    simpa [prefixWord, tailWord_708225, baseEnd_708225] using wordTrace_append hprefix tailTrace_708225
  have hstable : (prefixWord ++ tailWord_708225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708225).length < 2 ^ (prefixWord ++ tailWord_708225).sum := by decide
  have hdescent : baseEnd_708225 < baseStart_708225 := by decide
  rcases family_descends (prefixWord ++ tailWord_708225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708236 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_708236 : Nat := 118140960795 + 708236 * 2 ^ 59
def prefixEnd_708236 : Nat := 4983230072969 + 3 ^ 40 * 708236 * 2
def baseEnd_708236 : Nat := 323258208726930006304789

theorem tailTrace_708236 : CollatzResearch.WordTrace tailWord_708236 prefixEnd_708236 323258208726930006304789 := by
  unfold tailWord_708236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12915744531094701962012281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17220992708126269282683041 12915744531094701962012281)
  ·
    refine ⟨9686808398321026471509211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12915744531094701962012281 9686808398321026471509211)
    ·
      refine ⟨14530212597481539707263817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9686808398321026471509211 14530212597481539707263817)
      ·
        refine ⟨10897659448111154780447863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14530212597481539707263817 10897659448111154780447863)
        ·
          refine ⟨16346489172166732170671795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10897659448111154780447863 16346489172166732170671795)
          ·
            refine ⟨24519733758250098256007693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16346489172166732170671795 24519733758250098256007693)
            ·
              refine ⟨9194900159343786846002885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24519733758250098256007693 9194900159343786846002885)
              ·
                refine ⟨1724043779876960033625541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9194900159343786846002885 1724043779876960033625541)
                ·
                  refine ⟨323258208726930006304789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1724043779876960033625541 323258208726930006304789)
                  ·
                    rfl

theorem cell20_708236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_708236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708236 prefixEnd_708236 := by exact prefixLift 708236
  have htrace : WordTrace (prefixWord ++ tailWord_708236) baseStart_708236 baseEnd_708236 := by
    simpa [prefixWord, tailWord_708236, baseEnd_708236] using wordTrace_append hprefix tailTrace_708236
  have hstable : (prefixWord ++ tailWord_708236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708236).length < 2 ^ (prefixWord ++ tailWord_708236).sum := by decide
  have hdescent : baseEnd_708236 < baseStart_708236 := by decide
  rcases family_descends (prefixWord ++ tailWord_708236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708260 : List Nat := [2, 3, 1, 2, 2, 4, 6]
def baseStart_708260 : Nat := 118140960795 + 708260 * 2 ^ 59
def prefixEnd_708260 : Nat := 4983230072969 + 3 ^ 40 * 708260 * 2
def baseEnd_708260 : Nat := 35918795886765843278299

theorem tailTrace_708260 : CollatzResearch.WordTrace tailWord_708260 prefixEnd_708260 35918795886765843278299 := by
  unfold tailWord_708260
  simp only [CollatzResearch.WordTrace]
  refine ⟨12916182207051228011449117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17221576276068304015265489 12916182207051228011449117)
  ·
    refine ⟨4843568327644210504293419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12916182207051228011449117 4843568327644210504293419)
    ·
      refine ⟨7265352491466315756440129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4843568327644210504293419 7265352491466315756440129)
      ·
        refine ⟨5449014368599736817330097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7265352491466315756440129 5449014368599736817330097)
        ·
          refine ⟨4086760776449802612997573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5449014368599736817330097 4086760776449802612997573)
          ·
            refine ⟨766267645584337989937045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4086760776449802612997573 766267645584337989937045)
            ·
              refine ⟨35918795886765843278299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 766267645584337989937045 35918795886765843278299)
              ·
                rfl

theorem cell20_708260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 6].length) (baseStart_708260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708260 prefixEnd_708260 := by exact prefixLift 708260
  have htrace : WordTrace (prefixWord ++ tailWord_708260) baseStart_708260 baseEnd_708260 := by
    simpa [prefixWord, tailWord_708260, baseEnd_708260] using wordTrace_append hprefix tailTrace_708260
  have hstable : (prefixWord ++ tailWord_708260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708260).length < 2 ^ (prefixWord ++ tailWord_708260).sum := by decide
  have hdescent : baseEnd_708260 < baseStart_708260 := by decide
  rcases family_descends (prefixWord ++ tailWord_708260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708277 : List Nat := [1, 3, 3, 3, 2, 1, 2, 5]
def baseStart_708277 : Nat := 118140960795 + 708277 * 2 ^ 59
def prefixEnd_708277 : Nat := 4983230072969 + 3 ^ 40 * 708277 * 2
def baseEnd_708277 : Nat := 107758974081372028645985

theorem tailTrace_708277 : CollatzResearch.WordTrace tailWord_708277 prefixEnd_708277 107758974081372028645985 := by
  unfold tailWord_708277
  simp only [CollatzResearch.WordTrace]
  refine ⟨25832984455040867926267085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17221989636693911950844723 25832984455040867926267085)
  ·
    refine ⟨9687369170640325472350157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25832984455040867926267085 9687369170640325472350157)
    ·
      refine ⟨3632763438990122052131309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9687369170640325472350157 3632763438990122052131309)
      ·
        refine ⟨1362286289621295769549241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3632763438990122052131309 1362286289621295769549241)
        ·
          refine ⟨1021714717215971827161931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1362286289621295769549241 1021714717215971827161931)
          ·
            refine ⟨1532572075823957740742897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021714717215971827161931 1532572075823957740742897)
            ·
              refine ⟨1149429056867968305557173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1532572075823957740742897 1149429056867968305557173)
              ·
                refine ⟨107758974081372028645985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1149429056867968305557173 107758974081372028645985)
                ·
                  rfl

theorem cell20_708277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 5].length) (baseStart_708277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708277 prefixEnd_708277 := by exact prefixLift 708277
  have htrace : WordTrace (prefixWord ++ tailWord_708277) baseStart_708277 baseEnd_708277 := by
    simpa [prefixWord, tailWord_708277, baseEnd_708277] using wordTrace_append hprefix tailTrace_708277
  have hstable : (prefixWord ++ tailWord_708277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708277).length < 2 ^ (prefixWord ++ tailWord_708277).sum := by decide
  have hdescent : baseEnd_708277 < baseStart_708277 := by decide
  rcases family_descends (prefixWord ++ tailWord_708277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708281 : List Nat := [1, 2, 1, 4, 1, 1, 3, 7]
def baseStart_708281 : Nat := 118140960795 + 708281 * 2 ^ 59
def prefixEnd_708281 : Nat := 4983230072969 + 3 ^ 40 * 708281 * 2
def baseEnd_708281 : Nat := 107759582651036616601535

theorem tailTrace_708281 : CollatzResearch.WordTrace tailWord_708281 prefixEnd_708281 107759582651036616601535 := by
  unfold tailWord_708281
  simp only [CollatzResearch.WordTrace]
  refine ⟨25833130347026376609412697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17222086898017584406275131 25833130347026376609412697)
  ·
    refine ⟨19374847760269782457059523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25833130347026376609412697 19374847760269782457059523)
    ·
      refine ⟨29062271640404673685589285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19374847760269782457059523 29062271640404673685589285)
      ·
        refine ⟨5449175932575876316047991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29062271640404673685589285 5449175932575876316047991)
        ·
          refine ⟨8173763898863814474071987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449175932575876316047991 8173763898863814474071987)
          ·
            refine ⟨12260645848295721711107981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8173763898863814474071987 12260645848295721711107981)
            ·
              refine ⟨4597742193110895641665493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12260645848295721711107981 4597742193110895641665493)
              ·
                refine ⟨107759582651036616601535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4597742193110895641665493 107759582651036616601535)
                ·
                  rfl

theorem cell20_708281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 7].length) (baseStart_708281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708281 prefixEnd_708281 := by exact prefixLift 708281
  have htrace : WordTrace (prefixWord ++ tailWord_708281) baseStart_708281 baseEnd_708281 := by
    simpa [prefixWord, tailWord_708281, baseEnd_708281] using wordTrace_append hprefix tailTrace_708281
  have hstable : (prefixWord ++ tailWord_708281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708281).length < 2 ^ (prefixWord ++ tailWord_708281).sum := by decide
  have hdescent : baseEnd_708281 < baseStart_708281 := by decide
  rcases family_descends (prefixWord ++ tailWord_708281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708284 : List Nat := [2, 2, 2, 3, 1, 3, 1, 3, 3]
def baseStart_708284 : Nat := 118140960795 + 708284 * 2 ^ 59
def prefixEnd_708284 : Nat := 4983230072969 + 3 ^ 40 * 708284 * 2
def baseEnd_708284 : Nat := 323280117234855172704593

theorem tailTrace_708284 : CollatzResearch.WordTrace tailWord_708284 prefixEnd_708284 323280117234855172704593 := by
  unfold tailWord_708284
  simp only [CollatzResearch.WordTrace]
  refine ⟨12916619883007754060885953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17222159844010338747847937 12916619883007754060885953)
  ·
    refine ⟨9687464912255815545664465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12916619883007754060885953 9687464912255815545664465)
    ·
      refine ⟨7265598684191861659248349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9687464912255815545664465 7265598684191861659248349)
      ·
        refine ⟨2724599506571948122218131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7265598684191861659248349 2724599506571948122218131)
        ·
          refine ⟨4086899259857922183327197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2724599506571948122218131 4086899259857922183327197)
          ·
            refine ⟨1532587222446720818747699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4086899259857922183327197 1532587222446720818747699)
            ·
              refine ⟨2298880833670081228121549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1532587222446720818747699 2298880833670081228121549)
              ·
                refine ⟨862080312626280460545581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2298880833670081228121549 862080312626280460545581)
                ·
                  refine ⟨323280117234855172704593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862080312626280460545581 323280117234855172704593)
                  ·
                    rfl

theorem cell20_708284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_708284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708284 prefixEnd_708284 := by exact prefixLift 708284
  have htrace : WordTrace (prefixWord ++ tailWord_708284) baseStart_708284 baseEnd_708284 := by
    simpa [prefixWord, tailWord_708284, baseEnd_708284] using wordTrace_append hprefix tailTrace_708284
  have hstable : (prefixWord ++ tailWord_708284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708284).length < 2 ^ (prefixWord ++ tailWord_708284).sum := by decide
  have hdescent : baseEnd_708284 < baseStart_708284 := by decide
  rcases family_descends (prefixWord ++ tailWord_708284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708294 : List Nat := [6, 1, 2, 1, 1, 1, 2, 6]
def baseStart_708294 : Nat := 118140960795 + 708294 * 2 ^ 59
def prefixEnd_708294 : Nat := 4983230072969 + 3 ^ 40 * 708294 * 2
def baseEnd_708294 : Nat := 107761560502446527457073

theorem tailTrace_708294 : CollatzResearch.WordTrace tailWord_708294 prefixEnd_708294 107761560502446527457073 := by
  unfold tailWord_708294
  simp only [CollatzResearch.WordTrace]
  refine ⟨807300140499352494676123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17222402997319519886423957 807300140499352494676123)
  ·
    refine ⟨1210950210749028742014185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 807300140499352494676123 1210950210749028742014185)
    ·
      refine ⟨908212658061771556510639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1210950210749028742014185 908212658061771556510639)
      ·
        refine ⟨1362318987092657334765959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908212658061771556510639 1362318987092657334765959)
        ·
          refine ⟨2043478480638986002148939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362318987092657334765959 2043478480638986002148939)
          ·
            refine ⟨3065217720958479003223409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043478480638986002148939 3065217720958479003223409)
            ·
              refine ⟨2298913290718859252417557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3065217720958479003223409 2298913290718859252417557)
              ·
                refine ⟨107761560502446527457073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2298913290718859252417557 107761560502446527457073)
                ·
                  rfl

theorem cell20_708294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_708294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708294 prefixEnd_708294 := by exact prefixLift 708294
  have htrace : WordTrace (prefixWord ++ tailWord_708294) baseStart_708294 baseEnd_708294 := by
    simpa [prefixWord, tailWord_708294, baseEnd_708294] using wordTrace_append hprefix tailTrace_708294
  have hstable : (prefixWord ++ tailWord_708294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708294).length < 2 ^ (prefixWord ++ tailWord_708294).sum := by decide
  have hdescent : baseEnd_708294 < baseStart_708294 := by decide
  rcases family_descends (prefixWord ++ tailWord_708294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708343 : List Nat := [1, 1, 3, 1, 1, 1, 6, 3, 3]
def baseStart_708343 : Nat := 118140960795 + 708343 * 2 ^ 59
def prefixEnd_708343 : Nat := 4983230072969 + 3 ^ 40 * 708343 * 2
def baseEnd_708343 : Nat := 323307046442513189737685

theorem tailTrace_708343 : CollatzResearch.WordTrace tailWord_708343 prefixEnd_708343 323307046442513189737685 := by
  unfold tailWord_708343
  simp only [CollatzResearch.WordTrace]
  refine ⟨25835391672801761198169683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17223594448534507465446455 25835391672801761198169683)
  ·
    refine ⟨38753087509202641797254525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25835391672801761198169683 38753087509202641797254525)
    ·
      refine ⟨14532407815950990673970447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38753087509202641797254525 14532407815950990673970447)
      ·
        refine ⟨21798611723926486010955671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14532407815950990673970447 21798611723926486010955671)
        ·
          refine ⟨32697917585889729016433507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21798611723926486010955671 32697917585889729016433507)
          ·
            refine ⟨49046876378834593524650261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32697917585889729016433507 49046876378834593524650261)
            ·
              refine ⟨2299072330257871571467981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49046876378834593524650261 2299072330257871571467981)
              ·
                refine ⟨862152123846701839300493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2299072330257871571467981 862152123846701839300493)
                ·
                  refine ⟨323307046442513189737685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862152123846701839300493 323307046442513189737685)
                  ·
                    rfl

theorem cell20_708343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 3].length) (baseStart_708343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708343 prefixEnd_708343 := by exact prefixLift 708343
  have htrace : WordTrace (prefixWord ++ tailWord_708343) baseStart_708343 baseEnd_708343 := by
    simpa [prefixWord, tailWord_708343, baseEnd_708343] using wordTrace_append hprefix tailTrace_708343
  have hstable : (prefixWord ++ tailWord_708343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708343).length < 2 ^ (prefixWord ++ tailWord_708343).sum := by decide
  have hdescent : baseEnd_708343 < baseStart_708343 := by decide
  rcases family_descends (prefixWord ++ tailWord_708343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708412 : List Nat := [2, 2, 2, 2, 1, 1, 6, 4]
def baseStart_708412 : Nat := 118140960795 + 708412 * 2 ^ 59
def prefixEnd_708412 : Nat := 4983230072969 + 3 ^ 40 * 708412 * 2
def baseEnd_708412 : Nat := 107779513307551872145801

theorem tailTrace_708412 : CollatzResearch.WordTrace tailWord_708412 prefixEnd_708412 107779513307551872145801 := by
  unfold tailWord_708412
  simp only [CollatzResearch.WordTrace]
  refine ⟨12918954154775892991215745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17225272206367857321620993 12918954154775892991215745)
  ·
    refine ⟨9689215616081919743411809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12918954154775892991215745 9689215616081919743411809)
    ·
      refine ⟨7266911712061439807558857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9689215616081919743411809 7266911712061439807558857)
      ·
        refine ⟨5450183784046079855669143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7266911712061439807558857 5450183784046079855669143)
        ·
          refine ⟨8175275676069119783503715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5450183784046079855669143 8175275676069119783503715)
          ·
            refine ⟨12262913514103679675255573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8175275676069119783503715 12262913514103679675255573)
            ·
              refine ⟨574824070973609984777605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12262913514103679675255573 574824070973609984777605)
              ·
                refine ⟨107779513307551872145801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 574824070973609984777605 107779513307551872145801)
                ·
                  rfl

theorem cell20_708412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_708412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708412 prefixEnd_708412 := by exact prefixLift 708412
  have htrace : WordTrace (prefixWord ++ tailWord_708412) baseStart_708412 baseEnd_708412 := by
    simpa [prefixWord, tailWord_708412, baseEnd_708412] using wordTrace_append hprefix tailTrace_708412
  have hstable : (prefixWord ++ tailWord_708412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708412).length < 2 ^ (prefixWord ++ tailWord_708412).sum := by decide
  have hdescent : baseEnd_708412 < baseStart_708412 := by decide
  rcases family_descends (prefixWord ++ tailWord_708412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708429 : List Nat := [1, 6, 1, 2, 1, 3, 6]
def baseStart_708429 : Nat := 118140960795 + 708429 * 2 ^ 59
def prefixEnd_708429 : Nat := 4983230072969 + 3 ^ 40 * 708429 * 2
def baseEnd_708429 : Nat := 35927366576208790318963

theorem tailTrace_708429 : CollatzResearch.WordTrace tailWord_708429 prefixEnd_708429 35927366576208790318963 := by
  unfold tailWord_708429
  simp only [CollatzResearch.WordTrace]
  refine ⟨25838528350490197885800341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17225685566993465257200227 25838528350490197885800341)
  ·
    refine ⟨1211181016429228025896891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25838528350490197885800341 1211181016429228025896891)
    ·
      refine ⟨1816771524643842038845337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211181016429228025896891 1816771524643842038845337)
      ·
        refine ⟨1362578643482881529134003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1816771524643842038845337 1362578643482881529134003)
        ·
          refine ⟨2043867965224322293701005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362578643482881529134003 2043867965224322293701005)
          ·
            refine ⟨766450486959120860137877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2043867965224322293701005 766450486959120860137877)
            ·
              refine ⟨35927366576208790318963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 766450486959120860137877 35927366576208790318963)
              ·
                rfl

theorem cell20_708429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 6].length) (baseStart_708429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708429 prefixEnd_708429 := by exact prefixLift 708429
  have htrace : WordTrace (prefixWord ++ tailWord_708429) baseStart_708429 baseEnd_708429 := by
    simpa [prefixWord, tailWord_708429, baseEnd_708429] using wordTrace_append hprefix tailTrace_708429
  have hstable : (prefixWord ++ tailWord_708429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708429).length < 2 ^ (prefixWord ++ tailWord_708429).sum := by decide
  have hdescent : baseEnd_708429 < baseStart_708429 := by decide
  rcases family_descends (prefixWord ++ tailWord_708429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708433 : List Nat := [1, 2, 2, 1, 5, 1, 8]
def baseStart_708433 : Nat := 118140960795 + 708433 * 2 ^ 59
def prefixEnd_708433 : Nat := 4983230072969 + 3 ^ 40 * 708433 * 2
def baseEnd_708433 : Nat := 35927569432763652970813

theorem tailTrace_708433 : CollatzResearch.WordTrace tailWord_708433 prefixEnd_708433 35927569432763652970813 := by
  unfold tailWord_708433
  simp only [CollatzResearch.WordTrace]
  refine ⟨25838674242475706568945953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17225782828317137712630635 25838674242475706568945953)
  ·
    refine ⟨19379005681856779926709465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25838674242475706568945953 19379005681856779926709465)
    ·
      refine ⟨14534254261392584945032099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19379005681856779926709465 14534254261392584945032099)
      ·
        refine ⟨21801381392088877417548149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14534254261392584945032099 21801381392088877417548149)
        ·
          refine ⟨2043879505508332257895139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21801381392088877417548149 2043879505508332257895139)
          ·
            refine ⟨3065819258262498386842709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043879505508332257895139 3065819258262498386842709)
            ·
              refine ⟨35927569432763652970813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3065819258262498386842709 35927569432763652970813)
              ·
                rfl

theorem cell20_708433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 8].length) (baseStart_708433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708433 prefixEnd_708433 := by exact prefixLift 708433
  have htrace : WordTrace (prefixWord ++ tailWord_708433) baseStart_708433 baseEnd_708433 := by
    simpa [prefixWord, tailWord_708433, baseEnd_708433] using wordTrace_append hprefix tailTrace_708433
  have hstable : (prefixWord ++ tailWord_708433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708433).length < 2 ^ (prefixWord ++ tailWord_708433).sum := by decide
  have hdescent : baseEnd_708433 < baseStart_708433 := by decide
  rcases family_descends (prefixWord ++ tailWord_708433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708439 : List Nat := [1, 1, 3, 2, 5, 1, 3, 2, 2]
def baseStart_708439 : Nat := 118140960795 + 708439 * 2 ^ 59
def prefixEnd_708439 : Nat := 4983230072969 + 3 ^ 40 * 708439 * 2
def baseEnd_708439 : Nat := 323350863458363522537293

theorem tailTrace_708439 : CollatzResearch.WordTrace tailWord_708439 prefixEnd_708439 323350863458363522537293 := by
  unfold tailWord_708439
  simp only [CollatzResearch.WordTrace]
  refine ⟨25838893080453969593664371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17225928720302646395776247 25838893080453969593664371)
  ·
    refine ⟨38758339620680954390496557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25838893080453969593664371 38758339620680954390496557)
    ·
      refine ⟨14534377357755357896436209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38758339620680954390496557 14534377357755357896436209)
      ·
        refine ⟨10900783018316518422327157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14534377357755357896436209 10900783018316518422327157)
        ·
          refine ⟨1021948407967173602093171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10900783018316518422327157 1021948407967173602093171)
          ·
            refine ⟨1532922611950760403139757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021948407967173602093171 1532922611950760403139757)
            ·
              refine ⟨574845979481535151177409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1532922611950760403139757 574845979481535151177409)
              ·
                refine ⟨431134484611151363383057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574845979481535151177409 431134484611151363383057)
                ·
                  refine ⟨323350863458363522537293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431134484611151363383057 323350863458363522537293)
                  ·
                    rfl

theorem cell20_708439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 2].length) (baseStart_708439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708439 prefixEnd_708439 := by exact prefixLift 708439
  have htrace : WordTrace (prefixWord ++ tailWord_708439) baseStart_708439 baseEnd_708439 := by
    simpa [prefixWord, tailWord_708439, baseEnd_708439] using wordTrace_append hprefix tailTrace_708439
  have hstable : (prefixWord ++ tailWord_708439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708439).length < 2 ^ (prefixWord ++ tailWord_708439).sum := by decide
  have hdescent : baseEnd_708439 < baseStart_708439 := by decide
  rcases family_descends (prefixWord ++ tailWord_708439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708450 : List Nat := [3, 3, 2, 1, 2, 1, 1, 7]
def baseStart_708450 : Nat := 118140960795 + 708450 * 2 ^ 59
def prefixEnd_708450 : Nat := 4983230072969 + 3 ^ 40 * 708450 * 2
def baseEnd_708450 : Nat := 107785294719365457723527

theorem tailTrace_708450 : CollatzResearch.WordTrace tailWord_708450 prefixEnd_708450 107785294719365457723527 := by
  unfold tailWord_708450
  simp only [CollatzResearch.WordTrace]
  refine ⟨6459823570853529618078701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17226196188942745648209869 6459823570853529618078701)
  ·
    refine ⟨2422433839070073606779513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6459823570853529618078701 2422433839070073606779513)
    ·
      refine ⟨1816825379302555205084635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2422433839070073606779513 1816825379302555205084635)
      ·
        refine ⟨2725238068953832807626953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1816825379302555205084635 2725238068953832807626953)
        ·
          refine ⟨2043928551715374605720215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2725238068953832807626953 2043928551715374605720215)
          ·
            refine ⟨3065892827573061908580323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043928551715374605720215 3065892827573061908580323)
            ·
              refine ⟨4598839241359592862870485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3065892827573061908580323 4598839241359592862870485)
              ·
                refine ⟨107785294719365457723527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4598839241359592862870485 107785294719365457723527)
                ·
                  rfl

theorem cell20_708450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_708450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708450 prefixEnd_708450 := by exact prefixLift 708450
  have htrace : WordTrace (prefixWord ++ tailWord_708450) baseStart_708450 baseEnd_708450 := by
    simpa [prefixWord, tailWord_708450, baseEnd_708450] using wordTrace_append hprefix tailTrace_708450
  have hstable : (prefixWord ++ tailWord_708450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708450).length < 2 ^ (prefixWord ++ tailWord_708450).sum := by decide
  have hdescent : baseEnd_708450 < baseStart_708450 := by decide
  rcases family_descends (prefixWord ++ tailWord_708450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708488 : List Nat := [2, 1, 3, 3, 4, 7]
def baseStart_708488 : Nat := 118140960795 + 708488 * 2 ^ 59
def prefixEnd_708488 : Nat := 4983230072969 + 3 ^ 40 * 708488 * 2
def baseEnd_708488 : Nat := 11976786236797671477917

theorem tailTrace_708488 : CollatzResearch.WordTrace tailWord_708488 prefixEnd_708488 11976786236797671477917 := by
  unfold tailWord_708488
  simp only [CollatzResearch.WordTrace]
  refine ⟨12920340128638225481099059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17227120171517633974798745 12920340128638225481099059)
  ·
    refine ⟨19380510192957338221648589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12920340128638225481099059 19380510192957338221648589)
    ·
      refine ⟨7267691322359001833118221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19380510192957338221648589 7267691322359001833118221)
      ·
        refine ⟨2725384245884625687419333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7267691322359001833118221 2725384245884625687419333)
        ·
          refine ⟨511009546103367316391125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2725384245884625687419333 511009546103367316391125)
          ·
            refine ⟨11976786236797671477917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 511009546103367316391125 11976786236797671477917)
            ·
              rfl

theorem cell20_708488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 7].length) (baseStart_708488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708488 prefixEnd_708488 := by exact prefixLift 708488
  have htrace : WordTrace (prefixWord ++ tailWord_708488) baseStart_708488 baseEnd_708488 := by
    simpa [prefixWord, tailWord_708488, baseEnd_708488] using wordTrace_append hprefix tailTrace_708488
  have hstable : (prefixWord ++ tailWord_708488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708488).length < 2 ^ (prefixWord ++ tailWord_708488).sum := by decide
  have hdescent : baseEnd_708488 < baseStart_708488 := by decide
  rcases family_descends (prefixWord ++ tailWord_708488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708519 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 4]
def baseStart_708519 : Nat := 118140960795 + 708519 * 2 ^ 59
def prefixEnd_708519 : Nat := 4983230072969 + 3 ^ 40 * 708519 * 2
def baseEnd_708519 : Nat := 323387377638238799870299

theorem tailTrace_708519 : CollatzResearch.WordTrace tailWord_708519 prefixEnd_708519 323387377638238799870299 := by
  unfold tailWord_708519
  simp only [CollatzResearch.WordTrace]
  refine ⟨25841810920164143256576611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17227873946776095504384407 25841810920164143256576611)
  ·
    refine ⟨38762716380246214884864917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25841810920164143256576611 38762716380246214884864917)
    ·
      refine ⟨1817002330324041322728043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38762716380246214884864917 1817002330324041322728043)
      ·
        refine ⟨2725503495486061984092065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817002330324041322728043 2725503495486061984092065)
        ·
          refine ⟨2044127621614546488069049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2725503495486061984092065 2044127621614546488069049)
          ·
            refine ⟨1533095716210909866051787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2044127621614546488069049 1533095716210909866051787)
            ·
              refine ⟨2299643574316364799077681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533095716210909866051787 2299643574316364799077681)
              ·
                refine ⟨1724732680737273599308261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2299643574316364799077681 1724732680737273599308261)
                ·
                  refine ⟨323387377638238799870299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1724732680737273599308261 323387377638238799870299)
                  ·
                    rfl

theorem cell20_708519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_708519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708519 prefixEnd_708519 := by exact prefixLift 708519
  have htrace : WordTrace (prefixWord ++ tailWord_708519) baseStart_708519 baseEnd_708519 := by
    simpa [prefixWord, tailWord_708519, baseEnd_708519] using wordTrace_append hprefix tailTrace_708519
  have hstable : (prefixWord ++ tailWord_708519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708519).length < 2 ^ (prefixWord ++ tailWord_708519).sum := by decide
  have hdescent : baseEnd_708519 < baseStart_708519 := by decide
  rcases family_descends (prefixWord ++ tailWord_708519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708532 : List Nat := [2, 5, 2, 1, 2, 1, 2, 3, 2]
def baseStart_708532 : Nat := 118140960795 + 708532 * 2 ^ 59
def prefixEnd_708532 : Nat := 4983230072969 + 3 ^ 40 * 708532 * 2
def baseEnd_708532 : Nat := 323393311192468532436913

theorem tailTrace_708532 : CollatzResearch.WordTrace tailWord_708532 prefixEnd_708532 323393311192468532436913 := by
  unfold tailWord_708532
  simp only [CollatzResearch.WordTrace]
  refine ⟨12921142534558523238399925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17228190046078030984533233 12921142534558523238399925)
  ·
    refine ⟨1211357112614861553599993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12921142534558523238399925 1211357112614861553599993)
    ·
      refine ⟨908517834461146165199995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1211357112614861553599993 908517834461146165199995)
      ·
        refine ⟨1362776751691719247799993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 908517834461146165199995 1362776751691719247799993)
        ·
          refine ⟨1022082563768789435849995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1362776751691719247799993 1022082563768789435849995)
          ·
            refine ⟨1533123845653184153774993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022082563768789435849995 1533123845653184153774993)
            ·
              refine ⟨1149842884239888115331245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1533123845653184153774993 1149842884239888115331245)
              ·
                refine ⟨431191081589958043249217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1149842884239888115331245 431191081589958043249217)
                ·
                  refine ⟨323393311192468532436913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431191081589958043249217 323393311192468532436913)
                  ·
                    rfl

theorem cell20_708532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_708532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708532 prefixEnd_708532 := by exact prefixLift 708532
  have htrace : WordTrace (prefixWord ++ tailWord_708532) baseStart_708532 baseEnd_708532 := by
    simpa [prefixWord, tailWord_708532, baseEnd_708532] using wordTrace_append hprefix tailTrace_708532
  have hstable : (prefixWord ++ tailWord_708532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708532).length < 2 ^ (prefixWord ++ tailWord_708532).sum := by decide
  have hdescent : baseEnd_708532 < baseStart_708532 := by decide
  rcases family_descends (prefixWord ++ tailWord_708532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708592 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_708592 : Nat := 118140960795 + 708592 * 2 ^ 59
def prefixEnd_708592 : Nat := 4983230072969 + 3 ^ 40 * 708592 * 2
def baseEnd_708592 : Nat := 323420696827374990436667

theorem tailTrace_708592 : CollatzResearch.WordTrace tailWord_708592 prefixEnd_708592 323420696827374990436667 := by
  unfold tailWord_708592
  simp only [CollatzResearch.WordTrace]
  refine ⟨12922236724449838361992015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17229648965933117815989353 12922236724449838361992015)
  ·
    refine ⟨19383355086674757542988023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12922236724449838361992015 19383355086674757542988023)
    ·
      refine ⟨29075032630012136314482035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19383355086674757542988023 29075032630012136314482035)
      ·
        refine ⟨43612548945018204471723053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29075032630012136314482035 43612548945018204471723053)
        ·
          refine ⟨16354705854381826676896145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43612548945018204471723053 16354705854381826676896145)
          ·
            refine ⟨12266029390786370007672109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16354705854381826676896145 12266029390786370007672109)
            ·
              refine ⟨4599761021544888752877041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12266029390786370007672109 4599761021544888752877041)
              ·
                refine ⟨3449820766158666564657781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4599761021544888752877041 3449820766158666564657781)
                ·
                  refine ⟨323420696827374990436667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3449820766158666564657781 323420696827374990436667)
                  ·
                    rfl

theorem cell20_708592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_708592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708592 prefixEnd_708592 := by exact prefixLift 708592
  have htrace : WordTrace (prefixWord ++ tailWord_708592) baseStart_708592 baseEnd_708592 := by
    simpa [prefixWord, tailWord_708592, baseEnd_708592] using wordTrace_append hprefix tailTrace_708592
  have hstable : (prefixWord ++ tailWord_708592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708592).length < 2 ^ (prefixWord ++ tailWord_708592).sum := by decide
  have hdescent : baseEnd_708592 < baseStart_708592 := by decide
  rcases family_descends (prefixWord ++ tailWord_708592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708609 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 3]
def baseStart_708609 : Nat := 118140960795 + 708609 * 2 ^ 59
def prefixEnd_708609 : Nat := 4983230072969 + 3 ^ 40 * 708609 * 2
def baseEnd_708609 : Nat := 323428456090598486869931

theorem tailTrace_708609 : CollatzResearch.WordTrace tailWord_708609 prefixEnd_708609 323428456090598486869931 := by
  unfold tailWord_708609
  simp only [CollatzResearch.WordTrace]
  refine ⟨25845093489838088627352881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17230062326558725751568587 25845093489838088627352881)
  ·
    refine ⟨19383820117378566470514661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25845093489838088627352881 19383820117378566470514661)
    ·
      refine ⟨3634466272008481213221499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19383820117378566470514661 3634466272008481213221499)
      ·
        refine ⟨5451699408012721819832249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3634466272008481213221499 5451699408012721819832249)
        ·
          refine ⟨4088774556009541364874187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5451699408012721819832249 4088774556009541364874187)
          ·
            refine ⟨6133161834014312047311281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4088774556009541364874187 6133161834014312047311281)
            ·
              refine ⟨4599871375510734035483461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6133161834014312047311281 4599871375510734035483461)
              ·
                refine ⟨862475882908262631653149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4599871375510734035483461 862475882908262631653149)
                ·
                  refine ⟨323428456090598486869931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862475882908262631653149 323428456090598486869931)
                  ·
                    rfl

theorem cell20_708609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 3].length) (baseStart_708609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708609 prefixEnd_708609 := by exact prefixLift 708609
  have htrace : WordTrace (prefixWord ++ tailWord_708609) baseStart_708609 baseEnd_708609 := by
    simpa [prefixWord, tailWord_708609, baseEnd_708609] using wordTrace_append hprefix tailTrace_708609
  have hstable : (prefixWord ++ tailWord_708609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708609).length < 2 ^ (prefixWord ++ tailWord_708609).sum := by decide
  have hdescent : baseEnd_708609 < baseStart_708609 := by decide
  rcases family_descends (prefixWord ++ tailWord_708609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708664 : List Nat := [2, 1, 2, 1, 6, 1, 2, 2, 3]
def baseStart_708664 : Nat := 118140960795 + 708664 * 2 ^ 59
def prefixEnd_708664 : Nat := 4983230072969 + 3 ^ 40 * 708664 * 2
def baseEnd_708664 : Nat := 323453559589262740036373

theorem tailTrace_708664 : CollatzResearch.WordTrace tailWord_708664 prefixEnd_708664 323453559589262740036373 := by
  unfold tailWord_708664
  simp only [CollatzResearch.WordTrace]
  refine ⟨12923549752319416510302523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17231399669759222013736697 12923549752319416510302523)
  ·
    refine ⟨19385324628479124765453785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12923549752319416510302523 19385324628479124765453785)
    ·
      refine ⟨14538993471359343574090339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19385324628479124765453785 14538993471359343574090339)
      ·
        refine ⟨21808490207039015361135509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14538993471359343574090339 21808490207039015361135509)
        ·
          refine ⟨1022272978454953845053227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21808490207039015361135509 1022272978454953845053227)
          ·
            refine ⟨1533409467682430767579841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022272978454953845053227 1533409467682430767579841)
            ·
              refine ⟨1150057100761823075684881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1533409467682430767579841 1150057100761823075684881)
              ·
                refine ⟨862542825571367306763661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150057100761823075684881 862542825571367306763661)
                ·
                  refine ⟨323453559589262740036373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862542825571367306763661 323453559589262740036373)
                  ·
                    rfl

theorem cell20_708664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_708664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708664 prefixEnd_708664 := by exact prefixLift 708664
  have htrace : WordTrace (prefixWord ++ tailWord_708664) baseStart_708664 baseEnd_708664 := by
    simpa [prefixWord, tailWord_708664, baseEnd_708664] using wordTrace_append hprefix tailTrace_708664
  have hstable : (prefixWord ++ tailWord_708664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708664).length < 2 ^ (prefixWord ++ tailWord_708664).sum := by decide
  have hdescent : baseEnd_708664 < baseStart_708664 := by decide
  rcases family_descends (prefixWord ++ tailWord_708664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708709 : List Nat := [1, 3, 1, 3, 2, 2, 1, 5, 2]
def baseStart_708709 : Nat := 118140960795 + 708709 * 2 ^ 59
def prefixEnd_708709 : Nat := 4983230072969 + 3 ^ 40 * 708709 * 2
def baseEnd_708709 : Nat := 323474098815442583536189

theorem tailTrace_708709 : CollatzResearch.WordTrace tailWord_708709 prefixEnd_708709 323474098815442583536189 := by
  unfold tailWord_708709
  simp only [CollatzResearch.WordTrace]
  refine ⟨25848740789475805705993181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17232493859650537137328787 25848740789475805705993181)
  ·
    refine ⟨9693277796053427139747443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25848740789475805705993181 9693277796053427139747443)
    ·
      refine ⟨14539916694080140709621165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9693277796053427139747443 14539916694080140709621165)
      ·
        refine ⟨5452468760280052766107937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14539916694080140709621165 5452468760280052766107937)
        ·
          refine ⟨4089351570210039574580953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5452468760280052766107937 4089351570210039574580953)
          ·
            refine ⟨3067013677657529680935715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4089351570210039574580953 3067013677657529680935715)
            ·
              refine ⟨4600520516486294521403573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3067013677657529680935715 4600520516486294521403573)
              ·
                refine ⟨431298798420590111381585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4600520516486294521403573 431298798420590111381585)
                ·
                  refine ⟨323474098815442583536189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431298798420590111381585 323474098815442583536189)
                  ·
                    rfl

theorem cell20_708709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_708709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708709 prefixEnd_708709 := by exact prefixLift 708709
  have htrace : WordTrace (prefixWord ++ tailWord_708709) baseStart_708709 baseEnd_708709 := by
    simpa [prefixWord, tailWord_708709, baseEnd_708709] using wordTrace_append hprefix tailTrace_708709
  have hstable : (prefixWord ++ tailWord_708709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708709).length < 2 ^ (prefixWord ++ tailWord_708709).sum := by decide
  have hdescent : baseEnd_708709 < baseStart_708709 := by decide
  rcases family_descends (prefixWord ++ tailWord_708709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708713 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 6]
def baseStart_708713 : Nat := 118140960795 + 708713 * 2 ^ 59
def prefixEnd_708713 : Nat := 4983230072969 + 3 ^ 40 * 708713 * 2
def baseEnd_708713 : Nat := 323475924524436347402839

theorem tailTrace_708713 : CollatzResearch.WordTrace tailWord_708713 prefixEnd_708713 323475924524436347402839 := by
  unfold tailWord_708713
  simp only [CollatzResearch.WordTrace]
  refine ⟨25848886681461314389138793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17232591120974209592759195 25848886681461314389138793)
  ·
    refine ⟨19386665011095985791854095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25848886681461314389138793 19386665011095985791854095)
    ·
      refine ⟨29079997516643978687781143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19386665011095985791854095 29079997516643978687781143)
      ·
        refine ⟨43619996274965968031671715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29079997516643978687781143 43619996274965968031671715)
        ·
          refine ⟨65429994412448952047507573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43619996274965968031671715 65429994412448952047507573)
          ·
            refine ⟨6134061976167089254453835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65429994412448952047507573 6134061976167089254453835)
            ·
              refine ⟨9201092964250633881680753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6134061976167089254453835 9201092964250633881680753)
              ·
                refine ⟨6900819723187975411260565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9201092964250633881680753 6900819723187975411260565)
                ·
                  refine ⟨323475924524436347402839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6900819723187975411260565 323475924524436347402839)
                  ·
                    rfl

theorem cell20_708713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_708713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708713 prefixEnd_708713 := by exact prefixLift 708713
  have htrace : WordTrace (prefixWord ++ tailWord_708713) baseStart_708713 baseEnd_708713 := by
    simpa [prefixWord, tailWord_708713, baseEnd_708713] using wordTrace_append hprefix tailTrace_708713
  have hstable : (prefixWord ++ tailWord_708713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708713).length < 2 ^ (prefixWord ++ tailWord_708713).sum := by decide
  have hdescent : baseEnd_708713 < baseStart_708713 := by decide
  rcases family_descends (prefixWord ++ tailWord_708713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708726 : List Nat := [5, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_708726 : Nat := 118140960795 + 708726 * 2 ^ 59
def prefixEnd_708726 : Nat := 4983230072969 + 3 ^ 40 * 708726 * 2
def baseEnd_708726 : Nat := 323481858078666079969453

theorem tailTrace_708726 : CollatzResearch.WordTrace tailWord_708726 prefixEnd_708726 323481858078666079969453 := by
  unfold tailWord_708726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615585051900888600585127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17232907220276145072908021 1615585051900888600585127)
  ·
    refine ⟨2423377577851332900877691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1615585051900888600585127 2423377577851332900877691)
    ·
      refine ⟨3635066366776999351316537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2423377577851332900877691 3635066366776999351316537)
      ·
        refine ⟨2726299775082749513487403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3635066366776999351316537 2726299775082749513487403)
        ·
          refine ⟨4089449662624124270231105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2726299775082749513487403 4089449662624124270231105)
          ·
            refine ⟨3067087246968093202673329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4089449662624124270231105 3067087246968093202673329)
            ·
              refine ⟨2300315435226069902004997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3067087246968093202673329 2300315435226069902004997)
              ·
                refine ⟨431309144104888106625937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2300315435226069902004997 431309144104888106625937)
                ·
                  refine ⟨323481858078666079969453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431309144104888106625937 323481858078666079969453)
                  ·
                    rfl

theorem cell20_708726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_708726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708726 prefixEnd_708726 := by exact prefixLift 708726
  have htrace : WordTrace (prefixWord ++ tailWord_708726) baseStart_708726 baseEnd_708726 := by
    simpa [prefixWord, tailWord_708726, baseEnd_708726] using wordTrace_append hprefix tailTrace_708726
  have hstable : (prefixWord ++ tailWord_708726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708726).length < 2 ^ (prefixWord ++ tailWord_708726).sum := by decide
  have hdescent : baseEnd_708726 < baseStart_708726 := by decide
  rcases family_descends (prefixWord ++ tailWord_708726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708740 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 3]
def baseStart_708740 : Nat := 118140960795 + 708740 * 2 ^ 59
def prefixEnd_708740 : Nat := 4983230072969 + 3 ^ 40 * 708740 * 2
def baseEnd_708740 : Nat := 323488248060144253502729

theorem tailTrace_708740 : CollatzResearch.WordTrace tailWord_708740 prefixEnd_708740 323488248060144253502729 := by
  unfold tailWord_708740
  simp only [CollatzResearch.WordTrace]
  refine ⟨12924935726181749000185837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17233247634908998666914449 12924935726181749000185837)
  ·
    refine ⟨4846850897318155875069689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12924935726181749000185837 4846850897318155875069689)
    ·
      refine ⟨3635138172988616906302267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4846850897318155875069689 3635138172988616906302267)
      ·
        refine ⟨5452707259482925359453401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3635138172988616906302267 5452707259482925359453401)
        ·
          refine ⟨4089530444612194019590051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5452707259482925359453401 4089530444612194019590051)
          ·
            refine ⟨6134295666918291029385077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089530444612194019590051 6134295666918291029385077)
            ·
              refine ⟨575090218773589784004851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6134295666918291029385077 575090218773589784004851)
              ·
                refine ⟨862635328160384676007277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575090218773589784004851 862635328160384676007277)
                ·
                  refine ⟨323488248060144253502729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862635328160384676007277 323488248060144253502729)
                  ·
                    rfl

theorem cell20_708740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_708740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708740 prefixEnd_708740 := by exact prefixLift 708740
  have htrace : WordTrace (prefixWord ++ tailWord_708740) baseStart_708740 baseEnd_708740 := by
    simpa [prefixWord, tailWord_708740, baseEnd_708740] using wordTrace_append hprefix tailTrace_708740
  have hstable : (prefixWord ++ tailWord_708740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708740).length < 2 ^ (prefixWord ++ tailWord_708740).sum := by decide
  have hdescent : baseEnd_708740 < baseStart_708740 := by decide
  rcases family_descends (prefixWord ++ tailWord_708740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708750 : List Nat := [4, 1, 1, 3, 4, 1, 2, 4]
def baseStart_708750 : Nat := 118140960795 + 708750 * 2 ^ 59
def prefixEnd_708750 : Nat := 4983230072969 + 3 ^ 40 * 708750 * 2
def baseEnd_708750 : Nat := 107830937444209554389785

theorem tailTrace_708750 : CollatzResearch.WordTrace tailWord_708750 prefixEnd_708750 107830937444209554389785 := by
  unfold tailWord_708750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231279522790908713529463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17233490788218179805490469 3231279522790908713529463)
  ·
    refine ⟨4846919284186363070294195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3231279522790908713529463 4846919284186363070294195)
    ·
      refine ⟨7270378926279544605441293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4846919284186363070294195 7270378926279544605441293)
      ·
        refine ⟨2726392097354829227040485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7270378926279544605441293 2726392097354829227040485)
        ·
          refine ⟨511198518254030480070091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2726392097354829227040485 511198518254030480070091)
          ·
            refine ⟨766797777381045720105137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511198518254030480070091 766797777381045720105137)
            ·
              refine ⟨575098333035784290078853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 766797777381045720105137 575098333035784290078853)
              ·
                refine ⟨107830937444209554389785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 575098333035784290078853 107830937444209554389785)
                ·
                  rfl

theorem cell20_708750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_708750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708750 prefixEnd_708750 := by exact prefixLift 708750
  have htrace : WordTrace (prefixWord ++ tailWord_708750) baseStart_708750 baseEnd_708750 := by
    simpa [prefixWord, tailWord_708750, baseEnd_708750] using wordTrace_append hprefix tailTrace_708750
  have hstable : (prefixWord ++ tailWord_708750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708750).length < 2 ^ (prefixWord ++ tailWord_708750).sum := by decide
  have hdescent : baseEnd_708750 < baseStart_708750 := by decide
  rcases family_descends (prefixWord ++ tailWord_708750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708781 : List Nat := [1, 5, 2, 1, 2, 2, 3, 2, 2]
def baseStart_708781 : Nat := 118140960795 + 708781 * 2 ^ 59
def prefixEnd_708781 : Nat := 4983230072969 + 3 ^ 40 * 708781 * 2
def baseEnd_708781 : Nat := 323506961577330333135895

theorem tailTrace_708781 : CollatzResearch.WordTrace tailWord_708781 prefixEnd_708781 323506961577330333135895 := by
  unfold tailWord_708781
  simp only [CollatzResearch.WordTrace]
  refine ⟨25851366845214962002614197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17234244563476641335076131 25851366845214962002614197)
  ·
    refine ⟨2423565641738902687745081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25851366845214962002614197 2423565641738902687745081)
    ·
      refine ⟨1817674231304177015808811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2423565641738902687745081 1817674231304177015808811)
      ·
        refine ⟨2726511346956265523713217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1817674231304177015808811 2726511346956265523713217)
        ·
          refine ⟨2044883510217199142784913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2726511346956265523713217 2044883510217199142784913)
          ·
            refine ⟨1533662632662899357088685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2044883510217199142784913 1533662632662899357088685)
            ·
              refine ⟨575123487248587258908257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1533662632662899357088685 575123487248587258908257)
              ·
                refine ⟨431342615436440444181193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575123487248587258908257 431342615436440444181193)
                ·
                  refine ⟨323506961577330333135895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431342615436440444181193 323506961577330333135895)
                  ·
                    rfl

theorem cell20_708781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_708781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708781 prefixEnd_708781 := by exact prefixLift 708781
  have htrace : WordTrace (prefixWord ++ tailWord_708781) baseStart_708781 baseEnd_708781 := by
    simpa [prefixWord, tailWord_708781, baseEnd_708781] using wordTrace_append hprefix tailTrace_708781
  have hstable : (prefixWord ++ tailWord_708781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708781).length < 2 ^ (prefixWord ++ tailWord_708781).sum := by decide
  have hdescent : baseEnd_708781 < baseStart_708781 := by decide
  rcases family_descends (prefixWord ++ tailWord_708781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708837 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 3]
def baseStart_708837 : Nat := 118140960795 + 708837 * 2 ^ 59
def prefixEnd_708837 : Nat := 4983230072969 + 3 ^ 40 * 708837 * 2
def baseEnd_708837 : Nat := 323532521503243027268999

theorem tailTrace_708837 : CollatzResearch.WordTrace tailWord_708837 prefixEnd_708837 323532521503243027268999 := by
  unfold tailWord_708837
  simp only [CollatzResearch.WordTrace]
  refine ⟨25853409333012083566652765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17235606222008055711101843 25853409333012083566652765)
  ·
    refine ⟨9695028499879531337494787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25853409333012083566652765 9695028499879531337494787)
    ·
      refine ⟨14542542749819297006242181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9695028499879531337494787 14542542749819297006242181)
      ·
        refine ⟨2726726765591118188670409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14542542749819297006242181 2726726765591118188670409)
        ·
          refine ⟨2045045074193338641502807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2726726765591118188670409 2045045074193338641502807)
          ·
            refine ⟨3067567611290007962254211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045045074193338641502807 3067567611290007962254211)
            ·
              refine ⟨4601351416935011943381317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3067567611290007962254211 4601351416935011943381317)
              ·
                refine ⟨862753390675314739383997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4601351416935011943381317 862753390675314739383997)
                ·
                  refine ⟨323532521503243027268999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862753390675314739383997 323532521503243027268999)
                  ·
                    rfl

theorem cell20_708837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_708837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708837 prefixEnd_708837 := by exact prefixLift 708837
  have htrace : WordTrace (prefixWord ++ tailWord_708837) baseStart_708837 baseEnd_708837 := by
    simpa [prefixWord, tailWord_708837, baseEnd_708837] using wordTrace_append hprefix tailTrace_708837
  have hstable : (prefixWord ++ tailWord_708837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708837).length < 2 ^ (prefixWord ++ tailWord_708837).sum := by decide
  have hdescent : baseEnd_708837 < baseStart_708837 := by decide
  rcases family_descends (prefixWord ++ tailWord_708837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708840 : List Nat := [2, 1, 4, 1, 2, 2, 4, 2, 2]
def baseStart_708840 : Nat := 118140960795 + 708840 * 2 ^ 59
def prefixEnd_708840 : Nat := 4983230072969 + 3 ^ 40 * 708840 * 2
def baseEnd_708840 : Nat := 323533890784988350168987

theorem tailTrace_708840 : CollatzResearch.WordTrace tailWord_708840 prefixEnd_708840 323533890784988350168987 := by
  unfold tailWord_708840
  simp only [CollatzResearch.WordTrace]
  refine ⟨12926759376000607539505987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17235679168000810052674649 12926759376000607539505987)
  ·
    refine ⟨19390139064000911309258981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12926759376000607539505987 19390139064000911309258981)
    ·
      refine ⟨3635651074500170870486059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19390139064000911309258981 3635651074500170870486059)
      ·
        refine ⟨5453476611750256305729089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3635651074500170870486059 5453476611750256305729089)
        ·
          refine ⟨4090107458812692229296817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5453476611750256305729089 4090107458812692229296817)
          ·
            refine ⟨3067580594109519171972613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4090107458812692229296817 3067580594109519171972613)
            ·
              refine ⟨575171361395534844744865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3067580594109519171972613 575171361395534844744865)
              ·
                refine ⟨431378521046651133558649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575171361395534844744865 431378521046651133558649)
                ·
                  refine ⟨323533890784988350168987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431378521046651133558649 323533890784988350168987)
                  ·
                    rfl

theorem cell20_708840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 2].length) (baseStart_708840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708840 prefixEnd_708840 := by exact prefixLift 708840
  have htrace : WordTrace (prefixWord ++ tailWord_708840) baseStart_708840 baseEnd_708840 := by
    simpa [prefixWord, tailWord_708840, baseEnd_708840] using wordTrace_append hprefix tailTrace_708840
  have hstable : (prefixWord ++ tailWord_708840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708840).length < 2 ^ (prefixWord ++ tailWord_708840).sum := by decide
  have hdescent : baseEnd_708840 < baseStart_708840 := by decide
  rcases family_descends (prefixWord ++ tailWord_708840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708965 : List Nat := [1, 3, 1, 3, 1, 4, 2, 5]
def baseStart_708965 : Nat := 118140960795 + 708965 * 2 ^ 59
def prefixEnd_708965 : Nat := 4983230072969 + 3 ^ 40 * 708965 * 2
def baseEnd_708965 : Nat := 107863648063681157000603

theorem tailTrace_708965 : CollatzResearch.WordTrace tailWord_708965 prefixEnd_708965 107863648063681157000603 := by
  unfold tailWord_708965
  simp only [CollatzResearch.WordTrace]
  refine ⟨25858077876548361427312349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17238718584365574284874899 25858077876548361427312349)
  ·
    refine ⟨9696779203705635535242131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25858077876548361427312349 9696779203705635535242131)
    ·
      refine ⟨14545168805558453302863197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9696779203705635535242131 14545168805558453302863197)
      ·
        refine ⟨5454438302084419988573699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14545168805558453302863197 5454438302084419988573699)
        ·
          refine ⟨8181657453126629982860549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5454438302084419988573699 8181657453126629982860549)
          ·
            refine ⟨1534060772461243121786353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8181657453126629982860549 1534060772461243121786353)
            ·
              refine ⟨1150545579345932341339765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1534060772461243121786353 1150545579345932341339765)
              ·
                refine ⟨107863648063681157000603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1150545579345932341339765 107863648063681157000603)
                ·
                  rfl

theorem cell20_708965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 5].length) (baseStart_708965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708965 prefixEnd_708965 := by exact prefixLift 708965
  have htrace : WordTrace (prefixWord ++ tailWord_708965) baseStart_708965 baseEnd_708965 := by
    simpa [prefixWord, tailWord_708965, baseEnd_708965] using wordTrace_append hprefix tailTrace_708965
  have hstable : (prefixWord ++ tailWord_708965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708965).length < 2 ^ (prefixWord ++ tailWord_708965).sum := by decide
  have hdescent : baseEnd_708965 < baseStart_708965 := by decide
  rcases family_descends (prefixWord ++ tailWord_708965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_708968 : List Nat := [2, 1, 4, 2, 2, 1, 4, 1, 3]
def baseStart_708968 : Nat := 118140960795 + 708968 * 2 ^ 59
def prefixEnd_708968 : Nat := 4983230072969 + 3 ^ 40 * 708968 * 2
def baseEnd_708968 : Nat := 323592313472788793901797

theorem tailTrace_708968 : CollatzResearch.WordTrace tailWord_708968 prefixEnd_708968 323592313472788793901797 := by
  unfold tailWord_708968
  simp only [CollatzResearch.WordTrace]
  refine ⟨12929093647768746469835779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17238791530358328626447705 12929093647768746469835779)
  ·
    refine ⟨19393640471653119704753669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12929093647768746469835779 19393640471653119704753669)
    ·
      refine ⟨3636307588434959944641313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19393640471653119704753669 3636307588434959944641313)
      ·
        refine ⟨2727230691326219958480985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3636307588434959944641313 2727230691326219958480985)
        ·
          refine ⟨2045423018494664968860739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2727230691326219958480985 2045423018494664968860739)
          ·
            refine ⟨3068134527741997453291109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2045423018494664968860739 3068134527741997453291109)
            ·
              refine ⟨575275223951624522492083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3068134527741997453291109 575275223951624522492083)
              ·
                refine ⟨862912835927436783738125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575275223951624522492083 862912835927436783738125)
                ·
                  refine ⟨323592313472788793901797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862912835927436783738125 323592313472788793901797)
                  ·
                    rfl

theorem cell20_708968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_708968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_708968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_708968 prefixEnd_708968 := by exact prefixLift 708968
  have htrace : WordTrace (prefixWord ++ tailWord_708968) baseStart_708968 baseEnd_708968 := by
    simpa [prefixWord, tailWord_708968, baseEnd_708968] using wordTrace_append hprefix tailTrace_708968
  have hstable : (prefixWord ++ tailWord_708968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_708968).length < 2 ^ (prefixWord ++ tailWord_708968).sum := by decide
  have hdescent : baseEnd_708968 < baseStart_708968 := by decide
  rcases family_descends (prefixWord ++ tailWord_708968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709006 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_709006 : Nat := 118140960795 + 709006 * 2 ^ 59
def prefixEnd_709006 : Nat := 4983230072969 + 3 ^ 40 * 709006 * 2
def baseEnd_709006 : Nat := 323609657708229550634975

theorem tailTrace_709006 : CollatzResearch.WordTrace tailWord_709006 prefixEnd_709006 323609657708229550634975 := by
  unfold tailWord_709006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3232446658674978178694359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17239715512933216953036581 3232446658674978178694359)
  ·
    refine ⟨4848669988012467268041539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3232446658674978178694359 4848669988012467268041539)
    ·
      refine ⟨7273004982018700902062309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4848669988012467268041539 7273004982018700902062309)
      ·
        refine ⟨1363688434128506419136683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7273004982018700902062309 1363688434128506419136683)
        ·
          refine ⟨2045532651192759628705025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363688434128506419136683 2045532651192759628705025)
          ·
            refine ⟨1534149488394569721528769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2045532651192759628705025 1534149488394569721528769)
            ·
              refine ⟨1150612116295927291146577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1534149488394569721528769 1150612116295927291146577)
              ·
                refine ⟨862959087221945468359933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150612116295927291146577 862959087221945468359933)
                ·
                  refine ⟨323609657708229550634975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 862959087221945468359933 323609657708229550634975)
                  ·
                    rfl

theorem cell20_709006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_709006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709006 prefixEnd_709006 := by exact prefixLift 709006
  have htrace : WordTrace (prefixWord ++ tailWord_709006) baseStart_709006 baseEnd_709006 := by
    simpa [prefixWord, tailWord_709006, baseEnd_709006] using wordTrace_append hprefix tailTrace_709006
  have hstable : (prefixWord ++ tailWord_709006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709006).length < 2 ^ (prefixWord ++ tailWord_709006).sum := by decide
  have hdescent : baseEnd_709006 < baseStart_709006 := by decide
  rcases family_descends (prefixWord ++ tailWord_709006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709017 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 4]
def baseStart_709017 : Nat := 118140960795 + 709017 * 2 ^ 59
def prefixEnd_709017 : Nat := 4983230072969 + 3 ^ 40 * 709017 * 2
def baseEnd_709017 : Nat := 323614678407962401268263

theorem tailTrace_709017 : CollatzResearch.WordTrace tailWord_709017 prefixEnd_709017 323614678407962401268263 := by
  unfold tailWord_709017
  simp only [CollatzResearch.WordTrace]
  refine ⟨25859974472359974308205305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17239982981573316205470203 25859974472359974308205305)
  ·
    refine ⟨19394980854269980731153979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25859974472359974308205305 19394980854269980731153979)
    ·
      refine ⟨29092471281404971096730969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19394980854269980731153979 29092471281404971096730969)
      ·
        refine ⟨21819353461053728322548227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29092471281404971096730969 21819353461053728322548227)
        ·
          refine ⟨32729030191580592483822341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21819353461053728322548227 32729030191580592483822341)
          ·
            refine ⟨6136693160921361090716689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32729030191580592483822341 6136693160921361090716689)
            ·
              refine ⟨4602519870691020818037517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6136693160921361090716689 4602519870691020818037517)
              ·
                refine ⟨1725944951509132806764069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4602519870691020818037517 1725944951509132806764069)
                ·
                  refine ⟨323614678407962401268263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1725944951509132806764069 323614678407962401268263)
                  ·
                    rfl

theorem cell20_709017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_709017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709017 prefixEnd_709017 := by exact prefixLift 709017
  have htrace : WordTrace (prefixWord ++ tailWord_709017) baseStart_709017 baseEnd_709017 := by
    simpa [prefixWord, tailWord_709017, baseEnd_709017] using wordTrace_append hprefix tailTrace_709017
  have hstable : (prefixWord ++ tailWord_709017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709017).length < 2 ^ (prefixWord ++ tailWord_709017).sum := by decide
  have hdescent : baseEnd_709017 < baseStart_709017 := by decide
  rcases family_descends (prefixWord ++ tailWord_709017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709037 : List Nat := [1, 5, 2, 2, 2, 1, 3, 4]
def baseStart_709037 : Nat := 118140960795 + 709037 * 2 ^ 59
def prefixEnd_709037 : Nat := 4983230072969 + 3 ^ 40 * 709037 * 2
def baseEnd_709037 : Nat := 107874602317643740200505

theorem tailTrace_709037 : CollatzResearch.WordTrace tailWord_709037 prefixEnd_709037 107874602317643740200505 := by
  unfold tailWord_709037
  simp only [CollatzResearch.WordTrace]
  refine ⟨25860703932287517723933365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17240469288191678482622243 25860703932287517723933365)
  ·
    refine ⟨2424440993651954786618753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25860703932287517723933365 2424440993651954786618753)
    ·
      refine ⟨1818330745238966089964065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2424440993651954786618753 1818330745238966089964065)
      ·
        refine ⟨1363748058929224567473049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1818330745238966089964065 1363748058929224567473049)
        ·
          refine ⟨1022811044196918425604787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1363748058929224567473049 1022811044196918425604787)
          ·
            refine ⟨1534216566295377638407181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022811044196918425604787 1534216566295377638407181)
            ·
              refine ⟨575331212360766614402693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1534216566295377638407181 575331212360766614402693)
              ·
                refine ⟨107874602317643740200505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 575331212360766614402693 107874602317643740200505)
                ·
                  rfl

theorem cell20_709037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 4].length) (baseStart_709037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709037 prefixEnd_709037 := by exact prefixLift 709037
  have htrace : WordTrace (prefixWord ++ tailWord_709037) baseStart_709037 baseEnd_709037 := by
    simpa [prefixWord, tailWord_709037, baseEnd_709037] using wordTrace_append hprefix tailTrace_709037
  have hstable : (prefixWord ++ tailWord_709037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709037).length < 2 ^ (prefixWord ++ tailWord_709037).sum := by decide
  have hdescent : baseEnd_709037 < baseStart_709037 := by decide
  rcases family_descends (prefixWord ++ tailWord_709037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709057 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 3]
def baseStart_709057 : Nat := 118140960795 + 709057 * 2 ^ 59
def prefixEnd_709057 : Nat := 4983230072969 + 3 ^ 40 * 709057 * 2
def baseEnd_709057 : Nat := 323632935497900039934767

theorem tailTrace_709057 : CollatzResearch.WordTrace tailWord_709057 prefixEnd_709057 323632935497900039934767 := by
  unfold tailWord_709057
  simp only [CollatzResearch.WordTrace]
  refine ⟨25861433392215061139661425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17240955594810040759774283 25861433392215061139661425)
  ·
    refine ⟨19396075044161295854746069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25861433392215061139661425 19396075044161295854746069)
    ·
      refine ⟨454595508847530371595611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19396075044161295854746069 454595508847530371595611)
      ·
        refine ⟨681893263271295557393417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454595508847530371595611 681893263271295557393417)
        ·
          refine ⟨511419947453471668045063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681893263271295557393417 511419947453471668045063)
          ·
            refine ⟨767129921180207502067595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511419947453471668045063 767129921180207502067595)
            ·
              refine ⟨1150694881770311253101393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767129921180207502067595 1150694881770311253101393)
              ·
                refine ⟨863021161327733439826045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150694881770311253101393 863021161327733439826045)
                ·
                  refine ⟨323632935497900039934767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863021161327733439826045 323632935497900039934767)
                  ·
                    rfl

theorem cell20_709057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 3].length) (baseStart_709057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709057 prefixEnd_709057 := by exact prefixLift 709057
  have htrace : WordTrace (prefixWord ++ tailWord_709057) baseStart_709057 baseEnd_709057 := by
    simpa [prefixWord, tailWord_709057, baseEnd_709057] using wordTrace_append hprefix tailTrace_709057
  have hstable : (prefixWord ++ tailWord_709057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709057).length < 2 ^ (prefixWord ++ tailWord_709057).sum := by decide
  have hdescent : baseEnd_709057 < baseStart_709057 := by decide
  rcases family_descends (prefixWord ++ tailWord_709057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709096 : List Nat := [2, 1, 4, 1, 1, 5, 2, 4]
def baseStart_709096 : Nat := 118140960795 + 709096 * 2 ^ 59
def prefixEnd_709096 : Nat := 4983230072969 + 3 ^ 40 * 709096 * 2
def baseEnd_709096 : Nat := 107883578720196412544869

theorem tailTrace_709096 : CollatzResearch.WordTrace tailWord_709096 prefixEnd_709096 107883578720196412544869 := by
  unfold tailWord_709096
  simp only [CollatzResearch.WordTrace]
  refine ⟨12931427919536885400165571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17241903892715847200220761 12931427919536885400165571)
  ·
    refine ⟨19397141879305328100248357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12931427919536885400165571 19397141879305328100248357)
    ·
      refine ⟨3636964102369749018796567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19397141879305328100248357 3636964102369749018796567)
      ·
        refine ⟨5455446153554623528194851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3636964102369749018796567 5455446153554623528194851)
        ·
          refine ⟨8183169230331935292292277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5455446153554623528194851 8183169230331935292292277)
          ·
            refine ⟨767172115343618933652401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8183169230331935292292277 767172115343618933652401)
            ·
              refine ⟨575379086507714200239301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 767172115343618933652401 575379086507714200239301)
              ·
                refine ⟨107883578720196412544869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 575379086507714200239301 107883578720196412544869)
                ·
                  rfl

theorem cell20_709096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_709096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709096 prefixEnd_709096 := by exact prefixLift 709096
  have htrace : WordTrace (prefixWord ++ tailWord_709096) baseStart_709096 baseEnd_709096 := by
    simpa [prefixWord, tailWord_709096, baseEnd_709096] using wordTrace_append hprefix tailTrace_709096
  have hstable : (prefixWord ++ tailWord_709096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709096).length < 2 ^ (prefixWord ++ tailWord_709096).sum := by decide
  have hdescent : baseEnd_709096 < baseStart_709096 := by decide
  rcases family_descends (prefixWord ++ tailWord_709096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709100 : List Nat := [2, 2, 1, 1, 2, 1, 5, 6]
def baseStart_709100 : Nat := 118140960795 + 709100 * 2 ^ 59
def prefixEnd_709100 : Nat := 4983230072969 + 3 ^ 40 * 709100 * 2
def baseEnd_709100 : Nat := 107884187289861000500419

theorem tailTrace_709100 : CollatzResearch.WordTrace tailWord_709100 prefixEnd_709100 107884187289861000500419 := by
  unfold tailWord_709100
  simp only [CollatzResearch.WordTrace]
  refine ⟨12931500865529639741738377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17242001154039519655651169 12931500865529639741738377)
  ·
    refine ⟨9698625649147229806303783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12931500865529639741738377 9698625649147229806303783)
    ·
      refine ⟨14547938473720844709455675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9698625649147229806303783 14547938473720844709455675)
      ·
        refine ⟨21821907710581267064183513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14547938473720844709455675 21821907710581267064183513)
        ·
          refine ⟨16366430782935950298137635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21821907710581267064183513 16366430782935950298137635)
          ·
            refine ⟨24549646174403925447206453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16366430782935950298137635 24549646174403925447206453)
            ·
              refine ⟨2301529328850368010675605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24549646174403925447206453 2301529328850368010675605)
              ·
                refine ⟨107884187289861000500419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2301529328850368010675605 107884187289861000500419)
                ·
                  rfl

theorem cell20_709100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_709100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709100 prefixEnd_709100 := by exact prefixLift 709100
  have htrace : WordTrace (prefixWord ++ tailWord_709100) baseStart_709100 baseEnd_709100 := by
    simpa [prefixWord, tailWord_709100, baseEnd_709100] using wordTrace_append hprefix tailTrace_709100
  have hstable : (prefixWord ++ tailWord_709100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709100).length < 2 ^ (prefixWord ++ tailWord_709100).sum := by decide
  have hdescent : baseEnd_709100 < baseStart_709100 := by decide
  rcases family_descends (prefixWord ++ tailWord_709100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709107 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_709107 : Nat := 118140960795 + 709107 * 2 ^ 59
def prefixEnd_709107 : Nat := 4983230072969 + 3 ^ 40 * 709107 * 2
def baseEnd_709107 : Nat := 323655756860322088267895

theorem tailTrace_709107 : CollatzResearch.WordTrace tailWord_709107 prefixEnd_709107 323655756860322088267895 := by
  unfold tailWord_709107
  simp only [CollatzResearch.WordTrace]
  refine ⟨25863257042033919678981575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17242171361355946452654383 25863257042033919678981575)
  ·
    refine ⟨38794885563050879518472363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25863257042033919678981575 38794885563050879518472363)
    ·
      refine ⟨58192328344576319277708545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38794885563050879518472363 58192328344576319277708545)
      ·
        refine ⟨43644246258432239458281409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58192328344576319277708545 43644246258432239458281409)
        ·
          refine ⟨32733184693824179593711057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43644246258432239458281409 32733184693824179593711057)
          ·
            refine ⟨24549888520368134695283293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32733184693824179593711057 24549888520368134695283293)
            ·
              refine ⟨9206208195138050510731235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24549888520368134695283293 9206208195138050510731235)
              ·
                refine ⟨13809312292707075766096853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9206208195138050510731235 13809312292707075766096853)
                ·
                  refine ⟨323655756860322088267895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13809312292707075766096853 323655756860322088267895)
                  ·
                    rfl

theorem cell20_709107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_709107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709107 prefixEnd_709107 := by exact prefixLift 709107
  have htrace : WordTrace (prefixWord ++ tailWord_709107) baseStart_709107 baseEnd_709107 := by
    simpa [prefixWord, tailWord_709107, baseEnd_709107] using wordTrace_append hprefix tailTrace_709107
  have hstable : (prefixWord ++ tailWord_709107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709107).length < 2 ^ (prefixWord ++ tailWord_709107).sum := by decide
  have hdescent : baseEnd_709107 < baseStart_709107 := by decide
  rcases family_descends (prefixWord ++ tailWord_709107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709127 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 4]
def baseStart_709127 : Nat := 118140960795 + 709127 * 2 ^ 59
def prefixEnd_709127 : Nat := 4983230072969 + 3 ^ 40 * 709127 * 2
def baseEnd_709127 : Nat := 323664885405290907601147

theorem tailTrace_709127 : CollatzResearch.WordTrace tailWord_709127 prefixEnd_709127 323664885405290907601147 := by
  unfold tailWord_709127
  simp only [CollatzResearch.WordTrace]
  refine ⟨25863986501961463094709635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17242657667974308729806423 25863986501961463094709635)
  ·
    refine ⟨38795979752942194642064453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25863986501961463094709635 38795979752942194642064453)
    ·
      refine ⟨7274246203676661495387085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38795979752942194642064453 7274246203676661495387085)
      ·
        refine ⟨2727842326378748060770157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7274246203676661495387085 2727842326378748060770157)
        ·
          refine ⟨1022940872392030522788809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2727842326378748060770157 1022940872392030522788809)
          ·
            refine ⟨767205654294022892091607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1022940872392030522788809 767205654294022892091607)
            ·
              refine ⟨1150808481441034338137411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767205654294022892091607 1150808481441034338137411)
              ·
                refine ⟨1726212722161551507206117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150808481441034338137411 1726212722161551507206117)
                ·
                  refine ⟨323664885405290907601147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1726212722161551507206117 323664885405290907601147)
                  ·
                    rfl

theorem cell20_709127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 4].length) (baseStart_709127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709127 prefixEnd_709127 := by exact prefixLift 709127
  have htrace : WordTrace (prefixWord ++ tailWord_709127) baseStart_709127 baseEnd_709127 := by
    simpa [prefixWord, tailWord_709127, baseEnd_709127] using wordTrace_append hprefix tailTrace_709127
  have hstable : (prefixWord ++ tailWord_709127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709127).length < 2 ^ (prefixWord ++ tailWord_709127).sum := by decide
  have hdescent : baseEnd_709127 < baseStart_709127 := by decide
  rcases family_descends (prefixWord ++ tailWord_709127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709172 : List Nat := [2, 5, 1, 3, 1, 8]
def baseStart_709172 : Nat := 118140960795 + 709172 * 2 ^ 59
def prefixEnd_709172 : Nat := 4983230072969 + 3 ^ 40 * 709172 * 2
def baseEnd_709172 : Nat := 11988349060424842633369

theorem tailTrace_709172 : CollatzResearch.WordTrace tailWord_709172 prefixEnd_709172 11988349060424842633369 := by
  unfold tailWord_709172
  simp only [CollatzResearch.WordTrace]
  refine ⟨12932813893399217890048885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17243751857865623853398513 12932813893399217890048885)
  ·
    refine ⟨1212451302506176677192083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12932813893399217890048885 1212451302506176677192083)
    ·
      refine ⟨1818676953759265015788125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1212451302506176677192083 1818676953759265015788125)
      ·
        refine ⟨682003857659724380920547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1818676953759265015788125 682003857659724380920547)
        ·
          refine ⟨1023005786489586571380821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682003857659724380920547 1023005786489586571380821)
          ·
            refine ⟨11988349060424842633369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1023005786489586571380821 11988349060424842633369)
            ·
              rfl

theorem cell20_709172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 8].length) (baseStart_709172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709172 prefixEnd_709172 := by exact prefixLift 709172
  have htrace : WordTrace (prefixWord ++ tailWord_709172) baseStart_709172 baseEnd_709172 := by
    simpa [prefixWord, tailWord_709172, baseEnd_709172] using wordTrace_append hprefix tailTrace_709172
  have hstable : (prefixWord ++ tailWord_709172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709172).length < 2 ^ (prefixWord ++ tailWord_709172).sum := by decide
  have hdescent : baseEnd_709172 < baseStart_709172 := by decide
  rcases family_descends (prefixWord ++ tailWord_709172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709207 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 4]
def baseStart_709207 : Nat := 118140960795 + 709207 * 2 ^ 59
def prefixEnd_709207 : Nat := 4983230072969 + 3 ^ 40 * 709207 * 2
def baseEnd_709207 : Nat := 323701399585166184934153

theorem tailTrace_709207 : CollatzResearch.WordTrace tailWord_709207 prefixEnd_709207 323701399585166184934153 := by
  unfold tailWord_709207
  simp only [CollatzResearch.WordTrace]
  refine ⟨25866904341671636757621875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17244602894447757838414583 25866904341671636757621875)
  ·
    refine ⟨38800356512507455136432813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25866904341671636757621875 38800356512507455136432813)
    ·
      refine ⟨14550133692190295676162305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38800356512507455136432813 14550133692190295676162305)
      ·
        refine ⟨10912600269142721757121729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14550133692190295676162305 10912600269142721757121729)
        ·
          refine ⟨8184450201857041317841297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10912600269142721757121729 8184450201857041317841297)
          ·
            refine ⟨6138337651392780988380973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8184450201857041317841297 6138337651392780988380973)
            ·
              refine ⟨2301876619272292870642865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6138337651392780988380973 2301876619272292870642865)
              ·
                refine ⟨1726407464454219652982149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2301876619272292870642865 1726407464454219652982149)
                ·
                  refine ⟨323701399585166184934153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1726407464454219652982149 323701399585166184934153)
                  ·
                    rfl

theorem cell20_709207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_709207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709207 prefixEnd_709207 := by exact prefixLift 709207
  have htrace : WordTrace (prefixWord ++ tailWord_709207) baseStart_709207 baseEnd_709207 := by
    simpa [prefixWord, tailWord_709207, baseEnd_709207] using wordTrace_append hprefix tailTrace_709207
  have hstable : (prefixWord ++ tailWord_709207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709207).length < 2 ^ (prefixWord ++ tailWord_709207).sum := by decide
  have hdescent : baseEnd_709207 < baseStart_709207 := by decide
  rcases family_descends (prefixWord ++ tailWord_709207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709234 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_709234 : Nat := 118140960795 + 709234 * 2 ^ 59
def prefixEnd_709234 : Nat := 4983230072969 + 3 ^ 40 * 709234 * 2
def baseEnd_709234 : Nat := 323713723120874091034043

theorem tailTrace_709234 : CollatzResearch.WordTrace tailWord_709234 prefixEnd_709234 323713723120874091034043 := by
  unfold tailWord_709234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6466972278143455092213689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17245259408382546912569837 6466972278143455092213689)
  ·
    refine ⟨4850229208607591319160267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6466972278143455092213689 4850229208607591319160267)
    ·
      refine ⟨7275343812911386978740401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4850229208607591319160267 7275343812911386978740401)
      ·
        refine ⟨5456507859683540234055301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7275343812911386978740401 5456507859683540234055301)
        ·
          refine ⟨1023095223690663793885369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5456507859683540234055301 1023095223690663793885369)
          ·
            refine ⟨767321417767997845414027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1023095223690663793885369 767321417767997845414027)
            ·
              refine ⟨1150982126651996768121041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767321417767997845414027 1150982126651996768121041)
              ·
                refine ⟨863236594988997576090781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1150982126651996768121041 863236594988997576090781)
                ·
                  refine ⟨323713723120874091034043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863236594988997576090781 323713723120874091034043)
                  ·
                    rfl

theorem cell20_709234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_709234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709234 prefixEnd_709234 := by exact prefixLift 709234
  have htrace : WordTrace (prefixWord ++ tailWord_709234) baseStart_709234 baseEnd_709234 := by
    simpa [prefixWord, tailWord_709234, baseEnd_709234] using wordTrace_append hprefix tailTrace_709234
  have hstable : (prefixWord ++ tailWord_709234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709234).length < 2 ^ (prefixWord ++ tailWord_709234).sum := by decide
  have hdescent : baseEnd_709234 < baseStart_709234 := by decide
  rcases family_descends (prefixWord ++ tailWord_709234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709255 : List Nat := [1, 1, 4, 2, 1, 2, 5, 1, 3]
def baseStart_709255 : Nat := 118140960795 + 709255 * 2 ^ 59
def prefixEnd_709255 : Nat := 4983230072969 + 3 ^ 40 * 709255 * 2
def baseEnd_709255 : Nat := 323723308093091351333957

theorem tailTrace_709255 : CollatzResearch.WordTrace tailWord_709255 prefixEnd_709255 323723308093091351333957 := by
  unfold tailWord_709255
  simp only [CollatzResearch.WordTrace]
  refine ⟨25868655045497740955369219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17245770030331827303579479 25868655045497740955369219)
  ·
    refine ⟨38802982568246611433053829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25868655045497740955369219 38802982568246611433053829)
    ·
      refine ⟨7275559231546239643697593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38802982568246611433053829 7275559231546239643697593)
      ·
        refine ⟨5456669423659679732773195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7275559231546239643697593 5456669423659679732773195)
        ·
          refine ⟨8185004135489519599159793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5456669423659679732773195 8185004135489519599159793)
          ·
            refine ⟨6138753101617139699369845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8185004135489519599159793 6138753101617139699369845)
            ·
              refine ⟨575508103276606846815923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6138753101617139699369845 575508103276606846815923)
              ·
                refine ⟨863262154914910270223885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 575508103276606846815923 863262154914910270223885)
                ·
                  refine ⟨323723308093091351333957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863262154914910270223885 323723308093091351333957)
                  ·
                    rfl

theorem cell20_709255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 1, 3].length) (baseStart_709255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709255 prefixEnd_709255 := by exact prefixLift 709255
  have htrace : WordTrace (prefixWord ++ tailWord_709255) baseStart_709255 baseEnd_709255 := by
    simpa [prefixWord, tailWord_709255, baseEnd_709255] using wordTrace_append hprefix tailTrace_709255
  have hstable : (prefixWord ++ tailWord_709255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709255).length < 2 ^ (prefixWord ++ tailWord_709255).sum := by decide
  have hdescent : baseEnd_709255 < baseStart_709255 := by decide
  rcases family_descends (prefixWord ++ tailWord_709255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709276 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_709276 : Nat := 118140960795 + 709276 * 2 ^ 59
def prefixEnd_709276 : Nat := 4983230072969 + 3 ^ 40 * 709276 * 2
def baseEnd_709276 : Nat := 323732893065308611633871

theorem tailTrace_709276 : CollatzResearch.WordTrace tailWord_709276 prefixEnd_709276 323732893065308611633871 := by
  unfold tailWord_709276
  simp only [CollatzResearch.WordTrace]
  refine ⟨12934710489210830770941841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17246280652281107694589121 12934710489210830770941841)
  ·
    refine ⟨9701032866908123078206381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12934710489210830770941841 9701032866908123078206381)
    ·
      refine ⟨3637887325090546154327393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9701032866908123078206381 3637887325090546154327393)
      ·
        refine ⟨2728415493817909615745545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3637887325090546154327393 2728415493817909615745545)
        ·
          refine ⟨2046311620363432211809159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2728415493817909615745545 2046311620363432211809159)
          ·
            refine ⟨3069467430545148317713739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2046311620363432211809159 3069467430545148317713739)
            ·
              refine ⟨4604201145817722476570609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3069467430545148317713739 4604201145817722476570609)
              ·
                refine ⟨3453150859363291857427957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4604201145817722476570609 3453150859363291857427957)
                ·
                  refine ⟨323732893065308611633871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453150859363291857427957 323732893065308611633871)
                  ·
                    rfl

theorem cell20_709276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_709276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709276 prefixEnd_709276 := by exact prefixLift 709276
  have htrace : WordTrace (prefixWord ++ tailWord_709276) baseStart_709276 baseEnd_709276 := by
    simpa [prefixWord, tailWord_709276, baseEnd_709276] using wordTrace_append hprefix tailTrace_709276
  have hstable : (prefixWord ++ tailWord_709276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709276).length < 2 ^ (prefixWord ++ tailWord_709276).sum := by decide
  have hdescent : baseEnd_709276 < baseStart_709276 := by decide
  rcases family_descends (prefixWord ++ tailWord_709276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709338 : List Nat := [3, 1, 1, 2, 2, 2, 2, 5, 2]
def baseStart_709338 : Nat := 118140960795 + 709338 * 2 ^ 59
def prefixEnd_709338 : Nat := 4983230072969 + 3 ^ 40 * 709338 * 2
def baseEnd_709338 : Nat := 323761191554711951566951

theorem tailTrace_709338 : CollatzResearch.WordTrace tailWord_709338 prefixEnd_709338 323761191554711951566951 := by
  unfold tailWord_709338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6467920576049261532660167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17247788202798030753760445 6467920576049261532660167)
  ·
    refine ⟨9701880864073892298990251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6467920576049261532660167 9701880864073892298990251)
    ·
      refine ⟨14552821296110838448485377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9701880864073892298990251 14552821296110838448485377)
      ·
        refine ⟨10914615972083128836364033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14552821296110838448485377 10914615972083128836364033)
        ·
          refine ⟨8185961979062346627273025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10914615972083128836364033 8185961979062346627273025)
          ·
            refine ⟨6139471484296759970454769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8185961979062346627273025 6139471484296759970454769)
            ·
              refine ⟨4604603613222569977841077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6139471484296759970454769 4604603613222569977841077)
              ·
                refine ⟨431681588739615935422601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4604603613222569977841077 431681588739615935422601)
                ·
                  refine ⟨323761191554711951566951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431681588739615935422601 323761191554711951566951)
                  ·
                    rfl

theorem cell20_709338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_709338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709338 prefixEnd_709338 := by exact prefixLift 709338
  have htrace : WordTrace (prefixWord ++ tailWord_709338) baseStart_709338 baseEnd_709338 := by
    simpa [prefixWord, tailWord_709338, baseEnd_709338] using wordTrace_append hprefix tailTrace_709338
  have hstable : (prefixWord ++ tailWord_709338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709338).length < 2 ^ (prefixWord ++ tailWord_709338).sum := by decide
  have hdescent : baseEnd_709338 < baseStart_709338 := by decide
  rcases family_descends (prefixWord ++ tailWord_709338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709404 : List Nat := [2, 2, 3, 1, 1, 4, 7]
def baseStart_709404 : Nat := 118140960795 + 709404 * 2 ^ 59
def prefixEnd_709404 : Nat := 4983230072969 + 3 ^ 40 * 709404 * 2
def baseEnd_709404 : Nat := 35976812861456561707409

theorem tailTrace_709404 : CollatzResearch.WordTrace tailWord_709404 prefixEnd_709404 35976812861456561707409 := by
  unfold tailWord_709404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12937044760978969701271633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17249393014638626268362177 12937044760978969701271633)
  ·
    refine ⟨9702783570734227275953725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12937044760978969701271633 9702783570734227275953725)
    ·
      refine ⟨3638543839025335228482647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9702783570734227275953725 3638543839025335228482647)
      ·
        refine ⟨5457815758538002842723971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3638543839025335228482647 5457815758538002842723971)
        ·
          refine ⟨8186723637807004264085957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5457815758538002842723971 8186723637807004264085957)
          ·
            refine ⟨1535010682088813299516117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8186723637807004264085957 1535010682088813299516117)
            ·
              refine ⟨35976812861456561707409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1535010682088813299516117 35976812861456561707409)
              ·
                rfl

theorem cell20_709404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 7].length) (baseStart_709404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709404 prefixEnd_709404 := by exact prefixLift 709404
  have htrace : WordTrace (prefixWord ++ tailWord_709404) baseStart_709404 baseEnd_709404 := by
    simpa [prefixWord, tailWord_709404, baseEnd_709404] using wordTrace_append hprefix tailTrace_709404
  have hstable : (prefixWord ++ tailWord_709404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709404).length < 2 ^ (prefixWord ++ tailWord_709404).sum := by decide
  have hdescent : baseEnd_709404 < baseStart_709404 := by decide
  rcases family_descends (prefixWord ++ tailWord_709404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709407 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 3]
def baseStart_709407 : Nat := 118140960795 + 709407 * 2 ^ 59
def prefixEnd_709407 : Nat := 4983230072969 + 3 ^ 40 * 709407 * 2
def baseEnd_709407 : Nat := 323792685034854378266669

theorem tailTrace_709407 : CollatzResearch.WordTrace tailWord_709407 prefixEnd_709407 323792685034854378266669 := by
  unfold tailWord_709407
  simp only [CollatzResearch.WordTrace]
  refine ⟨25874198940947070914902475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17249465960631380609934983 25874198940947070914902475)
  ·
    refine ⟨38811298411420606372353713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25874198940947070914902475 38811298411420606372353713)
    ·
      refine ⟨29108473808565454779265285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38811298411420606372353713 29108473808565454779265285)
      ·
        refine ⟨5457838839106022771112241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29108473808565454779265285 5457838839106022771112241)
        ·
          refine ⟨4093379129329517078334181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5457838839106022771112241 4093379129329517078334181)
          ·
            refine ⟨767508586749284452187659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4093379129329517078334181 767508586749284452187659)
            ·
              refine ⟨1151262880123926678281489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767508586749284452187659 1151262880123926678281489)
              ·
                refine ⟨863447160092945008711117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151262880123926678281489 863447160092945008711117)
                ·
                  refine ⟨323792685034854378266669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863447160092945008711117 323792685034854378266669)
                  ·
                    rfl

theorem cell20_709407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 3].length) (baseStart_709407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709407 prefixEnd_709407 := by exact prefixLift 709407
  have htrace : WordTrace (prefixWord ++ tailWord_709407) baseStart_709407 baseEnd_709407 := by
    simpa [prefixWord, tailWord_709407, baseEnd_709407] using wordTrace_append hprefix tailTrace_709407
  have hstable : (prefixWord ++ tailWord_709407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709407).length < 2 ^ (prefixWord ++ tailWord_709407).sum := by decide
  have hdescent : baseEnd_709407 < baseStart_709407 := by decide
  rcases family_descends (prefixWord ++ tailWord_709407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709444 : List Nat := [2, 3, 4, 2, 2, 1, 1, 3, 2]
def baseStart_709444 : Nat := 118140960795 + 709444 * 2 ^ 59
def prefixEnd_709444 : Nat := 4983230072969 + 3 ^ 40 * 709444 * 2
def baseEnd_709444 : Nat := 323809572843046694033185

theorem tailTrace_709444 : CollatzResearch.WordTrace tailWord_709444 prefixEnd_709444 323809572843046694033185 := by
  unfold tailWord_709444
  simp only [CollatzResearch.WordTrace]
  refine ⟨12937774220906513116999693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17250365627875350822666257 12937774220906513116999693)
  ·
    refine ⟨4851665332839942418874885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12937774220906513116999693 4851665332839942418874885)
    ·
      refine ⟨909687249907489203539041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4851665332839942418874885 909687249907489203539041)
      ·
        refine ⟨682265437430616902654281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 909687249907489203539041 682265437430616902654281)
        ·
          refine ⟨511699078072962676990711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 682265437430616902654281 511699078072962676990711)
          ·
            refine ⟨767548617109444015486067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511699078072962676990711 767548617109444015486067)
            ·
              refine ⟨1151322925664166023229101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767548617109444015486067 1151322925664166023229101)
              ·
                refine ⟨431746097124062258710913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1151322925664166023229101 431746097124062258710913)
                ·
                  refine ⟨323809572843046694033185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431746097124062258710913 323809572843046694033185)
                  ·
                    rfl

theorem cell20_709444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_709444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709444 prefixEnd_709444 := by exact prefixLift 709444
  have htrace : WordTrace (prefixWord ++ tailWord_709444) baseStart_709444 baseEnd_709444 := by
    simpa [prefixWord, tailWord_709444, baseEnd_709444] using wordTrace_append hprefix tailTrace_709444
  have hstable : (prefixWord ++ tailWord_709444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709444).length < 2 ^ (prefixWord ++ tailWord_709444).sum := by decide
  have hdescent : baseEnd_709444 < baseStart_709444 := by decide
  rcases family_descends (prefixWord ++ tailWord_709444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709449 : List Nat := [1, 2, 1, 1, 2, 5, 1, 2, 5]
def baseStart_709449 : Nat := 118140960795 + 709449 * 2 ^ 59
def prefixEnd_709449 : Nat := 4983230072969 + 3 ^ 40 * 709449 * 2
def baseEnd_709449 : Nat := 323811854979288898866497

theorem tailTrace_709449 : CollatzResearch.WordTrace tailWord_709449 prefixEnd_709449 323811854979288898866497 := by
  unfold tailWord_709449
  simp only [CollatzResearch.WordTrace]
  refine ⟨25875730806794912087931401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17250487204529941391954267 25875730806794912087931401)
  ·
    refine ⟨19406798105096184065948551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25875730806794912087931401 19406798105096184065948551)
    ·
      refine ⟨29110197157644276098922827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19406798105096184065948551 29110197157644276098922827)
      ·
        refine ⟨43665295736466414148384241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29110197157644276098922827 43665295736466414148384241)
        ·
          refine ⟨32748971802349810611288181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43665295736466414148384241 32748971802349810611288181)
          ·
            refine ⟨3070216106470294744808267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32748971802349810611288181 3070216106470294744808267)
            ·
              refine ⟨4605324159705442117212401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070216106470294744808267 4605324159705442117212401)
              ·
                refine ⟨3453993119779081587909301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4605324159705442117212401 3453993119779081587909301)
                ·
                  refine ⟨323811854979288898866497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3453993119779081587909301 323811854979288898866497)
                  ·
                    rfl

theorem cell20_709449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_709449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709449 prefixEnd_709449 := by exact prefixLift 709449
  have htrace : WordTrace (prefixWord ++ tailWord_709449) baseStart_709449 baseEnd_709449 := by
    simpa [prefixWord, tailWord_709449, baseEnd_709449] using wordTrace_append hprefix tailTrace_709449
  have hstable : (prefixWord ++ tailWord_709449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709449).length < 2 ^ (prefixWord ++ tailWord_709449).sum := by decide
  have hdescent : baseEnd_709449 < baseStart_709449 := by decide
  rcases family_descends (prefixWord ++ tailWord_709449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709456 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_709456 : Nat := 118140960795 + 709456 * 2 ^ 59
def prefixEnd_709456 : Nat := 4983230072969 + 3 ^ 40 * 709456 * 2
def baseEnd_709456 : Nat := 323815049970027985633135

theorem tailTrace_709456 : CollatzResearch.WordTrace tailWord_709456 prefixEnd_709456 323815049970027985633135 := by
  unfold tailWord_709456
  simp only [CollatzResearch.WordTrace]
  refine ⟨12937993058884776141718111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17250657411846368188957481 12937993058884776141718111)
  ·
    refine ⟨19406989588327164212577167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12937993058884776141718111 19406989588327164212577167)
    ·
      refine ⟨29110484382490746318865751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19406989588327164212577167 29110484382490746318865751)
      ·
        refine ⟨43665726573736119478298627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29110484382490746318865751 43665726573736119478298627)
        ·
          refine ⟨65498589860604179217447941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43665726573736119478298627 65498589860604179217447941)
          ·
            refine ⟨12280985598863283603271489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65498589860604179217447941 12280985598863283603271489)
            ·
              refine ⟨9210739199147462702453617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12280985598863283603271489 9210739199147462702453617)
              ·
                refine ⟨6908054399360597026840213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9210739199147462702453617 6908054399360597026840213)
                ·
                  refine ⟨323815049970027985633135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6908054399360597026840213 323815049970027985633135)
                  ·
                    rfl

theorem cell20_709456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_709456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709456 prefixEnd_709456 := by exact prefixLift 709456
  have htrace : WordTrace (prefixWord ++ tailWord_709456) baseStart_709456 baseEnd_709456 := by
    simpa [prefixWord, tailWord_709456, baseEnd_709456] using wordTrace_append hprefix tailTrace_709456
  have hstable : (prefixWord ++ tailWord_709456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709456).length < 2 ^ (prefixWord ++ tailWord_709456).sum := by decide
  have hdescent : baseEnd_709456 < baseStart_709456 := by decide
  rcases family_descends (prefixWord ++ tailWord_709456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709480 : List Nat := [2, 1, 4, 2, 1, 2, 1, 7]
def baseStart_709480 : Nat := 118140960795 + 709480 * 2 ^ 59
def prefixEnd_709480 : Nat := 4983230072969 + 3 ^ 40 * 709480 * 2
def baseEnd_709480 : Nat := 107942001407996856277679

theorem tailTrace_709480 : CollatzResearch.WordTrace tailWord_709480 prefixEnd_709480 107942001407996856277679 := by
  unfold tailWord_709480
  simp only [CollatzResearch.WordTrace]
  refine ⟨12938430734841302191154947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17251240979788402921539929 12938430734841302191154947)
  ·
    refine ⟨19407646102261953286732421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12938430734841302191154947 19407646102261953286732421)
    ·
      refine ⟨3638933644174116241262329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19407646102261953286732421 3638933644174116241262329)
      ·
        refine ⟨2729200233130587180946747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3638933644174116241262329 2729200233130587180946747)
        ·
          refine ⟨4093800349695880771420121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2729200233130587180946747 4093800349695880771420121)
          ·
            refine ⟨3070350262271910578565091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4093800349695880771420121 3070350262271910578565091)
            ·
              refine ⟨4605525393407865867847637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3070350262271910578565091 4605525393407865867847637)
              ·
                refine ⟨107942001407996856277679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4605525393407865867847637 107942001407996856277679)
                ·
                  rfl

theorem cell20_709480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_709480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709480 prefixEnd_709480 := by exact prefixLift 709480
  have htrace : WordTrace (prefixWord ++ tailWord_709480) baseStart_709480 baseEnd_709480 := by
    simpa [prefixWord, tailWord_709480, baseEnd_709480] using wordTrace_append hprefix tailTrace_709480
  have hstable : (prefixWord ++ tailWord_709480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709480).length < 2 ^ (prefixWord ++ tailWord_709480).sum := by decide
  have hdescent : baseEnd_709480 < baseStart_709480 := by decide
  rcases family_descends (prefixWord ++ tailWord_709480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709535 : List Nat := [1, 1, 2, 5, 2, 3, 1, 5]
def baseStart_709535 : Nat := 118140960795 + 709535 * 2 ^ 59
def prefixEnd_709535 : Nat := 4983230072969 + 3 ^ 40 * 709535 * 2
def baseEnd_709535 : Nat := 107950369240884940666493

theorem tailTrace_709535 : CollatzResearch.WordTrace tailWord_709535 prefixEnd_709535 107950369240884940666493 := by
  unfold tailWord_709535
  simp only [CollatzResearch.WordTrace]
  refine ⟨25878867484483348775562059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17252578322988899183708039 25878867484483348775562059)
  ·
    refine ⟨38818301226725023163343089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25878867484483348775562059 38818301226725023163343089)
    ·
      refine ⟨29113725920043767372507317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38818301226725023163343089 29113725920043767372507317)
      ·
        refine ⟨2729411805004103191172561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29113725920043767372507317 2729411805004103191172561)
        ·
          refine ⟨2047058853753077393379421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2729411805004103191172561 2047058853753077393379421)
          ·
            refine ⟨767647070157404022517283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2047058853753077393379421 767647070157404022517283)
            ·
              refine ⟨1151470605236106033775925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767647070157404022517283 1151470605236106033775925)
              ·
                refine ⟨107950369240884940666493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1151470605236106033775925 107950369240884940666493)
                ·
                  rfl

theorem cell20_709535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 5].length) (baseStart_709535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709535 prefixEnd_709535 := by exact prefixLift 709535
  have htrace : WordTrace (prefixWord ++ tailWord_709535) baseStart_709535 baseEnd_709535 := by
    simpa [prefixWord, tailWord_709535, baseEnd_709535] using wordTrace_append hprefix tailTrace_709535
  have hstable : (prefixWord ++ tailWord_709535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709535).length < 2 ^ (prefixWord ++ tailWord_709535).sum := by decide
  have hdescent : baseEnd_709535 < baseStart_709535 := by decide
  rcases family_descends (prefixWord ++ tailWord_709535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709558 : List Nat := [5, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_709558 : Nat := 118140960795 + 709558 * 2 ^ 59
def prefixEnd_709558 : Nat := 4983230072969 + 3 ^ 40 * 709558 * 2
def baseEnd_709558 : Nat := 323861605549368964232719

theorem tailTrace_709558 : CollatzResearch.WordTrace tailWord_709558 prefixEnd_709558 323861605549368964232719 := by
  unfold tailWord_709558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1617481647712501481478083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17253137575600015802432885 1617481647712501481478083)
  ·
    refine ⟨2426222471568752222217125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1617481647712501481478083 2426222471568752222217125)
    ·
      refine ⟨454916713419141041665711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2426222471568752222217125 454916713419141041665711)
      ·
        refine ⟨682375070128711562498567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454916713419141041665711 682375070128711562498567)
        ·
          refine ⟨1023562605193067343747851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682375070128711562498567 1023562605193067343747851)
          ·
            refine ⟨1535343907789601015621777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023562605193067343747851 1535343907789601015621777)
            ·
              refine ⟨1151507930842200761716333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1535343907789601015621777 1151507930842200761716333)
              ·
                refine ⟨431815474065825285643625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1151507930842200761716333 431815474065825285643625)
                ·
                  refine ⟨323861605549368964232719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431815474065825285643625 323861605549368964232719)
                  ·
                    rfl

theorem cell20_709558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_709558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709558 prefixEnd_709558 := by exact prefixLift 709558
  have htrace : WordTrace (prefixWord ++ tailWord_709558) baseStart_709558 baseEnd_709558 := by
    simpa [prefixWord, tailWord_709558, baseEnd_709558] using wordTrace_append hprefix tailTrace_709558
  have hstable : (prefixWord ++ tailWord_709558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709558).length < 2 ^ (prefixWord ++ tailWord_709558).sum := by decide
  have hdescent : baseEnd_709558 < baseStart_709558 := by decide
  rcases family_descends (prefixWord ++ tailWord_709558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709576 : List Nat := [2, 1, 3, 1, 6, 1, 1, 2, 3]
def baseStart_709576 : Nat := 118140960795 + 709576 * 2 ^ 59
def prefixEnd_709576 : Nat := 4983230072969 + 3 ^ 40 * 709576 * 2
def baseEnd_709576 : Nat := 323869821239840901632645

theorem tailTrace_709576 : CollatzResearch.WordTrace tailWord_709576 prefixEnd_709576 323869821239840901632645 := by
  unfold tailWord_709576
  simp only [CollatzResearch.WordTrace]
  refine ⟨12940181438667406388902291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17253575251556541851869721 12940181438667406388902291)
  ·
    refine ⟨19410272158001109583353437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12940181438667406388902291 19410272158001109583353437)
    ·
      refine ⟨7278852059250416093757539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19410272158001109583353437 7278852059250416093757539)
      ·
        refine ⟨10918278088875624140636309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7278852059250416093757539 10918278088875624140636309)
        ·
          refine ⟨511794285416044881592327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10918278088875624140636309 511794285416044881592327)
          ·
            refine ⟨767691428124067322388491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 511794285416044881592327 767691428124067322388491)
            ·
              refine ⟨1151537142186100983582737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767691428124067322388491 1151537142186100983582737)
              ·
                refine ⟨863652856639575737687053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1151537142186100983582737 863652856639575737687053)
                ·
                  refine ⟨323869821239840901632645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863652856639575737687053 323869821239840901632645)
                  ·
                    rfl

theorem cell20_709576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 3].length) (baseStart_709576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709576 prefixEnd_709576 := by exact prefixLift 709576
  have htrace : WordTrace (prefixWord ++ tailWord_709576) baseStart_709576 baseEnd_709576 := by
    simpa [prefixWord, tailWord_709576, baseEnd_709576] using wordTrace_append hprefix tailTrace_709576
  have hstable : (prefixWord ++ tailWord_709576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709576).length < 2 ^ (prefixWord ++ tailWord_709576).sum := by decide
  have hdescent : baseEnd_709576 < baseStart_709576 := by decide
  rcases family_descends (prefixWord ++ tailWord_709576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709639 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 5]
def baseStart_709639 : Nat := 118140960795 + 709639 * 2 ^ 59
def prefixEnd_709639 : Nat := 4983230072969 + 3 ^ 40 * 709639 * 2
def baseEnd_709639 : Nat := 323898576156492682532387

theorem tailTrace_709639 : CollatzResearch.WordTrace tailWord_709639 prefixEnd_709639 323898576156492682532387 := by
  unfold tailWord_709639
  simp only [CollatzResearch.WordTrace]
  refine ⟨25882660676106574537347971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17255107117404383024898647 25882660676106574537347971)
  ·
    refine ⟨38823991014159861806021957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25882660676106574537347971 38823991014159861806021957)
    ·
      refine ⟨7279498315154974088629117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38823991014159861806021957 7279498315154974088629117)
      ·
        refine ⟨2729811868183115283235919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7279498315154974088629117 2729811868183115283235919)
        ·
          refine ⟨4094717802274672924853879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2729811868183115283235919 4094717802274672924853879)
          ·
            refine ⟨6142076703412009387280819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4094717802274672924853879 6142076703412009387280819)
            ·
              refine ⟨9213115055118014080921229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6142076703412009387280819 9213115055118014080921229)
              ·
                refine ⟨3454918145669255280345461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9213115055118014080921229 3454918145669255280345461)
                ·
                  refine ⟨323898576156492682532387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3454918145669255280345461 323898576156492682532387)
                  ·
                    rfl

theorem cell20_709639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_709639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709639 prefixEnd_709639 := by exact prefixLift 709639
  have htrace : WordTrace (prefixWord ++ tailWord_709639) baseStart_709639 baseEnd_709639 := by
    simpa [prefixWord, tailWord_709639, baseEnd_709639] using wordTrace_append hprefix tailTrace_709639
  have hstable : (prefixWord ++ tailWord_709639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709639).length < 2 ^ (prefixWord ++ tailWord_709639).sum := by decide
  have hdescent : baseEnd_709639 < baseStart_709639 := by decide
  rcases family_descends (prefixWord ++ tailWord_709639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709642 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_709642 : Nat := 118140960795 + 709642 * 2 ^ 59
def prefixEnd_709642 : Nat := 4983230072969 + 3 ^ 40 * 709642 * 2
def baseEnd_709642 : Nat := 323899945438238005432375

theorem tailTrace_709642 : CollatzResearch.WordTrace tailWord_709642 prefixEnd_709642 323899945438238005432375 := by
  unfold tailWord_709642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6470692523773926512426795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17255180063397137366471453 6470692523773926512426795)
  ·
    refine ⟨9706038785660889768640193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6470692523773926512426795 9706038785660889768640193)
    ·
      refine ⟨7279529089245667326480145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9706038785660889768640193 7279529089245667326480145)
      ·
        refine ⟨5459646816934250494860109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7279529089245667326480145 5459646816934250494860109)
        ·
          refine ⟨2047367556350343935572541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5459646816934250494860109 2047367556350343935572541)
          ·
            refine ⟨767762833631378975839703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2047367556350343935572541 767762833631378975839703)
            ·
              refine ⟨1151644250447068463759555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767762833631378975839703 1151644250447068463759555)
              ·
                refine ⟨1727466375670602695639333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1151644250447068463759555 1727466375670602695639333)
                ·
                  refine ⟨323899945438238005432375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1727466375670602695639333 323899945438238005432375)
                  ·
                    rfl

theorem cell20_709642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_709642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709642 prefixEnd_709642 := by exact prefixLift 709642
  have htrace : WordTrace (prefixWord ++ tailWord_709642) baseStart_709642 baseEnd_709642 := by
    simpa [prefixWord, tailWord_709642, baseEnd_709642] using wordTrace_append hprefix tailTrace_709642
  have hstable : (prefixWord ++ tailWord_709642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709642).length < 2 ^ (prefixWord ++ tailWord_709642).sum := by decide
  have hdescent : baseEnd_709642 < baseStart_709642 := by decide
  rcases family_descends (prefixWord ++ tailWord_709642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709656 : List Nat := [2, 1, 2, 3, 2, 3, 1, 3, 3]
def baseStart_709656 : Nat := 118140960795 + 709656 * 2 ^ 59
def prefixEnd_709656 : Nat := 4983230072969 + 3 ^ 40 * 709656 * 2
def baseEnd_709656 : Nat := 323906335419716178965651

theorem tailTrace_709656 : CollatzResearch.WordTrace tailWord_709656 prefixEnd_709656 323906335419716178965651 := by
  unfold tailWord_709656
  simp only [CollatzResearch.WordTrace]
  refine ⟨12941640358522493220358411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17255520478029990960477881 12941640358522493220358411)
  ·
    refine ⟨19412460537783739830537617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12941640358522493220358411 19412460537783739830537617)
    ·
      refine ⟨14559345403337804872903213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19412460537783739830537617 14559345403337804872903213)
      ·
        refine ⟨5459754526251676827338705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14559345403337804872903213 5459754526251676827338705)
        ·
          refine ⟨4094815894688757620504029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5459754526251676827338705 4094815894688757620504029)
          ·
            refine ⟨1535555960508284107689011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4094815894688757620504029 1535555960508284107689011)
            ·
              refine ⟨2303333940762426161533517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535555960508284107689011 2303333940762426161533517)
              ·
                refine ⟨863750227785909810575069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2303333940762426161533517 863750227785909810575069)
                ·
                  refine ⟨323906335419716178965651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863750227785909810575069 323906335419716178965651)
                  ·
                    rfl

theorem cell20_709656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_709656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709656 prefixEnd_709656 := by exact prefixLift 709656
  have htrace : WordTrace (prefixWord ++ tailWord_709656) baseStart_709656 baseEnd_709656 := by
    simpa [prefixWord, tailWord_709656, baseEnd_709656] using wordTrace_append hprefix tailTrace_709656
  have hstable : (prefixWord ++ tailWord_709656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709656).length < 2 ^ (prefixWord ++ tailWord_709656).sum := by decide
  have hdescent : baseEnd_709656 < baseStart_709656 := by decide
  rcases family_descends (prefixWord ++ tailWord_709656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709697 : List Nat := [1, 2, 5, 1, 3, 1, 1, 4, 2]
def baseStart_709697 : Nat := 118140960795 + 709697 * 2 ^ 59
def prefixEnd_709697 : Nat := 4983230072969 + 3 ^ 40 * 709697 * 2
def baseEnd_709697 : Nat := 323925048936902258598817

theorem tailTrace_709697 : CollatzResearch.WordTrace tailWord_709697 prefixEnd_709697 323925048936902258598817 := by
  unfold tailWord_709697
  simp only [CollatzResearch.WordTrace]
  refine ⟨25884776109896450442959345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17256517406597633628639563 25884776109896450442959345)
  ·
    refine ⟨19413582082422337832219509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25884776109896450442959345 19413582082422337832219509)
    ·
      refine ⟨1820023320227094171770579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19413582082422337832219509 1820023320227094171770579)
      ·
        refine ⟨2730034980340641257655869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1820023320227094171770579 2730034980340641257655869)
        ·
          refine ⟨1023763117627740471620951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2730034980340641257655869 1023763117627740471620951)
          ·
            refine ⟨1535644676441610707431427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023763117627740471620951 1535644676441610707431427)
            ·
              refine ⟨2303467014662416061147141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535644676441610707431427 2303467014662416061147141)
              ·
                refine ⟨431900065249203011465089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2303467014662416061147141 431900065249203011465089)
                ·
                  refine ⟨323925048936902258598817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431900065249203011465089 323925048936902258598817)
                  ·
                    rfl

theorem cell20_709697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 2].length) (baseStart_709697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709697 prefixEnd_709697 := by exact prefixLift 709697
  have htrace : WordTrace (prefixWord ++ tailWord_709697) baseStart_709697 baseEnd_709697 := by
    simpa [prefixWord, tailWord_709697, baseEnd_709697] using wordTrace_append hprefix tailTrace_709697
  have hstable : (prefixWord ++ tailWord_709697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709697).length < 2 ^ (prefixWord ++ tailWord_709697).sum := by decide
  have hdescent : baseEnd_709697 < baseStart_709697 := by decide
  rcases family_descends (prefixWord ++ tailWord_709697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709729 : List Nat := [1, 2, 3, 1, 1, 2, 2, 8]
def baseStart_709729 : Nat := 118140960795 + 709729 * 2 ^ 59
def prefixEnd_709729 : Nat := 4983230072969 + 3 ^ 40 * 709729 * 2
def baseEnd_709729 : Nat := 107979884869617456510673

theorem tailTrace_709729 : CollatzResearch.WordTrace tailWord_709729 prefixEnd_709729 107979884869617456510673 := by
  unfold tailWord_709729
  simp only [CollatzResearch.WordTrace]
  refine ⟨25885943245780519908124241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17257295497187013272082827 25885943245780519908124241)
  ·
    refine ⟨19414457434335389931093181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25885943245780519908124241 19414457434335389931093181)
    ·
      refine ⟨7280421537875771224159943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19414457434335389931093181 7280421537875771224159943)
      ·
        refine ⟨10920632306813656836239915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7280421537875771224159943 10920632306813656836239915)
        ·
          refine ⟨16380948460220485254359873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10920632306813656836239915 16380948460220485254359873)
          ·
            refine ⟨12285711345165363940769905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16380948460220485254359873 12285711345165363940769905)
            ·
              refine ⟨9214283508874022955577429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12285711345165363940769905 9214283508874022955577429)
              ·
                refine ⟨107979884869617456510673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9214283508874022955577429 107979884869617456510673)
                ·
                  rfl

theorem cell20_709729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_709729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709729 prefixEnd_709729 := by exact prefixLift 709729
  have htrace : WordTrace (prefixWord ++ tailWord_709729) baseStart_709729 baseEnd_709729 := by
    simpa [prefixWord, tailWord_709729, baseEnd_709729] using wordTrace_append hprefix tailTrace_709729
  have hstable : (prefixWord ++ tailWord_709729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709729).length < 2 ^ (prefixWord ++ tailWord_709729).sum := by decide
  have hdescent : baseEnd_709729 < baseStart_709729 := by decide
  rcases family_descends (prefixWord ++ tailWord_709729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709749 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 5]
def baseStart_709749 : Nat := 118140960795 + 709749 * 2 ^ 59
def prefixEnd_709749 : Nat := 4983230072969 + 3 ^ 40 * 709749 * 2
def baseEnd_709749 : Nat := 323948783153821188865271

theorem tailTrace_709749 : CollatzResearch.WordTrace tailWord_709749 prefixEnd_709749 323948783153821188865271 := by
  unfold tailWord_709749
  simp only [CollatzResearch.WordTrace]
  refine ⟨25886672705708063323852301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17257781803805375549234867 25886672705708063323852301)
  ·
    refine ⟨9707502264640523746444613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25886672705708063323852301 9707502264640523746444613)
    ·
      refine ⟨1820156674620098202458365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9707502264640523746444613 1820156674620098202458365)
      ·
        refine ⟨682558752982536825921887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1820156674620098202458365 682558752982536825921887)
        ·
          refine ⟨1023838129473805238882831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682558752982536825921887 1023838129473805238882831)
          ·
            refine ⟨1535757194210707858324247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1023838129473805238882831 1535757194210707858324247)
            ·
              refine ⟨2303635791316061787486371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535757194210707858324247 2303635791316061787486371)
              ·
                refine ⟨3455453686974092681229557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303635791316061787486371 3455453686974092681229557)
                ·
                  refine ⟨323948783153821188865271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3455453686974092681229557 323948783153821188865271)
                  ·
                    rfl

theorem cell20_709749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_709749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709749 prefixEnd_709749 := by exact prefixLift 709749
  have htrace : WordTrace (prefixWord ++ tailWord_709749) baseStart_709749 baseEnd_709749 := by
    simpa [prefixWord, tailWord_709749, baseEnd_709749] using wordTrace_append hprefix tailTrace_709749
  have hstable : (prefixWord ++ tailWord_709749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709749).length < 2 ^ (prefixWord ++ tailWord_709749).sum := by decide
  have hdescent : baseEnd_709749 < baseStart_709749 := by decide
  rcases family_descends (prefixWord ++ tailWord_709749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709760 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 4]
def baseStart_709760 : Nat := 118140960795 + 709760 * 2 ^ 59
def prefixEnd_709760 : Nat := 4983230072969 + 3 ^ 40 * 709760 * 2
def baseEnd_709760 : Nat := 323953803853554039498559

theorem tailTrace_709760 : CollatzResearch.WordTrace tailWord_709760 prefixEnd_709760 323953803853554039498559 := by
  unfold tailWord_709760
  simp only [CollatzResearch.WordTrace]
  refine ⟨12943536954334106101251367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17258049272445474801668489 12943536954334106101251367)
  ·
    refine ⟨19415305431501159151877051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12943536954334106101251367 19415305431501159151877051)
    ·
      refine ⟨29122958147251738727815577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19415305431501159151877051 29122958147251738727815577)
      ·
        refine ⟨21842218610438804045861683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29122958147251738727815577 21842218610438804045861683)
        ·
          refine ⟨32763327915658206068792525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21842218610438804045861683 32763327915658206068792525)
          ·
            refine ⟨12286247968371827275797197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32763327915658206068792525 12286247968371827275797197)
            ·
              refine ⟨4607342988139435228423949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12286247968371827275797197 4607342988139435228423949)
              ·
                refine ⟨1727753620552288210658981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4607342988139435228423949 1727753620552288210658981)
                ·
                  refine ⟨323953803853554039498559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1727753620552288210658981 323953803853554039498559)
                  ·
                    rfl

theorem cell20_709760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_709760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709760 prefixEnd_709760 := by exact prefixLift 709760
  have htrace : WordTrace (prefixWord ++ tailWord_709760) baseStart_709760 baseEnd_709760 := by
    simpa [prefixWord, tailWord_709760, baseEnd_709760] using wordTrace_append hprefix tailTrace_709760
  have hstable : (prefixWord ++ tailWord_709760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709760).length < 2 ^ (prefixWord ++ tailWord_709760).sum := by decide
  have hdescent : baseEnd_709760 < baseStart_709760 := by decide
  rcases family_descends (prefixWord ++ tailWord_709760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709767 : List Nat := [1, 1, 4, 2, 1, 1, 1, 9]
def baseStart_709767 : Nat := 118140960795 + 709767 * 2 ^ 59
def prefixEnd_709767 : Nat := 4983230072969 + 3 ^ 40 * 709767 * 2
def baseEnd_709767 : Nat := 107985666281431042088399

theorem tailTrace_709767 : CollatzResearch.WordTrace tailWord_709767 prefixEnd_709767 107985666281431042088399 := by
  unfold tailWord_709767
  simp only [CollatzResearch.WordTrace]
  refine ⟨25887329219642852398007555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17258219479761901598671703 25887329219642852398007555)
  ·
    refine ⟨38830993829464278597011333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25887329219642852398007555 38830993829464278597011333)
    ·
      refine ⟨7280811343024552236939625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38830993829464278597011333 7280811343024552236939625)
      ·
        refine ⟨5460608507268414177704719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7280811343024552236939625 5460608507268414177704719)
        ·
          refine ⟨8190912760902621266557079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5460608507268414177704719 8190912760902621266557079)
          ·
            refine ⟨12286369141353931899835619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8190912760902621266557079 12286369141353931899835619)
            ·
              refine ⟨18429553712030897849753429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12286369141353931899835619 18429553712030897849753429)
              ·
                refine ⟨107985666281431042088399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18429553712030897849753429 107985666281431042088399)
                ·
                  rfl

theorem cell20_709767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_709767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709767 prefixEnd_709767 := by exact prefixLift 709767
  have htrace : WordTrace (prefixWord ++ tailWord_709767) baseStart_709767 baseEnd_709767 := by
    simpa [prefixWord, tailWord_709767, baseEnd_709767] using wordTrace_append hprefix tailTrace_709767
  have hstable : (prefixWord ++ tailWord_709767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709767).length < 2 ^ (prefixWord ++ tailWord_709767).sum := by decide
  have hdescent : baseEnd_709767 < baseStart_709767 := by decide
  rcases family_descends (prefixWord ++ tailWord_709767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709784 : List Nat := [2, 1, 2, 4, 2, 2, 1, 6]
def baseStart_709784 : Nat := 118140960795 + 709784 * 2 ^ 59
def prefixEnd_709784 : Nat := 4983230072969 + 3 ^ 40 * 709784 * 2
def baseEnd_709784 : Nat := 107988252702505540899487

theorem tailTrace_709784 : CollatzResearch.WordTrace tailWord_709784 prefixEnd_709784 107988252702505540899487 := by
  unfold tailWord_709784
  simp only [CollatzResearch.WordTrace]
  refine ⟨12943974630290632150688203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17258632840387509534250937 12943974630290632150688203)
  ·
    refine ⟨19415961945435948226032305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12943974630290632150688203 19415961945435948226032305)
    ·
      refine ⟨14561971459076961169524229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19415961945435948226032305 14561971459076961169524229)
      ·
        refine ⟨2730369648576930219285793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14561971459076961169524229 2730369648576930219285793)
        ·
          refine ⟨2047777236432697664464345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2730369648576930219285793 2047777236432697664464345)
          ·
            refine ⟨1535832927324523248348259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2047777236432697664464345 1535832927324523248348259)
            ·
              refine ⟨2303749390986784872522389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535832927324523248348259 2303749390986784872522389)
              ·
                refine ⟨107988252702505540899487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2303749390986784872522389 107988252702505540899487)
                ·
                  rfl

theorem cell20_709784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_709784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709784 prefixEnd_709784 := by exact prefixLift 709784
  have htrace : WordTrace (prefixWord ++ tailWord_709784) baseStart_709784 baseEnd_709784 := by
    simpa [prefixWord, tailWord_709784, baseEnd_709784] using wordTrace_append hprefix tailTrace_709784
  have hstable : (prefixWord ++ tailWord_709784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709784).length < 2 ^ (prefixWord ++ tailWord_709784).sum := by decide
  have hdescent : baseEnd_709784 < baseStart_709784 := by decide
  rcases family_descends (prefixWord ++ tailWord_709784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709790 : List Nat := [4, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_709790 : Nat := 118140960795 + 709790 * 2 ^ 59
def prefixEnd_709790 : Nat := 4983230072969 + 3 ^ 40 * 709790 * 2
def baseEnd_709790 : Nat := 323967496671007268498437

theorem tailTrace_709790 : CollatzResearch.WordTrace tailWord_709790 prefixEnd_709790 323967496671007268498437 := by
  unfold tailWord_709790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3236021012319940915761853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17258778732373018217396549 3236021012319940915761853)
  ·
    refine ⟨1213507879619977843410695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3236021012319940915761853 1213507879619977843410695)
    ·
      refine ⟨1820261819429966765116043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1213507879619977843410695 1820261819429966765116043)
      ·
        refine ⟨2730392729144950147674065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1820261819429966765116043 2730392729144950147674065)
        ·
          refine ⟨2047794546858712610755549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2730392729144950147674065 2047794546858712610755549)
          ·
            refine ⟨767922955072017229033331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2047794546858712610755549 767922955072017229033331)
            ·
              refine ⟨1151884432608025843549997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767922955072017229033331 1151884432608025843549997)
              ·
                refine ⟨431956662228009691331249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1151884432608025843549997 431956662228009691331249)
                ·
                  refine ⟨323967496671007268498437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 431956662228009691331249 323967496671007268498437)
                  ·
                    rfl

theorem cell20_709790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_709790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709790 prefixEnd_709790 := by exact prefixLift 709790
  have htrace : WordTrace (prefixWord ++ tailWord_709790) baseStart_709790 baseEnd_709790 := by
    simpa [prefixWord, tailWord_709790, baseEnd_709790] using wordTrace_append hprefix tailTrace_709790
  have hstable : (prefixWord ++ tailWord_709790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709790).length < 2 ^ (prefixWord ++ tailWord_709790).sum := by decide
  have hdescent : baseEnd_709790 < baseStart_709790 := by decide
  rcases family_descends (prefixWord ++ tailWord_709790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709822 : List Nat := [4, 2, 1, 1, 3, 1, 1, 7]
def baseStart_709822 : Nat := 118140960795 + 709822 * 2 ^ 59
def prefixEnd_709822 : Nat := 4983230072969 + 3 ^ 40 * 709822 * 2
def baseEnd_709822 : Nat := 107994034114319126477213

theorem tailTrace_709822 : CollatzResearch.WordTrace tailWord_709822 prefixEnd_709822 107994034114319126477213 := by
  unfold tailWord_709822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3236166904305449598907465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17259556822962397860839813 3236166904305449598907465)
  ·
    refine ⟨2427125178229087199180599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3236166904305449598907465 2427125178229087199180599)
    ·
      refine ⟨3640687767343630798770899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2427125178229087199180599 3640687767343630798770899)
      ·
        refine ⟨5461031651015446198156349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640687767343630798770899 5461031651015446198156349)
        ·
          refine ⟨2047886869130792324308631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5461031651015446198156349 2047886869130792324308631)
          ·
            refine ⟨3071830303696188486462947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2047886869130792324308631 3071830303696188486462947)
            ·
              refine ⟨4607745455544282729694421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3071830303696188486462947 4607745455544282729694421)
              ·
                refine ⟨107994034114319126477213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4607745455544282729694421 107994034114319126477213)
                ·
                  rfl

theorem cell20_709822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_709822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709822 prefixEnd_709822 := by exact prefixLift 709822
  have htrace : WordTrace (prefixWord ++ tailWord_709822) baseStart_709822 baseEnd_709822 := by
    simpa [prefixWord, tailWord_709822, baseEnd_709822] using wordTrace_append hprefix tailTrace_709822
  have hstable : (prefixWord ++ tailWord_709822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709822).length < 2 ^ (prefixWord ++ tailWord_709822).sum := by decide
  have hdescent : baseEnd_709822 < baseStart_709822 := by decide
  rcases family_descends (prefixWord ++ tailWord_709822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709825 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 3]
def baseStart_709825 : Nat := 118140960795 + 709825 * 2 ^ 59
def prefixEnd_709825 : Nat := 4983230072969 + 3 ^ 40 * 709825 * 2
def baseEnd_709825 : Nat := 323983471624702702331627

theorem tailTrace_709825 : CollatzResearch.WordTrace tailWord_709825 prefixEnd_709825 323983471624702702331627 := by
  unfold tailWord_709825
  simp only [CollatzResearch.WordTrace]
  refine ⟨25889444653432728303618929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17259629768955152202412619 25889444653432728303618929)
  ·
    refine ⟨19417083490074546227714197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25889444653432728303618929 19417083490074546227714197)
    ·
      refine ⟨910175788597244354424103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19417083490074546227714197 910175788597244354424103)
      ·
        refine ⟨1365263682895866531636155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 910175788597244354424103 1365263682895866531636155)
        ·
          refine ⟨2047895524343799797454233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365263682895866531636155 2047895524343799797454233)
          ·
            refine ⟨1535921643257849848090675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2047895524343799797454233 1535921643257849848090675)
            ·
              refine ⟨2303882464886774772136013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535921643257849848090675 2303882464886774772136013)
              ·
                refine ⟨863955924332540539551005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2303882464886774772136013 863955924332540539551005)
                ·
                  refine ⟨323983471624702702331627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 863955924332540539551005 323983471624702702331627)
                  ·
                    rfl

theorem cell20_709825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_709825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709825 prefixEnd_709825 := by exact prefixLift 709825
  have htrace : WordTrace (prefixWord ++ tailWord_709825) baseStart_709825 baseEnd_709825 := by
    simpa [prefixWord, tailWord_709825, baseEnd_709825] using wordTrace_append hprefix tailTrace_709825
  have hstable : (prefixWord ++ tailWord_709825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709825).length < 2 ^ (prefixWord ++ tailWord_709825).sum := by decide
  have hdescent : baseEnd_709825 < baseStart_709825 := by decide
  rcases family_descends (prefixWord ++ tailWord_709825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709863 : List Nat := [1, 1, 5, 3, 2, 1, 2, 2, 3]
def baseStart_709863 : Nat := 118140960795 + 709863 * 2 ^ 59
def prefixEnd_709863 : Nat := 4983230072969 + 3 ^ 40 * 709863 * 2
def baseEnd_709863 : Nat := 324000815860143459064805

theorem tailTrace_709863 : CollatzResearch.WordTrace tailWord_709863 prefixEnd_709863 324000815860143459064805 := by
  unfold tailWord_709863
  simp only [CollatzResearch.WordTrace]
  refine ⟨25890830627295060793502243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17260553751530040529001495 25890830627295060793502243)
  ·
    refine ⟨38836245940942591190253365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25890830627295060793502243 38836245940942591190253365)
    ·
      refine ⟨3640898056963367924086253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38836245940942591190253365 3640898056963367924086253)
      ·
        refine ⟨1365336771361262971532345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3640898056963367924086253 1365336771361262971532345)
        ·
          refine ⟨1024002578520947228649259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1365336771361262971532345 1024002578520947228649259)
          ·
            refine ⟨1536003867781420842973889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024002578520947228649259 1536003867781420842973889)
            ·
              refine ⟨1152002900836065632230417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536003867781420842973889 1152002900836065632230417)
              ·
                refine ⟨864002175627049224172813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152002900836065632230417 864002175627049224172813)
                ·
                  refine ⟨324000815860143459064805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864002175627049224172813 324000815860143459064805)
                  ·
                    rfl

theorem cell20_709863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 3].length) (baseStart_709863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709863 prefixEnd_709863 := by exact prefixLift 709863
  have htrace : WordTrace (prefixWord ++ tailWord_709863) baseStart_709863 baseEnd_709863 := by
    simpa [prefixWord, tailWord_709863, baseEnd_709863] using wordTrace_append hprefix tailTrace_709863
  have hstable : (prefixWord ++ tailWord_709863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709863).length < 2 ^ (prefixWord ++ tailWord_709863).sum := by decide
  have hdescent : baseEnd_709863 < baseStart_709863 := by decide
  rcases family_descends (prefixWord ++ tailWord_709863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709867 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 3]
def baseStart_709867 : Nat := 118140960795 + 709867 * 2 ^ 59
def prefixEnd_709867 : Nat := 4983230072969 + 3 ^ 40 * 709867 * 2
def baseEnd_709867 : Nat := 324002641569137222931455

theorem tailTrace_709867 : CollatzResearch.WordTrace tailWord_709867 prefixEnd_709867 324002641569137222931455 := by
  unfold tailWord_709867
  simp only [CollatzResearch.WordTrace]
  refine ⟨25890976519280569476647855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17260651012853712984431903 25890976519280569476647855)
  ·
    refine ⟨38836464778920854214971783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25890976519280569476647855 38836464778920854214971783)
    ·
      refine ⟨58254697168381281322457675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38836464778920854214971783 58254697168381281322457675)
      ·
        refine ⟨87382045752571921983686513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58254697168381281322457675 87382045752571921983686513)
        ·
          refine ⟨65536534314428941487764885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87382045752571921983686513 65536534314428941487764885)
          ·
            refine ⟨3072025045988856632238979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 65536534314428941487764885 3072025045988856632238979)
            ·
              refine ⟨4608037568983284948358469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072025045988856632238979 4608037568983284948358469)
              ·
                refine ⟨864007044184365927817213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4608037568983284948358469 864007044184365927817213)
                ·
                  refine ⟨324002641569137222931455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864007044184365927817213 324002641569137222931455)
                  ·
                    rfl

theorem cell20_709867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 3].length) (baseStart_709867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709867 prefixEnd_709867 := by exact prefixLift 709867
  have htrace : WordTrace (prefixWord ++ tailWord_709867) baseStart_709867 baseEnd_709867 := by
    simpa [prefixWord, tailWord_709867, baseEnd_709867] using wordTrace_append hprefix tailTrace_709867
  have hstable : (prefixWord ++ tailWord_709867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709867).length < 2 ^ (prefixWord ++ tailWord_709867).sum := by decide
  have hdescent : baseEnd_709867 < baseStart_709867 := by decide
  rcases family_descends (prefixWord ++ tailWord_709867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709888 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_709888 : Nat := 118140960795 + 709888 * 2 ^ 59
def prefixEnd_709888 : Nat := 4983230072969 + 3 ^ 40 * 709888 * 2
def baseEnd_709888 : Nat := 324012226541354483231369

theorem tailTrace_709888 : CollatzResearch.WordTrace tailWord_709888 prefixEnd_709888 324012226541354483231369 := by
  unfold tailWord_709888
  simp only [CollatzResearch.WordTrace]
  refine ⟨12945871226102245031581159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17261161634802993375441545 12945871226102245031581159)
  ·
    refine ⟨19418806839153367547371739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12945871226102245031581159 19418806839153367547371739)
    ·
      refine ⟨29128210258730051321057609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19418806839153367547371739 29128210258730051321057609)
      ·
        refine ⟨21846157694047538490793207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29128210258730051321057609 21846157694047538490793207)
        ·
          refine ⟨32769236541071307736189811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21846157694047538490793207 32769236541071307736189811)
          ·
            refine ⟨49153854811606961604284717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32769236541071307736189811 49153854811606961604284717)
            ·
              refine ⟨18432695554352610601606769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49153854811606961604284717 18432695554352610601606769)
              ·
                refine ⟨13824521665764457951205077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18432695554352610601606769 13824521665764457951205077)
                ·
                  refine ⟨324012226541354483231369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13824521665764457951205077 324012226541354483231369)
                  ·
                    rfl

theorem cell20_709888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_709888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709888 prefixEnd_709888 := by exact prefixLift 709888
  have htrace : WordTrace (prefixWord ++ tailWord_709888) baseStart_709888 baseEnd_709888 := by
    simpa [prefixWord, tailWord_709888, baseEnd_709888] using wordTrace_append hprefix tailTrace_709888
  have hstable : (prefixWord ++ tailWord_709888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709888).length < 2 ^ (prefixWord ++ tailWord_709888).sum := by decide
  have hdescent : baseEnd_709888 < baseStart_709888 := by decide
  rcases family_descends (prefixWord ++ tailWord_709888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709922 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_709922 : Nat := 118140960795 + 709922 * 2 ^ 59
def prefixEnd_709922 : Nat := 4983230072969 + 3 ^ 40 * 709922 * 2
def baseEnd_709922 : Nat := 324027745067801476097897

theorem tailTrace_709922 : CollatzResearch.WordTrace tailWord_709922 prefixEnd_709922 324027745067801476097897 := by
  unfold tailWord_709922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6473245633520328467475005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17261988356054209246600013 6473245633520328467475005)
  ·
    refine ⟨2427467112570123175303127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6473245633520328467475005 2427467112570123175303127)
    ·
      refine ⟨3641200668855184762954691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2427467112570123175303127 3641200668855184762954691)
      ·
        refine ⟨5461801003282777144432037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3641200668855184762954691 5461801003282777144432037)
        ·
          refine ⟨1024087688115520714581007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5461801003282777144432037 1024087688115520714581007)
          ·
            refine ⟨1536131532173281071871511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024087688115520714581007 1536131532173281071871511)
            ·
              refine ⟨2304197298259921607807267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1536131532173281071871511 2304197298259921607807267)
              ·
                refine ⟨3456295947389882411710901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304197298259921607807267 3456295947389882411710901)
                ·
                  refine ⟨324027745067801476097897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3456295947389882411710901 324027745067801476097897)
                  ·
                    rfl

theorem cell20_709922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_709922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709922 prefixEnd_709922 := by exact prefixLift 709922
  have htrace : WordTrace (prefixWord ++ tailWord_709922) baseStart_709922 baseEnd_709922 := by
    simpa [prefixWord, tailWord_709922, baseEnd_709922] using wordTrace_append hprefix tailTrace_709922
  have hstable : (prefixWord ++ tailWord_709922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709922).length < 2 ^ (prefixWord ++ tailWord_709922).sum := by decide
  have hdescent : baseEnd_709922 < baseStart_709922 := by decide
  rcases family_descends (prefixWord ++ tailWord_709922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709949 : List Nat := [1, 4, 1, 5, 2, 1, 2, 4]
def baseStart_709949 : Nat := 118140960795 + 709949 * 2 ^ 59
def prefixEnd_709949 : Nat := 4983230072969 + 3 ^ 40 * 709949 * 2
def baseEnd_709949 : Nat := 108013356201169794065929

theorem tailTrace_709949 : CollatzResearch.WordTrace tailWord_709949 prefixEnd_709949 108013356201169794065929 := by
  unfold tailWord_709949
  simp only [CollatzResearch.WordTrace]
  refine ⟨25893967304983497481132901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17262644869988998320755267 25893967304983497481132901)
  ·
    refine ⟨4855118869684405777712419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25893967304983497481132901 4855118869684405777712419)
    ·
      refine ⟨7282678304526608666568629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4855118869684405777712419 7282678304526608666568629)
      ·
        refine ⟨682751091049369562490809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7282678304526608666568629 682751091049369562490809)
        ·
          refine ⟨512063318287027171868107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 682751091049369562490809 512063318287027171868107)
          ·
            refine ⟨768094977430540757802161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512063318287027171868107 768094977430540757802161)
            ·
              refine ⟨576071233072905568351621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768094977430540757802161 576071233072905568351621)
              ·
                refine ⟨108013356201169794065929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 576071233072905568351621 108013356201169794065929)
                ·
                  rfl

theorem cell20_709949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 4].length) (baseStart_709949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709949 prefixEnd_709949 := by exact prefixLift 709949
  have htrace : WordTrace (prefixWord ++ tailWord_709949) baseStart_709949 baseEnd_709949 := by
    simpa [prefixWord, tailWord_709949, baseEnd_709949] using wordTrace_append hprefix tailTrace_709949
  have hstable : (prefixWord ++ tailWord_709949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709949).length < 2 ^ (prefixWord ++ tailWord_709949).sum := by decide
  have hdescent : baseEnd_709949 < baseStart_709949 := by decide
  rcases family_descends (prefixWord ++ tailWord_709949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709953 : List Nat := [1, 2, 5, 2, 1, 1, 4, 4]
def baseStart_709953 : Nat := 118140960795 + 709953 * 2 ^ 59
def prefixEnd_709953 : Nat := 4983230072969 + 3 ^ 40 * 709953 * 2
def baseEnd_709953 : Nat := 108013964770834382021479

theorem tailTrace_709953 : CollatzResearch.WordTrace tailWord_709953 prefixEnd_709953 108013964770834382021479 := by
  unfold tailWord_709953
  simp only [CollatzResearch.WordTrace]
  refine ⟨25894113196969006164278513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17262742131312670776185675 25894113196969006164278513)
  ·
    refine ⟨19420584897726754623208885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25894113196969006164278513 19420584897726754623208885)
    ·
      refine ⟨1820679834161883245925833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19420584897726754623208885 1820679834161883245925833)
      ·
        refine ⟨1365509875621412434444375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1820679834161883245925833 1365509875621412434444375)
        ·
          refine ⟨2048264813432118651666563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1365509875621412434444375 2048264813432118651666563)
          ·
            refine ⟨3072397220148177977499845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048264813432118651666563 3072397220148177977499845)
            ·
              refine ⟨576074478777783370781221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3072397220148177977499845 576074478777783370781221)
              ·
                refine ⟨108013964770834382021479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 576074478777783370781221 108013964770834382021479)
                ·
                  rfl

theorem cell20_709953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 4].length) (baseStart_709953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709953 prefixEnd_709953 := by exact prefixLift 709953
  have htrace : WordTrace (prefixWord ++ tailWord_709953) baseStart_709953 baseEnd_709953 := by
    simpa [prefixWord, tailWord_709953, baseEnd_709953] using wordTrace_append hprefix tailTrace_709953
  have hstable : (prefixWord ++ tailWord_709953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709953).length < 2 ^ (prefixWord ++ tailWord_709953).sum := by decide
  have hdescent : baseEnd_709953 < baseStart_709953 := by decide
  rcases family_descends (prefixWord ++ tailWord_709953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_709994 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_709994 : Nat := 118140960795 + 709994 * 2 ^ 59
def prefixEnd_709994 : Nat := 4983230072969 + 3 ^ 40 * 709994 * 2
def baseEnd_709994 : Nat := 324060607829689225697603

theorem tailTrace_709994 : CollatzResearch.WordTrace tailWord_709994 prefixEnd_709994 324060607829689225697603 := by
  unfold tailWord_709994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6473902147455117541630259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17263739059880313444347357 6473902147455117541630259)
  ·
    refine ⟨9710853221182676312445389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6473902147455117541630259 9710853221182676312445389)
    ·
      refine ⟨3641569957943503617167021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9710853221182676312445389 3641569957943503617167021)
      ·
        refine ⟨1365588734228813856437633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3641569957943503617167021 1365588734228813856437633)
        ·
          refine ⟨1024191550671610392328225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1365588734228813856437633 1024191550671610392328225)
          ·
            refine ⟨768143663003707794246169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024191550671610392328225 768143663003707794246169)
            ·
              refine ⟨576107747252780845684627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768143663003707794246169 576107747252780845684627)
              ·
                refine ⟨864161620879171268526941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576107747252780845684627 864161620879171268526941)
                ·
                  refine ⟨324060607829689225697603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864161620879171268526941 324060607829689225697603)
                  ·
                    rfl

theorem cell20_709994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_709994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_709994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_709994 prefixEnd_709994 := by exact prefixLift 709994
  have htrace : WordTrace (prefixWord ++ tailWord_709994) baseStart_709994 baseEnd_709994 := by
    simpa [prefixWord, tailWord_709994, baseEnd_709994] using wordTrace_append hprefix tailTrace_709994
  have hstable : (prefixWord ++ tailWord_709994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_709994).length < 2 ^ (prefixWord ++ tailWord_709994).sum := by decide
  have hdescent : baseEnd_709994 < baseStart_709994 := by decide
  rcases family_descends (prefixWord ++ tailWord_709994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710036 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 3]
def baseStart_710036 : Nat := 118140960795 + 710036 * 2 ^ 59
def prefixEnd_710036 : Nat := 4983230072969 + 3 ^ 40 * 710036 * 2
def baseEnd_710036 : Nat := 324079777774123746297431

theorem tailTrace_710036 : CollatzResearch.WordTrace tailWord_710036 prefixEnd_710036 324079777774123746297431 := by
  unfold tailWord_710036
  simp only [CollatzResearch.WordTrace]
  refine ⟨12948570227834155669774981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17264760303778874226366641 12948570227834155669774981)
  ·
    refine ⟨2427856917718904188082809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12948570227834155669774981 2427856917718904188082809)
    ·
      refine ⟨1820892688289178141062107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2427856917718904188082809 1820892688289178141062107)
      ·
        refine ⟨2731339032433767211593161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1820892688289178141062107 2731339032433767211593161)
        ·
          refine ⟨2048504274325325408694871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2731339032433767211593161 2048504274325325408694871)
          ·
            refine ⟨3072756411487988113042307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2048504274325325408694871 3072756411487988113042307)
            ·
              refine ⟨4609134617231982169563461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3072756411487988113042307 4609134617231982169563461)
              ·
                refine ⟨864212740730996656793149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4609134617231982169563461 864212740730996656793149)
                ·
                  refine ⟨324079777774123746297431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864212740730996656793149 324079777774123746297431)
                  ·
                    rfl

theorem cell20_710036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_710036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710036 prefixEnd_710036 := by exact prefixLift 710036
  have htrace : WordTrace (prefixWord ++ tailWord_710036) baseStart_710036 baseEnd_710036 := by
    simpa [prefixWord, tailWord_710036, baseEnd_710036] using wordTrace_append hprefix tailTrace_710036
  have hstable : (prefixWord ++ tailWord_710036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710036).length < 2 ^ (prefixWord ++ tailWord_710036).sum := by decide
  have hdescent : baseEnd_710036 < baseStart_710036 := by decide
  rcases family_descends (prefixWord ++ tailWord_710036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710046 : List Nat := [4, 3, 1, 2, 2, 2, 1, 5]
def baseStart_710046 : Nat := 118140960795 + 710046 * 2 ^ 59
def prefixEnd_710046 : Nat := 4983230072969 + 3 ^ 40 * 710046 * 2
def baseEnd_710046 : Nat := 108028114015536051988019

theorem tailTrace_710046 : CollatzResearch.WordTrace tailWord_710046 prefixEnd_710046 108028114015536051988019 := by
  unfold tailWord_710046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3237188148204010380926749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17265003457088055364942661 3237188148204010380926749)
  ·
    refine ⟨1213945555576503892847531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3237188148204010380926749 1213945555576503892847531)
    ·
      refine ⟨1820918333364755839271297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1213945555576503892847531 1820918333364755839271297)
      ·
        refine ⟨1365688750023566879453473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1820918333364755839271297 1365688750023566879453473)
        ·
          refine ⟨1024266562517675159590105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1365688750023566879453473 1024266562517675159590105)
          ·
            refine ⟨768199921888256369692579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024266562517675159590105 768199921888256369692579)
            ·
              refine ⟨1152299882832384554538869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768199921888256369692579 1152299882832384554538869)
              ·
                refine ⟨108028114015536051988019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1152299882832384554538869 108028114015536051988019)
                ·
                  rfl

theorem cell20_710046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_710046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710046 prefixEnd_710046 := by exact prefixLift 710046
  have htrace : WordTrace (prefixWord ++ tailWord_710046) baseStart_710046 baseEnd_710046 := by
    simpa [prefixWord, tailWord_710046, baseEnd_710046] using wordTrace_append hprefix tailTrace_710046
  have hstable : (prefixWord ++ tailWord_710046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710046).length < 2 ^ (prefixWord ++ tailWord_710046).sum := by decide
  have hdescent : baseEnd_710046 < baseStart_710046 := by decide
  rcases family_descends (prefixWord ++ tailWord_710046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710050 : List Nat := [3, 3, 1, 2, 1, 2, 3, 5]
def baseStart_710050 : Nat := 118140960795 + 710050 * 2 ^ 59
def prefixEnd_710050 : Nat := 4983230072969 + 3 ^ 40 * 710050 * 2
def baseEnd_710050 : Nat := 108028722585200639943569

theorem tailTrace_710050 : CollatzResearch.WordTrace tailWord_710050 prefixEnd_710050 108028722585200639943569 := by
  unfold tailWord_710050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6474412769404397932639901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17265100718411727820373069 6474412769404397932639901)
  ·
    refine ⟨2427904788526649224739963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6474412769404397932639901 2427904788526649224739963)
    ·
      refine ⟨3641857182789973837109945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2427904788526649224739963 3641857182789973837109945)
      ·
        refine ⟨2731392887092480377832459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3641857182789973837109945 2731392887092480377832459)
        ·
          refine ⟨4097089330638720566748689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731392887092480377832459 4097089330638720566748689)
          ·
            refine ⟨3072816997979040425061517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4097089330638720566748689 3072816997979040425061517)
            ·
              refine ⟨1152306374242140159398069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3072816997979040425061517 1152306374242140159398069)
              ·
                refine ⟨108028722585200639943569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1152306374242140159398069 108028722585200639943569)
                ·
                  rfl

theorem cell20_710050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_710050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710050 prefixEnd_710050 := by exact prefixLift 710050
  have htrace : WordTrace (prefixWord ++ tailWord_710050) baseStart_710050 baseEnd_710050 := by
    simpa [prefixWord, tailWord_710050, baseEnd_710050] using wordTrace_append hprefix tailTrace_710050
  have hstable : (prefixWord ++ tailWord_710050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710050).length < 2 ^ (prefixWord ++ tailWord_710050).sum := by decide
  have hdescent : baseEnd_710050 < baseStart_710050 := by decide
  rcases family_descends (prefixWord ++ tailWord_710050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710095 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 3]
def baseStart_710095 : Nat := 118140960795 + 710095 * 2 ^ 59
def prefixEnd_710095 : Nat := 4983230072969 + 3 ^ 40 * 710095 * 2
def baseEnd_710095 : Nat := 324106706981781763330523

theorem tailTrace_710095 : CollatzResearch.WordTrace tailWord_710095 prefixEnd_710095 324106706981781763330523 := by
  unfold tailWord_710095
  simp only [CollatzResearch.WordTrace]
  refine ⟨25899292362454564415947739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17266194908303042943965159 25899292362454564415947739)
  ·
    refine ⟨38848938543681846623921609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25899292362454564415947739 38848938543681846623921609)
    ·
      refine ⟨29136703907761384967941207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38848938543681846623921609 29136703907761384967941207)
      ·
        refine ⟨43705055861642077451911811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29136703907761384967941207 43705055861642077451911811)
        ·
          refine ⟨65557583792463116177867717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43705055861642077451911811 65557583792463116177867717)
          ·
            refine ⟨12292046961086834283350197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65557583792463116177867717 12292046961086834283350197)
            ·
              refine ⟨1152379402601890714064081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12292046961086834283350197 1152379402601890714064081)
              ·
                refine ⟨864284551951418035548061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152379402601890714064081 864284551951418035548061)
                ·
                  refine ⟨324106706981781763330523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864284551951418035548061 324106706981781763330523)
                  ·
                    rfl

theorem cell20_710095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 3].length) (baseStart_710095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710095 prefixEnd_710095 := by exact prefixLift 710095
  have htrace : WordTrace (prefixWord ++ tailWord_710095) baseStart_710095 baseEnd_710095 := by
    simpa [prefixWord, tailWord_710095, baseEnd_710095] using wordTrace_append hprefix tailTrace_710095
  have hstable : (prefixWord ++ tailWord_710095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710095).length < 2 ^ (prefixWord ++ tailWord_710095).sum := by decide
  have hdescent : baseEnd_710095 < baseStart_710095 := by decide
  rcases family_descends (prefixWord ++ tailWord_710095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710122 : List Nat := [3, 1, 3, 1, 5, 1, 2, 4]
def baseStart_710122 : Nat := 118140960795 + 710122 * 2 ^ 59
def prefixEnd_710122 : Nat := 4983230072969 + 3 ^ 40 * 710122 * 2
def baseEnd_710122 : Nat := 108039676839163223143471

theorem tailTrace_710122 : CollatzResearch.WordTrace tailWord_710122 prefixEnd_710122 108039676839163223143471 := by
  unfold tailWord_710122
  simp only [CollatzResearch.WordTrace]
  refine ⟨6475069283339187006795155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17266851422237832018120413 6475069283339187006795155)
  ·
    refine ⟨9712603925008780510192733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6475069283339187006795155 9712603925008780510192733)
    ·
      refine ⟨3642226471878292691322275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9712603925008780510192733 3642226471878292691322275)
      ·
        refine ⟨5463339707817439036983413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3642226471878292691322275 5463339707817439036983413)
        ·
          refine ⟨512188097607884909717195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5463339707817439036983413 512188097607884909717195)
          ·
            refine ⟨768282146411827364575793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512188097607884909717195 768282146411827364575793)
            ·
              refine ⟨576211609808870523431845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768282146411827364575793 576211609808870523431845)
              ·
                refine ⟨108039676839163223143471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 576211609808870523431845 108039676839163223143471)
                ·
                  rfl

theorem cell20_710122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_710122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710122 prefixEnd_710122 := by exact prefixLift 710122
  have htrace : WordTrace (prefixWord ++ tailWord_710122) baseStart_710122 baseEnd_710122 := by
    simpa [prefixWord, tailWord_710122, baseEnd_710122] using wordTrace_append hprefix tailTrace_710122
  have hstable : (prefixWord ++ tailWord_710122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710122).length < 2 ^ (prefixWord ++ tailWord_710122).sum := by decide
  have hdescent : baseEnd_710122 < baseStart_710122 := by decide
  rcases family_descends (prefixWord ++ tailWord_710122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710123 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_710123 : Nat := 118140960795 + 710123 * 2 ^ 59
def prefixEnd_710123 : Nat := 4983230072969 + 3 ^ 40 * 710123 * 2
def baseEnd_710123 : Nat := 324119486944738110397075

theorem tailTrace_710123 : CollatzResearch.WordTrace tailWord_710123 prefixEnd_710123 324119486944738110397075 := by
  unfold tailWord_710123
  simp only [CollatzResearch.WordTrace]
  refine ⟨25900313606353125197967023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17266875737568750131978015 25900313606353125197967023)
  ·
    refine ⟨38850470409529687796950535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25900313606353125197967023 38850470409529687796950535)
    ·
      refine ⟨58275705614294531695425803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38850470409529687796950535 58275705614294531695425803)
      ·
        refine ⟨87413558421441797543138705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58275705614294531695425803 87413558421441797543138705)
        ·
          refine ⟨65560168816081348157354029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87413558421441797543138705 65560168816081348157354029)
          ·
            refine ⟨24585063306030505559007761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65560168816081348157354029 24585063306030505559007761)
            ·
              refine ⟨18438797479522879169255821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24585063306030505559007761 18438797479522879169255821)
              ·
                refine ⟨6914549054821079688470933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18438797479522879169255821 6914549054821079688470933)
                ·
                  refine ⟨324119486944738110397075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6914549054821079688470933 324119486944738110397075)
                  ·
                    rfl

theorem cell20_710123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_710123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710123 prefixEnd_710123 := by exact prefixLift 710123
  have htrace : WordTrace (prefixWord ++ tailWord_710123) baseStart_710123 baseEnd_710123 := by
    simpa [prefixWord, tailWord_710123, baseEnd_710123] using wordTrace_append hprefix tailTrace_710123
  have hstable : (prefixWord ++ tailWord_710123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710123).length < 2 ^ (prefixWord ++ tailWord_710123).sum := by decide
  have hdescent : baseEnd_710123 < baseStart_710123 := by decide
  rcases family_descends (prefixWord ++ tailWord_710123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710136 : List Nat := [2, 1, 2, 1, 1, 7, 1, 3, 2]
def baseStart_710136 : Nat := 118140960795 + 710136 * 2 ^ 59
def prefixEnd_710136 : Nat := 4983230072969 + 3 ^ 40 * 710136 * 2
def baseEnd_710136 : Nat := 324125420498967842963689

theorem tailTrace_710136 : CollatzResearch.WordTrace tailWord_710136 prefixEnd_710136 324125420498967842963689 := by
  unfold tailWord_710136
  simp only [CollatzResearch.WordTrace]
  refine ⟨12950393877653014209095131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17267191836870685612126841 12950393877653014209095131)
  ·
    refine ⟨19425590816479521313642697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12950393877653014209095131 19425590816479521313642697)
    ·
      refine ⟨14569193112359640985232023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19425590816479521313642697 14569193112359640985232023)
      ·
        refine ⟨21853789668539461477848035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14569193112359640985232023 21853789668539461477848035)
        ·
          refine ⟨32780684502809192216772053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21853789668539461477848035 32780684502809192216772053)
          ·
            refine ⟨768297293034590442580595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 32780684502809192216772053 768297293034590442580595)
            ·
              refine ⟨1152445939551885663870893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768297293034590442580595 1152445939551885663870893)
              ·
                refine ⟨432167227331957123951585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1152445939551885663870893 432167227331957123951585)
                ·
                  refine ⟨324125420498967842963689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432167227331957123951585 324125420498967842963689)
                  ·
                    rfl

theorem cell20_710136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 3, 2].length) (baseStart_710136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710136 prefixEnd_710136 := by exact prefixLift 710136
  have htrace : WordTrace (prefixWord ++ tailWord_710136) baseStart_710136 baseEnd_710136 := by
    simpa [prefixWord, tailWord_710136, baseEnd_710136] using wordTrace_append hprefix tailTrace_710136
  have hstable : (prefixWord ++ tailWord_710136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710136).length < 2 ^ (prefixWord ++ tailWord_710136).sum := by decide
  have hdescent : baseEnd_710136 < baseStart_710136 := by decide
  rcases family_descends (prefixWord ++ tailWord_710136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710178 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_710178 : Nat := 118140960795 + 710178 * 2 ^ 59
def prefixEnd_710178 : Nat := 4983230072969 + 3 ^ 40 * 710178 * 2
def baseEnd_710178 : Nat := 324144590443402363563517

theorem tailTrace_710178 : CollatzResearch.WordTrace tailWord_710178 prefixEnd_710178 324144590443402363563517 := by
  unfold tailWord_710178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6475579905288467397804797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17268213080769246394146125 6475579905288467397804797)
  ·
    refine ⟨2428342464483175274176799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6475579905288467397804797 2428342464483175274176799)
    ·
      refine ⟨3642513696724762911265199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2428342464483175274176799 3642513696724762911265199)
      ·
        refine ⟨5463770545087144366897799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3642513696724762911265199 5463770545087144366897799)
        ·
          refine ⟨8195655817630716550346699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5463770545087144366897799 8195655817630716550346699)
          ·
            refine ⟨12293483726446074825520049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8195655817630716550346699 12293483726446074825520049)
            ·
              refine ⟨9220112794834556119140037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12293483726446074825520049 9220112794834556119140037)
              ·
                refine ⟨1728771149031479272338757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9220112794834556119140037 1728771149031479272338757)
                ·
                  refine ⟨324144590443402363563517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1728771149031479272338757 324144590443402363563517)
                  ·
                    rfl

theorem cell20_710178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_710178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710178 prefixEnd_710178 := by exact prefixLift 710178
  have htrace : WordTrace (prefixWord ++ tailWord_710178) baseStart_710178 baseEnd_710178 := by
    simpa [prefixWord, tailWord_710178, baseEnd_710178] using wordTrace_append hprefix tailTrace_710178
  have hstable : (prefixWord ++ tailWord_710178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710178).length < 2 ^ (prefixWord ++ tailWord_710178).sum := by decide
  have hdescent : baseEnd_710178 < baseStart_710178 := by decide
  rcases family_descends (prefixWord ++ tailWord_710178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710250 : List Nat := [3, 1, 3, 2, 1, 3, 2, 3, 2]
def baseStart_710250 : Nat := 118140960795 + 710250 * 2 ^ 59
def prefixEnd_710250 : Nat := 4983230072969 + 3 ^ 40 * 710250 * 2
def baseEnd_710250 : Nat := 324177453205290113163223

theorem tailTrace_710250 : CollatzResearch.WordTrace tailWord_710250 prefixEnd_710250 324177453205290113163223 := by
  unfold tailWord_710250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6476236419223256471960051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17269963784595350591893469 6476236419223256471960051)
  ·
    refine ⟨9714354628834884707940077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6476236419223256471960051 9714354628834884707940077)
    ·
      refine ⟨3642882985813081765477529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9714354628834884707940077 3642882985813081765477529)
      ·
        refine ⟨2732162239359811324108147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3642882985813081765477529 2732162239359811324108147)
        ·
          refine ⟨4098243359039716986162221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2732162239359811324108147 4098243359039716986162221)
          ·
            refine ⟨1536841259639893869810833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4098243359039716986162221 1536841259639893869810833)
            ·
              refine ⟨1152630944729920402358125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1536841259639893869810833 1152630944729920402358125)
              ·
                refine ⟨432236604273720150884297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1152630944729920402358125 432236604273720150884297)
                ·
                  refine ⟨324177453205290113163223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432236604273720150884297 324177453205290113163223)
                  ·
                    rfl

theorem cell20_710250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_710250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710250 prefixEnd_710250 := by exact prefixLift 710250
  have htrace : WordTrace (prefixWord ++ tailWord_710250) baseStart_710250 baseEnd_710250 := by
    simpa [prefixWord, tailWord_710250, baseEnd_710250] using wordTrace_append hprefix tailTrace_710250
  have hstable : (prefixWord ++ tailWord_710250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710250).length < 2 ^ (prefixWord ++ tailWord_710250).sum := by decide
  have hdescent : baseEnd_710250 < baseStart_710250 := by decide
  rcases family_descends (prefixWord ++ tailWord_710250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710309 : List Nat := [1, 3, 1, 2, 1, 2, 5, 3, 2]
def baseStart_710309 : Nat := 118140960795 + 710309 * 2 ^ 59
def prefixEnd_710309 : Nat := 4983230072969 + 3 ^ 40 * 710309 * 2
def baseEnd_710309 : Nat := 324204382412948130196315

theorem tailTrace_710309 : CollatzResearch.WordTrace tailWord_710309 prefixEnd_710309 324204382412948130196315 := by
  unfold tailWord_710309
  simp only [CollatzResearch.WordTrace]
  refine ⟨25907097583679278964237981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17271398389119519309491987 25907097583679278964237981)
  ·
    refine ⟨9715161593879729611589243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25907097583679278964237981 9715161593879729611589243)
    ·
      refine ⟨14572742390819594417383865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9715161593879729611589243 14572742390819594417383865)
      ·
        refine ⟨10929556793114695813037899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14572742390819594417383865 10929556793114695813037899)
        ·
          refine ⟨16394335189672043719556849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10929556793114695813037899 16394335189672043719556849)
          ·
            refine ⟨12295751392254032789667637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16394335189672043719556849 12295751392254032789667637)
            ·
              refine ⟨1152726693023815574031341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12295751392254032789667637 1152726693023815574031341)
              ·
                refine ⟨432272509883930840261753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1152726693023815574031341 432272509883930840261753)
                ·
                  refine ⟨324204382412948130196315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432272509883930840261753 324204382412948130196315)
                  ·
                    rfl

theorem cell20_710309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_710309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710309 prefixEnd_710309 := by exact prefixLift 710309
  have htrace : WordTrace (prefixWord ++ tailWord_710309) baseStart_710309 baseEnd_710309 := by
    simpa [prefixWord, tailWord_710309, baseEnd_710309] using wordTrace_append hprefix tailTrace_710309
  have hstable : (prefixWord ++ tailWord_710309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710309).length < 2 ^ (prefixWord ++ tailWord_710309).sum := by decide
  have hdescent : baseEnd_710309 < baseStart_710309 := by decide
  rcases family_descends (prefixWord ++ tailWord_710309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710312 : List Nat := [2, 1, 7, 1, 1, 2, 6]
def baseStart_710312 : Nat := 118140960795 + 710312 * 2 ^ 59
def prefixEnd_710312 : Nat := 4983230072969 + 3 ^ 40 * 710312 * 2
def baseEnd_710312 : Nat := 36022861299410383677367

theorem tailTrace_710312 : CollatzResearch.WordTrace tailWord_710312 prefixEnd_710312 36022861299410383677367 := by
  unfold tailWord_710312
  simp only [CollatzResearch.WordTrace]
  refine ⟨12953603501334205238298595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17271471335112273651064793 12953603501334205238298595)
  ·
    refine ⟨19430405252001307857447893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12953603501334205238298595 19430405252001307857447893)
    ·
      refine ⟨455400123093780652908935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 19430405252001307857447893 455400123093780652908935)
      ·
        refine ⟨683100184640670979363403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455400123093780652908935 683100184640670979363403)
        ·
          refine ⟨1024650276961006469045105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683100184640670979363403 1024650276961006469045105)
          ·
            refine ⟨768487707720754851783829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024650276961006469045105 768487707720754851783829)
            ·
              refine ⟨36022861299410383677367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 768487707720754851783829 36022861299410383677367)
              ·
                rfl

theorem cell20_710312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 6].length) (baseStart_710312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710312 prefixEnd_710312 := by exact prefixLift 710312
  have htrace : WordTrace (prefixWord ++ tailWord_710312) baseStart_710312 baseEnd_710312 := by
    simpa [prefixWord, tailWord_710312, baseEnd_710312] using wordTrace_append hprefix tailTrace_710312
  have hstable : (prefixWord ++ tailWord_710312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710312).length < 2 ^ (prefixWord ++ tailWord_710312).sum := by decide
  have hdescent : baseEnd_710312 < baseStart_710312 := by decide
  rcases family_descends (prefixWord ++ tailWord_710312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710320 : List Nat := [2, 1, 1, 1, 2, 1, 12]
def baseStart_710320 : Nat := 118140960795 + 710320 * 2 ^ 59
def prefixEnd_710320 : Nat := 4983230072969 + 3 ^ 40 * 710320 * 2
def baseEnd_710320 : Nat := 36023267012520108981067

theorem tailTrace_710320 : CollatzResearch.WordTrace tailWord_710320 prefixEnd_710320 36023267012520108981067 := by
  unfold tailWord_710320
  simp only [CollatzResearch.WordTrace]
  refine ⟨12953749393319713921444207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17271665857759618561925609 12953749393319713921444207)
  ·
    refine ⟨19430624089979570882166311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12953749393319713921444207 19430624089979570882166311)
    ·
      refine ⟨29145936134969356323249467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19430624089979570882166311 29145936134969356323249467)
      ·
        refine ⟨43718904202454034484874201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29145936134969356323249467 43718904202454034484874201)
        ·
          refine ⟨32789178151840525863655651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43718904202454034484874201 32789178151840525863655651)
          ·
            refine ⟨49183767227760788795483477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32789178151840525863655651 49183767227760788795483477)
            ·
              refine ⟨36023267012520108981067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 49183767227760788795483477 36023267012520108981067)
              ·
                rfl

theorem cell20_710320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 12].length) (baseStart_710320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710320 prefixEnd_710320 := by exact prefixLift 710320
  have htrace : WordTrace (prefixWord ++ tailWord_710320) baseStart_710320 baseEnd_710320 := by
    simpa [prefixWord, tailWord_710320, baseEnd_710320] using wordTrace_append hprefix tailTrace_710320
  have hstable : (prefixWord ++ tailWord_710320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710320).length < 2 ^ (prefixWord ++ tailWord_710320).sum := by decide
  have hdescent : baseEnd_710320 < baseStart_710320 := by decide
  rcases family_descends (prefixWord ++ tailWord_710320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710326 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_710326 : Nat := 118140960795 + 710326 * 2 ^ 59
def prefixEnd_710326 : Nat := 4983230072969 + 3 ^ 40 * 710326 * 2
def baseEnd_710326 : Nat := 324212141676171626629579

theorem tailTrace_710326 : CollatzResearch.WordTrace tailWord_710326 prefixEnd_710326 324212141676171626629579 := by
  unfold tailWord_710326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619232351538605679225427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17271811749745127245071221 1619232351538605679225427)
  ·
    refine ⟨2428848527307908518838141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1619232351538605679225427 2428848527307908518838141)
    ·
      refine ⟨910818197740465694564303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2428848527307908518838141 910818197740465694564303)
      ·
        refine ⟨1366227296610698541846455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 910818197740465694564303 1366227296610698541846455)
        ·
          refine ⟨2049340944916047812769683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1366227296610698541846455 2049340944916047812769683)
          ·
            refine ⟨3074011417374071719154525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049340944916047812769683 3074011417374071719154525)
            ·
              refine ⟨1152754281515276894682947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3074011417374071719154525 1152754281515276894682947)
              ·
                refine ⟨1729131422272915342024421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152754281515276894682947 1729131422272915342024421)
                ·
                  refine ⟨324212141676171626629579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729131422272915342024421 324212141676171626629579)
                  ·
                    rfl

theorem cell20_710326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_710326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710326 prefixEnd_710326 := by exact prefixLift 710326
  have htrace : WordTrace (prefixWord ++ tailWord_710326) baseStart_710326 baseEnd_710326 := by
    simpa [prefixWord, tailWord_710326, baseEnd_710326] using wordTrace_append hprefix tailTrace_710326
  have hstable : (prefixWord ++ tailWord_710326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710326).length < 2 ^ (prefixWord ++ tailWord_710326).sum := by decide
  have hdescent : baseEnd_710326 < baseStart_710326 := by decide
  rcases family_descends (prefixWord ++ tailWord_710326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710330 : List Nat := [3, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_710330 : Nat := 118140960795 + 710330 * 2 ^ 59
def prefixEnd_710330 : Nat := 4983230072969 + 3 ^ 40 * 710330 * 2
def baseEnd_710330 : Nat := 324213967385165390496229

theorem tailTrace_710330 : CollatzResearch.WordTrace tailWord_710330 prefixEnd_710330 324213967385165390496229 := by
  unfold tailWord_710330
  simp only [CollatzResearch.WordTrace]
  refine ⟨6476965879150799887688111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17271909011068799700501629 6476965879150799887688111)
  ·
    refine ⟨9715448818726199831532167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6476965879150799887688111 9715448818726199831532167)
    ·
      refine ⟨14573173228089299747298251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9715448818726199831532167 14573173228089299747298251)
      ·
        refine ⟨21859759842133949620947377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14573173228089299747298251 21859759842133949620947377)
        ·
          refine ⟨16394819881600462215710533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21859759842133949620947377 16394819881600462215710533)
          ·
            refine ⟨3074028727800086665445725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16394819881600462215710533 3074028727800086665445725)
            ·
              refine ⟨1152760772925032499542147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3074028727800086665445725 1152760772925032499542147)
              ·
                refine ⟨1729141159387548749313221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152760772925032499542147 1729141159387548749313221)
                ·
                  refine ⟨324213967385165390496229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729141159387548749313221 324213967385165390496229)
                  ·
                    rfl

theorem cell20_710330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_710330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710330 prefixEnd_710330 := by exact prefixLift 710330
  have htrace : WordTrace (prefixWord ++ tailWord_710330) baseStart_710330 baseEnd_710330 := by
    simpa [prefixWord, tailWord_710330, baseEnd_710330] using wordTrace_append hprefix tailTrace_710330
  have hstable : (prefixWord ++ tailWord_710330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710330).length < 2 ^ (prefixWord ++ tailWord_710330).sum := by decide
  have hdescent : baseEnd_710330 < baseStart_710330 := by decide
  rcases family_descends (prefixWord ++ tailWord_710330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710351 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 4]
def baseStart_710351 : Nat := 118140960795 + 710351 * 2 ^ 59
def prefixEnd_710351 : Nat := 4983230072969 + 3 ^ 40 * 710351 * 2
def baseEnd_710351 : Nat := 324223552357382650796143

theorem tailTrace_710351 : CollatzResearch.WordTrace tailWord_710351 prefixEnd_710351 324223552357382650796143 := by
  unfold tailWord_710351
  simp only [CollatzResearch.WordTrace]
  refine ⟨25908629449527120137266907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17272419633018080091511271 25908629449527120137266907)
  ·
    refine ⟨38862944174290680205900361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25908629449527120137266907 38862944174290680205900361)
    ·
      refine ⟨29147208130718010154425271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38862944174290680205900361 29147208130718010154425271)
      ·
        refine ⟨43720812196077015231637907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29147208130718010154425271 43720812196077015231637907)
        ·
          refine ⟨65581218294115522847456861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43720812196077015231637907 65581218294115522847456861)
          ·
            refine ⟨24592956860293321067796323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65581218294115522847456861 24592956860293321067796323)
            ·
              refine ⟨36889435290439981601694485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24592956860293321067796323 36889435290439981601694485)
              ·
                refine ⟨1729192279239374137579429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36889435290439981601694485 1729192279239374137579429)
                ·
                  refine ⟨324223552357382650796143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729192279239374137579429 324223552357382650796143)
                  ·
                    rfl

theorem cell20_710351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 4].length) (baseStart_710351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710351 prefixEnd_710351 := by exact prefixLift 710351
  have htrace : WordTrace (prefixWord ++ tailWord_710351) baseStart_710351 baseEnd_710351 := by
    simpa [prefixWord, tailWord_710351, baseEnd_710351] using wordTrace_append hprefix tailTrace_710351
  have hstable : (prefixWord ++ tailWord_710351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710351).length < 2 ^ (prefixWord ++ tailWord_710351).sum := by decide
  have hdescent : baseEnd_710351 < baseStart_710351 := by decide
  rcases family_descends (prefixWord ++ tailWord_710351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710375 : List Nat := [1, 1, 5, 4, 9]
def baseStart_710375 : Nat := 118140960795 + 710375 * 2 ^ 59
def prefixEnd_710375 : Nat := 4983230072969 + 3 ^ 40 * 710375 * 2
def baseEnd_710375 : Nat := 4002895143349941160445

theorem tailTrace_710375 : CollatzResearch.WordTrace tailWord_710375 prefixEnd_710375 4002895143349941160445 := by
  unfold tailWord_710375
  simp only [CollatzResearch.WordTrace]
  refine ⟨25909504801440172236140579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17273003200960114824093719 25909504801440172236140579)
  ·
    refine ⟨38864257202160258354210869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25909504801440172236140579 38864257202160258354210869)
    ·
      refine ⟨3643524112702524220707269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38864257202160258354210869 3643524112702524220707269)
      ·
        refine ⟨683160771131723291382613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3643524112702524220707269 683160771131723291382613)
        ·
          refine ⟨4002895143349941160445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 683160771131723291382613 4002895143349941160445)
          ·
            rfl

theorem cell20_710375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 9].length) (baseStart_710375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710375 prefixEnd_710375 := by exact prefixLift 710375
  have htrace : WordTrace (prefixWord ++ tailWord_710375) baseStart_710375 baseEnd_710375 := by
    simpa [prefixWord, tailWord_710375, baseEnd_710375] using wordTrace_append hprefix tailTrace_710375
  have hstable : (prefixWord ++ tailWord_710375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710375).length < 2 ^ (prefixWord ++ tailWord_710375).sum := by decide
  have hdescent : baseEnd_710375 < baseStart_710375 := by decide
  rcases family_descends (prefixWord ++ tailWord_710375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710381 : List Nat := [1, 5, 1, 2, 1, 4, 2, 2, 2]
def baseStart_710381 : Nat := 118140960795 + 710381 * 2 ^ 59
def prefixEnd_710381 : Nat := 4983230072969 + 3 ^ 40 * 710381 * 2
def baseEnd_710381 : Nat := 324237245174835879796021

theorem tailTrace_710381 : CollatzResearch.WordTrace tailWord_710381 prefixEnd_710381 324237245174835879796021 := by
  unfold tailWord_710381
  simp only [CollatzResearch.WordTrace]
  refine ⟨25909723639418435260858997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17273149092945623507239331 25909723639418435260858997)
  ·
    refine ⟨2429036591195478305705531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25909723639418435260858997 2429036591195478305705531)
    ·
      refine ⟨3643554886793217458558297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2429036591195478305705531 3643554886793217458558297)
      ·
        refine ⟨2732666165094913093918723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3643554886793217458558297 2732666165094913093918723)
        ·
          refine ⟨4098999247642369640878085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2732666165094913093918723 4098999247642369640878085)
          ·
            refine ⟨768562358932944307664641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4098999247642369640878085 768562358932944307664641)
            ·
              refine ⟨576421769199708230748481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768562358932944307664641 576421769199708230748481)
              ·
                refine ⟨432316326899781173061361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576421769199708230748481 432316326899781173061361)
                ·
                  refine ⟨324237245174835879796021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432316326899781173061361 324237245174835879796021)
                  ·
                    rfl

theorem cell20_710381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_710381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710381 prefixEnd_710381 := by exact prefixLift 710381
  have htrace : WordTrace (prefixWord ++ tailWord_710381) baseStart_710381 baseEnd_710381 := by
    simpa [prefixWord, tailWord_710381, baseEnd_710381] using wordTrace_append hprefix tailTrace_710381
  have hstable : (prefixWord ++ tailWord_710381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710381).length < 2 ^ (prefixWord ++ tailWord_710381).sum := by decide
  have hdescent : baseEnd_710381 < baseStart_710381 := by decide
  rcases family_descends (prefixWord ++ tailWord_710381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710385 : List Nat := [1, 2, 2, 2, 2, 4, 1, 4, 2]
def baseStart_710385 : Nat := 118140960795 + 710385 * 2 ^ 59
def prefixEnd_710385 : Nat := 4983230072969 + 3 ^ 40 * 710385 * 2
def baseEnd_710385 : Nat := 324239070883829643662671

theorem tailTrace_710385 : CollatzResearch.WordTrace tailWord_710385 prefixEnd_710385 324239070883829643662671 := by
  unfold tailWord_710385
  simp only [CollatzResearch.WordTrace]
  refine ⟨25909869531403943944004609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17273246354269295962669739 25909869531403943944004609)
  ·
    refine ⟨19432402148552957958003457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25909869531403943944004609 19432402148552957958003457)
    ·
      refine ⟨14574301611414718468502593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19432402148552957958003457 14574301611414718468502593)
      ·
        refine ⟨10930726208561038851376945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14574301611414718468502593 10930726208561038851376945)
        ·
          refine ⟨8198044656420779138532709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10930726208561038851376945 8198044656420779138532709)
          ·
            refine ⟨1537133373078896088474883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8198044656420779138532709 1537133373078896088474883)
            ·
              refine ⟨2305700059618344132712325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537133373078896088474883 2305700059618344132712325)
              ·
                refine ⟨432318761178439524883561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2305700059618344132712325 432318761178439524883561)
                ·
                  refine ⟨324239070883829643662671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432318761178439524883561 324239070883829643662671)
                  ·
                    rfl

theorem cell20_710385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 2].length) (baseStart_710385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710385 prefixEnd_710385 := by exact prefixLift 710385
  have htrace : WordTrace (prefixWord ++ tailWord_710385) baseStart_710385 baseEnd_710385 := by
    simpa [prefixWord, tailWord_710385, baseEnd_710385] using wordTrace_append hprefix tailTrace_710385
  have hstable : (prefixWord ++ tailWord_710385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710385).length < 2 ^ (prefixWord ++ tailWord_710385).sum := by decide
  have hdescent : baseEnd_710385 < baseStart_710385 := by decide
  rcases family_descends (prefixWord ++ tailWord_710385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710388 : List Nat := [2, 6, 1, 1, 1, 3, 1, 5]
def baseStart_710388 : Nat := 118140960795 + 710388 * 2 ^ 59
def prefixEnd_710388 : Nat := 4983230072969 + 3 ^ 40 * 710388 * 2
def baseEnd_710388 : Nat := 108080146721858322187553

theorem tailTrace_710388 : CollatzResearch.WordTrace tailWord_710388 prefixEnd_710388 108080146721858322187553 := by
  unfold tailWord_710388
  simp only [CollatzResearch.WordTrace]
  refine ⟨12954989475196537728181909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17273319300262050304242545 12954989475196537728181909)
  ·
    refine ⟨607265131649837706008527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12954989475196537728181909 607265131649837706008527)
    ·
      refine ⟨910897697474756559012791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607265131649837706008527 910897697474756559012791)
      ·
        refine ⟨1366346546212134838519187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 910897697474756559012791 1366346546212134838519187)
        ·
          refine ⟨2049519819318202257778781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1366346546212134838519187 2049519819318202257778781)
          ·
            refine ⟨768569932244325846667043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2049519819318202257778781 768569932244325846667043)
            ·
              refine ⟨1152854898366488770000565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768569932244325846667043 1152854898366488770000565)
              ·
                refine ⟨108080146721858322187553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1152854898366488770000565 108080146721858322187553)
                ·
                  rfl

theorem cell20_710388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 5].length) (baseStart_710388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710388 prefixEnd_710388 := by exact prefixLift 710388
  have htrace : WordTrace (prefixWord ++ tailWord_710388) baseStart_710388 baseEnd_710388 := by
    simpa [prefixWord, tailWord_710388, baseEnd_710388] using wordTrace_append hprefix tailTrace_710388
  have hstable : (prefixWord ++ tailWord_710388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710388).length < 2 ^ (prefixWord ++ tailWord_710388).sum := by decide
  have hdescent : baseEnd_710388 < baseStart_710388 := by decide
  rcases family_descends (prefixWord ++ tailWord_710388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710423 : List Nat := [1, 1, 3, 4, 2, 1, 1, 5, 2]
def baseStart_710423 : Nat := 118140960795 + 710423 * 2 ^ 59
def prefixEnd_710423 : Nat := 4983230072969 + 3 ^ 40 * 710423 * 2
def baseEnd_710423 : Nat := 324256415119270400395849

theorem tailTrace_710423 : CollatzResearch.WordTrace tailWord_710423 prefixEnd_710423 324256415119270400395849 := by
  unfold tailWord_710423
  simp only [CollatzResearch.WordTrace]
  refine ⟨25911255505266276433887923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17274170336844184289258615 25911255505266276433887923)
  ·
    refine ⟨38866883257899414650831885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25911255505266276433887923 38866883257899414650831885)
    ·
      refine ⟨14575081221712280494061957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38866883257899414650831885 14575081221712280494061957)
      ·
        refine ⟨2732827729071052592636617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14575081221712280494061957 2732827729071052592636617)
        ·
          refine ⟨2049620796803289444477463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2732827729071052592636617 2049620796803289444477463)
          ·
            refine ⟨3074431195204934166716195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049620796803289444477463 3074431195204934166716195)
            ·
              refine ⟨4611646792807401250074293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3074431195204934166716195 4611646792807401250074293)
              ·
                refine ⟨432341886825693867194465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4611646792807401250074293 432341886825693867194465)
                ·
                  refine ⟨324256415119270400395849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432341886825693867194465 324256415119270400395849)
                  ·
                    rfl

theorem cell20_710423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 2].length) (baseStart_710423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710423 prefixEnd_710423 := by exact prefixLift 710423
  have htrace : WordTrace (prefixWord ++ tailWord_710423) baseStart_710423 baseEnd_710423 := by
    simpa [prefixWord, tailWord_710423, baseEnd_710423] using wordTrace_append hprefix tailTrace_710423
  have hstable : (prefixWord ++ tailWord_710423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710423).length < 2 ^ (prefixWord ++ tailWord_710423).sum := by decide
  have hdescent : baseEnd_710423 < baseStart_710423 := by decide
  rcases family_descends (prefixWord ++ tailWord_710423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710437 : List Nat := [1, 3, 1, 2, 3, 2, 3, 2, 3]
def baseStart_710437 : Nat := 118140960795 + 710437 * 2 ^ 59
def prefixEnd_710437 : Nat := 4983230072969 + 3 ^ 40 * 710437 * 2
def baseEnd_710437 : Nat := 324262805100748573929125

theorem tailTrace_710437 : CollatzResearch.WordTrace tailWord_710437 prefixEnd_710437 324262805100748573929125 := by
  unfold tailWord_710437
  simp only [CollatzResearch.WordTrace]
  refine ⟨25911766127215556824897565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17274510751477037883265043 25911766127215556824897565)
  ·
    refine ⟨9716912297705833809336587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25911766127215556824897565 9716912297705833809336587)
    ·
      refine ⟨14575368446558750714004881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9716912297705833809336587 14575368446558750714004881)
      ·
        refine ⟨10931526334919063035503661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14575368446558750714004881 10931526334919063035503661)
        ·
          refine ⟨4099322375594648638313873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10931526334919063035503661 4099322375594648638313873)
          ·
            refine ⟨3074491781695986478735405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4099322375594648638313873 3074491781695986478735405)
            ·
              refine ⟨1152934418135994929525777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3074491781695986478735405 1152934418135994929525777)
              ·
                refine ⟨864700813601996197144333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1152934418135994929525777 864700813601996197144333)
                ·
                  refine ⟨324262805100748573929125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864700813601996197144333 324262805100748573929125)
                  ·
                    rfl

theorem cell20_710437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_710437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710437 prefixEnd_710437 := by exact prefixLift 710437
  have htrace : WordTrace (prefixWord ++ tailWord_710437) baseStart_710437 baseEnd_710437 := by
    simpa [prefixWord, tailWord_710437, baseEnd_710437] using wordTrace_append hprefix tailTrace_710437
  have hstable : (prefixWord ++ tailWord_710437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710437).length < 2 ^ (prefixWord ++ tailWord_710437).sum := by decide
  have hdescent : baseEnd_710437 < baseStart_710437 := by decide
  rcases family_descends (prefixWord ++ tailWord_710437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710444 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 4]
def baseStart_710444 : Nat := 118140960795 + 710444 * 2 ^ 59
def prefixEnd_710444 : Nat := 4983230072969 + 3 ^ 40 * 710444 * 2
def baseEnd_710444 : Nat := 324266000091487660695763

theorem tailTrace_710444 : CollatzResearch.WordTrace tailWord_710444 prefixEnd_710444 324266000091487660695763 := by
  unfold tailWord_710444
  simp only [CollatzResearch.WordTrace]
  refine ⟨12956010719095098510201193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17274680958793464680268257 12956010719095098510201193)
  ·
    refine ⟨9717008039321323882650895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12956010719095098510201193 9717008039321323882650895)
    ·
      refine ⟨14575512058981985823976343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9717008039321323882650895 14575512058981985823976343)
      ·
        refine ⟨21863268088472978735964515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14575512058981985823976343 21863268088472978735964515)
        ·
          refine ⟨32794902132709468103946773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21863268088472978735964515 32794902132709468103946773)
          ·
            refine ⟨1537261037470756317372505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32794902132709468103946773 1537261037470756317372505)
            ·
              refine ⟨1152945778103067238029379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537261037470756317372505 1152945778103067238029379)
              ·
                refine ⟨1729418667154600857044069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1152945778103067238029379 1729418667154600857044069)
                ·
                  refine ⟨324266000091487660695763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729418667154600857044069 324266000091487660695763)
                  ·
                    rfl

theorem cell20_710444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_710444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710444 prefixEnd_710444 := by exact prefixLift 710444
  have htrace : WordTrace (prefixWord ++ tailWord_710444) baseStart_710444 baseEnd_710444 := by
    simpa [prefixWord, tailWord_710444, baseEnd_710444] using wordTrace_append hprefix tailTrace_710444
  have hstable : (prefixWord ++ tailWord_710444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710444).length < 2 ^ (prefixWord ++ tailWord_710444).sum := by decide
  have hdescent : baseEnd_710444 < baseStart_710444 := by decide
  rcases family_descends (prefixWord ++ tailWord_710444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710496 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_710496 : Nat := 118140960795 + 710496 * 2 ^ 59
def prefixEnd_710496 : Nat := 4983230072969 + 3 ^ 40 * 710496 * 2
def baseEnd_710496 : Nat := 324289734308406590962217

theorem tailTrace_710496 : CollatzResearch.WordTrace tailWord_710496 prefixEnd_710496 324289734308406590962217 := by
  unfold tailWord_710496
  simp only [CollatzResearch.WordTrace]
  refine ⟨12956959017000904950647671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17275945356001206600863561 12956959017000904950647671)
  ·
    refine ⟨19435438525501357425971507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12956959017000904950647671 19435438525501357425971507)
    ·
      refine ⟨29153157788252036138957261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19435438525501357425971507 29153157788252036138957261)
      ·
        refine ⟨10932434170594513552108973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29153157788252036138957261 10932434170594513552108973)
        ·
          refine ⟨4099662813972942582040865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10932434170594513552108973 4099662813972942582040865)
          ·
            refine ⟨3074747110479706936530649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4099662813972942582040865 3074747110479706936530649)
            ·
              refine ⟨2306060332859780202397987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3074747110479706936530649 2306060332859780202397987)
              ·
                refine ⟨3459090499289670303596981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306060332859780202397987 3459090499289670303596981)
                ·
                  refine ⟨324289734308406590962217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3459090499289670303596981 324289734308406590962217)
                  ·
                    rfl

theorem cell20_710496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_710496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710496 prefixEnd_710496 := by exact prefixLift 710496
  have htrace : WordTrace (prefixWord ++ tailWord_710496) baseStart_710496 baseEnd_710496 := by
    simpa [prefixWord, tailWord_710496, baseEnd_710496] using wordTrace_append hprefix tailTrace_710496
  have hstable : (prefixWord ++ tailWord_710496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710496).length < 2 ^ (prefixWord ++ tailWord_710496).sum := by decide
  have hdescent : baseEnd_710496 < baseStart_710496 := by decide
  rcases family_descends (prefixWord ++ tailWord_710496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710499 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 4]
def baseStart_710499 : Nat := 118140960795 + 710499 * 2 ^ 59
def prefixEnd_710499 : Nat := 4983230072969 + 3 ^ 40 * 710499 * 2
def baseEnd_710499 : Nat := 324291103590151913862205

theorem tailTrace_710499 : CollatzResearch.WordTrace tailWord_710499 prefixEnd_710499 324291103590151913862205 := by
  unfold tailWord_710499
  simp only [CollatzResearch.WordTrace]
  refine ⟨25914027452990941413654551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17276018301993960942436367 25914027452990941413654551)
  ·
    refine ⟨38871041179486412120481827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25914027452990941413654551 38871041179486412120481827)
    ·
      refine ⟨58306561769229618180722741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38871041179486412120481827 58306561769229618180722741)
      ·
        refine ⟨5466240165865276704442757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58306561769229618180722741 5466240165865276704442757)
        ·
          refine ⟨1024920031099739382083017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5466240165865276704442757 1024920031099739382083017)
          ·
            refine ⟨768690023324804536562263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1024920031099739382083017 768690023324804536562263)
            ·
              refine ⟨1153035034987206804843395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768690023324804536562263 1153035034987206804843395)
              ·
                refine ⟨1729552552480810207265093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153035034987206804843395 1729552552480810207265093)
                ·
                  refine ⟨324291103590151913862205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729552552480810207265093 324291103590151913862205)
                  ·
                    rfl

theorem cell20_710499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 4].length) (baseStart_710499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710499 prefixEnd_710499 := by exact prefixLift 710499
  have htrace : WordTrace (prefixWord ++ tailWord_710499) baseStart_710499 baseEnd_710499 := by
    simpa [prefixWord, tailWord_710499, baseEnd_710499] using wordTrace_append hprefix tailTrace_710499
  have hstable : (prefixWord ++ tailWord_710499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710499).length < 2 ^ (prefixWord ++ tailWord_710499).sum := by decide
  have hdescent : baseEnd_710499 < baseStart_710499 := by decide
  rcases family_descends (prefixWord ++ tailWord_710499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710550 : List Nat := [5, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_710550 : Nat := 118140960795 + 710550 * 2 ^ 59
def prefixEnd_710550 : Nat := 4983230072969 + 3 ^ 40 * 710550 * 2
def baseEnd_710550 : Nat := 324314381379822403161997

theorem tailTrace_710550 : CollatzResearch.WordTrace tailWord_710550 prefixEnd_710550 324314381379822403161997 := by
  unfold tailWord_710550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619742973487886070235069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17277258383870784749174069 1619742973487886070235069)
  ·
    refine ⟨607403615057957276338151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1619742973487886070235069 607403615057957276338151)
    ·
      refine ⟨911105422586935914507227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607403615057957276338151 911105422586935914507227)
      ·
        refine ⟨1366658133880403871760841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911105422586935914507227 1366658133880403871760841)
        ·
          refine ⟨1024993600410302903820631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1366658133880403871760841 1024993600410302903820631)
          ·
            refine ⟨1537490400615454355730947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1024993600410302903820631 1537490400615454355730947)
            ·
              refine ⟨2306235600923181533596421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537490400615454355730947 2306235600923181533596421)
              ·
                refine ⟨432419175173096537549329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2306235600923181533596421 432419175173096537549329)
                ·
                  refine ⟨324314381379822403161997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432419175173096537549329 324314381379822403161997)
                  ·
                    rfl

theorem cell20_710550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_710550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710550 prefixEnd_710550 := by exact prefixLift 710550
  have htrace : WordTrace (prefixWord ++ tailWord_710550) baseStart_710550 baseEnd_710550 := by
    simpa [prefixWord, tailWord_710550, baseEnd_710550] using wordTrace_append hprefix tailTrace_710550
  have hstable : (prefixWord ++ tailWord_710550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710550).length < 2 ^ (prefixWord ++ tailWord_710550).sum := by decide
  have hdescent : baseEnd_710550 < baseStart_710550 := by decide
  rcases family_descends (prefixWord ++ tailWord_710550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710551 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 3]
def baseStart_710551 : Nat := 118140960795 + 710551 * 2 ^ 59
def prefixEnd_710551 : Nat := 4983230072969 + 3 ^ 40 * 710551 * 2
def baseEnd_710551 : Nat := 324314837807070844128659

theorem tailTrace_710551 : CollatzResearch.WordTrace tailWord_710551 prefixEnd_710551 324314837807070844128659 := by
  unfold tailWord_710551
  simp only [CollatzResearch.WordTrace]
  refine ⟨25915924048802554294547507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17277282699201702863031671 25915924048802554294547507)
  ·
    refine ⟨38873886073203831441821261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25915924048802554294547507 38873886073203831441821261)
    ·
      refine ⟨14577707277451436790682973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38873886073203831441821261 14577707277451436790682973)
      ·
        refine ⟨5466640229044288796506115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14577707277451436790682973 5466640229044288796506115)
        ·
          refine ⟨8199960343566433194759173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5466640229044288796506115 8199960343566433194759173)
          ·
            refine ⟨1537492564418706224017345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8199960343566433194759173 1537492564418706224017345)
            ·
              refine ⟨1153119423314029668013009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537492564418706224017345 1153119423314029668013009)
              ·
                refine ⟨864839567485522251009757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1153119423314029668013009 864839567485522251009757)
                ·
                  refine ⟨324314837807070844128659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864839567485522251009757 324314837807070844128659)
                  ·
                    rfl

theorem cell20_710551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 3].length) (baseStart_710551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710551 prefixEnd_710551 := by exact prefixLift 710551
  have htrace : WordTrace (prefixWord ++ tailWord_710551) baseStart_710551 baseEnd_710551 := by
    simpa [prefixWord, tailWord_710551, baseEnd_710551] using wordTrace_append hprefix tailTrace_710551
  have hstable : (prefixWord ++ tailWord_710551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710551).length < 2 ^ (prefixWord ++ tailWord_710551).sum := by decide
  have hdescent : baseEnd_710551 < baseStart_710551 := by decide
  rcases family_descends (prefixWord ++ tailWord_710551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710554 : List Nat := [3, 1, 1, 4, 2, 1, 4, 2, 2]
def baseStart_710554 : Nat := 118140960795 + 710554 * 2 ^ 59
def prefixEnd_710554 : Nat := 4983230072969 + 3 ^ 40 * 710554 * 2
def baseEnd_710554 : Nat := 324316207088816167028647

theorem tailTrace_710554 : CollatzResearch.WordTrace tailWord_710554 prefixEnd_710554 324316207088816167028647 := by
  unfold tailWord_710554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479008366947921451726679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17277355645194457204604477 6479008366947921451726679)
  ·
    refine ⟨9718512550421882177590019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6479008366947921451726679 9718512550421882177590019)
    ·
      refine ⟨14577768825632823266385029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9718512550421882177590019 14577768825632823266385029)
      ·
        refine ⟨2733331654806154362447193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14577768825632823266385029 2733331654806154362447193)
        ·
          refine ⟨2049998741104615771835395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2733331654806154362447193 2049998741104615771835395)
          ·
            refine ⟨3074998111656923657753093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049998741104615771835395 3074998111656923657753093)
            ·
              refine ⟨576562145935673185828705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3074998111656923657753093 576562145935673185828705)
              ·
                refine ⟨432421609451754889371529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576562145935673185828705 432421609451754889371529)
                ·
                  refine ⟨324316207088816167028647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432421609451754889371529 324316207088816167028647)
                  ·
                    rfl

theorem cell20_710554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_710554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710554 prefixEnd_710554 := by exact prefixLift 710554
  have htrace : WordTrace (prefixWord ++ tailWord_710554) baseStart_710554 baseEnd_710554 := by
    simpa [prefixWord, tailWord_710554, baseEnd_710554] using wordTrace_append hprefix tailTrace_710554
  have hstable : (prefixWord ++ tailWord_710554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710554).length < 2 ^ (prefixWord ++ tailWord_710554).sum := by decide
  have hdescent : baseEnd_710554 < baseStart_710554 := by decide
  rcases family_descends (prefixWord ++ tailWord_710554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710561 : List Nat := [1, 2, 3, 4, 3, 1, 1, 5]
def baseStart_710561 : Nat := 118140960795 + 710561 * 2 ^ 59
def prefixEnd_710561 : Nat := 4983230072969 + 3 ^ 40 * 710561 * 2
def baseEnd_710561 : Nat := 108106467359851751265095

theorem tailTrace_710561 : CollatzResearch.WordTrace tailWord_710561 prefixEnd_710561 108106467359851751265095 := by
  unfold tailWord_710561
  simp only [CollatzResearch.WordTrace]
  refine ⟨25916288778766326002411537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17277525852510884001607691 25916288778766326002411537)
  ·
    refine ⟨19437216584074744501808653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25916288778766326002411537 19437216584074744501808653)
    ·
      refine ⟨7288956219028029188178245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19437216584074744501808653 7288956219028029188178245)
      ·
        refine ⟨1366679291067755472783421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7288956219028029188178245 1366679291067755472783421)
        ·
          refine ⟨512504734150408302293783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1366679291067755472783421 512504734150408302293783)
          ·
            refine ⟨768757101225612453440675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512504734150408302293783 768757101225612453440675)
            ·
              refine ⟨1153135651838418680161013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 768757101225612453440675 1153135651838418680161013)
              ·
                refine ⟨108106467359851751265095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1153135651838418680161013 108106467359851751265095)
                ·
                  rfl

theorem cell20_710561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 5].length) (baseStart_710561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710561 prefixEnd_710561 := by exact prefixLift 710561
  have htrace : WordTrace (prefixWord ++ tailWord_710561) baseStart_710561 baseEnd_710561 := by
    simpa [prefixWord, tailWord_710561, baseEnd_710561] using wordTrace_append hprefix tailTrace_710561
  have hstable : (prefixWord ++ tailWord_710561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710561).length < 2 ^ (prefixWord ++ tailWord_710561).sum := by decide
  have hdescent : baseEnd_710561 < baseStart_710561 := by decide
  rcases family_descends (prefixWord ++ tailWord_710561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710579 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 4]
def baseStart_710579 : Nat := 118140960795 + 710579 * 2 ^ 59
def prefixEnd_710579 : Nat := 4983230072969 + 3 ^ 40 * 710579 * 2
def baseEnd_710579 : Nat := 324327617770027191195211

theorem tailTrace_710579 : CollatzResearch.WordTrace tailWord_710579 prefixEnd_710579 324327617770027191195211 := by
  unfold tailWord_710579
  simp only [CollatzResearch.WordTrace]
  refine ⟨25916945292701115076566791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17277963528467410051044527 25916945292701115076566791)
  ·
    refine ⟨38875417939051672614850187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25916945292701115076566791 38875417939051672614850187)
    ·
      refine ⟨58313126908577508922275281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38875417939051672614850187 58313126908577508922275281)
      ·
        refine ⟨43734845181433131691706461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58313126908577508922275281 43734845181433131691706461)
        ·
          refine ⟨16400566943037424384389923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43734845181433131691706461 16400566943037424384389923)
          ·
            refine ⟨24600850414556136576584885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16400566943037424384389923 24600850414556136576584885)
            ·
              refine ⟨2306329726364637804054833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24600850414556136576584885 2306329726364637804054833)
              ·
                refine ⟨1729747294773478353041125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2306329726364637804054833 1729747294773478353041125)
                ·
                  refine ⟨324327617770027191195211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1729747294773478353041125 324327617770027191195211)
                  ·
                    rfl

theorem cell20_710579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 4].length) (baseStart_710579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710579 prefixEnd_710579 := by exact prefixLift 710579
  have htrace : WordTrace (prefixWord ++ tailWord_710579) baseStart_710579 baseEnd_710579 := by
    simpa [prefixWord, tailWord_710579, baseEnd_710579] using wordTrace_append hprefix tailTrace_710579
  have hstable : (prefixWord ++ tailWord_710579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710579).length < 2 ^ (prefixWord ++ tailWord_710579).sum := by decide
  have hdescent : baseEnd_710579 < baseStart_710579 := by decide
  rcases family_descends (prefixWord ++ tailWord_710579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710613 : List Nat := [1, 3, 2, 3, 2, 1, 2, 4, 2]
def baseStart_710613 : Nat := 118140960795 + 710613 * 2 ^ 59
def prefixEnd_710613 : Nat := 4983230072969 + 3 ^ 40 * 710613 * 2
def baseEnd_710613 : Nat := 324343136296474184061739

theorem tailTrace_710613 : CollatzResearch.WordTrace tailWord_710613 prefixEnd_710613 324343136296474184061739 := by
  unfold tailWord_710613
  simp only [CollatzResearch.WordTrace]
  refine ⟨25918185374577938883304493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17278790249718625922202995 25918185374577938883304493)
  ·
    refine ⟨9719319515466727081239185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25918185374577938883304493 9719319515466727081239185)
    ·
      refine ⟨7289489636600045310929389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9719319515466727081239185 7289489636600045310929389)
      ·
        refine ⟨2733558613725016991598521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7289489636600045310929389 2733558613725016991598521)
        ·
          refine ⟨2050168960293762743698891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2733558613725016991598521 2050168960293762743698891)
          ·
            refine ⟨3075253440440644115548337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2050168960293762743698891 3075253440440644115548337)
            ·
              refine ⟨2306440080330483086661253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3075253440440644115548337 2306440080330483086661253)
              ·
                refine ⟨432457515061965578748985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2306440080330483086661253 432457515061965578748985)
                ·
                  refine ⟨324343136296474184061739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432457515061965578748985 324343136296474184061739)
                  ·
                    rfl

theorem cell20_710613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_710613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710613 prefixEnd_710613 := by exact prefixLift 710613
  have htrace : WordTrace (prefixWord ++ tailWord_710613) baseStart_710613 baseEnd_710613 := by
    simpa [prefixWord, tailWord_710613, baseEnd_710613] using wordTrace_append hprefix tailTrace_710613
  have hstable : (prefixWord ++ tailWord_710613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710613).length < 2 ^ (prefixWord ++ tailWord_710613).sum := by decide
  have hdescent : baseEnd_710613 < baseStart_710613 := by decide
  rcases family_descends (prefixWord ++ tailWord_710613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710641 : List Nat := [1, 2, 2, 2, 5, 1, 1, 6]
def baseStart_710641 : Nat := 118140960795 + 710641 * 2 ^ 59
def prefixEnd_710641 : Nat := 4983230072969 + 3 ^ 40 * 710641 * 2
def baseEnd_710641 : Nat := 108118638753143510376097

theorem tailTrace_710641 : CollatzResearch.WordTrace tailWord_710641 prefixEnd_710641 108118638753143510376097 := by
  unfold tailWord_710641
  simp only [CollatzResearch.WordTrace]
  refine ⟨25919206618476499665323777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17279471078984333110215851 25919206618476499665323777)
  ·
    refine ⟨19439404963857374748992833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25919206618476499665323777 19439404963857374748992833)
    ·
      refine ⟨14579553722893031061744625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19439404963857374748992833 14579553722893031061744625)
      ·
        refine ⟨10934665292169773296308469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14579553722893031061744625 10934665292169773296308469)
        ·
          refine ⟨1025124871140916246528919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10934665292169773296308469 1025124871140916246528919)
          ·
            refine ⟨1537687306711374369793379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025124871140916246528919 1537687306711374369793379)
            ·
              refine ⟨2306530960067061554690069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537687306711374369793379 2306530960067061554690069)
              ·
                refine ⟨108118638753143510376097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2306530960067061554690069 108118638753143510376097)
                ·
                  rfl

theorem cell20_710641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 6].length) (baseStart_710641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710641 prefixEnd_710641 := by exact prefixLift 710641
  have htrace : WordTrace (prefixWord ++ tailWord_710641) baseStart_710641 baseEnd_710641 := by
    simpa [prefixWord, tailWord_710641, baseEnd_710641] using wordTrace_append hprefix tailTrace_710641
  have hstable : (prefixWord ++ tailWord_710641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710641).length < 2 ^ (prefixWord ++ tailWord_710641).sum := by decide
  have hdescent : baseEnd_710641 < baseStart_710641 := by decide
  rcases family_descends (prefixWord ++ tailWord_710641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710682 : List Nat := [3, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_710682 : Nat := 118140960795 + 710682 * 2 ^ 59
def prefixEnd_710682 : Nat := 4983230072969 + 3 ^ 40 * 710682 * 2
def baseEnd_710682 : Nat := 324374629776616610761457

theorem tailTrace_710682 : CollatzResearch.WordTrace tailWord_710682 prefixEnd_710682 324374629776616610761457 := by
  unfold tailWord_710682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6480175502831990916891575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17280468007551975778377533 6480175502831990916891575)
  ·
    refine ⟨9720263254247986375337363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6480175502831990916891575 9720263254247986375337363)
    ·
      refine ⟨14580394881371979563006045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9720263254247986375337363 14580394881371979563006045)
      ·
        refine ⟨5467648080514492336127267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14580394881371979563006045 5467648080514492336127267)
        ·
          refine ⟨8201472120771738504190901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5467648080514492336127267 8201472120771738504190901)
          ·
            refine ⟨768888011322350484767897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8201472120771738504190901 768888011322350484767897)
            ·
              refine ⟨576666008491762863575923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 768888011322350484767897 576666008491762863575923)
              ·
                refine ⟨864999012737644295363885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576666008491762863575923 864999012737644295363885)
                ·
                  refine ⟨324374629776616610761457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 864999012737644295363885 324374629776616610761457)
                  ·
                    rfl

theorem cell20_710682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_710682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710682 prefixEnd_710682 := by exact prefixLift 710682
  have htrace : WordTrace (prefixWord ++ tailWord_710682) baseStart_710682 baseEnd_710682 := by
    simpa [prefixWord, tailWord_710682, baseEnd_710682] using wordTrace_append hprefix tailTrace_710682
  have hstable : (prefixWord ++ tailWord_710682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710682).length < 2 ^ (prefixWord ++ tailWord_710682).sum := by decide
  have hdescent : baseEnd_710682 < baseStart_710682 := by decide
  rcases family_descends (prefixWord ++ tailWord_710682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710707 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_710707 : Nat := 118140960795 + 710707 * 2 ^ 59
def prefixEnd_710707 : Nat := 4983230072969 + 3 ^ 40 * 710707 * 2
def baseEnd_710707 : Nat := 324386040457827634928021

theorem tailTrace_710707 : CollatzResearch.WordTrace tailWord_710707 prefixEnd_710707 324386040457827634928021 := by
  unfold tailWord_710707
  simp only [CollatzResearch.WordTrace]
  refine ⟨25921613836237392937226375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17281075890824928624817583 25921613836237392937226375)
  ·
    refine ⟨38882420754356089405839563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25921613836237392937226375 38882420754356089405839563)
    ·
      refine ⟨58323631131534134108759345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38882420754356089405839563 58323631131534134108759345)
      ·
        refine ⟨43742723348650600581569509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58323631131534134108759345 43742723348650600581569509)
        ·
          refine ⟨8201760627871987609044283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43742723348650600581569509 8201760627871987609044283)
          ·
            refine ⟨12302640941807981413566425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8201760627871987609044283 12302640941807981413566425)
            ·
              refine ⟨9226980706355986060174819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12302640941807981413566425 9226980706355986060174819)
              ·
                refine ⟨13840471059533979090262229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9226980706355986060174819 13840471059533979090262229)
                ·
                  refine ⟨324386040457827634928021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13840471059533979090262229 324386040457827634928021)
                  ·
                    rfl

theorem cell20_710707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_710707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710707 prefixEnd_710707 := by exact prefixLift 710707
  have htrace : WordTrace (prefixWord ++ tailWord_710707) baseStart_710707 baseEnd_710707 := by
    simpa [prefixWord, tailWord_710707, baseEnd_710707] using wordTrace_append hprefix tailTrace_710707
  have hstable : (prefixWord ++ tailWord_710707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710707).length < 2 ^ (prefixWord ++ tailWord_710707).sum := by decide
  have hdescent : baseEnd_710707 < baseStart_710707 := by decide
  rcases family_descends (prefixWord ++ tailWord_710707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710748 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_710748 : Nat := 118140960795 + 710748 * 2 ^ 59
def prefixEnd_710748 : Nat := 4983230072969 + 3 ^ 40 * 710748 * 2
def baseEnd_710748 : Nat := 324404753975013714561187

theorem tailTrace_710748 : CollatzResearch.WordTrace tailWord_710748 prefixEnd_710748 324404753975013714561187 := by
  unfold tailWord_710748
  simp only [CollatzResearch.WordTrace]
  refine ⟨12961554614544428469734449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17282072819392571292979265 12961554614544428469734449)
  ·
    refine ⟨9721165960908321352300837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12961554614544428469734449 9721165960908321352300837)
    ·
      refine ⟨1822718617670310253556407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9721165960908321352300837 1822718617670310253556407)
      ·
        refine ⟨2734077926505465380334611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1822718617670310253556407 2734077926505465380334611)
        ·
          refine ⟨4101116889758198070501917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734077926505465380334611 4101116889758198070501917)
          ·
            refine ⟨1537918833659324276438219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4101116889758198070501917 1537918833659324276438219)
            ·
              refine ⟨2306878250488986414657329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537918833659324276438219 2306878250488986414657329)
              ·
                refine ⟨1730158687866739810992997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2306878250488986414657329 1730158687866739810992997)
                ·
                  refine ⟨324404753975013714561187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1730158687866739810992997 324404753975013714561187)
                  ·
                    rfl

theorem cell20_710748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_710748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710748 prefixEnd_710748 := by exact prefixLift 710748
  have htrace : WordTrace (prefixWord ++ tailWord_710748) baseStart_710748 baseEnd_710748 := by
    simpa [prefixWord, tailWord_710748, baseEnd_710748] using wordTrace_append hprefix tailTrace_710748
  have hstable : (prefixWord ++ tailWord_710748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710748).length < 2 ^ (prefixWord ++ tailWord_710748).sum := by decide
  have hdescent : baseEnd_710748 < baseStart_710748 := by decide
  rcases family_descends (prefixWord ++ tailWord_710748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710765 : List Nat := [1, 5, 1, 1, 2, 1, 4, 3, 2]
def baseStart_710765 : Nat := 118140960795 + 710765 * 2 ^ 59
def prefixEnd_710765 : Nat := 4983230072969 + 3 ^ 40 * 710765 * 2
def baseEnd_710765 : Nat := 324412513238237210994451

theorem tailTrace_710765 : CollatzResearch.WordTrace tailWord_710765 prefixEnd_710765 324412513238237210994451 := by
  unfold tailWord_710765
  simp only [CollatzResearch.WordTrace]
  refine ⟨25923729270027268842837749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17282486180018179228558499 25923729270027268842837749)
  ·
    refine ⟨2430349619065056454016039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25923729270027268842837749 2430349619065056454016039)
    ·
      refine ⟨3645524428597584681024059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2430349619065056454016039 3645524428597584681024059)
      ·
        refine ⟨5468286642896377021536089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3645524428597584681024059 5468286642896377021536089)
        ·
          refine ⟨4101214982172282766152067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5468286642896377021536089 4101214982172282766152067)
          ·
            refine ⟨6151822473258424149228101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101214982172282766152067 6151822473258424149228101)
            ·
              refine ⟨1153466713735954527980269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6151822473258424149228101 1153466713735954527980269)
              ·
                refine ⟨432550017650982947992601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1153466713735954527980269 432550017650982947992601)
                ·
                  refine ⟨324412513238237210994451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432550017650982947992601 324412513238237210994451)
                  ·
                    rfl

theorem cell20_710765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_710765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710765 prefixEnd_710765 := by exact prefixLift 710765
  have htrace : WordTrace (prefixWord ++ tailWord_710765) baseStart_710765 baseEnd_710765 := by
    simpa [prefixWord, tailWord_710765, baseEnd_710765] using wordTrace_append hprefix tailTrace_710765
  have hstable : (prefixWord ++ tailWord_710765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710765).length < 2 ^ (prefixWord ++ tailWord_710765).sum := by decide
  have hdescent : baseEnd_710765 < baseStart_710765 := by decide
  rcases family_descends (prefixWord ++ tailWord_710765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710820 : List Nat := [2, 3, 1, 2, 4, 2, 1, 3, 2]
def baseStart_710820 : Nat := 118140960795 + 710820 * 2 ^ 59
def prefixEnd_710820 : Nat := 4983230072969 + 3 ^ 40 * 710820 * 2
def baseEnd_710820 : Nat := 324437616736901464160893

theorem tailTrace_710820 : CollatzResearch.WordTrace tailWord_710820 prefixEnd_710820 324437616736901464160893 := by
  unfold tailWord_710820
  simp only [CollatzResearch.WordTrace]
  refine ⟨12962867642414006618044957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17283823523218675490726609 12962867642414006618044957)
  ·
    refine ⟨4861075365905252481766859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12962867642414006618044957 4861075365905252481766859)
    ·
      refine ⟨7291613048857878722650289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4861075365905252481766859 7291613048857878722650289)
      ·
        refine ⟨5468709786643409041987717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7291613048857878722650289 5468709786643409041987717)
        ·
          refine ⟨1025383084995639195372697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5468709786643409041987717 1025383084995639195372697)
          ·
            refine ⟨769037313746729396529523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1025383084995639195372697 769037313746729396529523)
            ·
              refine ⟨1153555970620094094794285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769037313746729396529523 1153555970620094094794285)
              ·
                refine ⟨432583488982535285547857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1153555970620094094794285 432583488982535285547857)
                ·
                  refine ⟨324437616736901464160893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432583488982535285547857 324437616736901464160893)
                  ·
                    rfl

theorem cell20_710820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_710820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710820 prefixEnd_710820 := by exact prefixLift 710820
  have htrace : WordTrace (prefixWord ++ tailWord_710820) baseStart_710820 baseEnd_710820 := by
    simpa [prefixWord, tailWord_710820, baseEnd_710820] using wordTrace_append hprefix tailTrace_710820
  have hstable : (prefixWord ++ tailWord_710820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710820).length < 2 ^ (prefixWord ++ tailWord_710820).sum := by decide
  have hdescent : baseEnd_710820 < baseStart_710820 := by decide
  rcases family_descends (prefixWord ++ tailWord_710820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710821 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_710821 : Nat := 118140960795 + 710821 * 2 ^ 59
def prefixEnd_710821 : Nat := 4983230072969 + 3 ^ 40 * 710821 * 2
def baseEnd_710821 : Nat := 324438073164149905127555

theorem tailTrace_710821 : CollatzResearch.WordTrace tailWord_710821 prefixEnd_710821 324438073164149905127555 := by
  unfold tailWord_710821
  simp only [CollatzResearch.WordTrace]
  refine ⟨25925771757824390406876317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17283847838549593604584211 25925771757824390406876317)
  ·
    refine ⟨9722164409184146402578619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25925771757824390406876317 9722164409184146402578619)
    ·
      refine ⟨14583246613776219603867929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9722164409184146402578619 14583246613776219603867929)
      ·
        refine ⟨10937434960332164702900947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14583246613776219603867929 10937434960332164702900947)
        ·
          refine ⟨16406152440498247054351421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10937434960332164702900947 16406152440498247054351421)
          ·
            refine ⟨6152307165186842645381783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16406152440498247054351421 6152307165186842645381783)
            ·
              refine ⟨9228460747780263968072675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6152307165186842645381783 9228460747780263968072675)
              ·
                refine ⟨13842691121670395952109013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9228460747780263968072675 13842691121670395952109013)
                ·
                  refine ⟨324438073164149905127555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13842691121670395952109013 324438073164149905127555)
                  ·
                    rfl

theorem cell20_710821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_710821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710821 prefixEnd_710821 := by exact prefixLift 710821
  have htrace : WordTrace (prefixWord ++ tailWord_710821) baseStart_710821 baseEnd_710821 := by
    simpa [prefixWord, tailWord_710821, baseEnd_710821] using wordTrace_append hprefix tailTrace_710821
  have hstable : (prefixWord ++ tailWord_710821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710821).length < 2 ^ (prefixWord ++ tailWord_710821).sum := by decide
  have hdescent : baseEnd_710821 < baseStart_710821 := by decide
  rcases family_descends (prefixWord ++ tailWord_710821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710837 : List Nat := [1, 3, 3, 4, 1, 1, 3, 2, 2]
def baseStart_710837 : Nat := 118140960795 + 710837 * 2 ^ 59
def prefixEnd_710837 : Nat := 4983230072969 + 3 ^ 40 * 710837 * 2
def baseEnd_710837 : Nat := 324445376000124960594157

theorem tailTrace_710837 : CollatzResearch.WordTrace tailWord_710837 prefixEnd_710837 324445376000124960594157 := by
  unfold tailWord_710837
  simp only [CollatzResearch.WordTrace]
  refine ⟨25926355325766425139458765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17284236883844283426305843 25926355325766425139458765)
  ·
    refine ⟨9722383247162409427297037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25926355325766425139458765 9722383247162409427297037)
    ·
      refine ⟨3645893717685903535236389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9722383247162409427297037 3645893717685903535236389)
      ·
        refine ⟨683605072066106912856823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3645893717685903535236389 683605072066106912856823)
        ·
          refine ⟨1025407608099160369285235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683605072066106912856823 1025407608099160369285235)
          ·
            refine ⟨1538111412148740553927853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025407608099160369285235 1538111412148740553927853)
            ·
              refine ⟨576791779555777707722945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1538111412148740553927853 576791779555777707722945)
              ·
                refine ⟨432593834666833280792209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576791779555777707722945 432593834666833280792209)
                ·
                  refine ⟨324445376000124960594157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432593834666833280792209 324445376000124960594157)
                  ·
                    rfl

theorem cell20_710837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 2].length) (baseStart_710837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710837 prefixEnd_710837 := by exact prefixLift 710837
  have htrace : WordTrace (prefixWord ++ tailWord_710837) baseStart_710837 baseEnd_710837 := by
    simpa [prefixWord, tailWord_710837, baseEnd_710837] using wordTrace_append hprefix tailTrace_710837
  have hstable : (prefixWord ++ tailWord_710837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710837).length < 2 ^ (prefixWord ++ tailWord_710837).sum := by decide
  have hdescent : baseEnd_710837 < baseStart_710837 := by decide
  rcases family_descends (prefixWord ++ tailWord_710837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710841 : List Nat := [1, 2, 1, 4, 1, 2, 5, 2, 2]
def baseStart_710841 : Nat := 118140960795 + 710841 * 2 ^ 59
def prefixEnd_710841 : Nat := 4983230072969 + 3 ^ 40 * 710841 * 2
def baseEnd_710841 : Nat := 324447201709118724460807

theorem tailTrace_710841 : CollatzResearch.WordTrace tailWord_710841 prefixEnd_710841 324447201709118724460807 := by
  unfold tailWord_710841
  simp only [CollatzResearch.WordTrace]
  refine ⟨25926501217751933822604377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17284334145167955881736251 25926501217751933822604377)
  ·
    refine ⟨19444875913313950366953283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25926501217751933822604377 19444875913313950366953283)
    ·
      refine ⟨29167313869970925550429925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19444875913313950366953283 29167313869970925550429925)
      ·
        refine ⟨5468871350619548540705611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29167313869970925550429925 5468871350619548540705611)
        ·
          refine ⟨8203307025929322811058417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5468871350619548540705611 8203307025929322811058417)
          ·
            refine ⟨6152480269446992108293813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8203307025929322811058417 6152480269446992108293813)
            ·
              refine ⟨576795025260655510152545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6152480269446992108293813 576795025260655510152545)
              ·
                refine ⟨432596268945491632614409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576795025260655510152545 432596268945491632614409)
                ·
                  refine ⟨324447201709118724460807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432596268945491632614409 324447201709118724460807)
                  ·
                    rfl

theorem cell20_710841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 2].length) (baseStart_710841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710841 prefixEnd_710841 := by exact prefixLift 710841
  have htrace : WordTrace (prefixWord ++ tailWord_710841) baseStart_710841 baseEnd_710841 := by
    simpa [prefixWord, tailWord_710841, baseEnd_710841] using wordTrace_append hprefix tailTrace_710841
  have hstable : (prefixWord ++ tailWord_710841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710841).length < 2 ^ (prefixWord ++ tailWord_710841).sum := by decide
  have hdescent : baseEnd_710841 < baseStart_710841 := by decide
  rcases family_descends (prefixWord ++ tailWord_710841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710897 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 5]
def baseStart_710897 : Nat := 118140960795 + 710897 * 2 ^ 59
def prefixEnd_710897 : Nat := 4983230072969 + 3 ^ 40 * 710897 * 2
def baseEnd_710897 : Nat := 324472761635031418593911

theorem tailTrace_710897 : CollatzResearch.WordTrace tailWord_710897 prefixEnd_710897 324472761635031418593911 := by
  unfold tailWord_710897
  simp only [CollatzResearch.WordTrace]
  refine ⟨25928543705549055386642945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17285695803699370257761963 25928543705549055386642945)
  ·
    refine ⟨19446407779161791539982209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25928543705549055386642945 19446407779161791539982209)
    ·
      refine ⟨14584805834371343654986657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19446407779161791539982209 14584805834371343654986657)
      ·
        refine ⟨10938604375778507741239993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14584805834371343654986657 10938604375778507741239993)
        ·
          refine ⟨8203953281833880805929995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10938604375778507741239993 8203953281833880805929995)
          ·
            refine ⟨12305929922750821208894993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8203953281833880805929995 12305929922750821208894993)
            ·
              refine ⟨9229447442063115906671245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12305929922750821208894993 9229447442063115906671245)
              ·
                refine ⟨3461042790773668465001717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9229447442063115906671245 3461042790773668465001717)
                ·
                  refine ⟨324472761635031418593911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3461042790773668465001717 324472761635031418593911)
                  ·
                    rfl

theorem cell20_710897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_710897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710897 prefixEnd_710897 := by exact prefixLift 710897
  have htrace : WordTrace (prefixWord ++ tailWord_710897) baseStart_710897 baseEnd_710897 := by
    simpa [prefixWord, tailWord_710897, baseEnd_710897] using wordTrace_append hprefix tailTrace_710897
  have hstable : (prefixWord ++ tailWord_710897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710897).length < 2 ^ (prefixWord ++ tailWord_710897).sum := by decide
  have hdescent : baseEnd_710897 < baseStart_710897 := by decide
  rcases family_descends (prefixWord ++ tailWord_710897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710904 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_710904 : Nat := 118140960795 + 710904 * 2 ^ 59
def prefixEnd_710904 : Nat := 4983230072969 + 3 ^ 40 * 710904 * 2
def baseEnd_710904 : Nat := 324475956625770505360549

theorem tailTrace_710904 : CollatzResearch.WordTrace tailWord_710904 prefixEnd_710904 324475956625770505360549 := by
  unfold tailWord_710904
  simp only [CollatzResearch.WordTrace]
  refine ⟨12964399508261847791073883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17285866011015797054765177 12964399508261847791073883)
  ·
    refine ⟨19446599262392771686610825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12964399508261847791073883 19446599262392771686610825)
    ·
      refine ⟨14584949446794578764958119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19446599262392771686610825 14584949446794578764958119)
      ·
        refine ⟨21877424170191868147437179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14584949446794578764958119 21877424170191868147437179)
        ·
          refine ⟨32816136255287802221155769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21877424170191868147437179 32816136255287802221155769)
          ·
            refine ⟨24612102191465851665866827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32816136255287802221155769 24612102191465851665866827)
            ·
              refine ⟨36918153287198777498800241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24612102191465851665866827 36918153287198777498800241)
              ·
                refine ⟨27688614965399083124100181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36918153287198777498800241 27688614965399083124100181)
                ·
                  refine ⟨324475956625770505360549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27688614965399083124100181 324475956625770505360549)
                  ·
                    rfl

theorem cell20_710904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_710904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710904 prefixEnd_710904 := by exact prefixLift 710904
  have htrace : WordTrace (prefixWord ++ tailWord_710904) baseStart_710904 baseEnd_710904 := by
    simpa [prefixWord, tailWord_710904, baseEnd_710904] using wordTrace_append hprefix tailTrace_710904
  have hstable : (prefixWord ++ tailWord_710904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710904).length < 2 ^ (prefixWord ++ tailWord_710904).sum := by decide
  have hdescent : baseEnd_710904 < baseStart_710904 := by decide
  rcases family_descends (prefixWord ++ tailWord_710904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710921 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 4]
def baseStart_710921 : Nat := 118140960795 + 710921 * 2 ^ 59
def prefixEnd_710921 : Nat := 4983230072969 + 3 ^ 40 * 710921 * 2
def baseEnd_710921 : Nat := 324483715888994001793813

theorem tailTrace_710921 : CollatzResearch.WordTrace tailWord_710921 prefixEnd_710921 324483715888994001793813 := by
  unfold tailWord_710921
  simp only [CollatzResearch.WordTrace]
  refine ⟨25929419057462107485516617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17286279371641404990344411 25929419057462107485516617)
  ·
    refine ⟨19447064293096580614137463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25929419057462107485516617 19447064293096580614137463)
    ·
      refine ⟨29170596439644870921206195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19447064293096580614137463 29170596439644870921206195)
      ·
        refine ⟨43755894659467306381809293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29170596439644870921206195 43755894659467306381809293)
        ·
          refine ⟨16408460497300239893178485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43755894659467306381809293 16408460497300239893178485)
          ·
            refine ⟨1538293171621897489985483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16408460497300239893178485 1538293171621897489985483)
            ·
              refine ⟨2307439757432846234978225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538293171621897489985483 2307439757432846234978225)
              ·
                refine ⟨1730579818074634676233669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2307439757432846234978225 1730579818074634676233669)
                ·
                  refine ⟨324483715888994001793813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1730579818074634676233669 324483715888994001793813)
                  ·
                    rfl

theorem cell20_710921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_710921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710921 prefixEnd_710921 := by exact prefixLift 710921
  have htrace : WordTrace (prefixWord ++ tailWord_710921) baseStart_710921 baseEnd_710921 := by
    simpa [prefixWord, tailWord_710921, baseEnd_710921] using wordTrace_append hprefix tailTrace_710921
  have hstable : (prefixWord ++ tailWord_710921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710921).length < 2 ^ (prefixWord ++ tailWord_710921).sum := by decide
  have hdescent : baseEnd_710921 < baseStart_710921 := by decide
  rcases family_descends (prefixWord ++ tailWord_710921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710993 : List Nat := [1, 2, 2, 1, 4, 4, 1, 3, 2]
def baseStart_710993 : Nat := 118140960795 + 710993 * 2 ^ 59
def prefixEnd_710993 : Nat := 4983230072969 + 3 ^ 40 * 710993 * 2
def baseEnd_710993 : Nat := 324516578650881751393519

theorem tailTrace_710993 : CollatzResearch.WordTrace tailWord_710993 prefixEnd_710993 324516578650881751393519 := by
  unfold tailWord_710993
  simp only [CollatzResearch.WordTrace]
  refine ⟨25932045113201263782137633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17288030075467509188091755 25932045113201263782137633)
  ·
    refine ⟨19449033834900947836603225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25932045113201263782137633 19449033834900947836603225)
    ·
      refine ⟨14586775376175710877452419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19449033834900947836603225 14586775376175710877452419)
      ·
        refine ⟨21880163064263566316178629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14586775376175710877452419 21880163064263566316178629)
        ·
          refine ⟨4102530574549418684283493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21880163064263566316178629 4102530574549418684283493)
          ·
            refine ⟨769224482728016003303155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4102530574549418684283493 769224482728016003303155)
            ·
              refine ⟨1153836724092024004954733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769224482728016003303155 1153836724092024004954733)
              ·
                refine ⟨432688771534509001858025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1153836724092024004954733 432688771534509001858025)
                ·
                  refine ⟨324516578650881751393519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432688771534509001858025 324516578650881751393519)
                  ·
                    rfl

theorem cell20_710993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 2].length) (baseStart_710993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_710993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_710993 prefixEnd_710993 := by exact prefixLift 710993
  have htrace : WordTrace (prefixWord ++ tailWord_710993) baseStart_710993 baseEnd_710993 := by
    simpa [prefixWord, tailWord_710993, baseEnd_710993] using wordTrace_append hprefix tailTrace_710993
  have hstable : (prefixWord ++ tailWord_710993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710993).length < 2 ^ (prefixWord ++ tailWord_710993).sum := by decide
  have hdescent : baseEnd_710993 < baseStart_710993 := by decide
  rcases family_descends (prefixWord ++ tailWord_710993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711006 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_711006 : Nat := 118140960795 + 711006 * 2 ^ 59
def prefixEnd_711006 : Nat := 4983230072969 + 3 ^ 40 * 711006 * 2
def baseEnd_711006 : Nat := 324522512205111483960133

theorem tailTrace_711006 : CollatzResearch.WordTrace tailWord_711006 prefixEnd_711006 324522512205111483960133 := by
  unfold tailWord_711006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3241564907769270875295109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17288346174769444668240581 3241564907769270875295109)
  ·
    refine ⟨607793420206738289117833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3241564907769270875295109 607793420206738289117833)
    ·
      refine ⟨455845065155053716838375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 607793420206738289117833 455845065155053716838375)
      ·
        refine ⟨683767597732580575257563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455845065155053716838375 683767597732580575257563)
        ·
          refine ⟨1025651396598870862886345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683767597732580575257563 1025651396598870862886345)
          ·
            refine ⟨769238547449153147164759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1025651396598870862886345 769238547449153147164759)
            ·
              refine ⟨1153857821173729720747139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769238547449153147164759 1153857821173729720747139)
              ·
                refine ⟨1730786731760594581120709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153857821173729720747139 1730786731760594581120709)
                ·
                  refine ⟨324522512205111483960133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1730786731760594581120709 324522512205111483960133)
                  ·
                    rfl

theorem cell20_711006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_711006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711006 prefixEnd_711006 := by exact prefixLift 711006
  have htrace : WordTrace (prefixWord ++ tailWord_711006) baseStart_711006 baseEnd_711006 := by
    simpa [prefixWord, tailWord_711006, baseEnd_711006] using wordTrace_append hprefix tailTrace_711006
  have hstable : (prefixWord ++ tailWord_711006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711006).length < 2 ^ (prefixWord ++ tailWord_711006).sum := by decide
  have hdescent : baseEnd_711006 < baseStart_711006 := by decide
  rcases family_descends (prefixWord ++ tailWord_711006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711010 : List Nat := [3, 3, 2, 1, 1, 3, 3, 2, 2]
def baseStart_711010 : Nat := 118140960795 + 711010 * 2 ^ 59
def prefixEnd_711010 : Nat := 4983230072969 + 3 ^ 40 * 711010 * 2
def baseEnd_711010 : Nat := 324524337914105247826783

theorem tailTrace_711010 : CollatzResearch.WordTrace tailWord_711010 prefixEnd_711010 324524337914105247826783 := by
  unfold tailWord_711010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6483166288534918921376621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17288443436093117123670989 6483166288534918921376621)
  ·
    refine ⟨2431187358200594595516233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6483166288534918921376621 2431187358200594595516233)
    ·
      refine ⟨1823390518650445946637175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2431187358200594595516233 1823390518650445946637175)
      ·
        refine ⟨2735085777975668919955763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1823390518650445946637175 2735085777975668919955763)
        ·
          refine ⟨4102628666963503379933645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2735085777975668919955763 4102628666963503379933645)
          ·
            refine ⟨1538485750111313767475117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4102628666963503379933645 1538485750111313767475117)
            ·
              refine ⟨576932156291742662803169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1538485750111313767475117 576932156291742662803169)
              ·
                refine ⟨432699117218806997102377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576932156291742662803169 432699117218806997102377)
                ·
                  refine ⟨324524337914105247826783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432699117218806997102377 324524337914105247826783)
                  ·
                    rfl

theorem cell20_711010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_711010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711010 prefixEnd_711010 := by exact prefixLift 711010
  have htrace : WordTrace (prefixWord ++ tailWord_711010) baseStart_711010 baseEnd_711010 := by
    simpa [prefixWord, tailWord_711010, baseEnd_711010] using wordTrace_append hprefix tailTrace_711010
  have hstable : (prefixWord ++ tailWord_711010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711010).length < 2 ^ (prefixWord ++ tailWord_711010).sum := by decide
  have hdescent : baseEnd_711010 < baseStart_711010 := by decide
  rcases family_descends (prefixWord ++ tailWord_711010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711011 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_711011 : Nat := 118140960795 + 711011 * 2 ^ 59
def prefixEnd_711011 : Nat := 4983230072969 + 3 ^ 40 * 711011 * 2
def baseEnd_711011 : Nat := 324524794341353688793445

theorem tailTrace_711011 : CollatzResearch.WordTrace tailWord_711011 prefixEnd_711011 324524794341353688793445 := by
  unfold tailWord_711011
  simp only [CollatzResearch.WordTrace]
  refine ⟨25932701627136052856292887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17288467751424035237528591 25932701627136052856292887)
  ·
    refine ⟨38899052440704079284439331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25932701627136052856292887 38899052440704079284439331)
    ·
      refine ⟨58348578661056118926658997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38899052440704079284439331 58348578661056118926658997)
      ·
        refine ⟨5470179249474011149374281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58348578661056118926658997 5470179249474011149374281)
        ·
          refine ⟨4102634437105508362030711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5470179249474011149374281 4102634437105508362030711)
          ·
            refine ⟨6153951655658262543046067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4102634437105508362030711 6153951655658262543046067)
            ·
              refine ⟨9230927483487393814569101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6153951655658262543046067 9230927483487393814569101)
              ·
                refine ⟨3461597806307772680463413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9230927483487393814569101 3461597806307772680463413)
                ·
                  refine ⟨324524794341353688793445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3461597806307772680463413 324524794341353688793445)
                  ·
                    rfl

theorem cell20_711011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_711011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711011 prefixEnd_711011 := by exact prefixLift 711011
  have htrace : WordTrace (prefixWord ++ tailWord_711011) baseStart_711011 baseEnd_711011 := by
    simpa [prefixWord, tailWord_711011, baseEnd_711011] using wordTrace_append hprefix tailTrace_711011
  have hstable : (prefixWord ++ tailWord_711011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711011).length < 2 ^ (prefixWord ++ tailWord_711011).sum := by decide
  have hdescent : baseEnd_711011 < baseStart_711011 := by decide
  rcases family_descends (prefixWord ++ tailWord_711011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711066 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_711066 : Nat := 118140960795 + 711066 * 2 ^ 59
def prefixEnd_711066 : Nat := 4983230072969 + 3 ^ 40 * 711066 * 2
def baseEnd_711066 : Nat := 324549897840017941959887

theorem tailTrace_711066 : CollatzResearch.WordTrace tailWord_711066 prefixEnd_711066 324549897840017941959887 := by
  unfold tailWord_711066
  simp only [CollatzResearch.WordTrace]
  refine ⟨6483676910484199312386263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17289805094624531499696701 6483676910484199312386263)
  ·
    refine ⟨9725515365726298968579395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6483676910484199312386263 9725515365726298968579395)
    ·
      refine ⟨14588273048589448452869093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9725515365726298968579395 14588273048589448452869093)
      ·
        refine ⟨2735301196610521584912955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14588273048589448452869093 2735301196610521584912955)
        ·
          refine ⟨4102951794915782377369433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2735301196610521584912955 4102951794915782377369433)
          ·
            refine ⟨3077213846186836783027075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4102951794915782377369433 3077213846186836783027075)
            ·
              refine ⟨4615820769280255174540613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3077213846186836783027075 4615820769280255174540613)
              ·
                refine ⟨865466394240047845226365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4615820769280255174540613 865466394240047845226365)
                ·
                  refine ⟨324549897840017941959887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865466394240047845226365 324549897840017941959887)
                  ·
                    rfl

theorem cell20_711066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_711066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711066 prefixEnd_711066 := by exact prefixLift 711066
  have htrace : WordTrace (prefixWord ++ tailWord_711066) baseStart_711066 baseEnd_711066 := by
    simpa [prefixWord, tailWord_711066, baseEnd_711066] using wordTrace_append hprefix tailTrace_711066
  have hstable : (prefixWord ++ tailWord_711066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711066).length < 2 ^ (prefixWord ++ tailWord_711066).sum := by decide
  have hdescent : baseEnd_711066 < baseStart_711066 := by decide
  rcases family_descends (prefixWord ++ tailWord_711066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711069 : List Nat := [1, 4, 2, 1, 4, 1, 1, 4, 2]
def baseStart_711069 : Nat := 118140960795 + 711069 * 2 ^ 59
def prefixEnd_711069 : Nat := 4983230072969 + 3 ^ 40 * 711069 * 2
def baseEnd_711069 : Nat := 324551267121763264859875

theorem tailTrace_711069 : CollatzResearch.WordTrace tailWord_711069 prefixEnd_711069 324551267121763264859875 := by
  unfold tailWord_711069
  simp only [CollatzResearch.WordTrace]
  refine ⟨25934817060925928761904261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17289878040617285841269507 25934817060925928761904261)
  ·
    refine ⟨4862778198923611642857049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25934817060925928761904261 4862778198923611642857049)
    ·
      refine ⟨3647083649192708732142787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4862778198923611642857049 3647083649192708732142787)
      ·
        refine ⟨5470625473789063098214181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3647083649192708732142787 5470625473789063098214181)
        ·
          refine ⟨1025742276335449330915159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5470625473789063098214181 1025742276335449330915159)
          ·
            refine ⟨1538613414503173996372739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025742276335449330915159 1538613414503173996372739)
            ·
              refine ⟨2307920121754760994559109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538613414503173996372739 2307920121754760994559109)
              ·
                refine ⟨432735022829017686479833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2307920121754760994559109 432735022829017686479833)
                ·
                  refine ⟨324551267121763264859875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432735022829017686479833 324551267121763264859875)
                  ·
                    rfl

theorem cell20_711069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_711069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711069 prefixEnd_711069 := by exact prefixLift 711069
  have htrace : WordTrace (prefixWord ++ tailWord_711069) baseStart_711069 baseEnd_711069 := by
    simpa [prefixWord, tailWord_711069, baseEnd_711069] using wordTrace_append hprefix tailTrace_711069
  have hstable : (prefixWord ++ tailWord_711069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711069).length < 2 ^ (prefixWord ++ tailWord_711069).sum := by decide
  have hdescent : baseEnd_711069 < baseStart_711069 := by decide
  rcases family_descends (prefixWord ++ tailWord_711069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711097 : List Nat := [1, 2, 1, 4, 3, 2, 3, 4]
def baseStart_711097 : Nat := 118140960795 + 711097 * 2 ^ 59
def prefixEnd_711097 : Nat := 4983230072969 + 3 ^ 40 * 711097 * 2
def baseEnd_711097 : Nat := 108188015694906537308809

theorem tailTrace_711097 : CollatzResearch.WordTrace tailWord_711097 prefixEnd_711097 108188015694906537308809 := by
  unfold tailWord_711097
  simp only [CollatzResearch.WordTrace]
  refine ⟨25935838304824489543923545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17290558869882993029282363 25935838304824489543923545)
  ·
    refine ⟨19451878728618367157942659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25935838304824489543923545 19451878728618367157942659)
    ·
      refine ⟨29177818092927550736913989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19451878728618367157942659 29177818092927550736913989)
      ·
        refine ⟨5470840892423915763171373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29177818092927550736913989 5470840892423915763171373)
        ·
          refine ⟨2051565334658968411189265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5470840892423915763171373 2051565334658968411189265)
          ·
            refine ⟨1538674000994226308391949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2051565334658968411189265 1538674000994226308391949)
            ·
              refine ⟨577002750372834865646981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1538674000994226308391949 577002750372834865646981)
              ·
                refine ⟨108188015694906537308809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 577002750372834865646981 108188015694906537308809)
                ·
                  rfl

theorem cell20_711097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 4].length) (baseStart_711097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711097 prefixEnd_711097 := by exact prefixLift 711097
  have htrace : WordTrace (prefixWord ++ tailWord_711097) baseStart_711097 baseEnd_711097 := by
    simpa [prefixWord, tailWord_711097, baseEnd_711097] using wordTrace_append hprefix tailTrace_711097
  have hstable : (prefixWord ++ tailWord_711097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711097).length < 2 ^ (prefixWord ++ tailWord_711097).sum := by decide
  have hdescent : baseEnd_711097 < baseStart_711097 := by decide
  rcases family_descends (prefixWord ++ tailWord_711097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711197 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 3]
def baseStart_711197 : Nat := 118140960795 + 711197 * 2 ^ 59
def prefixEnd_711197 : Nat := 4983230072969 + 3 ^ 40 * 711197 * 2
def baseEnd_711197 : Nat := 324609689809563708592685

theorem tailTrace_711197 : CollatzResearch.WordTrace tailWord_711197 prefixEnd_711197 324609689809563708592685 := by
  unfold tailWord_711197
  simp only [CollatzResearch.WordTrace]
  refine ⟨25939485604462206622563845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17292990402974804415042563 25939485604462206622563845)
  ·
    refine ⟨4863653550836663741730721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25939485604462206622563845 4863653550836663741730721)
    ·
      refine ⟨3647740163127497806298041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4863653550836663741730721 3647740163127497806298041)
      ·
        refine ⟨2735805122345623354723531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3647740163127497806298041 2735805122345623354723531)
        ·
          refine ⟨4103707683518435032085297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2735805122345623354723531 4103707683518435032085297)
          ·
            refine ⟨3077780762638826274063973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4103707683518435032085297 3077780762638826274063973)
            ·
              refine ⟨577083892994779926386995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3077780762638826274063973 577083892994779926386995)
              ·
                refine ⟨865625839492169889580493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577083892994779926386995 865625839492169889580493)
                ·
                  refine ⟨324609689809563708592685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865625839492169889580493 324609689809563708592685)
                  ·
                    rfl

theorem cell20_711197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_711197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711197 prefixEnd_711197 := by exact prefixLift 711197
  have htrace : WordTrace (prefixWord ++ tailWord_711197) baseStart_711197 baseEnd_711197 := by
    simpa [prefixWord, tailWord_711197, baseEnd_711197] using wordTrace_append hprefix tailTrace_711197
  have hstable : (prefixWord ++ tailWord_711197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711197).length < 2 ^ (prefixWord ++ tailWord_711197).sum := by decide
  have hdescent : baseEnd_711197 < baseStart_711197 := by decide
  rcases family_descends (prefixWord ++ tailWord_711197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711238 : List Nat := [6, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_711238 : Nat := 118140960795 + 711238 * 2 ^ 59
def prefixEnd_711238 : Nat := 4983230072969 + 3 ^ 40 * 711238 * 2
def baseEnd_711238 : Nat := 324628403326749788225851

theorem tailTrace_711238 : CollatzResearch.WordTrace tailWord_711238 prefixEnd_711238 324628403326749788225851 := by
  unfold tailWord_711238
  simp only [CollatzResearch.WordTrace]
  refine ⟨810655656166052207025199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17293987331542447083204245 810655656166052207025199)
  ·
    refine ⟨1215983484249078310537799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810655656166052207025199 1215983484249078310537799)
    ·
      refine ⟨1823975226373617465806699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1215983484249078310537799 1823975226373617465806699)
      ·
        refine ⟨2735962839560426198710049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1823975226373617465806699 2735962839560426198710049)
        ·
          refine ⟨2051972129670319649032537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2735962839560426198710049 2051972129670319649032537)
          ·
            refine ⟨1538979097252739736774403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2051972129670319649032537 1538979097252739736774403)
            ·
              refine ⟨2308468645879109605161605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538979097252739736774403 2308468645879109605161605)
              ·
                refine ⟨432837871102333050967801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2308468645879109605161605 432837871102333050967801)
                ·
                  refine ⟨324628403326749788225851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432837871102333050967801 324628403326749788225851)
                  ·
                    rfl

theorem cell20_711238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_711238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711238 prefixEnd_711238 := by exact prefixLift 711238
  have htrace : WordTrace (prefixWord ++ tailWord_711238) baseStart_711238 baseEnd_711238 := by
    simpa [prefixWord, tailWord_711238, baseEnd_711238] using wordTrace_append hprefix tailTrace_711238
  have hstable : (prefixWord ++ tailWord_711238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711238).length < 2 ^ (prefixWord ++ tailWord_711238).sum := by decide
  have hdescent : baseEnd_711238 < baseStart_711238 := by decide
  rcases family_descends (prefixWord ++ tailWord_711238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711242 : List Nat := [3, 1, 2, 1, 1, 5, 1, 4, 2]
def baseStart_711242 : Nat := 118140960795 + 711242 * 2 ^ 59
def prefixEnd_711242 : Nat := 4983230072969 + 3 ^ 40 * 711242 * 2
def baseEnd_711242 : Nat := 324630229035743552092501

theorem tailTrace_711242 : CollatzResearch.WordTrace tailWord_711242 prefixEnd_711242 324630229035743552092501 := by
  unfold tailWord_711242
  simp only [CollatzResearch.WordTrace]
  refine ⟨6485281722324794826987995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17294084592866119538634653 6485281722324794826987995)
  ·
    refine ⟨9727922583487192240481993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6485281722324794826987995 9727922583487192240481993)
    ·
      refine ⟨7295941937615394180361495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9727922583487192240481993 7295941937615394180361495)
      ·
        refine ⟨10943912906423091270542243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7295941937615394180361495 10943912906423091270542243)
        ·
          refine ⟨16415869359634636905813365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10943912906423091270542243 16415869359634636905813365)
          ·
            refine ⟨1538987752465747209920003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16415869359634636905813365 1538987752465747209920003)
            ·
              refine ⟨2308481628698620814880005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538987752465747209920003 2308481628698620814880005)
              ·
                refine ⟨432840305380991402790001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2308481628698620814880005 432840305380991402790001)
                ·
                  refine ⟨324630229035743552092501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432840305380991402790001 324630229035743552092501)
                  ·
                    rfl

theorem cell20_711242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_711242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711242 prefixEnd_711242 := by exact prefixLift 711242
  have htrace : WordTrace (prefixWord ++ tailWord_711242) baseStart_711242 baseEnd_711242 := by
    simpa [prefixWord, tailWord_711242, baseEnd_711242] using wordTrace_append hprefix tailTrace_711242
  have hstable : (prefixWord ++ tailWord_711242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711242).length < 2 ^ (prefixWord ++ tailWord_711242).sum := by decide
  have hdescent : baseEnd_711242 < baseStart_711242 := by decide
  rcases family_descends (prefixWord ++ tailWord_711242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711262 : List Nat := [4, 4, 1, 2, 1, 1, 3, 4]
def baseStart_711262 : Nat := 118140960795 + 711262 * 2 ^ 59
def prefixEnd_711262 : Nat := 4983230072969 + 3 ^ 40 * 711262 * 2
def baseEnd_711262 : Nat := 108213119193570790475251

theorem tailTrace_711262 : CollatzResearch.WordTrace tailWord_711262 prefixEnd_711262 108213119193570790475251 := by
  unfold tailWord_711262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242732043653340340460005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17294570899484481815786693 3242732043653340340460005)
  ·
    refine ⟨608012258185001313836251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3242732043653340340460005 608012258185001313836251)
    ·
      refine ⟨912018387277501970754377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 608012258185001313836251 912018387277501970754377)
      ·
        refine ⟨684013790458126478065783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912018387277501970754377 684013790458126478065783)
        ·
          refine ⟨1026020685687189717098675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684013790458126478065783 1026020685687189717098675)
          ·
            refine ⟨1539031028530784575648013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026020685687189717098675 1539031028530784575648013)
            ·
              refine ⟨577136635699044215868005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1539031028530784575648013 577136635699044215868005)
              ·
                refine ⟨108213119193570790475251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 577136635699044215868005 108213119193570790475251)
                ·
                  rfl

theorem cell20_711262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_711262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711262 prefixEnd_711262 := by exact prefixLift 711262
  have htrace : WordTrace (prefixWord ++ tailWord_711262) baseStart_711262 baseEnd_711262 := by
    simpa [prefixWord, tailWord_711262, baseEnd_711262] using wordTrace_append hprefix tailTrace_711262
  have hstable : (prefixWord ++ tailWord_711262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711262).length < 2 ^ (prefixWord ++ tailWord_711262).sum := by decide
  have hdescent : baseEnd_711262 < baseStart_711262 := by decide
  rcases family_descends (prefixWord ++ tailWord_711262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711301 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 4]
def baseStart_711301 : Nat := 118140960795 + 711301 * 2 ^ 59
def prefixEnd_711301 : Nat := 4983230072969 + 3 ^ 40 * 711301 * 2
def baseEnd_711301 : Nat := 324657158243401569125593

theorem tailTrace_711301 : CollatzResearch.WordTrace tailWord_711301 prefixEnd_711301 324657158243401569125593 := by
  unfold tailWord_711301
  simp only [CollatzResearch.WordTrace]
  refine ⟨25943278796085432384349757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17295519197390288256233171 25943278796085432384349757)
  ·
    refine ⟨9728729548532037144131159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25943278796085432384349757 9728729548532037144131159)
    ·
      refine ⟨14593094322798055716196739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9728729548532037144131159 14593094322798055716196739)
      ·
        refine ⟨21889641484197083574295109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14593094322798055716196739 21889641484197083574295109)
        ·
          refine ⟨4104307778286953170180333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21889641484197083574295109 4104307778286953170180333)
          ·
            refine ⟨1539115416857607438817625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4104307778286953170180333 1539115416857607438817625)
            ·
              refine ⟨1154336562643205579113219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539115416857607438817625 1154336562643205579113219)
              ·
                refine ⟨1731504843964808368669829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154336562643205579113219 1731504843964808368669829)
                ·
                  refine ⟨324657158243401569125593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1731504843964808368669829 324657158243401569125593)
                  ·
                    rfl

theorem cell20_711301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_711301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711301 prefixEnd_711301 := by exact prefixLift 711301
  have htrace : WordTrace (prefixWord ++ tailWord_711301) baseStart_711301 baseEnd_711301 := by
    simpa [prefixWord, tailWord_711301, baseEnd_711301] using wordTrace_append hprefix tailTrace_711301
  have hstable : (prefixWord ++ tailWord_711301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711301).length < 2 ^ (prefixWord ++ tailWord_711301).sum := by decide
  have hdescent : baseEnd_711301 < baseStart_711301 := by decide
  rcases family_descends (prefixWord ++ tailWord_711301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711353 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 3]
def baseStart_711353 : Nat := 118140960795 + 711353 * 2 ^ 59
def prefixEnd_711353 : Nat := 4983230072969 + 3 ^ 40 * 711353 * 2
def baseEnd_711353 : Nat := 324680892460320499392047

theorem tailTrace_711353 : CollatzResearch.WordTrace tailWord_711353 prefixEnd_711353 324680892460320499392047 := by
  unfold tailWord_711353
  simp only [CollatzResearch.WordTrace]
  refine ⟨25945175391897045265242713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17296783594598030176828475 25945175391897045265242713)
  ·
    refine ⟨19458881543922783948932035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25945175391897045265242713 19458881543922783948932035)
    ·
      refine ⟨29188322315884175923398053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19458881543922783948932035 29188322315884175923398053)
      ·
        refine ⟨5472810434228282985637135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29188322315884175923398053 5472810434228282985637135)
        ·
          refine ⟨8209215651342424478455703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5472810434228282985637135 8209215651342424478455703)
          ·
            refine ⟨12313823477013636717683555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8209215651342424478455703 12313823477013636717683555)
            ·
              refine ⟨18470735215520455076525333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12313823477013636717683555 18470735215520455076525333)
              ·
                refine ⟨865815713227521331712125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18470735215520455076525333 865815713227521331712125)
                ·
                  refine ⟨324680892460320499392047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865815713227521331712125 324680892460320499392047)
                  ·
                    rfl

theorem cell20_711353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_711353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711353 prefixEnd_711353 := by exact prefixLift 711353
  have htrace : WordTrace (prefixWord ++ tailWord_711353) baseStart_711353 baseEnd_711353 := by
    simpa [prefixWord, tailWord_711353, baseEnd_711353] using wordTrace_append hprefix tailTrace_711353
  have hstable : (prefixWord ++ tailWord_711353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711353).length < 2 ^ (prefixWord ++ tailWord_711353).sum := by decide
  have hdescent : baseEnd_711353 < baseStart_711353 := by decide
  rcases family_descends (prefixWord ++ tailWord_711353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711370 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_711370 : Nat := 118140960795 + 711370 * 2 ^ 59
def prefixEnd_711370 : Nat := 4983230072969 + 3 ^ 40 * 711370 * 2
def baseEnd_711370 : Nat := 324688651723543995825311

theorem tailTrace_711370 : CollatzResearch.WordTrace tailWord_711370 prefixEnd_711370 324688651723543995825311 := by
  unfold tailWord_711370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6486448858208864292152891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17297196955223638112407709 6486448858208864292152891)
  ·
    refine ⟨9729673287313296438229337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6486448858208864292152891 9729673287313296438229337)
    ·
      refine ⟨7297254965484972328672003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9729673287313296438229337 7297254965484972328672003)
      ·
        refine ⟨10945882448227458493008005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7297254965484972328672003 10945882448227458493008005)
        ·
          refine ⟨2052352959042648467439001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10945882448227458493008005 2052352959042648467439001)
          ·
            refine ⟨1539264719281986350579251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2052352959042648467439001 1539264719281986350579251)
            ·
              refine ⟨2308897078922979525868877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539264719281986350579251 2308897078922979525868877)
              ·
                refine ⟨865836404596117322200829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2308897078922979525868877 865836404596117322200829)
                ·
                  refine ⟨324688651723543995825311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 865836404596117322200829 324688651723543995825311)
                  ·
                    rfl

theorem cell20_711370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_711370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711370 prefixEnd_711370 := by exact prefixLift 711370
  have htrace : WordTrace (prefixWord ++ tailWord_711370) baseStart_711370 baseEnd_711370 := by
    simpa [prefixWord, tailWord_711370, baseEnd_711370] using wordTrace_append hprefix tailTrace_711370
  have hstable : (prefixWord ++ tailWord_711370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711370).length < 2 ^ (prefixWord ++ tailWord_711370).sum := by decide
  have hdescent : baseEnd_711370 < baseStart_711370 := by decide
  rcases family_descends (prefixWord ++ tailWord_711370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711460 : List Nat := [2, 3, 1, 3, 3, 1, 7]
def baseStart_711460 : Nat := 118140960795 + 711460 * 2 ^ 59
def prefixEnd_711460 : Nat := 4983230072969 + 3 ^ 40 * 711460 * 2
def baseEnd_711460 : Nat := 36081081130655964758327

theorem tailTrace_711460 : CollatzResearch.WordTrace tailWord_711460 prefixEnd_711460 36081081130655964758327 := by
  unfold tailWord_711460
  simp only [CollatzResearch.WordTrace]
  refine ⟨12974539001254701269693917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17299385335006268359591889 12974539001254701269693917)
  ·
    refine ⟨4865452125470512976135219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12974539001254701269693917 4865452125470512976135219)
    ·
      refine ⟨7298178188205769464202829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4865452125470512976135219 7298178188205769464202829)
      ·
        refine ⟨2736816820577163549076061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7298178188205769464202829 2736816820577163549076061)
        ·
          refine ⟨1026306307716436330903523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2736816820577163549076061 1026306307716436330903523)
          ·
            refine ⟨1539459461574654496355285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026306307716436330903523 1539459461574654496355285)
            ·
              refine ⟨36081081130655964758327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1539459461574654496355285 36081081130655964758327)
              ·
                rfl

theorem cell20_711460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 7].length) (baseStart_711460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711460 prefixEnd_711460 := by exact prefixLift 711460
  have htrace : WordTrace (prefixWord ++ tailWord_711460) baseStart_711460 baseEnd_711460 := by
    simpa [prefixWord, tailWord_711460, baseEnd_711460] using wordTrace_append hprefix tailTrace_711460
  have hstable : (prefixWord ++ tailWord_711460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711460).length < 2 ^ (prefixWord ++ tailWord_711460).sum := by decide
  have hdescent : baseEnd_711460 < baseStart_711460 := by decide
  rcases family_descends (prefixWord ++ tailWord_711460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711470 : List Nat := [4, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_711470 : Nat := 118140960795 + 711470 * 2 ^ 59
def prefixEnd_711470 : Nat := 4983230072969 + 3 ^ 40 * 711470 * 2
def baseEnd_711470 : Nat := 324734294448388092491569

theorem tailTrace_711470 : CollatzResearch.WordTrace tailWord_711470 prefixEnd_711470 324734294448388092491569 := by
  unfold tailWord_711470
  simp only [CollatzResearch.WordTrace]
  refine ⟨3243680341559146780906483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17299628488315449498167909 3243680341559146780906483)
  ·
    refine ⟨4865520512338720171359725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3243680341559146780906483 4865520512338720171359725)
    ·
      refine ⟨1824570192127020064259897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4865520512338720171359725 1824570192127020064259897)
      ·
        refine ⟨1368427644095265048194923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1824570192127020064259897 1368427644095265048194923)
        ·
          refine ⟨2052641466142897572292385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1368427644095265048194923 2052641466142897572292385)
          ·
            refine ⟨1539481099607173179219289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2052641466142897572292385 1539481099607173179219289)
            ·
              refine ⟨1154610824705379884414467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539481099607173179219289 1154610824705379884414467)
              ·
                refine ⟨1731916237058069826621701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154610824705379884414467 1731916237058069826621701)
                ·
                  refine ⟨324734294448388092491569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1731916237058069826621701 324734294448388092491569)
                  ·
                    rfl

theorem cell20_711470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_711470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711470 prefixEnd_711470 := by exact prefixLift 711470
  have htrace : WordTrace (prefixWord ++ tailWord_711470) baseStart_711470 baseEnd_711470 := by
    simpa [prefixWord, tailWord_711470, baseEnd_711470] using wordTrace_append hprefix tailTrace_711470
  have hstable : (prefixWord ++ tailWord_711470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711470).length < 2 ^ (prefixWord ++ tailWord_711470).sum := by decide
  have hdescent : baseEnd_711470 < baseStart_711470 := by decide
  rcases family_descends (prefixWord ++ tailWord_711470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711494 : List Nat := [6, 1, 1, 2, 2, 1, 1, 6]
def baseStart_711494 : Nat := 118140960795 + 711494 * 2 ^ 59
def prefixEnd_711494 : Nat := 4983230072969 + 3 ^ 40 * 711494 * 2
def baseEnd_711494 : Nat := 108248416234116891897157

theorem tailTrace_711494 : CollatzResearch.WordTrace tailWord_711494 prefixEnd_711494 108248416234116891897157 := by
  unfold tailWord_711494
  simp only [CollatzResearch.WordTrace]
  refine ⟨810947440137069573316423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17300212056257484230750357 810947440137069573316423)
  ·
    refine ⟨1216421160205604359974635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810947440137069573316423 1216421160205604359974635)
    ·
      refine ⟨1824631740308406539961953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216421160205604359974635 1824631740308406539961953)
      ·
        refine ⟨1368473805231304904971465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1824631740308406539961953 1368473805231304904971465)
        ·
          refine ⟨1026355353923478678728599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1368473805231304904971465 1026355353923478678728599)
          ·
            refine ⟨1539533030885218018092899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026355353923478678728599 1539533030885218018092899)
            ·
              refine ⟨2309299546327827027139349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539533030885218018092899 2309299546327827027139349)
              ·
                refine ⟨108248416234116891897157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2309299546327827027139349 108248416234116891897157)
                ·
                  rfl

theorem cell20_711494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_711494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711494 prefixEnd_711494 := by exact prefixLift 711494
  have htrace : WordTrace (prefixWord ++ tailWord_711494) baseStart_711494 baseEnd_711494 := by
    simpa [prefixWord, tailWord_711494, baseEnd_711494] using wordTrace_append hprefix tailTrace_711494
  have hstable : (prefixWord ++ tailWord_711494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711494).length < 2 ^ (prefixWord ++ tailWord_711494).sum := by decide
  have hdescent : baseEnd_711494 < baseStart_711494 := by decide
  rcases family_descends (prefixWord ++ tailWord_711494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711557 : List Nat := [1, 3, 1, 1, 3, 3, 2, 6]
def baseStart_711557 : Nat := 118140960795 + 711557 * 2 ^ 59
def prefixEnd_711557 : Nat := 4983230072969 + 3 ^ 40 * 711557 * 2
def baseEnd_711557 : Nat := 108258001206334152197071

theorem tailTrace_711557 : CollatzResearch.WordTrace tailWord_711557 prefixEnd_711557 108258001206334152197071 := by
  unfold tailWord_711557
  simp only [CollatzResearch.WordTrace]
  refine ⟨25952615883157988105668925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17301743922105325403779283 25952615883157988105668925)
  ·
    refine ⟨9732230956184245539625847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25952615883157988105668925 9732230956184245539625847)
    ·
      refine ⟨14598346434276368309438771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9732230956184245539625847 14598346434276368309438771)
      ·
        refine ⟨21897519651414552464158157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14598346434276368309438771 21897519651414552464158157)
        ·
          refine ⟨8211569869280457174059309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21897519651414552464158157 8211569869280457174059309)
          ·
            refine ⟨3079338700980171440272241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8211569869280457174059309 3079338700980171440272241)
            ·
              refine ⟨2309504025735128580204181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3079338700980171440272241 2309504025735128580204181)
              ·
                refine ⟨108258001206334152197071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2309504025735128580204181 108258001206334152197071)
                ·
                  rfl

theorem cell20_711557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_711557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711557 prefixEnd_711557 := by exact prefixLift 711557
  have htrace : WordTrace (prefixWord ++ tailWord_711557) baseStart_711557 baseEnd_711557 := by
    simpa [prefixWord, tailWord_711557, baseEnd_711557] using wordTrace_append hprefix tailTrace_711557
  have hstable : (prefixWord ++ tailWord_711557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711557).length < 2 ^ (prefixWord ++ tailWord_711557).sum := by decide
  have hdescent : baseEnd_711557 < baseStart_711557 := by decide
  rcases family_descends (prefixWord ++ tailWord_711557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711564 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_711564 : Nat := 118140960795 + 711564 * 2 ^ 59
def prefixEnd_711564 : Nat := 4983230072969 + 3 ^ 40 * 711564 * 2
def baseEnd_711564 : Nat := 324777198609741543357851

theorem tailTrace_711564 : CollatzResearch.WordTrace tailWord_711564 prefixEnd_711564 324777198609741543357851 := by
  unfold tailWord_711564
  simp only [CollatzResearch.WordTrace]
  refine ⟨12976435597066314150586873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17301914129421752200782497 12976435597066314150586873)
  ·
    refine ⟨9732326697799735612940155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12976435597066314150586873 9732326697799735612940155)
    ·
      refine ⟨14598490046699603419410233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9732326697799735612940155 14598490046699603419410233)
      ·
        refine ⟨10948867535024702564557675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14598490046699603419410233 10948867535024702564557675)
        ·
          refine ⟨16423301302537053846836513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10948867535024702564557675 16423301302537053846836513)
          ·
            refine ⟨12317475976902790385127385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16423301302537053846836513 12317475976902790385127385)
            ·
              refine ⟨9238106982677092788845539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12317475976902790385127385 9238106982677092788845539)
              ·
                refine ⟨13857160474015639183268309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9238106982677092788845539 13857160474015639183268309)
                ·
                  refine ⟨324777198609741543357851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13857160474015639183268309 324777198609741543357851)
                  ·
                    rfl

theorem cell20_711564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_711564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711564 prefixEnd_711564 := by exact prefixLift 711564
  have htrace : WordTrace (prefixWord ++ tailWord_711564) baseStart_711564 baseEnd_711564 := by
    simpa [prefixWord, tailWord_711564, baseEnd_711564] using wordTrace_append hprefix tailTrace_711564
  have hstable : (prefixWord ++ tailWord_711564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711564).length < 2 ^ (prefixWord ++ tailWord_711564).sum := by decide
  have hdescent : baseEnd_711564 < baseStart_711564 := by decide
  rcases family_descends (prefixWord ++ tailWord_711564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711571 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_711571 : Nat := 118140960795 + 711571 * 2 ^ 59
def prefixEnd_711571 : Nat := 4983230072969 + 3 ^ 40 * 711571 * 2
def baseEnd_711571 : Nat := 324780393600480630124489

theorem tailTrace_711571 : CollatzResearch.WordTrace tailWord_711571 prefixEnd_711571 324780393600480630124489 := by
  unfold tailWord_711571
  simp only [CollatzResearch.WordTrace]
  refine ⟨25953126505107268496678567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17302084336738178997785711 25953126505107268496678567)
  ·
    refine ⟨38929689757660902745017851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25953126505107268496678567 38929689757660902745017851)
    ·
      refine ⟨58394534636491354117526777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38929689757660902745017851 58394534636491354117526777)
      ·
        refine ⟨43795900977368515588145083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58394534636491354117526777 43795900977368515588145083)
        ·
          refine ⟨65693851466052773382217625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43795900977368515588145083 65693851466052773382217625)
          ·
            refine ⟨49270388599539580036663219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65693851466052773382217625 49270388599539580036663219)
            ·
              refine ⟨73905582899309370054994829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49270388599539580036663219 73905582899309370054994829)
              ·
                refine ⟨27714593587241013770623061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73905582899309370054994829 27714593587241013770623061)
                ·
                  refine ⟨324780393600480630124489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27714593587241013770623061 324780393600480630124489)
                  ·
                    rfl

theorem cell20_711571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_711571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711571 prefixEnd_711571 := by exact prefixLift 711571
  have htrace : WordTrace (prefixWord ++ tailWord_711571) baseStart_711571 baseEnd_711571 := by
    simpa [prefixWord, tailWord_711571, baseEnd_711571] using wordTrace_append hprefix tailTrace_711571
  have hstable : (prefixWord ++ tailWord_711571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711571).length < 2 ^ (prefixWord ++ tailWord_711571).sum := by decide
  have hdescent : baseEnd_711571 < baseStart_711571 := by decide
  rcases family_descends (prefixWord ++ tailWord_711571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711580 : List Nat := [2, 2, 3, 3, 2, 2, 2, 2, 2]
def baseStart_711580 : Nat := 118140960795 + 711580 * 2 ^ 59
def prefixEnd_711580 : Nat := 4983230072969 + 3 ^ 40 * 711580 * 2
def baseEnd_711580 : Nat := 324784501445716598824453

theorem tailTrace_711580 : CollatzResearch.WordTrace tailWord_711580 prefixEnd_711580 324784501445716598824453 := by
  unfold tailWord_711580
  simp only [CollatzResearch.WordTrace]
  refine ⟨12976727381037331516878097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17302303174716442022504129 12976727381037331516878097)
  ·
    refine ⟨9732545535777998637658573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12976727381037331516878097 9732545535777998637658573)
    ·
      refine ⟨3649704575916749489121965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9732545535777998637658573 3649704575916749489121965)
      ·
        refine ⟨1368639215968781058420737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3649704575916749489121965 1368639215968781058420737)
        ·
          refine ⟨1026479411976585793815553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1368639215968781058420737 1026479411976585793815553)
          ·
            refine ⟨769859558982439345361665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1026479411976585793815553 769859558982439345361665)
            ·
              refine ⟨577394669236829509021249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769859558982439345361665 577394669236829509021249)
              ·
                refine ⟨433046001927622131765937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577394669236829509021249 433046001927622131765937)
                ·
                  refine ⟨324784501445716598824453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433046001927622131765937 324784501445716598824453)
                  ·
                    rfl

theorem cell20_711580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_711580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711580 prefixEnd_711580 := by exact prefixLift 711580
  have htrace : WordTrace (prefixWord ++ tailWord_711580) baseStart_711580 baseEnd_711580 := by
    simpa [prefixWord, tailWord_711580, baseEnd_711580] using wordTrace_append hprefix tailTrace_711580
  have hstable : (prefixWord ++ tailWord_711580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711580).length < 2 ^ (prefixWord ++ tailWord_711580).sum := by decide
  have hdescent : baseEnd_711580 < baseStart_711580 := by decide
  rcases family_descends (prefixWord ++ tailWord_711580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711584 : List Nat := [2, 1, 1, 4, 1, 1, 6, 2, 2]
def baseStart_711584 : Nat := 118140960795 + 711584 * 2 ^ 59
def prefixEnd_711584 : Nat := 4983230072969 + 3 ^ 40 * 711584 * 2
def baseEnd_711584 : Nat := 324786327154710362691103

theorem tailTrace_711584 : CollatzResearch.WordTrace tailWord_711584 prefixEnd_711584 324786327154710362691103 := by
  unfold tailWord_711584
  simp only [CollatzResearch.WordTrace]
  refine ⟨12976800327030085858450903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17302400436040114477934537 12976800327030085858450903)
  ·
    refine ⟨19465200490545128787676355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12976800327030085858450903 19465200490545128787676355)
    ·
      refine ⟨29197800735817693181514533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19465200490545128787676355 29197800735817693181514533)
      ·
        refine ⟨5474587637965817471533975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29197800735817693181514533 5474587637965817471533975)
        ·
          refine ⟨8211881456948726207300963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5474587637965817471533975 8211881456948726207300963)
          ·
            refine ⟨12317822185423089310951445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8211881456948726207300963 12317822185423089310951445)
            ·
              refine ⟨577397914941707311450849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12317822185423089310951445 577397914941707311450849)
              ·
                refine ⟨433048436206280483588137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577397914941707311450849 433048436206280483588137)
                ·
                  refine ⟨324786327154710362691103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433048436206280483588137 324786327154710362691103)
                  ·
                    rfl

theorem cell20_711584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 2].length) (baseStart_711584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711584 prefixEnd_711584 := by exact prefixLift 711584
  have htrace : WordTrace (prefixWord ++ tailWord_711584) baseStart_711584 baseEnd_711584 := by
    simpa [prefixWord, tailWord_711584, baseEnd_711584] using wordTrace_append hprefix tailTrace_711584
  have hstable : (prefixWord ++ tailWord_711584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711584).length < 2 ^ (prefixWord ++ tailWord_711584).sum := by decide
  have hdescent : baseEnd_711584 < baseStart_711584 := by decide
  rcases family_descends (prefixWord ++ tailWord_711584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711588 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_711588 : Nat := 118140960795 + 711588 * 2 ^ 59
def prefixEnd_711588 : Nat := 4983230072969 + 3 ^ 40 * 711588 * 2
def baseEnd_711588 : Nat := 324788152863704126557753

theorem tailTrace_711588 : CollatzResearch.WordTrace tailWord_711588 prefixEnd_711588 324788152863704126557753 := by
  unfold tailWord_711588
  simp only [CollatzResearch.WordTrace]
  refine ⟨12976873273022840200023709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17302497697363786933364945 12976873273022840200023709)
  ·
    refine ⟨4866327477383565075008891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12976873273022840200023709 4866327477383565075008891)
    ·
      refine ⟨7299491216075347612513337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4866327477383565075008891 7299491216075347612513337)
      ·
        refine ⟨5474618412056510709385003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7299491216075347612513337 5474618412056510709385003)
        ·
          refine ⟨8211927618084766064077505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5474618412056510709385003 8211927618084766064077505)
          ·
            refine ⟨6158945713563574548058129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8211927618084766064077505 6158945713563574548058129)
            ·
              refine ⟨4619209285172680911043597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6158945713563574548058129 4619209285172680911043597)
              ·
                refine ⟨1732203481939755341641349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4619209285172680911043597 1732203481939755341641349)
                ·
                  refine ⟨324788152863704126557753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732203481939755341641349 324788152863704126557753)
                  ·
                    rfl

theorem cell20_711588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_711588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711588 prefixEnd_711588 := by exact prefixLift 711588
  have htrace : WordTrace (prefixWord ++ tailWord_711588) baseStart_711588 baseEnd_711588 := by
    simpa [prefixWord, tailWord_711588, baseEnd_711588] using wordTrace_append hprefix tailTrace_711588
  have hstable : (prefixWord ++ tailWord_711588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711588).length < 2 ^ (prefixWord ++ tailWord_711588).sum := by decide
  have hdescent : baseEnd_711588 < baseStart_711588 := by decide
  rcases family_descends (prefixWord ++ tailWord_711588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711591 : List Nat := [1, 1, 6, 1, 3, 2, 1, 5]
def baseStart_711591 : Nat := 118140960795 + 711591 * 2 ^ 59
def prefixEnd_711591 : Nat := 4983230072969 + 3 ^ 40 * 711591 * 2
def baseEnd_711591 : Nat := 108263174048483149819247

theorem tailTrace_711591 : CollatzResearch.WordTrace tailWord_711591 prefixEnd_711591 108263174048483149819247 := by
  unfold tailWord_711591
  simp only [CollatzResearch.WordTrace]
  refine ⟨25953855965034811912406627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17302570643356541274937751 25953855965034811912406627)
  ·
    refine ⟨38930783947552217868609941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25953855965034811912406627 38930783947552217868609941)
    ·
      refine ⟨1824880497541510212591091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38930783947552217868609941 1824880497541510212591091)
      ·
        refine ⟨2737320746312265318886637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824880497541510212591091 2737320746312265318886637)
        ·
          refine ⟨1026495279867099494582489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2737320746312265318886637 1026495279867099494582489)
          ·
            refine ⟨769871459900324620936867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1026495279867099494582489 769871459900324620936867)
            ·
              refine ⟨1154807189850486931405301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769871459900324620936867 1154807189850486931405301)
              ·
                refine ⟨108263174048483149819247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1154807189850486931405301 108263174048483149819247)
                ·
                  rfl

theorem cell20_711591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 5].length) (baseStart_711591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711591 prefixEnd_711591 := by exact prefixLift 711591
  have htrace : WordTrace (prefixWord ++ tailWord_711591) baseStart_711591 baseEnd_711591 := by
    simpa [prefixWord, tailWord_711591, baseEnd_711591] using wordTrace_append hprefix tailTrace_711591
  have hstable : (prefixWord ++ tailWord_711591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711591).length < 2 ^ (prefixWord ++ tailWord_711591).sum := by decide
  have hdescent : baseEnd_711591 < baseStart_711591 := by decide
  rcases family_descends (prefixWord ++ tailWord_711591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711602 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_711602 : Nat := 118140960795 + 711602 * 2 ^ 59
def prefixEnd_711602 : Nat := 4983230072969 + 3 ^ 40 * 711602 * 2
def baseEnd_711602 : Nat := 324794542845182300091029

theorem tailTrace_711602 : CollatzResearch.WordTrace tailWord_711602 prefixEnd_711602 324794542845182300091029 := by
  unfold tailWord_711602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6488564291998740197764265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17302838111996640527371373 6488564291998740197764265)
  ·
    refine ⟨4866423218999055148323199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6488564291998740197764265 4866423218999055148323199)
    ·
      refine ⟨7299634828498582722484799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4866423218999055148323199 7299634828498582722484799)
      ·
        refine ⟨10949452242747874083727199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7299634828498582722484799 10949452242747874083727199)
        ·
          refine ⟨16424178364121811125590799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10949452242747874083727199 16424178364121811125590799)
          ·
            refine ⟨24636267546182716688386199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16424178364121811125590799 24636267546182716688386199)
            ·
              refine ⟨36954401319274075032579299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24636267546182716688386199 36954401319274075032579299)
              ·
                refine ⟨55431601978911112548868949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36954401319274075032579299 55431601978911112548868949)
                ·
                  refine ⟨324794542845182300091029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55431601978911112548868949 324794542845182300091029)
                  ·
                    rfl

theorem cell20_711602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_711602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711602 prefixEnd_711602 := by exact prefixLift 711602
  have htrace : WordTrace (prefixWord ++ tailWord_711602) baseStart_711602 baseEnd_711602 := by
    simpa [prefixWord, tailWord_711602, baseEnd_711602] using wordTrace_append hprefix tailTrace_711602
  have hstable : (prefixWord ++ tailWord_711602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711602).length < 2 ^ (prefixWord ++ tailWord_711602).sum := by decide
  have hdescent : baseEnd_711602 < baseStart_711602 := by decide
  rcases family_descends (prefixWord ++ tailWord_711602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711636 : List Nat := [2, 4, 1, 2, 1, 2, 3, 2, 3]
def baseStart_711636 : Nat := 118140960795 + 711636 * 2 ^ 59
def prefixEnd_711636 : Nat := 4983230072969 + 3 ^ 40 * 711636 * 2
def baseEnd_711636 : Nat := 324810061371629292957557

theorem tailTrace_711636 : CollatzResearch.WordTrace tailWord_711636 prefixEnd_711636 324810061371629292957557 := by
  unfold tailWord_711636
  simp only [CollatzResearch.WordTrace]
  refine ⟨12977748624935892298897381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17303664833247856398529841 12977748624935892298897381)
  ·
    refine ⟨2433327867175479806043259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12977748624935892298897381 2433327867175479806043259)
    ·
      refine ⟨3649991800763219709064889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2433327867175479806043259 3649991800763219709064889)
      ·
        refine ⟨2737493850572414781798667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3649991800763219709064889 2737493850572414781798667)
        ·
          refine ⟨4106240775858622172698001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737493850572414781798667 4106240775858622172698001)
          ·
            refine ⟨3079680581893966629523501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4106240775858622172698001 3079680581893966629523501)
            ·
              refine ⟨1154880218210237486071313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3079680581893966629523501 1154880218210237486071313)
              ·
                refine ⟨866160163657678114553485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154880218210237486071313 866160163657678114553485)
                ·
                  refine ⟨324810061371629292957557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 866160163657678114553485 324810061371629292957557)
                  ·
                    rfl

theorem cell20_711636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_711636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711636 prefixEnd_711636 := by exact prefixLift 711636
  have htrace : WordTrace (prefixWord ++ tailWord_711636) baseStart_711636 baseEnd_711636 := by
    simpa [prefixWord, tailWord_711636, baseEnd_711636] using wordTrace_append hprefix tailTrace_711636
  have hstable : (prefixWord ++ tailWord_711636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711636).length < 2 ^ (prefixWord ++ tailWord_711636).sum := by decide
  have hdescent : baseEnd_711636 < baseStart_711636 := by decide
  rcases family_descends (prefixWord ++ tailWord_711636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711708 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 3]
def baseStart_711708 : Nat := 118140960795 + 711708 * 2 ^ 59
def prefixEnd_711708 : Nat := 4983230072969 + 3 ^ 40 * 711708 * 2
def baseEnd_711708 : Nat := 324842924133517042557263

theorem tailTrace_711708 : CollatzResearch.WordTrace tailWord_711708 prefixEnd_711708 324842924133517042557263 := by
  unfold tailWord_711708
  simp only [CollatzResearch.WordTrace]
  refine ⟨12979061652805470447207889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17305415537073960596277185 12979061652805470447207889)
  ·
    refine ⟨9734296239604102835405917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12979061652805470447207889 9734296239604102835405917)
    ·
      refine ⟨3650361089851538563277219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9734296239604102835405917 3650361089851538563277219)
      ·
        refine ⟨5475541634777307844915829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3650361089851538563277219 5475541634777307844915829)
        ·
          refine ⟨513332028260372610460859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5475541634777307844915829 513332028260372610460859)
          ·
            refine ⟨769998042390558915691289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513332028260372610460859 769998042390558915691289)
            ·
              refine ⟨577498531792919186768467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769998042390558915691289 577498531792919186768467)
              ·
                refine ⟨866247797689378780152701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577498531792919186768467 866247797689378780152701)
                ·
                  refine ⟨324842924133517042557263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 866247797689378780152701 324842924133517042557263)
                  ·
                    rfl

theorem cell20_711708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_711708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711708 prefixEnd_711708 := by exact prefixLift 711708
  have htrace : WordTrace (prefixWord ++ tailWord_711708) baseStart_711708 baseEnd_711708 := by
    simpa [prefixWord, tailWord_711708, baseEnd_711708] using wordTrace_append hprefix tailTrace_711708
  have hstable : (prefixWord ++ tailWord_711708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711708).length < 2 ^ (prefixWord ++ tailWord_711708).sum := by decide
  have hdescent : baseEnd_711708 < baseStart_711708 := by decide
  rcases family_descends (prefixWord ++ tailWord_711708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711723 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_711723 : Nat := 118140960795 + 711723 * 2 ^ 59
def prefixEnd_711723 : Nat := 4983230072969 + 3 ^ 40 * 711723 * 2
def baseEnd_711723 : Nat := 324849770542243657057201

theorem tailTrace_711723 : CollatzResearch.WordTrace tailWord_711723 prefixEnd_711723 324849770542243657057201 := by
  unfold tailWord_711723
  simp only [CollatzResearch.WordTrace]
  refine ⟨25958670400556598456211823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17305780267037732304141215 25958670400556598456211823)
  ·
    refine ⟨38938005600834897684317735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25958670400556598456211823 38938005600834897684317735)
    ·
      refine ⟨58407008401252346526476603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38938005600834897684317735 58407008401252346526476603)
      ·
        refine ⟨87610512601878519789714905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58407008401252346526476603 87610512601878519789714905)
        ·
          refine ⟨65707884451408889842286179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87610512601878519789714905 65707884451408889842286179)
          ·
            refine ⟨98561826677113334763429269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65707884451408889842286179 98561826677113334763429269)
            ·
              refine ⟨4620085625489687567035747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98561826677113334763429269 4620085625489687567035747)
              ·
                refine ⟨6930128438234531350553621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620085625489687567035747 6930128438234531350553621)
                ·
                  refine ⟨324849770542243657057201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6930128438234531350553621 324849770542243657057201)
                  ·
                    rfl

theorem cell20_711723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_711723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711723 prefixEnd_711723 := by exact prefixLift 711723
  have htrace : WordTrace (prefixWord ++ tailWord_711723) baseStart_711723 baseEnd_711723 := by
    simpa [prefixWord, tailWord_711723, baseEnd_711723] using wordTrace_append hprefix tailTrace_711723
  have hstable : (prefixWord ++ tailWord_711723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711723).length < 2 ^ (prefixWord ++ tailWord_711723).sum := by decide
  have hdescent : baseEnd_711723 < baseStart_711723 := by decide
  rcases family_descends (prefixWord ++ tailWord_711723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711754 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_711754 : Nat := 118140960795 + 711754 * 2 ^ 59
def prefixEnd_711754 : Nat := 4983230072969 + 3 ^ 40 * 711754 * 2
def baseEnd_711754 : Nat := 324863919786945327023741

theorem tailTrace_711754 : CollatzResearch.WordTrace tailWord_711754 prefixEnd_711754 324863919786945327023741 := by
  unfold tailWord_711754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6489950265861072687647579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17306534042296193833726877 6489950265861072687647579)
  ·
    refine ⟨9734925398791609031471369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6489950265861072687647579 9734925398791609031471369)
    ·
      refine ⟨7301194049093706773603527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9734925398791609031471369 7301194049093706773603527)
      ·
        refine ⟨10951791073640560160405291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7301194049093706773603527 10951791073640560160405291)
        ·
          refine ⟨16427686610460840240607937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10951791073640560160405291 16427686610460840240607937)
          ·
            refine ⟨12320764957845630180455953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16427686610460840240607937 12320764957845630180455953)
            ·
              refine ⟨9240573718384222635341965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12320764957845630180455953 9240573718384222635341965)
              ·
                refine ⟨3465215144394083488253237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9240573718384222635341965 3465215144394083488253237)
                ·
                  refine ⟨324863919786945327023741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3465215144394083488253237 324863919786945327023741)
                  ·
                    rfl

theorem cell20_711754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_711754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711754 prefixEnd_711754 := by exact prefixLift 711754
  have htrace : WordTrace (prefixWord ++ tailWord_711754) baseStart_711754 baseEnd_711754 := by
    simpa [prefixWord, tailWord_711754, baseEnd_711754] using wordTrace_append hprefix tailTrace_711754
  have hstable : (prefixWord ++ tailWord_711754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711754).length < 2 ^ (prefixWord ++ tailWord_711754).sum := by decide
  have hdescent : baseEnd_711754 < baseStart_711754 := by decide
  rcases family_descends (prefixWord ++ tailWord_711754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711774 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_711774 : Nat := 118140960795 + 711774 * 2 ^ 59
def prefixEnd_711774 : Nat := 4983230072969 + 3 ^ 40 * 711774 * 2
def baseEnd_711774 : Nat := 324873048331914146356993

theorem tailTrace_711774 : CollatzResearch.WordTrace tailWord_711774 prefixEnd_711774 324873048331914146356993 := by
  unfold tailWord_711774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245066315421479270789797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17307020348914556110878917 3245066315421479270789797)
  ·
    refine ⟨608449934141527363273087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3245066315421479270789797 608449934141527363273087)
    ·
      refine ⟨912674901212291044909631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 608449934141527363273087 912674901212291044909631)
      ·
        refine ⟨1369012351818436567364447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 912674901212291044909631 1369012351818436567364447)
        ·
          refine ⟨2053518527727654851046671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369012351818436567364447 2053518527727654851046671)
          ·
            refine ⟨3080277791591482276570007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053518527727654851046671 3080277791591482276570007)
            ·
              refine ⟨4620416687387223414855011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3080277791591482276570007 4620416687387223414855011)
              ·
                refine ⟨6930625031080835122282517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620416687387223414855011 6930625031080835122282517)
                ·
                  refine ⟨324873048331914146356993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6930625031080835122282517 324873048331914146356993)
                  ·
                    rfl

theorem cell20_711774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_711774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711774 prefixEnd_711774 := by exact prefixLift 711774
  have htrace : WordTrace (prefixWord ++ tailWord_711774) baseStart_711774 baseEnd_711774 := by
    simpa [prefixWord, tailWord_711774, baseEnd_711774] using wordTrace_append hprefix tailTrace_711774
  have hstable : (prefixWord ++ tailWord_711774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711774).length < 2 ^ (prefixWord ++ tailWord_711774).sum := by decide
  have hdescent : baseEnd_711774 < baseStart_711774 := by decide
  rcases family_descends (prefixWord ++ tailWord_711774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711792 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_711792 : Nat := 118140960795 + 711792 * 2 ^ 59
def prefixEnd_711792 : Nat := 4983230072969 + 3 ^ 40 * 711792 * 2
def baseEnd_711792 : Nat := 324881264022386083756919

theorem tailTrace_711792 : CollatzResearch.WordTrace tailWord_711792 prefixEnd_711792 324881264022386083756919 := by
  unfold tailWord_711792
  simp only [CollatzResearch.WordTrace]
  refine ⟨12980593518653311620236815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17307458024871082160315753 12980593518653311620236815)
  ·
    refine ⟨19470890277979967430355223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12980593518653311620236815 19470890277979967430355223)
    ·
      refine ⟨29206335416969951145532835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19470890277979967430355223 29206335416969951145532835)
      ·
        refine ⟨43809503125454926718299253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29206335416969951145532835 43809503125454926718299253)
        ·
          refine ⟨4107140918011399379840555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43809503125454926718299253 4107140918011399379840555)
          ·
            refine ⟨6160711377017099069760833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4107140918011399379840555 6160711377017099069760833)
            ·
              refine ⟨4620533532762824302320625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6160711377017099069760833 4620533532762824302320625)
              ·
                refine ⟨3465400149572118226740469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4620533532762824302320625 3465400149572118226740469)
                ·
                  refine ⟨324881264022386083756919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3465400149572118226740469 324881264022386083756919)
                  ·
                    rfl

theorem cell20_711792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_711792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711792 prefixEnd_711792 := by exact prefixLift 711792
  have htrace : WordTrace (prefixWord ++ tailWord_711792) baseStart_711792 baseEnd_711792 := by
    simpa [prefixWord, tailWord_711792, baseEnd_711792] using wordTrace_append hprefix tailTrace_711792
  have hstable : (prefixWord ++ tailWord_711792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711792).length < 2 ^ (prefixWord ++ tailWord_711792).sum := by decide
  have hdescent : baseEnd_711792 < baseStart_711792 := by decide
  rcases family_descends (prefixWord ++ tailWord_711792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711799 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_711799 : Nat := 118140960795 + 711799 * 2 ^ 59
def prefixEnd_711799 : Nat := 4983230072969 + 3 ^ 40 * 711799 * 2
def baseEnd_711799 : Nat := 324884459013125170523557

theorem tailTrace_711799 : CollatzResearch.WordTrace tailWord_711799 prefixEnd_711799 324884459013125170523557 := by
  unfold tailWord_711799
  simp only [CollatzResearch.WordTrace]
  refine ⟨25961442348281263435978451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17307628232187508957318967 25961442348281263435978451)
  ·
    refine ⟨38942163522421895153967677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25961442348281263435978451 38942163522421895153967677)
    ·
      refine ⟨14603311320908210682737879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38942163522421895153967677 14603311320908210682737879)
      ·
        refine ⟨21904966981362316024106819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14603311320908210682737879 21904966981362316024106819)
        ·
          refine ⟨32857450472043474036160229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21904966981362316024106819 32857450472043474036160229)
          ·
            refine ⟨6160771963508151381780043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32857450472043474036160229 6160771963508151381780043)
            ·
              refine ⟨9241157945262227072670065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6160771963508151381780043 9241157945262227072670065)
              ·
                refine ⟨6930868458946670304502549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9241157945262227072670065 6930868458946670304502549)
                ·
                  refine ⟨324884459013125170523557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6930868458946670304502549 324884459013125170523557)
                  ·
                    rfl

theorem cell20_711799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_711799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711799 prefixEnd_711799 := by exact prefixLift 711799
  have htrace : WordTrace (prefixWord ++ tailWord_711799) baseStart_711799 baseEnd_711799 := by
    simpa [prefixWord, tailWord_711799, baseEnd_711799] using wordTrace_append hprefix tailTrace_711799
  have hstable : (prefixWord ++ tailWord_711799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711799).length < 2 ^ (prefixWord ++ tailWord_711799).sum := by decide
  have hdescent : baseEnd_711799 < baseStart_711799 := by decide
  rcases family_descends (prefixWord ++ tailWord_711799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711809 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 5]
def baseStart_711809 : Nat := 118140960795 + 711809 * 2 ^ 59
def prefixEnd_711809 : Nat := 4983230072969 + 3 ^ 40 * 711809 * 2
def baseEnd_711809 : Nat := 324889023285609580190183

theorem tailTrace_711809 : CollatzResearch.WordTrace tailWord_711809 prefixEnd_711809 324889023285609580190183 := by
  unfold tailWord_711809
  simp only [CollatzResearch.WordTrace]
  refine ⟨25961807078245035143842481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17307871385496690095894987 25961807078245035143842481)
  ·
    refine ⟨19471355308683776357881861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25961807078245035143842481 19471355308683776357881861)
    ·
      refine ⟨3650879120378208067102849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19471355308683776357881861 3650879120378208067102849)
      ·
        refine ⟨2738159340283656050327137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3650879120378208067102849 2738159340283656050327137)
        ·
          refine ⟨2053619505212742037745353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2738159340283656050327137 2053619505212742037745353)
          ·
            refine ⟨1540214628909556528309015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2053619505212742037745353 1540214628909556528309015)
            ·
              refine ⟨2310321943364334792463523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540214628909556528309015 2310321943364334792463523)
              ·
                refine ⟨3465482915046502188695285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310321943364334792463523 3465482915046502188695285)
                ·
                  refine ⟨324889023285609580190183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3465482915046502188695285 324889023285609580190183)
                  ·
                    rfl

theorem cell20_711809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_711809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711809 prefixEnd_711809 := by exact prefixLift 711809
  have htrace : WordTrace (prefixWord ++ tailWord_711809) baseStart_711809 baseEnd_711809 := by
    simpa [prefixWord, tailWord_711809, baseEnd_711809] using wordTrace_append hprefix tailTrace_711809
  have hstable : (prefixWord ++ tailWord_711809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711809).length < 2 ^ (prefixWord ++ tailWord_711809).sum := by decide
  have hdescent : baseEnd_711809 < baseStart_711809 := by decide
  rcases family_descends (prefixWord ++ tailWord_711809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711847 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 5]
def baseStart_711847 : Nat := 118140960795 + 711847 * 2 ^ 59
def prefixEnd_711847 : Nat := 4983230072969 + 3 ^ 40 * 711847 * 2
def baseEnd_711847 : Nat := 324906367521050336923361

theorem tailTrace_711847 : CollatzResearch.WordTrace tailWord_711847 prefixEnd_711847 324906367521050336923361 := by
  unfold tailWord_711847
  simp only [CollatzResearch.WordTrace]
  refine ⟨25963193052107367633725795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17308795368071578422483863 25963193052107367633725795)
  ·
    refine ⟨38944789578161051450588693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25963193052107367633725795 38944789578161051450588693)
    ·
      refine ⟨1825537011476299286746345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38944789578161051450588693 1825537011476299286746345)
      ·
        refine ⟨1369152758607224465059759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1825537011476299286746345 1369152758607224465059759)
        ·
          refine ⟨2053729137910836697589639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1369152758607224465059759 2053729137910836697589639)
          ·
            refine ⟨3080593706866255046384459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053729137910836697589639 3080593706866255046384459)
            ·
              refine ⟨4620890560299382569576689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3080593706866255046384459 4620890560299382569576689)
              ·
                refine ⟨3465667920224536927182517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4620890560299382569576689 3465667920224536927182517)
                ·
                  refine ⟨324906367521050336923361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3465667920224536927182517 324906367521050336923361)
                  ·
                    rfl

theorem cell20_711847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_711847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711847 prefixEnd_711847 := by exact prefixLift 711847
  have htrace : WordTrace (prefixWord ++ tailWord_711847) baseStart_711847 baseEnd_711847 := by
    simpa [prefixWord, tailWord_711847, baseEnd_711847] using wordTrace_append hprefix tailTrace_711847
  have hstable : (prefixWord ++ tailWord_711847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711847).length < 2 ^ (prefixWord ++ tailWord_711847).sum := by decide
  have hdescent : baseEnd_711847 < baseStart_711847 := by decide
  rcases family_descends (prefixWord ++ tailWord_711847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711874 : List Nat := [3, 5, 1, 1, 2, 1, 2, 5]
def baseStart_711874 : Nat := 118140960795 + 711874 * 2 ^ 59
def prefixEnd_711874 : Nat := 4983230072969 + 3 ^ 40 * 711874 * 2
def baseEnd_711874 : Nat := 108306230352252747674417

theorem tailTrace_711874 : CollatzResearch.WordTrace tailWord_711874 prefixEnd_711874 108306230352252747674417 := by
  unfold tailWord_711874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491044455752387811239669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17309451882006367496639117 6491044455752387811239669)
  ·
    refine ⟨608535417726786357303719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6491044455752387811239669 608535417726786357303719)
    ·
      refine ⟨912803126590179535955579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 608535417726786357303719 912803126590179535955579)
      ·
        refine ⟨1369204689885269303933369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 912803126590179535955579 1369204689885269303933369)
        ·
          refine ⟨1026903517413951977950027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1369204689885269303933369 1026903517413951977950027)
          ·
            refine ⟨1540355276120927966925041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026903517413951977950027 1540355276120927966925041)
            ·
              refine ⟨1155266457090695975193781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1540355276120927966925041 1155266457090695975193781)
              ·
                refine ⟨108306230352252747674417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1155266457090695975193781 108306230352252747674417)
                ·
                  rfl

theorem cell20_711874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_711874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711874 prefixEnd_711874 := by exact prefixLift 711874
  have htrace : WordTrace (prefixWord ++ tailWord_711874) baseStart_711874 baseEnd_711874 := by
    simpa [prefixWord, tailWord_711874, baseEnd_711874] using wordTrace_append hprefix tailTrace_711874
  have hstable : (prefixWord ++ tailWord_711874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711874).length < 2 ^ (prefixWord ++ tailWord_711874).sum := by decide
  have hdescent : baseEnd_711874 < baseStart_711874 := by decide
  rcases family_descends (prefixWord ++ tailWord_711874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711875 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 4]
def baseStart_711875 : Nat := 118140960795 + 711875 * 2 ^ 59
def prefixEnd_711875 : Nat := 4983230072969 + 3 ^ 40 * 711875 * 2
def baseEnd_711875 : Nat := 324919147484006683989913

theorem tailTrace_711875 : CollatzResearch.WordTrace tailWord_711875 prefixEnd_711875 324919147484006683989913 := by
  unfold tailWord_711875
  simp only [CollatzResearch.WordTrace]
  refine ⟨25964214296005928415745079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17309476197337285610496719 25964214296005928415745079)
  ·
    refine ⟨38946321444008892623617619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25964214296005928415745079 38946321444008892623617619)
    ·
      refine ⟨58419482166013338935426429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38946321444008892623617619 58419482166013338935426429)
      ·
        refine ⟨21907305812255002100784911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58419482166013338935426429 21907305812255002100784911)
        ·
          refine ⟨32860958718382503151177367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21907305812255002100784911 32860958718382503151177367)
          ·
            refine ⟨49291438077573754726766051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32860958718382503151177367 49291438077573754726766051)
            ·
              refine ⟨73937157116360632090149077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49291438077573754726766051 73937157116360632090149077)
              ·
                refine ⟨1732902119914702314612869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 73937157116360632090149077 1732902119914702314612869)
                ·
                  refine ⟨324919147484006683989913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1732902119914702314612869 324919147484006683989913)
                  ·
                    rfl

theorem cell20_711875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_711875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_711875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_711875 prefixEnd_711875 := by exact prefixLift 711875
  have htrace : WordTrace (prefixWord ++ tailWord_711875) baseStart_711875 baseEnd_711875 := by
    simpa [prefixWord, tailWord_711875, baseEnd_711875] using wordTrace_append hprefix tailTrace_711875
  have hstable : (prefixWord ++ tailWord_711875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711875).length < 2 ^ (prefixWord ++ tailWord_711875).sum := by decide
  have hdescent : baseEnd_711875 < baseStart_711875 := by decide
  rcases family_descends (prefixWord ++ tailWord_711875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
