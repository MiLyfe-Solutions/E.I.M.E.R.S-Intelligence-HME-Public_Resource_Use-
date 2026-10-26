import V185TrunkScan23Chunk0049

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_295866 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3]
def baseStart_295866 : Nat := 118140960795 + 295866 * 2 ^ 59
def prefixEnd_295866 : Nat := 4983230072969 + 3 ^ 40 * 295866 * 2
def baseEnd_295866 : Nat := 151921467323244656614343

theorem tailTrace_295866 : CollatzResearch.WordTrace tailWord_295866 prefixEnd_295866 151921467323244656614343 := by
  unfold tailWord_295866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697779886533871683754863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7194079697423657823346301 2697779886533871683754863)
  ·
    refine ⟨4046669829800807525632295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2697779886533871683754863 4046669829800807525632295)
    ·
      refine ⟨6070004744701211288448443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4046669829800807525632295 6070004744701211288448443)
      ·
        refine ⟨9105007117051816932672665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6070004744701211288448443 9105007117051816932672665)
        ·
          refine ⟨6828755337788862699504499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9105007117051816932672665 6828755337788862699504499)
          ·
            refine ⟨10243133006683294049256749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6828755337788862699504499 10243133006683294049256749)
            ·
              refine ⟨3841174877506235268471281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10243133006683294049256749 3841174877506235268471281)
              ·
                refine ⟨2880881158129676451353461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3841174877506235268471281 2880881158129676451353461)
                ·
                  refine ⟨270082608574657167314387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2880881158129676451353461 270082608574657167314387)
                  ·
                    refine ⟨405123912861985750971581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 270082608574657167314387 405123912861985750971581)
                    ·
                      refine ⟨151921467323244656614343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 405123912861985750971581 151921467323244656614343)
                      ·
                        rfl

theorem cell23_295866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_295866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295866 prefixEnd_295866 := by exact prefixLift 295866
  have htrace : WordTrace (prefixWord ++ tailWord_295866) baseStart_295866 baseEnd_295866 := by
    simpa [prefixWord, tailWord_295866, baseEnd_295866] using wordTrace_append hprefix tailTrace_295866
  have hstable : (prefixWord ++ tailWord_295866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295866).length < 2 ^ (prefixWord ++ tailWord_295866).sum := by decide
  have hdescent : baseEnd_295866 < baseStart_295866 := by decide
  rcases family_descends (prefixWord ++ tailWord_295866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295883 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 3, 1, 3]
def baseStart_295883 : Nat := 118140960795 + 295883 * 2 ^ 59
def prefixEnd_295883 : Nat := 4983230072969 + 3 ^ 40 * 295883 * 2
def baseEnd_295883 : Nat := 151930196494371090101765

theorem tailTrace_295883 : CollatzResearch.WordTrace tailWord_295883 prefixEnd_295883 151930196494371090101765 := by
  unfold tailWord_295883
  simp only [CollatzResearch.WordTrace]
  refine ⟨10791739587073898638388303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7194493058049265758925535 10791739587073898638388303)
  ·
    refine ⟨16187609380610847957582455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10791739587073898638388303 16187609380610847957582455)
    ·
      refine ⟨24281414070916271936373683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16187609380610847957582455 24281414070916271936373683)
      ·
        refine ⟨36422121106374407904560525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24281414070916271936373683 36422121106374407904560525)
        ·
          refine ⟨13658295414890402964210197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36422121106374407904560525 13658295414890402964210197)
          ·
            refine ⟨640232597572987638947353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13658295414890402964210197 640232597572987638947353)
            ·
              refine ⟨480174448179740729210515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640232597572987638947353 480174448179740729210515)
              ·
                refine ⟨720261672269611093815773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480174448179740729210515 720261672269611093815773)
                ·
                  refine ⟨270098127101104160180915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720261672269611093815773 270098127101104160180915)
                  ·
                    refine ⟨405147190651656240271373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 270098127101104160180915 405147190651656240271373)
                    ·
                      refine ⟨151930196494371090101765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 405147190651656240271373 151930196494371090101765)
                      ·
                        rfl

theorem cell23_295883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 1, 3].length) (baseStart_295883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295883 prefixEnd_295883 := by exact prefixLift 295883
  have htrace : WordTrace (prefixWord ++ tailWord_295883) baseStart_295883 baseEnd_295883 := by
    simpa [prefixWord, tailWord_295883, baseEnd_295883] using wordTrace_append hprefix tailTrace_295883
  have hstable : (prefixWord ++ tailWord_295883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295883).length < 2 ^ (prefixWord ++ tailWord_295883).sum := by decide
  have hdescent : baseEnd_295883 < baseStart_295883 := by decide
  rcases family_descends (prefixWord ++ tailWord_295883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295903 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 1, 5]
def baseStart_295903 : Nat := 118140960795 + 295903 * 2 ^ 59
def prefixEnd_295903 : Nat := 4983230072969 + 3 ^ 40 * 295903 * 2
def baseEnd_295903 : Nat := 50646822035820337283891

theorem tailTrace_295903 : CollatzResearch.WordTrace tailWord_295903 prefixEnd_295903 50646822035820337283891 := by
  unfold tailWord_295903
  simp only [CollatzResearch.WordTrace]
  refine ⟨10792469047001442054116363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7194979364667628036077575 10792469047001442054116363)
  ·
    refine ⟨16188703570502163081174545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10792469047001442054116363 16188703570502163081174545)
    ·
      refine ⟨12141527677876622310880909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16188703570502163081174545 12141527677876622310880909)
      ·
        refine ⟨4553072879203733366580341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12141527677876622310880909 4553072879203733366580341)
        ·
          refine ⟨426850582425350003116907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4553072879203733366580341 426850582425350003116907)
          ·
            refine ⟨640275873638025004675361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426850582425350003116907 640275873638025004675361)
            ·
              refine ⟨480206905228518753506521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640275873638025004675361 480206905228518753506521)
              ·
                refine ⟨360155178921389065129891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480206905228518753506521 360155178921389065129891)
                ·
                  refine ⟨540232768382083597694837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360155178921389065129891 540232768382083597694837)
                  ·
                    refine ⟨50646822035820337283891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 540232768382083597694837 50646822035820337283891)
                    ·
                      rfl

theorem cell23_295903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 5].length) (baseStart_295903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295903 prefixEnd_295903 := by exact prefixLift 295903
  have htrace : WordTrace (prefixWord ++ tailWord_295903) baseStart_295903 baseEnd_295903 := by
    simpa [prefixWord, tailWord_295903, baseEnd_295903] using wordTrace_append hprefix tailTrace_295903
  have hstable : (prefixWord ++ tailWord_295903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295903).length < 2 ^ (prefixWord ++ tailWord_295903).sum := by decide
  have hdescent : baseEnd_295903 < baseStart_295903 := by decide
  rcases family_descends (prefixWord ++ tailWord_295903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295934 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_295934 : Nat := 118140960795 + 295934 * 2 ^ 59
def prefixEnd_295934 : Nat := 4983230072969 + 3 ^ 40 * 295934 * 2
def baseEnd_295934 : Nat := 151956384007750390564031

theorem tailTrace_295934 : CollatzResearch.WordTrace tailWord_295934 prefixEnd_295934 151956384007750390564031 := by
  unfold tailWord_295934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349199963736141793561857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7195733139926089565663237 1349199963736141793561857)
  ·
    refine ⟨1011899972802106345171393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1349199963736141793561857 1011899972802106345171393)
    ·
      refine ⟨758924979601579758878545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1011899972802106345171393 758924979601579758878545)
      ·
        refine ⟨569193734701184819158909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 758924979601579758878545 569193734701184819158909)
        ·
          refine ⟨213447650512944307184591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 569193734701184819158909 213447650512944307184591)
          ·
            refine ⟨320171475769416460776887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213447650512944307184591 320171475769416460776887)
            ·
              refine ⟨480257213654124691165331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320171475769416460776887 480257213654124691165331)
              ·
                refine ⟨720385820481187036747997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480257213654124691165331 720385820481187036747997)
                ·
                  refine ⟨270144682680445138780499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720385820481187036747997 270144682680445138780499)
                  ·
                    refine ⟨405217024020667708170749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 270144682680445138780499 405217024020667708170749)
                    ·
                      refine ⟨151956384007750390564031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 405217024020667708170749 151956384007750390564031)
                      ·
                        rfl

theorem cell23_295934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_295934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295934 prefixEnd_295934 := by exact prefixLift 295934
  have htrace : WordTrace (prefixWord ++ tailWord_295934) baseStart_295934 baseEnd_295934 := by
    simpa [prefixWord, tailWord_295934, baseEnd_295934] using wordTrace_append hprefix tailTrace_295934
  have hstable : (prefixWord ++ tailWord_295934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295934).length < 2 ^ (prefixWord ++ tailWord_295934).sum := by decide
  have hdescent : baseEnd_295934 < baseStart_295934 := by decide
  rcases family_descends (prefixWord ++ tailWord_295934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295946 : List Nat := [3, 1, 2, 2, 3, 2, 2, 8]
def baseStart_295946 : Nat := 118140960795 + 295946 * 2 ^ 59
def prefixEnd_295946 : Nat := 4983230072969 + 3 ^ 40 * 295946 * 2
def baseEnd_295946 : Nat := 5628242436133494207925

theorem tailTrace_295946 : CollatzResearch.WordTrace tailWord_295946 prefixEnd_295946 5628242436133494207925 := by
  unfold tailWord_295946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2698509346461415099482923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7196024923897106931954461 2698509346461415099482923)
  ·
    refine ⟨4047764019692122649224385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2698509346461415099482923 4047764019692122649224385)
    ·
      refine ⟨3035823014769091986918289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4047764019692122649224385 3035823014769091986918289)
      ·
        refine ⟨2276867261076818990188717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3035823014769091986918289 2276867261076818990188717)
        ·
          refine ⟨853825222903807121320769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2276867261076818990188717 853825222903807121320769)
          ·
            refine ⟨640368917177855340990577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 853825222903807121320769 640368917177855340990577)
            ·
              refine ⟨480276687883391505742933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640368917177855340990577 480276687883391505742933)
              ·
                refine ⟨5628242436133494207925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 480276687883391505742933 5628242436133494207925)
                ·
                  rfl

theorem cell23_295946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 8].length) (baseStart_295946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295946 prefixEnd_295946 := by exact prefixLift 295946
  have htrace : WordTrace (prefixWord ++ tailWord_295946) baseStart_295946 baseEnd_295946 := by
    simpa [prefixWord, tailWord_295946, baseEnd_295946] using wordTrace_append hprefix tailTrace_295946
  have hstable : (prefixWord ++ tailWord_295946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295946).length < 2 ^ (prefixWord ++ tailWord_295946).sum := by decide
  have hdescent : baseEnd_295946 < baseStart_295946 := by decide
  rcases family_descends (prefixWord ++ tailWord_295946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295950 : List Nat := [4, 1, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_295950 : Nat := 118140960795 + 295950 * 2 ^ 59
def prefixEnd_295950 : Nat := 4983230072969 + 3 ^ 40 * 295950 * 2
def baseEnd_295950 : Nat := 50654866566074109321319

theorem tailTrace_295950 : CollatzResearch.WordTrace tailWord_295950 prefixEnd_295950 50654866566074109321319 := by
  unfold tailWord_295950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349272909728896135134663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7196122185220779387384869 1349272909728896135134663)
  ·
    refine ⟨2023909364593344202701995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1349272909728896135134663 2023909364593344202701995)
    ·
      refine ⟨3035864046890016304052993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2023909364593344202701995 3035864046890016304052993)
      ·
        refine ⟨2276898035167512228039745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3035864046890016304052993 2276898035167512228039745)
        ·
          refine ⟨1707673526375634171029809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2276898035167512228039745 1707673526375634171029809)
          ·
            refine ⟨1280755144781725628272357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1707673526375634171029809 1280755144781725628272357)
            ·
              refine ⟨240141589646573555301067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1280755144781725628272357 240141589646573555301067)
              ·
                refine ⟨360212384469860332951601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240141589646573555301067 360212384469860332951601)
                ·
                  refine ⟨270159288352395249713701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360212384469860332951601 270159288352395249713701)
                  ·
                    refine ⟨50654866566074109321319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270159288352395249713701 50654866566074109321319)
                    ·
                      rfl

theorem cell23_295950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_295950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295950 prefixEnd_295950 := by exact prefixLift 295950
  have htrace : WordTrace (prefixWord ++ tailWord_295950) baseStart_295950 baseEnd_295950 := by
    simpa [prefixWord, tailWord_295950, baseEnd_295950] using wordTrace_append hprefix tailTrace_295950
  have hstable : (prefixWord ++ tailWord_295950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295950).length < 2 ^ (prefixWord ++ tailWord_295950).sum := by decide
  have hdescent : baseEnd_295950 < baseStart_295950 := by decide
  rcases family_descends (prefixWord ++ tailWord_295950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295954 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_295954 : Nat := 118140960795 + 295954 * 2 ^ 59
def prefixEnd_295954 : Nat := 4983230072969 + 3 ^ 40 * 295954 * 2
def baseEnd_295954 : Nat := 50655551206946770771313

theorem tailTrace_295954 : CollatzResearch.WordTrace tailWord_295954 prefixEnd_295954 50655551206946770771313 := by
  unfold tailWord_295954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2698582292454169441055729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7196219446544451842815277 2698582292454169441055729)
  ·
    refine ⟨2023936719340627080791797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2698582292454169441055729 2023936719340627080791797)
    ·
      refine ⟨189744067438183788824231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2023936719340627080791797 189744067438183788824231)
      ·
        refine ⟨284616101157275683236347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189744067438183788824231 284616101157275683236347)
        ·
          refine ⟨426924151735913524854521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284616101157275683236347 426924151735913524854521)
          ·
            refine ⟨320193113801935143640891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 426924151735913524854521 320193113801935143640891)
            ·
              refine ⟨480289670702902715461337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320193113801935143640891 480289670702902715461337)
              ·
                refine ⟨360217253027177036596003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480289670702902715461337 360217253027177036596003)
                ·
                  refine ⟨540325879540765554894005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360217253027177036596003 540325879540765554894005)
                  ·
                    refine ⟨50655551206946770771313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 540325879540765554894005 50655551206946770771313)
                    ·
                      rfl

theorem cell23_295954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_295954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295954 prefixEnd_295954 := by exact prefixLift 295954
  have htrace : WordTrace (prefixWord ++ tailWord_295954) baseStart_295954 baseEnd_295954 := by
    simpa [prefixWord, tailWord_295954, baseEnd_295954] using wordTrace_append hprefix tailTrace_295954
  have hstable : (prefixWord ++ tailWord_295954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295954).length < 2 ^ (prefixWord ++ tailWord_295954).sum := by decide
  have hdescent : baseEnd_295954 < baseStart_295954 := by decide
  rcases family_descends (prefixWord ++ tailWord_295954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295960 : List Nat := [2, 1, 2, 3, 2, 4, 1, 2, 1, 2, 3]
def baseStart_295960 : Nat := 118140960795 + 295960 * 2 ^ 59
def prefixEnd_295960 : Nat := 4983230072969 + 3 ^ 40 * 295960 * 2
def baseEnd_295960 : Nat := 151969734504767288838911

theorem tailTrace_295960 : CollatzResearch.WordTrace tailWord_295960 prefixEnd_295960 151969734504767288838911 := by
  unfold tailWord_295960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5397274003897470394470667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7196365338529960525960889 5397274003897470394470667)
  ·
    refine ⟨8095911005846205591706001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5397274003897470394470667 8095911005846205591706001)
    ·
      refine ⟨6071933254384654193779501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8095911005846205591706001 6071933254384654193779501)
      ·
        refine ⟨2276974970394245322667313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6071933254384654193779501 2276974970394245322667313)
        ·
          refine ⟨1707731227795683992000485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2276974970394245322667313 1707731227795683992000485)
          ·
            refine ⟨320199605211690748500091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1707731227795683992000485 320199605211690748500091)
            ·
              refine ⟨480299407817536122750137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320199605211690748500091 480299407817536122750137)
              ·
                refine ⟨360224555863152092062603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 480299407817536122750137 360224555863152092062603)
                ·
                  refine ⟨540336833794728138093905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360224555863152092062603 540336833794728138093905)
                  ·
                    refine ⟨405252625346046103570429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 540336833794728138093905 405252625346046103570429)
                    ·
                      refine ⟨151969734504767288838911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 405252625346046103570429 151969734504767288838911)
                      ·
                        rfl

theorem cell23_295960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_295960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295960 prefixEnd_295960 := by exact prefixLift 295960
  have htrace : WordTrace (prefixWord ++ tailWord_295960) baseStart_295960 baseEnd_295960 := by
    simpa [prefixWord, tailWord_295960, baseEnd_295960] using wordTrace_append hprefix tailTrace_295960
  have hstable : (prefixWord ++ tailWord_295960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295960).length < 2 ^ (prefixWord ++ tailWord_295960).sum := by decide
  have hdescent : baseEnd_295960 < baseStart_295960 := by decide
  rcases family_descends (prefixWord ++ tailWord_295960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_295996 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_295996 : Nat := 118140960795 + 295996 * 2 ^ 59
def prefixEnd_295996 : Nat := 4983230072969 + 3 ^ 40 * 295996 * 2
def baseEnd_295996 : Nat := 151988219808329147988745

theorem tailTrace_295996 : CollatzResearch.WordTrace tailWord_295996 prefixEnd_295996 151988219808329147988745 := by
  unfold tailWord_295996
  simp only [CollatzResearch.WordTrace]
  refine ⟨5397930517832259468625921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7197240690443012624834561 5397930517832259468625921)
  ·
    refine ⟨4048447888374194601469441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5397930517832259468625921 4048447888374194601469441)
    ·
      refine ⟨3036335916280645951102081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4048447888374194601469441 3036335916280645951102081)
      ·
        refine ⟨2277251937210484463326561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3036335916280645951102081 2277251937210484463326561)
        ·
          refine ⟨1707938952907863347494921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2277251937210484463326561 1707938952907863347494921)
          ·
            refine ⟨1280954214680897510621191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1707938952907863347494921 1280954214680897510621191)
            ·
              refine ⟨1921431322021346265931787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280954214680897510621191 1921431322021346265931787)
              ·
                refine ⟨2882146983032019398897681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1921431322021346265931787 2882146983032019398897681)
                ·
                  refine ⟨2161610237274014549173261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2882146983032019398897681 2161610237274014549173261)
                  ·
                    refine ⟨810603838977755455939973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2161610237274014549173261 810603838977755455939973)
                    ·
                      refine ⟨151988219808329147988745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 810603838977755455939973 151988219808329147988745)
                      ·
                        rfl

theorem cell23_295996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_295996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_295996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_295996 prefixEnd_295996 := by exact prefixLift 295996
  have htrace : WordTrace (prefixWord ++ tailWord_295996) baseStart_295996 baseEnd_295996 := by
    simpa [prefixWord, tailWord_295996, baseEnd_295996] using wordTrace_append hprefix tailTrace_295996
  have hstable : (prefixWord ++ tailWord_295996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_295996).length < 2 ^ (prefixWord ++ tailWord_295996).sum := by decide
  have hdescent : baseEnd_295996 < baseStart_295996 := by decide
  rcases family_descends (prefixWord ++ tailWord_295996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296019 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 9]
def baseStart_296019 : Nat := 118140960795 + 296019 * 2 ^ 59
def prefixEnd_296019 : Nat := 4983230072969 + 3 ^ 40 * 296019 * 2
def baseEnd_296019 : Nat := 16888892207042506444571

theorem tailTrace_296019 : CollatzResearch.WordTrace tailWord_296019 prefixEnd_296019 16888892207042506444571 := by
  unfold tailWord_296019
  simp only [CollatzResearch.WordTrace]
  refine ⟨10796699914581193865339111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7197799943054129243559407 10796699914581193865339111)
  ·
    refine ⟨16195049871871790798008667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10796699914581193865339111 16195049871871790798008667)
    ·
      refine ⟨24292574807807686197013001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16195049871871790798008667 24292574807807686197013001)
      ·
        refine ⟨18219431105855764647759751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24292574807807686197013001 18219431105855764647759751)
        ·
          refine ⟨27329146658783646971639627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18219431105855764647759751 27329146658783646971639627)
          ·
            refine ⟨40993719988175470457459441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27329146658783646971639627 40993719988175470457459441)
            ·
              refine ⟨30745289991131602843094581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40993719988175470457459441 30745289991131602843094581)
              ·
                refine ⟨2882370936668587766540117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30745289991131602843094581 2882370936668587766540117)
                ·
                  refine ⟨16888892207042506444571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2882370936668587766540117 16888892207042506444571)
                  ·
                    rfl

theorem cell23_296019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 9].length) (baseStart_296019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296019 prefixEnd_296019 := by exact prefixLift 296019
  have htrace : WordTrace (prefixWord ++ tailWord_296019) baseStart_296019 baseEnd_296019 := by
    simpa [prefixWord, tailWord_296019, baseEnd_296019] using wordTrace_append hprefix tailTrace_296019
  have hstable : (prefixWord ++ tailWord_296019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296019).length < 2 ^ (prefixWord ++ tailWord_296019).sum := by decide
  have hdescent : baseEnd_296019 < baseStart_296019 := by decide
  rcases family_descends (prefixWord ++ tailWord_296019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296034 : List Nat := [3, 3, 2, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_296034 : Nat := 118140960795 + 296034 * 2 ^ 59
def prefixEnd_296034 : Nat := 4983230072969 + 3 ^ 40 * 296034 * 2
def baseEnd_296034 : Nat := 152007732073199999313571

theorem tailTrace_296034 : CollatzResearch.WordTrace tailWord_296034 prefixEnd_296034 152007732073199999313571 := by
  unfold tailWord_296034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699311752381712856783789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7198164673017900951423437 2699311752381712856783789)
  ·
    refine ⟨1012241907143142321293921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2699311752381712856783789 1012241907143142321293921)
    ·
      refine ⟨759181430357356740970441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1012241907143142321293921 759181430357356740970441)
      ·
        refine ⟨569386072768017555727831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 759181430357356740970441 569386072768017555727831)
        ·
          refine ⟨854079109152026333591747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569386072768017555727831 854079109152026333591747)
          ·
            refine ⟨1281118663728039500387621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854079109152026333591747 1281118663728039500387621)
            ·
              refine ⟨240209749449007406322679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1281118663728039500387621 240209749449007406322679)
              ·
                refine ⟨360314624173511109484019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240209749449007406322679 360314624173511109484019)
                ·
                  refine ⟨540471936260266664226029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360314624173511109484019 540471936260266664226029)
                  ·
                    refine ⟨202676976097599999084761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 540471936260266664226029 202676976097599999084761)
                    ·
                      refine ⟨152007732073199999313571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 202676976097599999084761 152007732073199999313571)
                      ·
                        rfl

theorem cell23_296034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_296034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296034 prefixEnd_296034 := by exact prefixLift 296034
  have htrace : WordTrace (prefixWord ++ tailWord_296034) baseStart_296034 baseEnd_296034 := by
    simpa [prefixWord, tailWord_296034, baseEnd_296034] using wordTrace_append hprefix tailTrace_296034
  have hstable : (prefixWord ++ tailWord_296034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296034).length < 2 ^ (prefixWord ++ tailWord_296034).sum := by decide
  have hdescent : baseEnd_296034 < baseStart_296034 := by decide
  rcases family_descends (prefixWord ++ tailWord_296034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296190 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_296190 : Nat := 118140960795 + 296190 * 2 ^ 59
def prefixEnd_296190 : Nat := 4983230072969 + 3 ^ 40 * 296190 * 2
def baseEnd_296190 : Nat := 50695945018433796320951

theorem tailTrace_296190 : CollatzResearch.WordTrace tailWord_296190 prefixEnd_296190 50695945018433796320951 := by
  unfold tailWord_296190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1350367099620211258726753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7201957864641126713209349 1350367099620211258726753)
  ·
    refine ⟨1012775324715158444045065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1350367099620211258726753 1012775324715158444045065)
    ·
      refine ⟨759581493536368833033799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1012775324715158444045065 759581493536368833033799)
      ·
        refine ⟨1139372240304553249550699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759581493536368833033799 1139372240304553249550699)
        ·
          refine ⟨1709058360456829874326049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139372240304553249550699 1709058360456829874326049)
          ·
            refine ⟨1281793770342622405744537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1709058360456829874326049 1281793770342622405744537)
            ·
              refine ⟨961345327756966804308403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281793770342622405744537 961345327756966804308403)
              ·
                refine ⟨1442017991635450206462605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961345327756966804308403 1442017991635450206462605)
                ·
                  refine ⟨540756746863293827423477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1442017991635450206462605 540756746863293827423477)
                  ·
                    refine ⟨50695945018433796320951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 540756746863293827423477 50695945018433796320951)
                    ·
                      rfl

theorem cell23_296190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_296190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296190 prefixEnd_296190 := by exact prefixLift 296190
  have htrace : WordTrace (prefixWord ++ tailWord_296190) baseStart_296190 baseEnd_296190 := by
    simpa [prefixWord, tailWord_296190, baseEnd_296190] using wordTrace_append hprefix tailTrace_296190
  have hstable : (prefixWord ++ tailWord_296190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296190).length < 2 ^ (prefixWord ++ tailWord_296190).sum := by decide
  have hdescent : baseEnd_296190 < baseStart_296190 := by decide
  rcases family_descends (prefixWord ++ tailWord_296190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296203 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 1, 6]
def baseStart_296203 : Nat := 118140960795 + 296203 * 2 ^ 59
def prefixEnd_296203 : Nat := 4983230072969 + 3 ^ 40 * 296203 * 2
def baseEnd_296203 : Nat := 50698170101269946033431

theorem tailTrace_296203 : CollatzResearch.WordTrace tailWord_296203 prefixEnd_296203 50698170101269946033431 := by
  unfold tailWord_296203
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803410945914593290037263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7202273963943062193358175 10803410945914593290037263)
  ·
    refine ⟨16205116418871889935055895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10803410945914593290037263 16205116418871889935055895)
    ·
      refine ⟨24307674628307834902583843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16205116418871889935055895 24307674628307834902583843)
      ·
        refine ⟨36461511942461752353875765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24307674628307834902583843 36461511942461752353875765)
        ·
          refine ⟨3418266744605789283175853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36461511942461752353875765 3418266744605789283175853)
          ·
            refine ⟨1281850029227170981190945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3418266744605789283175853 1281850029227170981190945)
            ·
              refine ⟨961387521920378235893209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281850029227170981190945 961387521920378235893209)
              ·
                refine ⟨721040641440283676919907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961387521920378235893209 721040641440283676919907)
                ·
                  refine ⟨1081560962160425515379861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721040641440283676919907 1081560962160425515379861)
                  ·
                    refine ⟨50698170101269946033431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1081560962160425515379861 50698170101269946033431)
                    ·
                      rfl

theorem cell23_296203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 6].length) (baseStart_296203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296203 prefixEnd_296203 := by exact prefixLift 296203
  have htrace : WordTrace (prefixWord ++ tailWord_296203) baseStart_296203 baseEnd_296203 := by
    simpa [prefixWord, tailWord_296203, baseEnd_296203] using wordTrace_append hprefix tailTrace_296203
  have hstable : (prefixWord ++ tailWord_296203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296203).length < 2 ^ (prefixWord ++ tailWord_296203).sum := by decide
  have hdescent : baseEnd_296203 < baseStart_296203 := by decide
  rcases family_descends (prefixWord ++ tailWord_296203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296204 : List Nat := [2, 2, 1, 2, 2, 4, 2, 3, 1, 1, 3]
def baseStart_296204 : Nat := 118140960795 + 296204 * 2 ^ 59
def prefixEnd_296204 : Nat := 4983230072969 + 3 ^ 40 * 296204 * 2
def baseEnd_296204 : Nat := 152095023784464334187789

theorem tailTrace_296204 : CollatzResearch.WordTrace tailWord_296204 prefixEnd_296204 152095023784464334187789 := by
  unfold tailWord_296204
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401723709455485230411833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7202298279273980307215777 5401723709455485230411833)
  ·
    refine ⟨4051292782091613922808875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5401723709455485230411833 4051292782091613922808875)
    ·
      refine ⟨6076939173137420884213313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4051292782091613922808875 6076939173137420884213313)
      ·
        refine ⟨4557704379853065663159985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6076939173137420884213313 4557704379853065663159985)
        ·
          refine ⟨3418278284889799247369989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4557704379853065663159985 3418278284889799247369989)
          ·
            refine ⟨640927178416837358881873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3418278284889799247369989 640927178416837358881873)
            ·
              refine ⟨480695383812628019161405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640927178416837358881873 480695383812628019161405)
              ·
                refine ⟨180260768929735507185527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 480695383812628019161405 180260768929735507185527)
                ·
                  refine ⟨270391153394603260778291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180260768929735507185527 270391153394603260778291)
                  ·
                    refine ⟨405586730091904891167437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 270391153394603260778291 405586730091904891167437)
                    ·
                      refine ⟨152095023784464334187789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 405586730091904891167437 152095023784464334187789)
                      ·
                        rfl

theorem cell23_296204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_296204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296204 prefixEnd_296204 := by exact prefixLift 296204
  have htrace : WordTrace (prefixWord ++ tailWord_296204) baseStart_296204 baseEnd_296204 := by
    simpa [prefixWord, tailWord_296204, baseEnd_296204] using wordTrace_append hprefix tailTrace_296204
  have hstable : (prefixWord ++ tailWord_296204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296204).length < 2 ^ (prefixWord ++ tailWord_296204).sum := by decide
  have hdescent : baseEnd_296204 < baseStart_296204 := by decide
  rcases family_descends (prefixWord ++ tailWord_296204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296213 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_296213 : Nat := 118140960795 + 296213 * 2 ^ 59
def prefixEnd_296213 : Nat := 4983230072969 + 3 ^ 40 * 296213 * 2
def baseEnd_296213 : Nat := 152099645110354798975247

theorem tailTrace_296213 : CollatzResearch.WordTrace tailWord_296213 prefixEnd_296213 152099645110354798975247 := by
  unfold tailWord_296213
  simp only [CollatzResearch.WordTrace]
  refine ⟨10803775675878364997901293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7202517117252243331934195 10803775675878364997901293)
  ·
    refine ⟨4051415878454386874212985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10803775675878364997901293 4051415878454386874212985)
    ·
      refine ⟨3038561908840790155659739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4051415878454386874212985 3038561908840790155659739)
      ·
        refine ⟨4557842863261185233489609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3038561908840790155659739 4557842863261185233489609)
        ·
          refine ⟨3418382147445888925117207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4557842863261185233489609 3418382147445888925117207)
          ·
            refine ⟨5127573221168833387675811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3418382147445888925117207 5127573221168833387675811)
            ·
              refine ⟨7691359831753250081513717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5127573221168833387675811 7691359831753250081513717)
              ·
                refine ⟨721064984226867195141911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7691359831753250081513717 721064984226867195141911)
                ·
                  refine ⟨1081597476340300792712867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721064984226867195141911 1081597476340300792712867)
                  ·
                    refine ⟨1622396214510451189069301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1081597476340300792712867 1622396214510451189069301)
                    ·
                      refine ⟨152099645110354798975247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1622396214510451189069301 152099645110354798975247)
                      ·
                        rfl

theorem cell23_296213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_296213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296213 prefixEnd_296213 := by exact prefixLift 296213
  have htrace : WordTrace (prefixWord ++ tailWord_296213) baseStart_296213 baseEnd_296213 := by
    simpa [prefixWord, tailWord_296213, baseEnd_296213] using wordTrace_append hprefix tailTrace_296213
  have hstable : (prefixWord ++ tailWord_296213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296213).length < 2 ^ (prefixWord ++ tailWord_296213).sum := by decide
  have hdescent : baseEnd_296213 < baseStart_296213 := by decide
  rcases family_descends (prefixWord ++ tailWord_296213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296227 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 3, 2, 2]
def baseStart_296227 : Nat := 118140960795 + 296227 * 2 ^ 59
def prefixEnd_296227 : Nat := 4983230072969 + 3 ^ 40 * 296227 * 2
def baseEnd_296227 : Nat := 152106833839517744200183

theorem tailTrace_296227 : CollatzResearch.WordTrace tailWord_296227 prefixEnd_296227 152106833839517744200183 := by
  unfold tailWord_296227
  simp only [CollatzResearch.WordTrace]
  refine ⟨10804286297827645388910935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7202857531885096925940623 10804286297827645388910935)
  ·
    refine ⟨16206429446741468083366403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10804286297827645388910935 16206429446741468083366403)
    ·
      refine ⟨24309644170112202125049605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16206429446741468083366403 24309644170112202125049605)
      ·
        refine ⟨4558058281896037898446801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24309644170112202125049605 4558058281896037898446801)
        ·
          refine ⟨3418543711422028423835101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4558058281896037898446801 3418543711422028423835101)
          ·
            refine ⟨1281953891783260658938163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3418543711422028423835101 1281953891783260658938163)
            ·
              refine ⟨1922930837674890988407245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281953891783260658938163 1922930837674890988407245)
              ·
                refine ⟨721099064128084120652717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1922930837674890988407245 721099064128084120652717)
                ·
                  refine ⟨270412149048031545244769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721099064128084120652717 270412149048031545244769)
                  ·
                    refine ⟨202809111786023658933577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 270412149048031545244769 202809111786023658933577)
                    ·
                      refine ⟨152106833839517744200183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 202809111786023658933577 152106833839517744200183)
                      ·
                        rfl

theorem cell23_296227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_296227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296227 prefixEnd_296227 := by exact prefixLift 296227
  have htrace : WordTrace (prefixWord ++ tailWord_296227) baseStart_296227 baseEnd_296227 := by
    simpa [prefixWord, tailWord_296227, baseEnd_296227] using wordTrace_append hprefix tailTrace_296227
  have hstable : (prefixWord ++ tailWord_296227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296227).length < 2 ^ (prefixWord ++ tailWord_296227).sum := by decide
  have hdescent : baseEnd_296227 < baseStart_296227 := by decide
  rcases family_descends (prefixWord ++ tailWord_296227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296237 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_296237 : Nat := 118140960795 + 296237 * 2 ^ 59
def prefixEnd_296237 : Nat := 4983230072969 + 3 ^ 40 * 296237 * 2
def baseEnd_296237 : Nat := 50703989548687568358379

theorem tailTrace_296237 : CollatzResearch.WordTrace tailWord_296237 prefixEnd_296237 50703989548687568358379 := by
  unfold tailWord_296237
  simp only [CollatzResearch.WordTrace]
  refine ⟨10804651027791417096774965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7203100685194278064516643 10804651027791417096774965)
  ·
    refine ⟨1012936033855445352822653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10804651027791417096774965 1012936033855445352822653)
    ·
      refine ⟨379851012695792007308495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1012936033855445352822653 379851012695792007308495)
      ·
        refine ⟨569776519043688010962743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379851012695792007308495 569776519043688010962743)
        ·
          refine ⟨854664778565532016444115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569776519043688010962743 854664778565532016444115)
          ·
            refine ⟨1281997167848298024666173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854664778565532016444115 1281997167848298024666173)
            ·
              refine ⟨480748937943111759249815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1281997167848298024666173 480748937943111759249815)
              ·
                refine ⟨721123406914667638874723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480748937943111759249815 721123406914667638874723)
                ·
                  refine ⟨1081685110372001458312085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721123406914667638874723 1081685110372001458312085)
                  ·
                    refine ⟨50703989548687568358379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1081685110372001458312085 50703989548687568358379)
                    ·
                      rfl

theorem cell23_296237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_296237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296237 prefixEnd_296237 := by exact prefixLift 296237
  have htrace : WordTrace (prefixWord ++ tailWord_296237) baseStart_296237 baseEnd_296237 := by
    simpa [prefixWord, tailWord_296237, baseEnd_296237] using wordTrace_append hprefix tailTrace_296237
  have hstable : (prefixWord ++ tailWord_296237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296237).length < 2 ^ (prefixWord ++ tailWord_296237).sum := by decide
  have hdescent : baseEnd_296237 < baseStart_296237 := by decide
  rcases family_descends (prefixWord ++ tailWord_296237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296244 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_296244 : Nat := 118140960795 + 296244 * 2 ^ 59
def prefixEnd_296244 : Nat := 4983230072969 + 3 ^ 40 * 296244 * 2
def baseEnd_296244 : Nat := 152115563010644177687605

theorem tailTrace_296244 : CollatzResearch.WordTrace tailWord_296244 prefixEnd_296244 152115563010644177687605 := by
  unfold tailWord_296244
  simp only [CollatzResearch.WordTrace]
  refine ⟨5402453169383028646139893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7203270892510704861519857 5402453169383028646139893)
  ·
    refine ⟨506479984629658935575615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5402453169383028646139893 506479984629658935575615)
    ·
      refine ⟨759719976944488403363423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 506479984629658935575615 759719976944488403363423)
      ·
        refine ⟨1139579965416732605045135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759719976944488403363423 1139579965416732605045135)
        ·
          refine ⟨1709369948125098907567703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139579965416732605045135 1709369948125098907567703)
          ·
            refine ⟨2564054922187648361351555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709369948125098907567703 2564054922187648361351555)
            ·
              refine ⟨3846082383281472542027333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564054922187648361351555 3846082383281472542027333)
              ·
                refine ⟨721140446865276101630125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3846082383281472542027333 721140446865276101630125)
                ·
                  refine ⟨270427667574478538111297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721140446865276101630125 270427667574478538111297)
                  ·
                    refine ⟨202820750680858903583473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 270427667574478538111297 202820750680858903583473)
                    ·
                      refine ⟨152115563010644177687605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 202820750680858903583473 152115563010644177687605)
                      ·
                        rfl

theorem cell23_296244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_296244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296244 prefixEnd_296244 := by exact prefixLift 296244
  have htrace : WordTrace (prefixWord ++ tailWord_296244) baseStart_296244 baseEnd_296244 := by
    simpa [prefixWord, tailWord_296244, baseEnd_296244] using wordTrace_append hprefix tailTrace_296244
  have hstable : (prefixWord ++ tailWord_296244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296244).length < 2 ^ (prefixWord ++ tailWord_296244).sum := by decide
  have hdescent : baseEnd_296244 < baseStart_296244 := by decide
  rcases family_descends (prefixWord ++ tailWord_296244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296273 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_296273 : Nat := 118140960795 + 296273 * 2 ^ 59
def prefixEnd_296273 : Nat := 4983230072969 + 3 ^ 40 * 296273 * 2
def baseEnd_296273 : Nat := 152130453949624564224971

theorem tailTrace_296273 : CollatzResearch.WordTrace tailWord_296273 prefixEnd_296273 152130453949624564224971 := by
  unfold tailWord_296273
  simp only [CollatzResearch.WordTrace]
  refine ⟨10805964055660995245085473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7203976037107330163390315 10805964055660995245085473)
  ·
    refine ⟨8104473041745746433814105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10805964055660995245085473 8104473041745746433814105)
    ·
      refine ⟨6078354781309309825360579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8104473041745746433814105 6078354781309309825360579)
      ·
        refine ⟨9117532171963964738040869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6078354781309309825360579 9117532171963964738040869)
        ·
          refine ⟨1709537282243243388382663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9117532171963964738040869 1709537282243243388382663)
          ·
            refine ⟨2564305923364865082573995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709537282243243388382663 2564305923364865082573995)
            ·
              refine ⟨3846458885047297623860993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564305923364865082573995 3846458885047297623860993)
              ·
                refine ⟨2884844163785473217895745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3846458885047297623860993 2884844163785473217895745)
                ·
                  refine ⟨2163633122839104913421809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2884844163785473217895745 2163633122839104913421809)
                  ·
                    refine ⟨1622724842129328685066357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2163633122839104913421809 1622724842129328685066357)
                    ·
                      refine ⟨152130453949624564224971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1622724842129328685066357 152130453949624564224971)
                      ·
                        rfl

theorem cell23_296273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_296273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296273 prefixEnd_296273 := by exact prefixLift 296273
  have htrace : WordTrace (prefixWord ++ tailWord_296273) baseStart_296273 baseEnd_296273 := by
    simpa [prefixWord, tailWord_296273, baseEnd_296273] using wordTrace_append hprefix tailTrace_296273
  have hstable : (prefixWord ++ tailWord_296273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296273).length < 2 ^ (prefixWord ++ tailWord_296273).sum := by decide
  have hdescent : baseEnd_296273 < baseStart_296273 := by decide
  rcases family_descends (prefixWord ++ tailWord_296273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296277 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_296277 : Nat := 118140960795 + 296277 * 2 ^ 59
def prefixEnd_296277 : Nat := 4983230072969 + 3 ^ 40 * 296277 * 2
def baseEnd_296277 : Nat := 152132507872242548574953

theorem tailTrace_296277 : CollatzResearch.WordTrace tailWord_296277 prefixEnd_296277 152132507872242548574953 := by
  unfold tailWord_296277
  simp only [CollatzResearch.WordTrace]
  refine ⟨10806109947646503928231085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7204073298431002618820723 10806109947646503928231085)
  ·
    refine ⟨4052291230367438973086657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10806109947646503928231085 4052291230367438973086657)
    ·
      refine ⟨3039218422775579229814993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4052291230367438973086657 3039218422775579229814993)
      ·
        refine ⟨2279413817081684422361245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3039218422775579229814993 2279413817081684422361245)
        ·
          refine ⟨854780181405631658385467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2279413817081684422361245 854780181405631658385467)
          ·
            refine ⟨1282170272108447487578201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854780181405631658385467 1282170272108447487578201)
            ·
              refine ⟨961627704081335615683651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1282170272108447487578201 961627704081335615683651)
              ·
                refine ⟨1442441556122003423525477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961627704081335615683651 1442441556122003423525477)
                ·
                  refine ⟨270457791772875641911027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1442441556122003423525477 270457791772875641911027)
                  ·
                    refine ⟨405686687659313462866541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 270457791772875641911027 405686687659313462866541)
                    ·
                      refine ⟨152132507872242548574953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 405686687659313462866541 152132507872242548574953)
                      ·
                        rfl

theorem cell23_296277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_296277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296277 prefixEnd_296277 := by exact prefixLift 296277
  have htrace : WordTrace (prefixWord ++ tailWord_296277) baseStart_296277 baseEnd_296277 := by
    simpa [prefixWord, tailWord_296277, baseEnd_296277] using wordTrace_append hprefix tailTrace_296277
  have hstable : (prefixWord ++ tailWord_296277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296277).length < 2 ^ (prefixWord ++ tailWord_296277).sum := by decide
  have hdescent : baseEnd_296277 < baseStart_296277 := by decide
  rcases family_descends (prefixWord ++ tailWord_296277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296293 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_296293 : Nat := 118140960795 + 296293 * 2 ^ 59
def prefixEnd_296293 : Nat := 4983230072969 + 3 ^ 40 * 296293 * 2
def baseEnd_296293 : Nat := 50713574520904828658293

theorem tailTrace_296293 : CollatzResearch.WordTrace tailWord_296293 prefixEnd_296293 50713574520904828658293 := by
  unfold tailWord_296293
  simp only [CollatzResearch.WordTrace]
  refine ⟨10806693515588538660813533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7204462343725692440542355 10806693515588538660813533)
  ·
    refine ⟨4052510068345701997805075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10806693515588538660813533 4052510068345701997805075)
    ·
      refine ⟨6078765102518552996707613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4052510068345701997805075 6078765102518552996707613)
      ·
        refine ⟨2279536913444457373765355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6078765102518552996707613 2279536913444457373765355)
        ·
          refine ⟨3419305370166686060648033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2279536913444457373765355 3419305370166686060648033)
          ·
            refine ⟨2564479027625014545486025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3419305370166686060648033 2564479027625014545486025)
            ·
              refine ⟨1923359270718760909114519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2564479027625014545486025 1923359270718760909114519)
              ·
                refine ⟨2885038906078141363671779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923359270718760909114519 2885038906078141363671779)
                ·
                  refine ⟨4327558359117212045507669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2885038906078141363671779 4327558359117212045507669)
                  ·
                    refine ⟨50713574520904828658293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4327558359117212045507669 50713574520904828658293)
                    ·
                      rfl

theorem cell23_296293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_296293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296293 prefixEnd_296293 := by exact prefixLift 296293
  have htrace : WordTrace (prefixWord ++ tailWord_296293) baseStart_296293 baseEnd_296293 := by
    simpa [prefixWord, tailWord_296293, baseEnd_296293] using wordTrace_append hprefix tailTrace_296293
  have hstable : (prefixWord ++ tailWord_296293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296293).length < 2 ^ (prefixWord ++ tailWord_296293).sum := by decide
  have hdescent : baseEnd_296293 < baseStart_296293 := by decide
  rcases family_descends (prefixWord ++ tailWord_296293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296303 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 5]
def baseStart_296303 : Nat := 118140960795 + 296303 * 2 ^ 59
def prefixEnd_296303 : Nat := 4983230072969 + 3 ^ 40 * 296303 * 2
def baseEnd_296303 : Nat := 152145858369259446849833

theorem tailTrace_296303 : CollatzResearch.WordTrace tailWord_296303 prefixEnd_296303 152145858369259446849833 := by
  unfold tailWord_296303
  simp only [CollatzResearch.WordTrace]
  refine ⟨10807058245552310368677563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7204705497034873579118375 10807058245552310368677563)
  ·
    refine ⟨16210587368328465553016345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10807058245552310368677563 16210587368328465553016345)
    ·
      refine ⟨12157940526246349164762259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16210587368328465553016345 12157940526246349164762259)
      ·
        refine ⟨18236910789369523747143389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12157940526246349164762259 18236910789369523747143389)
        ·
          refine ⟨6838841546013571405178771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18236910789369523747143389 6838841546013571405178771)
          ·
            refine ⟨10258262319020357107768157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6838841546013571405178771 10258262319020357107768157)
            ·
              refine ⟨3846848369632633915413059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10258262319020357107768157 3846848369632633915413059)
              ·
                refine ⟨5770272554448950873119589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846848369632633915413059 5770272554448950873119589)
                ·
                  refine ⟨1081926103959178288709923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5770272554448950873119589 1081926103959178288709923)
                  ·
                    refine ⟨1622889155938767433064885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1081926103959178288709923 1622889155938767433064885)
                    ·
                      refine ⟨152145858369259446849833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1622889155938767433064885 152145858369259446849833)
                      ·
                        rfl

theorem cell23_296303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_296303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296303 prefixEnd_296303 := by exact prefixLift 296303
  have htrace : WordTrace (prefixWord ++ tailWord_296303) baseStart_296303 baseEnd_296303 := by
    simpa [prefixWord, tailWord_296303, baseEnd_296303] using wordTrace_append hprefix tailTrace_296303
  have hstable : (prefixWord ++ tailWord_296303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296303).length < 2 ^ (prefixWord ++ tailWord_296303).sum := by decide
  have hdescent : baseEnd_296303 < baseStart_296303 := by decide
  rcases family_descends (prefixWord ++ tailWord_296303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296317 : List Nat := [1, 4, 1, 1, 2, 2, 3, 2, 1, 4, 2]
def baseStart_296317 : Nat := 118140960795 + 296317 * 2 ^ 59
def prefixEnd_296317 : Nat := 4983230072969 + 3 ^ 40 * 296317 * 2
def baseEnd_296317 : Nat := 152153047098422392074769

theorem tailTrace_296317 : CollatzResearch.WordTrace tailWord_296317 prefixEnd_296317 152153047098422392074769 := by
  unfold tailWord_296317
  simp only [CollatzResearch.WordTrace]
  refine ⟨10807568867501590759687205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7205045911667727173124803 10807568867501590759687205)
  ·
    refine ⟨2026419162656548267441351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10807568867501590759687205 2026419162656548267441351)
    ·
      refine ⟨3039628743984822401162027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2026419162656548267441351 3039628743984822401162027)
      ·
        refine ⟨4559443115977233601743041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3039628743984822401162027 4559443115977233601743041)
        ·
          refine ⟨3419582336982925201307281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4559443115977233601743041 3419582336982925201307281)
          ·
            refine ⟨2564686752737193900980461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3419582336982925201307281 2564686752737193900980461)
            ·
              refine ⟨961757532276447712867673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2564686752737193900980461 961757532276447712867673)
              ·
                refine ⟨721318149207335784650755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961757532276447712867673 721318149207335784650755)
                ·
                  refine ⟨1081977223811003676976133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 721318149207335784650755 1081977223811003676976133)
                  ·
                    refine ⟨202870729464563189433025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1081977223811003676976133 202870729464563189433025)
                    ·
                      refine ⟨152153047098422392074769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 202870729464563189433025 152153047098422392074769)
                      ·
                        rfl

theorem cell23_296317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_296317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296317 prefixEnd_296317 := by exact prefixLift 296317
  have htrace : WordTrace (prefixWord ++ tailWord_296317) baseStart_296317 baseEnd_296317 := by
    simpa [prefixWord, tailWord_296317, baseEnd_296317] using wordTrace_append hprefix tailTrace_296317
  have hstable : (prefixWord ++ tailWord_296317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296317).length < 2 ^ (prefixWord ++ tailWord_296317).sum := by decide
  have hdescent : baseEnd_296317 < baseStart_296317 := by decide
  rcases family_descends (prefixWord ++ tailWord_296317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296343 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_296343 : Nat := 118140960795 + 296343 * 2 ^ 59
def prefixEnd_296343 : Nat := 4983230072969 + 3 ^ 40 * 296343 * 2
def baseEnd_296343 : Nat := 152166397595439290349649

theorem tailTrace_296343 : CollatzResearch.WordTrace tailWord_296343 prefixEnd_296343 152166397595439290349649 := by
  unfold tailWord_296343
  simp only [CollatzResearch.WordTrace]
  refine ⟨10808517165407397200133683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7205678110271598133422455 10808517165407397200133683)
  ·
    refine ⟨16212775748111095800200525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10808517165407397200133683 16212775748111095800200525)
    ·
      refine ⟨6079790905541660925075197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16212775748111095800200525 6079790905541660925075197)
      ·
        refine ⟨2279921589578122846903199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6079790905541660925075197 2279921589578122846903199)
        ·
          refine ⟨3419882384367184270354799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2279921589578122846903199 3419882384367184270354799)
          ·
            refine ⟨5129823576550776405532199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3419882384367184270354799 5129823576550776405532199)
            ·
              refine ⟨7694735364826164608298299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5129823576550776405532199 7694735364826164608298299)
              ·
                refine ⟨11542103047239246912447449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7694735364826164608298299 11542103047239246912447449)
                ·
                  refine ⟨8656577285429435184335587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11542103047239246912447449 8656577285429435184335587)
                  ·
                    refine ⟨12984865928144152776503381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8656577285429435184335587 12984865928144152776503381)
                    ·
                      refine ⟨152166397595439290349649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 12984865928144152776503381 152166397595439290349649)
                      ·
                        rfl

theorem cell23_296343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_296343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296343 prefixEnd_296343 := by exact prefixLift 296343
  have htrace : WordTrace (prefixWord ++ tailWord_296343) baseStart_296343 baseEnd_296343 := by
    simpa [prefixWord, tailWord_296343, baseEnd_296343] using wordTrace_append hprefix tailTrace_296343
  have hstable : (prefixWord ++ tailWord_296343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296343).length < 2 ^ (prefixWord ++ tailWord_296343).sum := by decide
  have hdescent : baseEnd_296343 < baseStart_296343 := by decide
  rcases family_descends (prefixWord ++ tailWord_296343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296370 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_296370 : Nat := 118140960795 + 296370 * 2 ^ 59
def prefixEnd_296370 : Nat := 4983230072969 + 3 ^ 40 * 296370 * 2
def baseEnd_296370 : Nat := 50726753857703561570675

theorem tailTrace_296370 : CollatzResearch.WordTrace tailWord_296370 prefixEnd_296370 50726753857703561570675 := by
  unfold tailWord_296370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2702375484077395202841641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7206334624206387207577709 2702375484077395202841641)
  ·
    refine ⟨2026781613058046402131231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2702375484077395202841641 2026781613058046402131231)
    ·
      refine ⟨3040172419587069603196847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2026781613058046402131231 3040172419587069603196847)
      ·
        refine ⟨4560258629380604404795271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040172419587069603196847 4560258629380604404795271)
        ·
          refine ⟨6840387944070906607192907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4560258629380604404795271 6840387944070906607192907)
          ·
            refine ⟨10260581916106359910789361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6840387944070906607192907 10260581916106359910789361)
            ·
              refine ⟨7695436437079769933092021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10260581916106359910789361 7695436437079769933092021)
              ·
                refine ⟨721447165976228431227377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7695436437079769933092021 721447165976228431227377)
                ·
                  refine ⟨541085374482171323420533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 721447165976228431227377 541085374482171323420533)
                  ·
                    refine ⟨50726753857703561570675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 541085374482171323420533 50726753857703561570675)
                    ·
                      rfl

theorem cell23_296370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_296370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296370 prefixEnd_296370 := by exact prefixLift 296370
  have htrace : WordTrace (prefixWord ++ tailWord_296370) baseStart_296370 baseEnd_296370 := by
    simpa [prefixWord, tailWord_296370, baseEnd_296370] using wordTrace_append hprefix tailTrace_296370
  have hstable : (prefixWord ++ tailWord_296370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296370).length < 2 ^ (prefixWord ++ tailWord_296370).sum := by decide
  have hdescent : baseEnd_296370 < baseStart_296370 := by decide
  rcases family_descends (prefixWord ++ tailWord_296370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296383 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 1, 10]
def baseStart_296383 : Nat := 118140960795 + 296383 * 2 ^ 59
def prefixEnd_296383 : Nat := 4983230072969 + 3 ^ 40 * 296383 * 2
def baseEnd_296383 : Nat := 50728978940539711283155

theorem tailTrace_296383 : CollatzResearch.WordTrace tailWord_296383 prefixEnd_296383 50728978940539711283155 := by
  unfold tailWord_296383
  simp only [CollatzResearch.WordTrace]
  refine ⟨10809976085262484031589803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7206650723508322687726535 10809976085262484031589803)
  ·
    refine ⟨16214964127893726047384705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10809976085262484031589803 16214964127893726047384705)
    ·
      refine ⟨12161223095920294535538529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16214964127893726047384705 12161223095920294535538529)
      ·
        refine ⟨9120917321940220901653897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12161223095920294535538529 9120917321940220901653897)
        ·
          refine ⟨6840687991455165676240423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9120917321940220901653897 6840687991455165676240423)
          ·
            refine ⟨10261031987182748514360635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6840687991455165676240423 10261031987182748514360635)
            ·
              refine ⟨15391547980774122771540953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10261031987182748514360635 15391547980774122771540953)
              ·
                refine ⟨11543660985580592078655715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15391547980774122771540953 11543660985580592078655715)
                ·
                  refine ⟨17315491478370888117983573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11543660985580592078655715 17315491478370888117983573)
                  ·
                    refine ⟨50728978940539711283155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 17315491478370888117983573 50728978940539711283155)
                    ·
                      rfl

theorem cell23_296383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_296383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296383 prefixEnd_296383 := by exact prefixLift 296383
  have htrace : WordTrace (prefixWord ++ tailWord_296383) baseStart_296383 baseEnd_296383 := by
    simpa [prefixWord, tailWord_296383, baseEnd_296383] using wordTrace_append hprefix tailTrace_296383
  have hstable : (prefixWord ++ tailWord_296383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296383).length < 2 ^ (prefixWord ++ tailWord_296383).sum := by decide
  have hdescent : baseEnd_296383 < baseStart_296383 := by decide
  rcases family_descends (prefixWord ++ tailWord_296383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296400 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 7, 4]
def baseStart_296400 : Nat := 118140960795 + 296400 * 2 ^ 59
def prefixEnd_296400 : Nat := 4983230072969 + 3 ^ 40 * 296400 * 2
def baseEnd_296400 : Nat := 50731888664248522445629

theorem tailTrace_296400 : CollatzResearch.WordTrace tailWord_296400 prefixEnd_296400 50731888664248522445629 := by
  unfold tailWord_296400
  simp only [CollatzResearch.WordTrace]
  refine ⟨5405298063100447967479327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7207064084133930623305769 5405298063100447967479327)
  ·
    refine ⟨8107947094650671951218991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5405298063100447967479327 8107947094650671951218991)
    ·
      refine ⟨12161920641976007926828487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8107947094650671951218991 12161920641976007926828487)
      ·
        refine ⟨18242880962964011890242731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12161920641976007926828487 18242880962964011890242731)
        ·
          refine ⟨27364321444446017835364097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18242880962964011890242731 27364321444446017835364097)
          ·
            refine ⟨20523241083334513376523073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27364321444446017835364097 20523241083334513376523073)
            ·
              refine ⟨15392430812500885032392305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20523241083334513376523073 15392430812500885032392305)
              ·
                refine ⟨11544323109375663774294229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15392430812500885032392305 11544323109375663774294229)
                ·
                  refine ⟨270570072875992119710021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11544323109375663774294229 270570072875992119710021)
                  ·
                    refine ⟨50731888664248522445629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270570072875992119710021 50731888664248522445629)
                    ·
                      rfl

theorem cell23_296400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 7, 4].length) (baseStart_296400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296400 prefixEnd_296400 := by exact prefixLift 296400
  have htrace : WordTrace (prefixWord ++ tailWord_296400) baseStart_296400 baseEnd_296400 := by
    simpa [prefixWord, tailWord_296400, baseEnd_296400] using wordTrace_append hprefix tailTrace_296400
  have hstable : (prefixWord ++ tailWord_296400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296400).length < 2 ^ (prefixWord ++ tailWord_296400).sum := by decide
  have hdescent : baseEnd_296400 < baseStart_296400 := by decide
  rcases family_descends (prefixWord ++ tailWord_296400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296403 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 10]
def baseStart_296403 : Nat := 118140960795 + 296403 * 2 ^ 59
def prefixEnd_296403 : Nat := 4983230072969 + 3 ^ 40 * 296403 * 2
def baseEnd_296403 : Nat := 152197206434709055599373

theorem tailTrace_296403 : CollatzResearch.WordTrace tailWord_296403 prefixEnd_296403 152197206434709055599373 := by
  unfold tailWord_296403
  simp only [CollatzResearch.WordTrace]
  refine ⟨10810705545190027447317863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7207137030126684964878575 10810705545190027447317863)
  ·
    refine ⟨16216058317785041170976795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10810705545190027447317863 16216058317785041170976795)
    ·
      refine ⟨24324087476677561756465193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16216058317785041170976795 24324087476677561756465193)
      ·
        refine ⟨18243065607508171317348895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24324087476677561756465193 18243065607508171317348895)
        ·
          refine ⟨27364598411262256976023343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18243065607508171317348895 27364598411262256976023343)
          ·
            refine ⟨41046897616893385464035015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27364598411262256976023343 41046897616893385464035015)
            ·
              refine ⟨61570346425340078196052523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41046897616893385464035015 61570346425340078196052523)
              ·
                refine ⟨92355519638010117294078785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61570346425340078196052523 92355519638010117294078785)
                ·
                  refine ⟨69266639728507587970559089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92355519638010117294078785 69266639728507587970559089)
                  ·
                    refine ⟨51949979796380690977919317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69266639728507587970559089 51949979796380690977919317)
                    ·
                      refine ⟨152197206434709055599373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 51949979796380690977919317 152197206434709055599373)
                      ·
                        rfl

theorem cell23_296403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_296403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296403 prefixEnd_296403 := by exact prefixLift 296403
  have htrace : WordTrace (prefixWord ++ tailWord_296403) baseStart_296403 baseEnd_296403 := by
    simpa [prefixWord, tailWord_296403, baseEnd_296403] using wordTrace_append hprefix tailTrace_296403
  have hstable : (prefixWord ++ tailWord_296403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296403).length < 2 ^ (prefixWord ++ tailWord_296403).sum := by decide
  have hdescent : baseEnd_296403 < baseStart_296403 := by decide
  rcases family_descends (prefixWord ++ tailWord_296403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296417 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 3, 4]
def baseStart_296417 : Nat := 118140960795 + 296417 * 2 ^ 59
def prefixEnd_296417 : Nat := 4983230072969 + 3 ^ 40 * 296417 * 2
def baseEnd_296417 : Nat := 50734798387957333608103

theorem tailTrace_296417 : CollatzResearch.WordTrace tailWord_296417 prefixEnd_296417 50734798387957333608103 := by
  unfold tailWord_296417
  simp only [CollatzResearch.WordTrace]
  refine ⟨10811216167139307838327505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7207477444759538558885003 10811216167139307838327505)
  ·
    refine ⟨8108412125354480878745629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10811216167139307838327505 8108412125354480878745629)
    ·
      refine ⟨3040654547007930329529611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8108412125354480878745629 3040654547007930329529611)
      ·
        refine ⟨4560981820511895494294417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3040654547007930329529611 4560981820511895494294417)
        ·
          refine ⟨3420736365383921620720813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4560981820511895494294417 3420736365383921620720813)
          ·
            refine ⟨1282776137018970607770305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3420736365383921620720813 1282776137018970607770305)
            ·
              refine ⟨962082102764227955827729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1282776137018970607770305 962082102764227955827729)
              ·
                refine ⟨721561577073170966870797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962082102764227955827729 721561577073170966870797)
                ·
                  refine ⟨270585591402439112576549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721561577073170966870797 270585591402439112576549)
                  ·
                    refine ⟨50734798387957333608103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270585591402439112576549 50734798387957333608103)
                    ·
                      rfl

theorem cell23_296417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_296417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296417 prefixEnd_296417 := by exact prefixLift 296417
  have htrace : WordTrace (prefixWord ++ tailWord_296417) baseStart_296417 baseEnd_296417 := by
    simpa [prefixWord, tailWord_296417, baseEnd_296417] using wordTrace_append hprefix tailTrace_296417
  have hstable : (prefixWord ++ tailWord_296417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296417).length < 2 ^ (prefixWord ++ tailWord_296417).sum := by decide
  have hdescent : baseEnd_296417 < baseStart_296417 := by decide
  rcases family_descends (prefixWord ++ tailWord_296417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296430 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_296430 : Nat := 118140960795 + 296430 * 2 ^ 59
def prefixEnd_296430 : Nat := 4983230072969 + 3 ^ 40 * 296430 * 2
def baseEnd_296430 : Nat := 16912341156931161106861

theorem tailTrace_296430 : CollatzResearch.WordTrace tailWord_296430 prefixEnd_296430 16912341156931161106861 := by
  unfold tailWord_296430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1351461289511526382318843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7207793544061474039033829 1351461289511526382318843)
  ·
    refine ⟨2027191934267289573478265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1351461289511526382318843 2027191934267289573478265)
    ·
      refine ⟨1520393950700467180108699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2027191934267289573478265 1520393950700467180108699)
      ·
        refine ⟨2280590926050700770163049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1520393950700467180108699 2280590926050700770163049)
        ·
          refine ⟨1710443194538025577622287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2280590926050700770163049 1710443194538025577622287)
          ·
            refine ⟨2565664791807038366433431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710443194538025577622287 2565664791807038366433431)
            ·
              refine ⟨3848497187710557549650147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2565664791807038366433431 3848497187710557549650147)
              ·
                refine ⟨5772745781565836324475221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3848497187710557549650147 5772745781565836324475221)
                ·
                  refine ⟨16912341156931161106861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 5772745781565836324475221 16912341156931161106861)
                  ·
                    rfl

theorem cell23_296430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_296430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296430 prefixEnd_296430 := by exact prefixLift 296430
  have htrace : WordTrace (prefixWord ++ tailWord_296430) baseStart_296430 baseEnd_296430 := by
    simpa [prefixWord, tailWord_296430, baseEnd_296430] using wordTrace_append hprefix tailTrace_296430
  have hstable : (prefixWord ++ tailWord_296430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296430).length < 2 ^ (prefixWord ++ tailWord_296430).sum := by decide
  have hdescent : baseEnd_296430 < baseStart_296430 := by decide
  rcases family_descends (prefixWord ++ tailWord_296430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296477 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_296477 : Nat := 118140960795 + 296477 * 2 ^ 59
def prefixEnd_296477 : Nat := 4983230072969 + 3 ^ 40 * 296477 * 2
def baseEnd_296477 : Nat := 50745068001047255358011

theorem tailTrace_296477 : CollatzResearch.WordTrace tailWord_296477 prefixEnd_296477 50745068001047255358011 := by
  unfold tailWord_296477
  simp only [CollatzResearch.WordTrace]
  refine ⟨10813404546921938085511685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7208936364614625390341123 10813404546921938085511685)
  ·
    refine ⟨2027513352547863391033441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10813404546921938085511685 2027513352547863391033441)
    ·
      refine ⟨1520635014410897543275081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2027513352547863391033441 1520635014410897543275081)
      ·
        refine ⟨1140476260808173157456311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1520635014410897543275081 1140476260808173157456311)
        ·
          refine ⟨1710714391212259736184467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140476260808173157456311 1710714391212259736184467)
          ·
            refine ⟨2566071586818389604276701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710714391212259736184467 2566071586818389604276701)
            ·
              refine ⟨962276845056896101603763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2566071586818389604276701 962276845056896101603763)
              ·
                refine ⟨1443415267585344152405645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962276845056896101603763 1443415267585344152405645)
                ·
                  refine ⟨541280725344504057152117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1443415267585344152405645 541280725344504057152117)
                  ·
                    refine ⟨50745068001047255358011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 541280725344504057152117 50745068001047255358011)
                    ·
                      rfl

theorem cell23_296477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_296477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296477 prefixEnd_296477 := by exact prefixLift 296477
  have htrace : WordTrace (prefixWord ++ tailWord_296477) baseStart_296477 baseEnd_296477 := by
    simpa [prefixWord, tailWord_296477, baseEnd_296477] using wordTrace_append hprefix tailTrace_296477
  have hstable : (prefixWord ++ tailWord_296477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296477).length < 2 ^ (prefixWord ++ tailWord_296477).sum := by decide
  have hdescent : baseEnd_296477 < baseStart_296477 := by decide
  rcases family_descends (prefixWord ++ tailWord_296477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296502 : List Nat := [5, 1, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_296502 : Nat := 118140960795 + 296502 * 2 ^ 59
def prefixEnd_296502 : Nat := 4983230072969 + 3 ^ 40 * 296502 * 2
def baseEnd_296502 : Nat := 50749347006501389420473

theorem tailTrace_296502 : CollatzResearch.WordTrace tailWord_296502 prefixEnd_296502 50749347006501389420473 := by
  unfold tailWord_296502
  simp only [CollatzResearch.WordTrace]
  refine ⟨675894773239460459698235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7209544247887578236781173 675894773239460459698235)
  ·
    refine ⟨1013842159859190689547353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 675894773239460459698235 1013842159859190689547353)
    ·
      refine ⟨760381619894393017160515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1013842159859190689547353 760381619894393017160515)
      ·
        refine ⟨1140572429841589525740773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760381619894393017160515 1140572429841589525740773)
        ·
          refine ⟨213857330595298036076395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1140572429841589525740773 213857330595298036076395)
          ·
            refine ⟨320785995892947054114593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213857330595298036076395 320785995892947054114593)
            ·
              refine ⟨240589496919710290585945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320785995892947054114593 240589496919710290585945)
              ·
                refine ⟨180442122689782717939459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240589496919710290585945 180442122689782717939459)
                ·
                  refine ⟨270663184034674076909189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180442122689782717939459 270663184034674076909189)
                  ·
                    refine ⟨50749347006501389420473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270663184034674076909189 50749347006501389420473)
                    ·
                      rfl

theorem cell23_296502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_296502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296502 prefixEnd_296502 := by exact prefixLift 296502
  have htrace : WordTrace (prefixWord ++ tailWord_296502) baseStart_296502 baseEnd_296502 := by
    simpa [prefixWord, tailWord_296502, baseEnd_296502] using wordTrace_append hprefix tailTrace_296502
  have hstable : (prefixWord ++ tailWord_296502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296502).length < 2 ^ (prefixWord ++ tailWord_296502).sum := by decide
  have hdescent : baseEnd_296502 < baseStart_296502 := by decide
  rcases family_descends (prefixWord ++ tailWord_296502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296508 : List Nat := [2, 2, 2, 2, 4, 1, 1, 4, 1, 1, 3]
def baseStart_296508 : Nat := 118140960795 + 296508 * 2 ^ 59
def prefixEnd_296508 : Nat := 4983230072969 + 3 ^ 40 * 296508 * 2
def baseEnd_296508 : Nat := 152251121903431144786391

theorem tailTrace_296508 : CollatzResearch.WordTrace tailWord_296508 prefixEnd_296508 152251121903431144786391 := by
  unfold tailWord_296508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407267604904815189945089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7209690139873086919926785 5407267604904815189945089)
  ·
    refine ⟨4055450703678611392458817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5407267604904815189945089 4055450703678611392458817)
    ·
      refine ⟨3041588027758958544344113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4055450703678611392458817 3041588027758958544344113)
      ·
        refine ⟨2281191020819218908258085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3041588027758958544344113 2281191020819218908258085)
        ·
          refine ⟨427723316403603545298391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2281191020819218908258085 427723316403603545298391)
          ·
            refine ⟨641584974605405317947587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427723316403603545298391 641584974605405317947587)
            ·
              refine ⟨962377461908107976921381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641584974605405317947587 962377461908107976921381)
              ·
                refine ⟨180445774107770245672759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 962377461908107976921381 180445774107770245672759)
                ·
                  refine ⟨270668661161655368509139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180445774107770245672759 270668661161655368509139)
                  ·
                    refine ⟨406002991742483052763709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 270668661161655368509139 406002991742483052763709)
                    ·
                      refine ⟨152251121903431144786391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 406002991742483052763709 152251121903431144786391)
                      ·
                        rfl

theorem cell23_296508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_296508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296508 prefixEnd_296508 := by exact prefixLift 296508
  have htrace : WordTrace (prefixWord ++ tailWord_296508) baseStart_296508 baseEnd_296508 := by
    simpa [prefixWord, tailWord_296508, baseEnd_296508] using wordTrace_append hprefix tailTrace_296508
  have hstable : (prefixWord ++ tailWord_296508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296508).length < 2 ^ (prefixWord ++ tailWord_296508).sum := by decide
  have hdescent : baseEnd_296508 < baseStart_296508 := by decide
  rcases family_descends (prefixWord ++ tailWord_296508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296517 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 5, 2, 3]
def baseStart_296517 : Nat := 118140960795 + 296517 * 2 ^ 59
def prefixEnd_296517 : Nat := 4983230072969 + 3 ^ 40 * 296517 * 2
def baseEnd_296517 : Nat := 152255743229321609573849

theorem tailTrace_296517 : CollatzResearch.WordTrace tailWord_296517 prefixEnd_296517 152255743229321609573849 := by
  unfold tailWord_296517
  simp only [CollatzResearch.WordTrace]
  refine ⟨10814863466777024916967805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7209908977851349944645203 10814863466777024916967805)
  ·
    refine ⟨4055573800041384343862927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10814863466777024916967805 4055573800041384343862927)
    ·
      refine ⟨6083360700062076515794391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4055573800041384343862927 6083360700062076515794391)
      ·
        refine ⟨9125041050093114773691587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6083360700062076515794391 9125041050093114773691587)
        ·
          refine ⟨13687561575139672160537381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9125041050093114773691587 13687561575139672160537381)
          ·
            refine ⟨2566417795338688530100759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13687561575139672160537381 2566417795338688530100759)
            ·
              refine ⟨3849626693008032795151139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2566417795338688530100759 3849626693008032795151139)
              ·
                refine ⟨5774440039512049192726709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3849626693008032795151139 5774440039512049192726709)
                ·
                  refine ⟨541353753704254611818129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5774440039512049192726709 541353753704254611818129)
                  ·
                    refine ⟨406015315278190958863597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 541353753704254611818129 406015315278190958863597)
                    ·
                      refine ⟨152255743229321609573849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 406015315278190958863597 152255743229321609573849)
                      ·
                        rfl

theorem cell23_296517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_296517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296517 prefixEnd_296517 := by exact prefixLift 296517
  have htrace : WordTrace (prefixWord ++ tailWord_296517) baseStart_296517 baseEnd_296517 := by
    simpa [prefixWord, tailWord_296517, baseEnd_296517] using wordTrace_append hprefix tailTrace_296517
  have hstable : (prefixWord ++ tailWord_296517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296517).length < 2 ^ (prefixWord ++ tailWord_296517).sum := by decide
  have hdescent : baseEnd_296517 < baseStart_296517 := by decide
  rcases family_descends (prefixWord ++ tailWord_296517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296524 : List Nat := [2, 2, 1, 3, 1, 3, 2, 3, 2, 4]
def baseStart_296524 : Nat := 118140960795 + 296524 * 2 ^ 59
def prefixEnd_296524 : Nat := 4983230072969 + 3 ^ 40 * 296524 * 2
def baseEnd_296524 : Nat := 50753112531301027395439

theorem tailTrace_296524 : CollatzResearch.WordTrace tailWord_296524 prefixEnd_296524 50753112531301027395439 := by
  unfold tailWord_296524
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407559388875832556236313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7210079185167776741648417 5407559388875832556236313)
  ·
    refine ⟨4055669541656874417177235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5407559388875832556236313 4055669541656874417177235)
    ·
      refine ⟨6083504312485311625765853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4055669541656874417177235 6083504312485311625765853)
      ·
        refine ⟨2281314117181991859662195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6083504312485311625765853 2281314117181991859662195)
        ·
          refine ⟨3421971175772987789493293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281314117181991859662195 3421971175772987789493293)
          ·
            refine ⟨1283239190914870421059985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3421971175772987789493293 1283239190914870421059985)
            ·
              refine ⟨962429393186152815794989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283239190914870421059985 962429393186152815794989)
              ·
                refine ⟨360911022444807305923121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 962429393186152815794989 360911022444807305923121)
                ·
                  refine ⟨270683266833605479442341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360911022444807305923121 270683266833605479442341)
                  ·
                    refine ⟨50753112531301027395439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270683266833605479442341 50753112531301027395439)
                    ·
                      rfl

theorem cell23_296524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_296524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296524 prefixEnd_296524 := by exact prefixLift 296524
  have htrace : WordTrace (prefixWord ++ tailWord_296524) baseStart_296524 baseEnd_296524 := by
    simpa [prefixWord, tailWord_296524, baseEnd_296524] using wordTrace_append hprefix tailTrace_296524
  have hstable : (prefixWord ++ tailWord_296524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296524).length < 2 ^ (prefixWord ++ tailWord_296524).sum := by decide
  have hdescent : baseEnd_296524 < baseStart_296524 := by decide
  rcases family_descends (prefixWord ++ tailWord_296524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296548 : List Nat := [2, 3, 1, 1, 2, 3, 1, 5, 1, 2, 2]
def baseStart_296548 : Nat := 118140960795 + 296548 * 2 ^ 59
def prefixEnd_296548 : Nat := 4983230072969 + 3 ^ 40 * 296548 * 2
def baseEnd_296548 : Nat := 152271661129610988286207

theorem tailTrace_296548 : CollatzResearch.WordTrace tailWord_296548 prefixEnd_296548 152271661129610988286207 := by
  unfold tailWord_296548
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407997064832358605673149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7210662753109811474230865 5407997064832358605673149)
  ·
    refine ⟨2027998899312134477127431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5407997064832358605673149 2027998899312134477127431)
    ·
      refine ⟨3041998348968201715691147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2027998899312134477127431 3041998348968201715691147)
      ·
        refine ⟨4562997523452302573536721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3041998348968201715691147 4562997523452302573536721)
        ·
          refine ⟨3422248142589226930152541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4562997523452302573536721 3422248142589226930152541)
          ·
            refine ⟨1283343053470960098807203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3422248142589226930152541 1283343053470960098807203)
            ·
              refine ⟨1925014580206440148210805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283343053470960098807203 1925014580206440148210805)
              ·
                refine ⟨180470116894353763894763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1925014580206440148210805 180470116894353763894763)
                ·
                  refine ⟨270705175341530645842145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180470116894353763894763 270705175341530645842145)
                  ·
                    refine ⟨203028881506147984381609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 270705175341530645842145 203028881506147984381609)
                    ·
                      refine ⟨152271661129610988286207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203028881506147984381609 152271661129610988286207)
                      ·
                        rfl

theorem cell23_296548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_296548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296548 prefixEnd_296548 := by exact prefixLift 296548
  have htrace : WordTrace (prefixWord ++ tailWord_296548) baseStart_296548 baseEnd_296548 := by
    simpa [prefixWord, tailWord_296548, baseEnd_296548] using wordTrace_append hprefix tailTrace_296548
  have hstable : (prefixWord ++ tailWord_296548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296548).length < 2 ^ (prefixWord ++ tailWord_296548).sum := by decide
  have hdescent : baseEnd_296548 < baseStart_296548 := by decide
  rcases family_descends (prefixWord ++ tailWord_296548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296551 : List Nat := [1, 1, 5, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_296551 : Nat := 118140960795 + 296551 * 2 ^ 59
def prefixEnd_296551 : Nat := 4983230072969 + 3 ^ 40 * 296551 * 2
def baseEnd_296551 : Nat := 152273201571574476548693

theorem tailTrace_296551 : CollatzResearch.WordTrace tailWord_296551 prefixEnd_296551 152273201571574476548693 := by
  unfold tailWord_296551
  simp only [CollatzResearch.WordTrace]
  refine ⟨10816103548653848723705507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7210735699102565815803671 10816103548653848723705507)
  ·
    refine ⟨16224155322980773085558261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10816103548653848723705507 16224155322980773085558261)
    ·
      refine ⟨1521014561529447476771087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16224155322980773085558261 1521014561529447476771087)
      ·
        refine ⟨2281521842294171215156631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1521014561529447476771087 2281521842294171215156631)
        ·
          refine ⟨3422282763441256822734947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281521842294171215156631 3422282763441256822734947)
          ·
            refine ⟨5133424145161885234102421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3422282763441256822734947 5133424145161885234102421)
            ·
              refine ⟨240629256804463370348551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5133424145161885234102421 240629256804463370348551)
              ·
                refine ⟨360943885206695055522827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240629256804463370348551 360943885206695055522827)
                ·
                  refine ⟨541415827810042583284241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360943885206695055522827 541415827810042583284241)
                  ·
                    refine ⟨406061870857531937463181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 541415827810042583284241 406061870857531937463181)
                    ·
                      refine ⟨152273201571574476548693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 406061870857531937463181 152273201571574476548693)
                      ·
                        rfl

theorem cell23_296551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_296551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296551 prefixEnd_296551 := by exact prefixLift 296551
  have htrace : WordTrace (prefixWord ++ tailWord_296551) baseStart_296551 baseEnd_296551 := by
    simpa [prefixWord, tailWord_296551, baseEnd_296551] using wordTrace_append hprefix tailTrace_296551
  have hstable : (prefixWord ++ tailWord_296551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296551).length < 2 ^ (prefixWord ++ tailWord_296551).sum := by decide
  have hdescent : baseEnd_296551 < baseStart_296551 := by decide
  rcases family_descends (prefixWord ++ tailWord_296551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296558 : List Nat := [4, 1, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_296558 : Nat := 118140960795 + 296558 * 2 ^ 59
def prefixEnd_296558 : Nat := 4983230072969 + 3 ^ 40 * 296558 * 2
def baseEnd_296558 : Nat := 50758931978718649720387

theorem tailTrace_296558 : CollatzResearch.WordTrace tailWord_296558 prefixEnd_296558 50758931978718649720387 := by
  unfold tailWord_296558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1352044857453561114901291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7210905906418992612806885 1352044857453561114901291)
  ·
    refine ⟨2028067286180341672351937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1352044857453561114901291 2028067286180341672351937)
    ·
      refine ⟨1521050464635256254263953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2028067286180341672351937 1521050464635256254263953)
      ·
        refine ⟨1140787848476442190697965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1521050464635256254263953 1140787848476442190697965)
        ·
          refine ⟨427795443178665821511737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1140787848476442190697965 427795443178665821511737)
          ·
            refine ⟨320846582383999366133803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427795443178665821511737 320846582383999366133803)
            ·
              refine ⟨481269873575999049200705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320846582383999366133803 481269873575999049200705)
              ·
                refine ⟨360952405181999286900529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481269873575999049200705 360952405181999286900529)
                ·
                  refine ⟨270714303886499465175397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360952405181999286900529 270714303886499465175397)
                  ·
                    refine ⟨50758931978718649720387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270714303886499465175397 50758931978718649720387)
                    ·
                      rfl

theorem cell23_296558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_296558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296558 prefixEnd_296558 := by exact prefixLift 296558
  have htrace : WordTrace (prefixWord ++ tailWord_296558) baseStart_296558 baseEnd_296558 := by
    simpa [prefixWord, tailWord_296558, baseEnd_296558] using wordTrace_append hprefix tailTrace_296558
  have hstable : (prefixWord ++ tailWord_296558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296558).length < 2 ^ (prefixWord ++ tailWord_296558).sum := by decide
  have hdescent : baseEnd_296558 < baseStart_296558 := by decide
  rcases family_descends (prefixWord ++ tailWord_296558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296565 : List Nat := [1, 3, 4, 2, 1, 1, 2, 4, 1, 2, 2]
def baseStart_296565 : Nat := 118140960795 + 296565 * 2 ^ 59
def prefixEnd_296565 : Nat := 4983230072969 + 3 ^ 40 * 296565 * 2
def baseEnd_296565 : Nat := 152280390300737421773629

theorem tailTrace_296565 : CollatzResearch.WordTrace tailWord_296565 prefixEnd_296565 152280390300737421773629 := by
  unfold tailWord_296565
  simp only [CollatzResearch.WordTrace]
  refine ⟨10816614170603129114715149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7211076113735419409810099 10816614170603129114715149)
  ·
    refine ⟨4056230313976173418018181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10816614170603129114715149 4056230313976173418018181)
    ·
      refine ⟨760543183870532515878409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4056230313976173418018181 760543183870532515878409)
      ·
        refine ⟨570407387902899386908807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 760543183870532515878409 570407387902899386908807)
        ·
          refine ⟨855611081854349080363211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570407387902899386908807 855611081854349080363211)
          ·
            refine ⟨1283416622781523620544817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855611081854349080363211 1283416622781523620544817)
            ·
              refine ⟨962562467086142715408613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283416622781523620544817 962562467086142715408613)
              ·
                refine ⟨180480462578651759139115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 962562467086142715408613 180480462578651759139115)
                ·
                  refine ⟨270720693867977638708673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180480462578651759139115 270720693867977638708673)
                  ·
                    refine ⟨203040520400983229031505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 270720693867977638708673 203040520400983229031505)
                    ·
                      refine ⟨152280390300737421773629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203040520400983229031505 152280390300737421773629)
                      ·
                        rfl

theorem cell23_296565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_296565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296565 prefixEnd_296565 := by exact prefixLift 296565
  have htrace : WordTrace (prefixWord ++ tailWord_296565) baseStart_296565 baseEnd_296565 := by
    simpa [prefixWord, tailWord_296565, baseEnd_296565] using wordTrace_append hprefix tailTrace_296565
  have hstable : (prefixWord ++ tailWord_296565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296565).length < 2 ^ (prefixWord ++ tailWord_296565).sum := by decide
  have hdescent : baseEnd_296565 < baseStart_296565 := by decide
  rcases family_descends (prefixWord ++ tailWord_296565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296616 : List Nat := [2, 1, 7, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_296616 : Nat := 118140960795 + 296616 * 2 ^ 59
def prefixEnd_296616 : Nat := 4983230072969 + 3 ^ 40 * 296616 * 2
def baseEnd_296616 : Nat := 152306577814116722235895

theorem tailTrace_296616 : CollatzResearch.WordTrace tailWord_296616 prefixEnd_296616 152306577814116722235895 := by
  unfold tailWord_296616
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409237146709182412410851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7212316195612243216547801 5409237146709182412410851)
  ·
    refine ⟨8113855720063773618616277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5409237146709182412410851 8113855720063773618616277)
    ·
      refine ⟨190168493438994694186319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8113855720063773618616277 190168493438994694186319)
      ·
        refine ⟨285252740158492041279479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190168493438994694186319 285252740158492041279479)
        ·
          refine ⟨427879110237738061919219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285252740158492041279479 427879110237738061919219)
          ·
            refine ⟨641818665356607092878829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427879110237738061919219 641818665356607092878829)
            ·
              refine ⟨240681999508727659829561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 641818665356607092878829 240681999508727659829561)
              ·
                refine ⟨180511499631545744872171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240681999508727659829561 180511499631545744872171)
                ·
                  refine ⟨270767249447318617308257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180511499631545744872171 270767249447318617308257)
                  ·
                    refine ⟨203075437085488962981193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 270767249447318617308257 203075437085488962981193)
                    ·
                      refine ⟨152306577814116722235895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203075437085488962981193 152306577814116722235895)
                      ·
                        rfl

theorem cell23_296616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_296616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296616 prefixEnd_296616 := by exact prefixLift 296616
  have htrace : WordTrace (prefixWord ++ tailWord_296616) baseStart_296616 baseEnd_296616 := by
    simpa [prefixWord, tailWord_296616, baseEnd_296616] using wordTrace_append hprefix tailTrace_296616
  have hstable : (prefixWord ++ tailWord_296616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296616).length < 2 ^ (prefixWord ++ tailWord_296616).sum := by decide
  have hdescent : baseEnd_296616 < baseStart_296616 := by decide
  rcases family_descends (prefixWord ++ tailWord_296616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296642 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_296642 : Nat := 118140960795 + 296642 * 2 ^ 59
def prefixEnd_296642 : Nat := 4983230072969 + 3 ^ 40 * 296642 * 2
def baseEnd_296642 : Nat := 152319928311133620510775

theorem tailTrace_296642 : CollatzResearch.WordTrace tailWord_296642 prefixEnd_296642 152319928311133620510775 := by
  unfold tailWord_296642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2704855647831042816317045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7212948394216114176845453 2704855647831042816317045)
  ·
    refine ⟨253580216984160264029723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2704855647831042816317045 253580216984160264029723)
    ·
      refine ⟨380370325476240396044585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253580216984160264029723 380370325476240396044585)
      ·
        refine ⟨285277744107180297033439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380370325476240396044585 285277744107180297033439)
        ·
          refine ⟨427916616160770445550159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285277744107180297033439 427916616160770445550159)
          ·
            refine ⟨641874924241155668325239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427916616160770445550159 641874924241155668325239)
            ·
              refine ⟨962812386361733502487859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641874924241155668325239 962812386361733502487859)
              ·
                refine ⟨1444218579542600253731789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962812386361733502487859 1444218579542600253731789)
                ·
                  refine ⟨541581967328475095149421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1444218579542600253731789 541581967328475095149421)
                  ·
                    refine ⟨203093237748178160681033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 541581967328475095149421 203093237748178160681033)
                    ·
                      refine ⟨152319928311133620510775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203093237748178160681033 152319928311133620510775)
                      ·
                        rfl

theorem cell23_296642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_296642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296642 prefixEnd_296642 := by exact prefixLift 296642
  have htrace : WordTrace (prefixWord ++ tailWord_296642) baseStart_296642 baseEnd_296642 := by
    simpa [prefixWord, tailWord_296642, baseEnd_296642] using wordTrace_append hprefix tailTrace_296642
  have hstable : (prefixWord ++ tailWord_296642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296642).length < 2 ^ (prefixWord ++ tailWord_296642).sum := by decide
  have hdescent : baseEnd_296642 < baseStart_296642 := by decide
  rcases family_descends (prefixWord ++ tailWord_296642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296704 : List Nat := [2, 1, 1, 2, 1, 1, 2, 6, 3, 4]
def baseStart_296704 : Nat := 118140960795 + 296704 * 2 ^ 59
def prefixEnd_296704 : Nat := 4983230072969 + 3 ^ 40 * 296704 * 2
def baseEnd_296704 : Nat := 50783921370570792645163

theorem tailTrace_296704 : CollatzResearch.WordTrace tailWord_296704 prefixEnd_296704 50783921370570792645163 := by
  unfold tailWord_296704
  simp only [CollatzResearch.WordTrace]
  refine ⟨5410841958549777927012583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7214455944733037236016777 5410841958549777927012583)
  ·
    refine ⟨8116262937824666890518875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5410841958549777927012583 8116262937824666890518875)
    ·
      refine ⟨12174394406737000335778313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8116262937824666890518875 12174394406737000335778313)
      ·
        refine ⟨9130795805052750251833735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12174394406737000335778313 9130795805052750251833735)
        ·
          refine ⟨13696193707579125377750603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9130795805052750251833735 13696193707579125377750603)
          ·
            refine ⟨20544290561368688066625905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13696193707579125377750603 20544290561368688066625905)
            ·
              refine ⟨15408217921026516049969429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20544290561368688066625905 15408217921026516049969429)
              ·
                refine ⟨722260215048117939842317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15408217921026516049969429 722260215048117939842317)
                ·
                  refine ⟨270847580643044227440869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722260215048117939842317 270847580643044227440869)
                  ·
                    refine ⟨50783921370570792645163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270847580643044227440869 50783921370570792645163)
                    ·
                      rfl

theorem cell23_296704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 3, 4].length) (baseStart_296704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296704 prefixEnd_296704 := by exact prefixLift 296704
  have htrace : WordTrace (prefixWord ++ tailWord_296704) baseStart_296704 baseEnd_296704 := by
    simpa [prefixWord, tailWord_296704, baseEnd_296704] using wordTrace_append hprefix tailTrace_296704
  have hstable : (prefixWord ++ tailWord_296704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296704).length < 2 ^ (prefixWord ++ tailWord_296704).sum := by decide
  have hdescent : baseEnd_296704 < baseStart_296704 := by decide
  rcases family_descends (prefixWord ++ tailWord_296704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296710 : List Nat := [6, 2, 2, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_296710 : Nat := 118140960795 + 296710 * 2 ^ 59
def prefixEnd_296710 : Nat := 4983230072969 + 3 ^ 40 * 296710 * 2
def baseEnd_296710 : Nat := 152354844995639354460463

theorem tailTrace_296710 : CollatzResearch.WordTrace tailWord_296710 prefixEnd_296710 152354844995639354460463 := by
  unfold tailWord_296710
  simp only [CollatzResearch.WordTrace]
  refine ⟨338184461096181839960737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7214601836718545919162389 338184461096181839960737)
  ·
    refine ⟨253638345822136379970553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 338184461096181839960737 253638345822136379970553)
    ·
      refine ⟨190228759366602284977915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253638345822136379970553 190228759366602284977915)
      ·
        refine ⟨285343139049903427466873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190228759366602284977915 285343139049903427466873)
        ·
          refine ⟨214007354287427570600155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285343139049903427466873 214007354287427570600155)
          ·
            refine ⟨321011031431141355900233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214007354287427570600155 321011031431141355900233)
            ·
              refine ⟨240758273573356016925175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321011031431141355900233 240758273573356016925175)
              ·
                refine ⟨361137410360034025387763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240758273573356016925175 361137410360034025387763)
                ·
                  refine ⟨541706115540051038081645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361137410360034025387763 541706115540051038081645)
                  ·
                    refine ⟨203139793327519139280617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 541706115540051038081645 203139793327519139280617)
                    ·
                      refine ⟨152354844995639354460463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203139793327519139280617 152354844995639354460463)
                      ·
                        rfl

theorem cell23_296710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_296710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296710 prefixEnd_296710 := by exact prefixLift 296710
  have htrace : WordTrace (prefixWord ++ tailWord_296710) baseStart_296710 baseEnd_296710 := by
    simpa [prefixWord, tailWord_296710, baseEnd_296710] using wordTrace_append hprefix tailTrace_296710
  have hstable : (prefixWord ++ tailWord_296710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296710).length < 2 ^ (prefixWord ++ tailWord_296710).sum := by decide
  have hdescent : baseEnd_296710 < baseStart_296710 := by decide
  rcases family_descends (prefixWord ++ tailWord_296710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296711 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_296711 : Nat := 118140960795 + 296711 * 2 ^ 59
def prefixEnd_296711 : Nat := 4983230072969 + 3 ^ 40 * 296711 * 2
def baseEnd_296711 : Nat := 152355358476293850547957

theorem tailTrace_296711 : CollatzResearch.WordTrace tailWord_296711 prefixEnd_296711 152355358476293850547957 := by
  unfold tailWord_296711
  simp only [CollatzResearch.WordTrace]
  refine ⟨10821939228074196049529987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7214626152049464033019991 10821939228074196049529987)
  ·
    refine ⟨16232908842111294074294981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10821939228074196049529987 16232908842111294074294981)
    ·
      refine ⟨3043670407895867638930309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16232908842111294074294981 3043670407895867638930309)
      ·
        refine ⟨570688201480475182299433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3043670407895867638930309 570688201480475182299433)
        ·
          refine ⟨428016151110356386724575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570688201480475182299433 428016151110356386724575)
          ·
            refine ⟨642024226665534580086863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428016151110356386724575 642024226665534580086863)
            ·
              refine ⟨963036339998301870130295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 642024226665534580086863 963036339998301870130295)
              ·
                refine ⟨1444554509997452805195443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963036339998301870130295 1444554509997452805195443)
                ·
                  refine ⟨2166831764996179207793165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444554509997452805195443 2166831764996179207793165)
                  ·
                    refine ⟨812561911873567202922437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2166831764996179207793165 812561911873567202922437)
                    ·
                      refine ⟨152355358476293850547957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 812561911873567202922437 152355358476293850547957)
                      ·
                        rfl

theorem cell23_296711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_296711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296711 prefixEnd_296711 := by exact prefixLift 296711
  have htrace : WordTrace (prefixWord ++ tailWord_296711) baseStart_296711 baseEnd_296711 := by
    simpa [prefixWord, tailWord_296711, baseEnd_296711] using wordTrace_append hprefix tailTrace_296711
  have hstable : (prefixWord ++ tailWord_296711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296711).length < 2 ^ (prefixWord ++ tailWord_296711).sum := by decide
  have hdescent : baseEnd_296711 < baseStart_296711 := by decide
  rcases family_descends (prefixWord ++ tailWord_296711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296738 : List Nat := [3, 3, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_296738 : Nat := 118140960795 + 296738 * 2 ^ 59
def prefixEnd_296738 : Nat := 4983230072969 + 3 ^ 40 * 296738 * 2
def baseEnd_296738 : Nat := 50789740817988414970111

theorem tailTrace_296738 : CollatzResearch.WordTrace tailWord_296738 prefixEnd_296738 50789740817988414970111 := by
  unfold tailWord_296738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2705730999744094915190717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7215282665984253107175245 2705730999744094915190717)
  ·
    refine ⟨1014649124904035593196519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2705730999744094915190717 1014649124904035593196519)
    ·
      refine ⟨1521973687356053389794779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014649124904035593196519 1521973687356053389794779)
      ·
        refine ⟨2282960531034080084692169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1521973687356053389794779 2282960531034080084692169)
        ·
          refine ⟨1712220398275560063519127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2282960531034080084692169 1712220398275560063519127)
          ·
            refine ⟨2568330597413340095278691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712220398275560063519127 2568330597413340095278691)
            ·
              refine ⟨3852495896120010142918037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2568330597413340095278691 3852495896120010142918037)
              ·
                refine ⟨180585745130625475449283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3852495896120010142918037 180585745130625475449283)
                ·
                  refine ⟨270878617695938213173925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180585745130625475449283 270878617695938213173925)
                  ·
                    refine ⟨50789740817988414970111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 270878617695938213173925 50789740817988414970111)
                    ·
                      rfl

theorem cell23_296738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_296738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296738 prefixEnd_296738 := by exact prefixLift 296738
  have htrace : WordTrace (prefixWord ++ tailWord_296738) baseStart_296738 baseEnd_296738 := by
    simpa [prefixWord, tailWord_296738, baseEnd_296738] using wordTrace_append hprefix tailTrace_296738
  have hstable : (prefixWord ++ tailWord_296738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296738).length < 2 ^ (prefixWord ++ tailWord_296738).sum := by decide
  have hdescent : baseEnd_296738 < baseStart_296738 := by decide
  rcases family_descends (prefixWord ++ tailWord_296738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296764 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_296764 : Nat := 118140960795 + 296764 * 2 ^ 59
def prefixEnd_296764 : Nat := 4983230072969 + 3 ^ 40 * 296764 * 2
def baseEnd_296764 : Nat := 50794190983660714395071

theorem tailTrace_296764 : CollatzResearch.WordTrace tailWord_296764 prefixEnd_296764 50794190983660714395071 := by
  unfold tailWord_296764
  simp only [CollatzResearch.WordTrace]
  refine ⟨5411936148441093050604673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7215914864588124067472897 5411936148441093050604673)
  ·
    refine ⟨4058952111330819787953505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5411936148441093050604673 4058952111330819787953505)
    ·
      refine ⟨3044214083498114840965129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4058952111330819787953505 3044214083498114840965129)
      ·
        refine ⟨2283160562623586130723847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3044214083498114840965129 2283160562623586130723847)
        ·
          refine ⟨3424740843935379196085771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283160562623586130723847 3424740843935379196085771)
          ·
            refine ⟨5137111265903068794128657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424740843935379196085771 5137111265903068794128657)
            ·
              refine ⟨3852833449427301595596493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5137111265903068794128657 3852833449427301595596493)
              ·
                refine ⟨1444812543535238098348685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3852833449427301595596493 1444812543535238098348685)
                ·
                  refine ⟨541804703825714286880757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1444812543535238098348685 541804703825714286880757)
                  ·
                    refine ⟨50794190983660714395071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 541804703825714286880757 50794190983660714395071)
                    ·
                      rfl

theorem cell23_296764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_296764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296764 prefixEnd_296764 := by exact prefixLift 296764
  have htrace : WordTrace (prefixWord ++ tailWord_296764) baseStart_296764 baseEnd_296764 := by
    simpa [prefixWord, tailWord_296764, baseEnd_296764] using wordTrace_append hprefix tailTrace_296764
  have hstable : (prefixWord ++ tailWord_296764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296764).length < 2 ^ (prefixWord ++ tailWord_296764).sum := by decide
  have hdescent : baseEnd_296764 < baseStart_296764 := by decide
  rcases family_descends (prefixWord ++ tailWord_296764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296771 : List Nat := [1, 1, 1, 3, 1, 5, 2, 1, 1, 5, 2]
def baseStart_296771 : Nat := 118140960795 + 296771 * 2 ^ 59
def prefixEnd_296771 : Nat := 4983230072969 + 3 ^ 40 * 296771 * 2
def baseEnd_296771 : Nat := 152386167315563615797681

theorem tailTrace_296771 : CollatzResearch.WordTrace tailWord_296771 prefixEnd_296771 152386167315563615797681 := by
  unfold tailWord_296771
  simp only [CollatzResearch.WordTrace]
  refine ⟨10824127607856826296714167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7216085071904550864476111 10824127607856826296714167)
  ·
    refine ⟨16236191411785239445071251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10824127607856826296714167 16236191411785239445071251)
    ·
      refine ⟨24354287117677859167606877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16236191411785239445071251 24354287117677859167606877)
      ·
        refine ⟨9132857669129197187852579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24354287117677859167606877 9132857669129197187852579)
        ·
          refine ⟨13699286503693795781778869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9132857669129197187852579 13699286503693795781778869)
          ·
            refine ⟨1284308109721293354541769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13699286503693795781778869 1284308109721293354541769)
            ·
              refine ⟨963231082290970015906327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1284308109721293354541769 963231082290970015906327)
              ·
                refine ⟨1444846623436455023859491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963231082290970015906327 1444846623436455023859491)
                ·
                  refine ⟨2167269935154682535789237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1444846623436455023859491 2167269935154682535789237)
                  ·
                    refine ⟨203181556420751487730241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2167269935154682535789237 203181556420751487730241)
                    ·
                      refine ⟨152386167315563615797681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203181556420751487730241 152386167315563615797681)
                      ·
                        rfl

theorem cell23_296771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 5, 2].length) (baseStart_296771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296771 prefixEnd_296771 := by exact prefixLift 296771
  have htrace : WordTrace (prefixWord ++ tailWord_296771) baseStart_296771 baseEnd_296771 := by
    simpa [prefixWord, tailWord_296771, baseEnd_296771] using wordTrace_append hprefix tailTrace_296771
  have hstable : (prefixWord ++ tailWord_296771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296771).length < 2 ^ (prefixWord ++ tailWord_296771).sum := by decide
  have hdescent : baseEnd_296771 < baseStart_296771 := by decide
  rcases family_descends (prefixWord ++ tailWord_296771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296784 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 4]
def baseStart_296784 : Nat := 118140960795 + 296784 * 2 ^ 59
def prefixEnd_296784 : Nat := 4983230072969 + 3 ^ 40 * 296784 * 2
def baseEnd_296784 : Nat := 152392842564072064935121

theorem tailTrace_296784 : CollatzResearch.WordTrace tailWord_296784 prefixEnd_296784 152392842564072064935121 := by
  unfold tailWord_296784
  simp only [CollatzResearch.WordTrace]
  refine ⟨5412300878404864758468703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7216401171206486344624937 5412300878404864758468703)
  ·
    refine ⟨8118451317607297137703055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5412300878404864758468703 8118451317607297137703055)
    ·
      refine ⟨12177676976410945706554583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8118451317607297137703055 12177676976410945706554583)
      ·
        refine ⟨18266515464616418559831875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12177676976410945706554583 18266515464616418559831875)
        ·
          refine ⟨27399773196924627839747813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18266515464616418559831875 27399773196924627839747813)
          ·
            refine ⟨5137457474423367719952715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27399773196924627839747813 5137457474423367719952715)
            ·
              refine ⟨7706186211635051579929073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5137457474423367719952715 7706186211635051579929073)
              ·
                refine ⟨5779639658726288684946805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7706186211635051579929073 5779639658726288684946805)
                ·
                  refine ⟨541841218005589564213763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5779639658726288684946805 541841218005589564213763)
                  ·
                    refine ⟨812761827008384346320645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 541841218005589564213763 812761827008384346320645)
                    ·
                      refine ⟨152392842564072064935121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 812761827008384346320645 152392842564072064935121)
                      ·
                        rfl

theorem cell23_296784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_296784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296784 prefixEnd_296784 := by exact prefixLift 296784
  have htrace : WordTrace (prefixWord ++ tailWord_296784) baseStart_296784 baseEnd_296784 := by
    simpa [prefixWord, tailWord_296784, baseEnd_296784] using wordTrace_append hprefix tailTrace_296784
  have hstable : (prefixWord ++ tailWord_296784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296784).length < 2 ^ (prefixWord ++ tailWord_296784).sum := by decide
  have hdescent : baseEnd_296784 < baseStart_296784 := by decide
  rcases family_descends (prefixWord ++ tailWord_296784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296788 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 4, 3, 2]
def baseStart_296788 : Nat := 118140960795 + 296788 * 2 ^ 59
def prefixEnd_296788 : Nat := 4983230072969 + 3 ^ 40 * 296788 * 2
def baseEnd_296788 : Nat := 152394896486690049285103

theorem tailTrace_296788 : CollatzResearch.WordTrace tailWord_296788 prefixEnd_296788 152394896486690049285103 := by
  unfold tailWord_296788
  simp only [CollatzResearch.WordTrace]
  refine ⟨5412373824397619100041509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7216498432530158800055345 5412373824397619100041509)
  ·
    refine ⟨1014820092074553581257783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5412373824397619100041509 1014820092074553581257783)
    ·
      refine ⟨1522230138111830371886675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014820092074553581257783 1522230138111830371886675)
      ·
        refine ⟨2283345207167745557830013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1522230138111830371886675 2283345207167745557830013)
        ·
          refine ⟨856254452687904584186255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2283345207167745557830013 856254452687904584186255)
          ·
            refine ⟨1284381679031856876279383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856254452687904584186255 1284381679031856876279383)
            ·
              refine ⟨1926572518547785314419075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284381679031856876279383 1926572518547785314419075)
              ·
                refine ⟨2889858777821677971628613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926572518547785314419075 2889858777821677971628613)
                ·
                  refine ⟨541848520841564619680365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2889858777821677971628613 541848520841564619680365)
                  ·
                    refine ⟨203193195315586732380137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 541848520841564619680365 203193195315586732380137)
                    ·
                      refine ⟨152394896486690049285103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203193195315586732380137 152394896486690049285103)
                      ·
                        rfl

theorem cell23_296788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_296788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296788 prefixEnd_296788 := by exact prefixLift 296788
  have htrace : WordTrace (prefixWord ++ tailWord_296788) baseStart_296788 baseEnd_296788 := by
    simpa [prefixWord, tailWord_296788, baseEnd_296788] using wordTrace_append hprefix tailTrace_296788
  have hstable : (prefixWord ++ tailWord_296788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296788).length < 2 ^ (prefixWord ++ tailWord_296788).sum := by decide
  have hdescent : baseEnd_296788 < baseStart_296788 := by decide
  rcases family_descends (prefixWord ++ tailWord_296788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296818 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 5, 2, 2]
def baseStart_296818 : Nat := 118140960795 + 296818 * 2 ^ 59
def prefixEnd_296818 : Nat := 4983230072969 + 3 ^ 40 * 296818 * 2
def baseEnd_296818 : Nat := 152410300906324931909965

theorem tailTrace_296818 : CollatzResearch.WordTrace tailWord_296818 prefixEnd_296818 152410300906324931909965 := by
  unfold tailWord_296818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706460459671638330918777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7217227892457702215783405 2706460459671638330918777)
  ·
    refine ⟨2029845344753728748189083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2706460459671638330918777 2029845344753728748189083)
    ·
      refine ⟨3044768017130593122283625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2029845344753728748189083 3044768017130593122283625)
      ·
        refine ⟨2283576012847944841712719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3044768017130593122283625 2283576012847944841712719)
        ·
          refine ⟨3425364019271917262569079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283576012847944841712719 3425364019271917262569079)
          ·
            refine ⟨5138046028907875893853619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425364019271917262569079 5138046028907875893853619)
            ·
              refine ⟨7707069043361813840780429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138046028907875893853619 7707069043361813840780429)
              ·
                refine ⟨2890150891260680190292661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7707069043361813840780429 2890150891260680190292661)
                ·
                  refine ⟨270951646055688767839937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2890150891260680190292661 270951646055688767839937)
                  ·
                    refine ⟨203213734541766575879953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 270951646055688767839937 203213734541766575879953)
                    ·
                      refine ⟨152410300906324931909965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203213734541766575879953 152410300906324931909965)
                      ·
                        rfl

theorem cell23_296818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_296818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296818 prefixEnd_296818 := by exact prefixLift 296818
  have htrace : WordTrace (prefixWord ++ tailWord_296818) baseStart_296818 baseEnd_296818 := by
    simpa [prefixWord, tailWord_296818, baseEnd_296818] using wordTrace_append hprefix tailTrace_296818
  have hstable : (prefixWord ++ tailWord_296818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296818).length < 2 ^ (prefixWord ++ tailWord_296818).sum := by decide
  have hdescent : baseEnd_296818 < baseStart_296818 := by decide
  rcases family_descends (prefixWord ++ tailWord_296818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296822 : List Nat := [5, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_296822 : Nat := 118140960795 + 296822 * 2 ^ 59
def prefixEnd_296822 : Nat := 4983230072969 + 3 ^ 40 * 296822 * 2
def baseEnd_296822 : Nat := 152412354828942916259947

theorem tailTrace_296822 : CollatzResearch.WordTrace tailWord_296822 prefixEnd_296822 152412354828942916259947 := by
  unfold tailWord_296822
  simp only [CollatzResearch.WordTrace]
  refine ⟨676624233167003875426295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7217325153781374671213813 676624233167003875426295)
  ·
    refine ⟨1014936349750505813139443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 676624233167003875426295 1014936349750505813139443)
    ·
      refine ⟨1522404524625758719709165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014936349750505813139443 1522404524625758719709165)
      ·
        refine ⟨570901696734659519890937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1522404524625758719709165 570901696734659519890937)
        ·
          refine ⟨428176272550994639918203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570901696734659519890937 428176272550994639918203)
          ·
            refine ⟨642264408826491959877305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428176272550994639918203 642264408826491959877305)
            ·
              refine ⟨481698306619868969907979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642264408826491959877305 481698306619868969907979)
              ·
                refine ⟨722547459929803454861969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481698306619868969907979 722547459929803454861969)
                ·
                  refine ⟨541910594947352591146477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 722547459929803454861969 541910594947352591146477)
                  ·
                    refine ⟨203216473105257221679929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 541910594947352591146477 203216473105257221679929)
                    ·
                      refine ⟨152412354828942916259947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203216473105257221679929 152412354828942916259947)
                      ·
                        rfl

theorem cell23_296822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_296822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296822 prefixEnd_296822 := by exact prefixLift 296822
  have htrace : WordTrace (prefixWord ++ tailWord_296822) baseStart_296822 baseEnd_296822 := by
    simpa [prefixWord, tailWord_296822, baseEnd_296822] using wordTrace_append hprefix tailTrace_296822
  have hstable : (prefixWord ++ tailWord_296822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296822).length < 2 ^ (prefixWord ++ tailWord_296822).sum := by decide
  have hdescent : baseEnd_296822 < baseStart_296822 := by decide
  rcases family_descends (prefixWord ++ tailWord_296822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296846 : List Nat := [4, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3]
def baseStart_296846 : Nat := 118140960795 + 296846 * 2 ^ 59
def prefixEnd_296846 : Nat := 4983230072969 + 3 ^ 40 * 296846 * 2
def baseEnd_296846 : Nat := 152424678364650822359837

theorem tailTrace_296846 : CollatzResearch.WordTrace tailWord_296846 prefixEnd_296846 152424678364650822359837 := by
  unfold tailWord_296846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353357885323139263211799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7217908721723409403796261 1353357885323139263211799)
  ·
    refine ⟨2030036827984708894817699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1353357885323139263211799 2030036827984708894817699)
    ·
      refine ⟨3045055241977063342226549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2030036827984708894817699 3045055241977063342226549)
      ·
        refine ⟨285473928935349688333739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3045055241977063342226549 285473928935349688333739)
        ·
          refine ⟨428210893403024532500609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285473928935349688333739 428210893403024532500609)
          ·
            refine ⟨321158170052268399375457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428210893403024532500609 321158170052268399375457)
            ·
              refine ⟨240868627539201299531593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321158170052268399375457 240868627539201299531593)
              ·
                refine ⟨180651470654400974648695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240868627539201299531593 180651470654400974648695)
                ·
                  refine ⟨270977205981601461973043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180651470654400974648695 270977205981601461973043)
                  ·
                    refine ⟨406465808972402192959565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 270977205981601461973043 406465808972402192959565)
                    ·
                      refine ⟨152424678364650822359837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 406465808972402192959565 152424678364650822359837)
                      ·
                        rfl

theorem cell23_296846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_296846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296846 prefixEnd_296846 := by exact prefixLift 296846
  have htrace : WordTrace (prefixWord ++ tailWord_296846) baseStart_296846 baseEnd_296846 := by
    simpa [prefixWord, tailWord_296846, baseEnd_296846] using wordTrace_append hprefix tailTrace_296846
  have hstable : (prefixWord ++ tailWord_296846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296846).length < 2 ^ (prefixWord ++ tailWord_296846).sum := by decide
  have hdescent : baseEnd_296846 < baseStart_296846 := by decide
  rcases family_descends (prefixWord ++ tailWord_296846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296851 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 8, 1, 3]
def baseStart_296851 : Nat := 118140960795 + 296851 * 2 ^ 59
def prefixEnd_296851 : Nat := 4983230072969 + 3 ^ 40 * 296851 * 2
def baseEnd_296851 : Nat := 152427245767923302797313

theorem tailTrace_296851 : CollatzResearch.WordTrace tailWord_296851 prefixEnd_296851 152427245767923302797313 := by
  unfold tailWord_296851
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827045447566999959626407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7218030298377999973084271 10827045447566999959626407)
  ·
    refine ⟨16240568171350499939439611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10827045447566999959626407 16240568171350499939439611)
    ·
      refine ⟨24360852257025749909159417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16240568171350499939439611 24360852257025749909159417)
      ·
        refine ⟨18270639192769312431869563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24360852257025749909159417 18270639192769312431869563)
        ·
          refine ⟨27405958789153968647804345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18270639192769312431869563 27405958789153968647804345)
          ·
            refine ⟨20554469091865476485853259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27405958789153968647804345 20554469091865476485853259)
            ·
              refine ⟨30831703637798214728779889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20554469091865476485853259 30831703637798214728779889)
              ·
                refine ⟨23123777728348661046584917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30831703637798214728779889 23123777728348661046584917)
                ·
                  refine ⟨270981770254085871639667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23123777728348661046584917 270981770254085871639667)
                  ·
                    refine ⟨406472655381128807459501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 270981770254085871639667 406472655381128807459501)
                    ·
                      refine ⟨152427245767923302797313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 406472655381128807459501 152427245767923302797313)
                      ·
                        rfl

theorem cell23_296851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 1, 3].length) (baseStart_296851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296851 prefixEnd_296851 := by exact prefixLift 296851
  have htrace : WordTrace (prefixWord ++ tailWord_296851) baseStart_296851 baseEnd_296851 := by
    simpa [prefixWord, tailWord_296851, baseEnd_296851] using wordTrace_append hprefix tailTrace_296851
  have hstable : (prefixWord ++ tailWord_296851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296851).length < 2 ^ (prefixWord ++ tailWord_296851).sum := by decide
  have hdescent : baseEnd_296851 < baseStart_296851 := by decide
  rcases family_descends (prefixWord ++ tailWord_296851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296864 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_296864 : Nat := 118140960795 + 296864 * 2 ^ 59
def prefixEnd_296864 : Nat := 4983230072969 + 3 ^ 40 * 296864 * 2
def baseEnd_296864 : Nat := 152433921016431751934753

theorem tailTrace_296864 : CollatzResearch.WordTrace tailWord_296864 prefixEnd_296864 152433921016431751934753 := by
  unfold tailWord_296864
  simp only [CollatzResearch.WordTrace]
  refine ⟨5413759798259951589924823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7218346397679935453233097 5413759798259951589924823)
  ·
    refine ⟨8120639697389927384887235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5413759798259951589924823 8120639697389927384887235)
    ·
      refine ⟨12180959546084891077330853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8120639697389927384887235 12180959546084891077330853)
      ·
        refine ⟨2283929914890917076999535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12180959546084891077330853 2283929914890917076999535)
        ·
          refine ⟨3425894872336375615499303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283929914890917076999535 3425894872336375615499303)
          ·
            refine ⟨5138842308504563423248955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425894872336375615499303 5138842308504563423248955)
            ·
              refine ⟨7708263462756845134873433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138842308504563423248955 7708263462756845134873433)
              ·
                refine ⟨5781197597067633851155075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7708263462756845134873433 5781197597067633851155075)
                ·
                  refine ⟨8671796395601450776732613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5781197597067633851155075 8671796395601450776732613)
                  ·
                    refine ⟨1625961824175272020637365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8671796395601450776732613 1625961824175272020637365)
                    ·
                      refine ⟨152433921016431751934753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1625961824175272020637365 152433921016431751934753)
                      ·
                        rfl

theorem cell23_296864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_296864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296864 prefixEnd_296864 := by exact prefixLift 296864
  have htrace : WordTrace (prefixWord ++ tailWord_296864) baseStart_296864 baseEnd_296864 := by
    simpa [prefixWord, tailWord_296864, baseEnd_296864] using wordTrace_append hprefix tailTrace_296864
  have hstable : (prefixWord ++ tailWord_296864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296864).length < 2 ^ (prefixWord ++ tailWord_296864).sum := by decide
  have hdescent : baseEnd_296864 < baseStart_296864 := by decide
  rcases family_descends (prefixWord ++ tailWord_296864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296868 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_296868 : Nat := 118140960795 + 296868 * 2 ^ 59
def prefixEnd_296868 : Nat := 4983230072969 + 3 ^ 40 * 296868 * 2
def baseEnd_296868 : Nat := 152435974939049736284735

theorem tailTrace_296868 : CollatzResearch.WordTrace tailWord_296868 prefixEnd_296868 152435974939049736284735 := by
  unfold tailWord_296868
  simp only [CollatzResearch.WordTrace]
  refine ⟨5413832744252705931497629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7218443659003607908663505 5413832744252705931497629)
  ·
    refine ⟨2030187279094764724311611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5413832744252705931497629 2030187279094764724311611)
    ·
      refine ⟨3045280918642147086467417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2030187279094764724311611 3045280918642147086467417)
      ·
        refine ⟨2283960688981610314850563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3045280918642147086467417 2283960688981610314850563)
        ·
          refine ⟨3425941033472415472275845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283960688981610314850563 3425941033472415472275845)
          ·
            refine ⟨642363943776077901051721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3425941033472415472275845 642363943776077901051721)
            ·
              refine ⟨481772957832058425788791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642363943776077901051721 481772957832058425788791)
              ·
                refine ⟨722659436748087638683187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481772957832058425788791 722659436748087638683187)
                ·
                  refine ⟨1083989155122131458024781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 722659436748087638683187 1083989155122131458024781)
                  ·
                    refine ⟨406495933170799296759293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1083989155122131458024781 406495933170799296759293)
                    ·
                      refine ⟨152435974939049736284735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 406495933170799296759293 152435974939049736284735)
                      ·
                        rfl

theorem cell23_296868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_296868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296868 prefixEnd_296868 := by exact prefixLift 296868
  have htrace : WordTrace (prefixWord ++ tailWord_296868) baseStart_296868 baseEnd_296868 := by
    simpa [prefixWord, tailWord_296868, baseEnd_296868] using wordTrace_append hprefix tailTrace_296868
  have hstable : (prefixWord ++ tailWord_296868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296868).length < 2 ^ (prefixWord ++ tailWord_296868).sum := by decide
  have hdescent : baseEnd_296868 < baseStart_296868 := by decide
  rcases family_descends (prefixWord ++ tailWord_296868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296931 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 7]
def baseStart_296931 : Nat := 118140960795 + 296931 * 2 ^ 59
def prefixEnd_296931 : Nat := 4983230072969 + 3 ^ 40 * 296931 * 2
def baseEnd_296931 : Nat := 16940924913364776644105

theorem tailTrace_296931 : CollatzResearch.WordTrace tailWord_296931 prefixEnd_296931 16940924913364776644105 := by
  unfold tailWord_296931
  simp only [CollatzResearch.WordTrace]
  refine ⟨10829963287277173622538647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7219975524851449081692431 10829963287277173622538647)
  ·
    refine ⟨16244944930915760433807971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10829963287277173622538647 16244944930915760433807971)
    ·
      refine ⟨24367417396373640650711957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16244944930915760433807971 24367417396373640650711957)
      ·
        refine ⟨1142222690455014405502123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24367417396373640650711957 1142222690455014405502123)
        ·
          refine ⟨1713334035682521608253185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142222690455014405502123 1713334035682521608253185)
          ·
            refine ⟨1285000526761891206189889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1713334035682521608253185 1285000526761891206189889)
            ·
              refine ⟨963750395071418404642417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285000526761891206189889 963750395071418404642417)
              ·
                refine ⟨722812796303563803481813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 963750395071418404642417 722812796303563803481813)
                ·
                  refine ⟨16940924913364776644105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 722812796303563803481813 16940924913364776644105)
                  ·
                    rfl

theorem cell23_296931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 7].length) (baseStart_296931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296931 prefixEnd_296931 := by exact prefixLift 296931
  have htrace : WordTrace (prefixWord ++ tailWord_296931) baseStart_296931 baseEnd_296931 := by
    simpa [prefixWord, tailWord_296931, baseEnd_296931] using wordTrace_append hprefix tailTrace_296931
  have hstable : (prefixWord ++ tailWord_296931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296931).length < 2 ^ (prefixWord ++ tailWord_296931).sum := by decide
  have hdescent : baseEnd_296931 < baseStart_296931 := by decide
  rcases family_descends (prefixWord ++ tailWord_296931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296965 : List Nat := [1, 3, 1, 1, 2, 5, 3, 2, 5]
def baseStart_296965 : Nat := 118140960795 + 296965 * 2 ^ 59
def prefixEnd_296965 : Nat := 4983230072969 + 3 ^ 40 * 296965 * 2
def baseEnd_296965 : Nat := 16942864729170650752421

theorem tailTrace_296965 : CollatzResearch.WordTrace tailWord_296965 prefixEnd_296965 16942864729170650752421 := by
  unfold tailWord_296965
  simp only [CollatzResearch.WordTrace]
  refine ⟨10831203369153997429276349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7220802246102664952850899 10831203369153997429276349)
  ·
    refine ⟨4061701263432749035978631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10831203369153997429276349 4061701263432749035978631)
    ·
      refine ⟨6092551895149123553967947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4061701263432749035978631 6092551895149123553967947)
      ·
        refine ⟨9138827842723685330951921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6092551895149123553967947 9138827842723685330951921)
        ·
          refine ⟨6854120882042763998213941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9138827842723685330951921 6854120882042763998213941)
          ·
            refine ⟨642573832691509124832557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6854120882042763998213941 642573832691509124832557)
            ·
              refine ⟨240965187259315921812209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 642573832691509124832557 240965187259315921812209)
              ·
                refine ⟨180723890444486941359157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240965187259315921812209 180723890444486941359157)
                ·
                  refine ⟨16942864729170650752421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180723890444486941359157 16942864729170650752421)
                  ·
                    rfl

theorem cell23_296965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_296965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296965 prefixEnd_296965 := by exact prefixLift 296965
  have htrace : WordTrace (prefixWord ++ tailWord_296965) baseStart_296965 baseEnd_296965 := by
    simpa [prefixWord, tailWord_296965, baseEnd_296965] using wordTrace_append hprefix tailTrace_296965
  have hstable : (prefixWord ++ tailWord_296965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296965).length < 2 ^ (prefixWord ++ tailWord_296965).sum := by decide
  have hdescent : baseEnd_296965 < baseStart_296965 := by decide
  rcases family_descends (prefixWord ++ tailWord_296965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296968 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 2, 5, 2]
def baseStart_296968 : Nat := 118140960795 + 296968 * 2 ^ 59
def prefixEnd_296968 : Nat := 4983230072969 + 3 ^ 40 * 296968 * 2
def baseEnd_296968 : Nat := 152487323004499345034275

theorem tailTrace_296968 : CollatzResearch.WordTrace tailWord_296968 prefixEnd_296968 152487323004499345034275 := by
  unfold tailWord_296968
  simp only [CollatzResearch.WordTrace]
  refine ⟨5415656394071564470817779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7220875192095419294423705 5415656394071564470817779)
  ·
    refine ⟨8123484591107346706226669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5415656394071564470817779 8123484591107346706226669)
    ·
      refine ⟨3046306721665255014835001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8123484591107346706226669 3046306721665255014835001)
      ·
        refine ⟨2284730041248941261126251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3046306721665255014835001 2284730041248941261126251)
        ·
          refine ⟨3427095061873411891689377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2284730041248941261126251 3427095061873411891689377)
          ·
            refine ⟨2570321296405058918767033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3427095061873411891689377 2570321296405058918767033)
            ·
              refine ⟨1927740972303794189075275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2570321296405058918767033 1927740972303794189075275)
              ·
                refine ⟨2891611458455691283612913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1927740972303794189075275 2891611458455691283612913)
                ·
                  refine ⟨2168708593841768462709685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2891611458455691283612913 2168708593841768462709685)
                  ·
                    refine ⟨203316430672665793379033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2168708593841768462709685 203316430672665793379033)
                    ·
                      refine ⟨152487323004499345034275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203316430672665793379033 152487323004499345034275)
                      ·
                        rfl

theorem cell23_296968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_296968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296968 prefixEnd_296968 := by exact prefixLift 296968
  have htrace : WordTrace (prefixWord ++ tailWord_296968) baseStart_296968 baseEnd_296968 := by
    simpa [prefixWord, tailWord_296968, baseEnd_296968] using wordTrace_append hprefix tailTrace_296968
  have hstable : (prefixWord ++ tailWord_296968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296968).length < 2 ^ (prefixWord ++ tailWord_296968).sum := by decide
  have hdescent : baseEnd_296968 < baseStart_296968 := by decide
  rcases family_descends (prefixWord ++ tailWord_296968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_296971 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 5]
def baseStart_296971 : Nat := 118140960795 + 296971 * 2 ^ 59
def prefixEnd_296971 : Nat := 4983230072969 + 3 ^ 40 * 296971 * 2
def baseEnd_296971 : Nat := 152488863446462833296761

theorem tailTrace_296971 : CollatzResearch.WordTrace tailWord_296971 prefixEnd_296971 152488863446462833296761 := by
  unfold tailWord_296971
  simp only [CollatzResearch.WordTrace]
  refine ⟨10831422207132260453994767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7220948138088173635996511 10831422207132260453994767)
  ·
    refine ⟨16247133310698390680992151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10831422207132260453994767 16247133310698390680992151)
    ·
      refine ⟨24370699966047586021488227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16247133310698390680992151 24370699966047586021488227)
      ·
        refine ⟨36556049949071379032232341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24370699966047586021488227 36556049949071379032232341)
        ·
          refine ⟨1713564841362720892135891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36556049949071379032232341 1713564841362720892135891)
          ·
            refine ⟨2570347262044081338203837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713564841362720892135891 2570347262044081338203837)
            ·
              refine ⟨963880223266530501826439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2570347262044081338203837 963880223266530501826439)
              ·
                refine ⟨1445820334899795752739659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963880223266530501826439 1445820334899795752739659)
                ·
                  refine ⟨2168730502349693629109489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1445820334899795752739659 2168730502349693629109489)
                  ·
                    refine ⟨1626547876762270221832117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2168730502349693629109489 1626547876762270221832117)
                    ·
                      refine ⟨152488863446462833296761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1626547876762270221832117 152488863446462833296761)
                      ·
                        rfl

theorem cell23_296971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 5].length) (baseStart_296971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_296971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_296971 prefixEnd_296971 := by exact prefixLift 296971
  have htrace : WordTrace (prefixWord ++ tailWord_296971) baseStart_296971 baseEnd_296971 := by
    simpa [prefixWord, tailWord_296971, baseEnd_296971] using wordTrace_append hprefix tailTrace_296971
  have hstable : (prefixWord ++ tailWord_296971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_296971).length < 2 ^ (prefixWord ++ tailWord_296971).sum := by decide
  have hdescent : baseEnd_296971 < baseStart_296971 := by decide
  rcases family_descends (prefixWord ++ tailWord_296971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297001 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 7, 4, 3]
def baseStart_297001 : Nat := 118140960795 + 297001 * 2 ^ 59
def prefixEnd_297001 : Nat := 4983230072969 + 3 ^ 40 * 297001 * 2
def baseEnd_297001 : Nat := 152504267866097715921623

theorem tailTrace_297001 : CollatzResearch.WordTrace tailWord_297001 prefixEnd_297001 152504267866097715921623 := by
  unfold tailWord_297001
  simp only [CollatzResearch.WordTrace]
  refine ⟨10832516397023575577586857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7221677598015717051724571 10832516397023575577586857)
  ·
    refine ⟨8124387297767681683190143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10832516397023575577586857 8124387297767681683190143)
    ·
      refine ⟨12186580946651522524785215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8124387297767681683190143 12186580946651522524785215)
      ·
        refine ⟨18279871419977283787177823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12186580946651522524785215 18279871419977283787177823)
        ·
          refine ⟨27419807129965925680766735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18279871419977283787177823 27419807129965925680766735)
          ·
            refine ⟨41129710694948888521150103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27419807129965925680766735 41129710694948888521150103)
            ·
              refine ⟨61694566042423332781725155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41129710694948888521150103 61694566042423332781725155)
              ·
                refine ⟨92541849063634999172587733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61694566042423332781725155 92541849063634999172587733)
                ·
                  refine ⟨2168949587428945293107525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 92541849063634999172587733 2168949587428945293107525)
                  ·
                    refine ⟨406678047642927242457661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2168949587428945293107525 406678047642927242457661)
                    ·
                      refine ⟨152504267866097715921623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 406678047642927242457661 152504267866097715921623)
                      ·
                        rfl

theorem cell23_297001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4, 3].length) (baseStart_297001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297001 prefixEnd_297001 := by exact prefixLift 297001
  have htrace : WordTrace (prefixWord ++ tailWord_297001) baseStart_297001 baseEnd_297001 := by
    simpa [prefixWord, tailWord_297001, baseEnd_297001] using wordTrace_append hprefix tailTrace_297001
  have hstable : (prefixWord ++ tailWord_297001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297001).length < 2 ^ (prefixWord ++ tailWord_297001).sum := by decide
  have hdescent : baseEnd_297001 < baseStart_297001 := by decide
  rcases family_descends (prefixWord ++ tailWord_297001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297038 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_297038 : Nat := 118140960795 + 297038 * 2 ^ 59
def prefixEnd_297038 : Nat := 4983230072969 + 3 ^ 40 * 297038 * 2
def baseEnd_297038 : Nat := 16947029627812674573217

theorem tailTrace_297038 : CollatzResearch.WordTrace tailWord_297038 prefixEnd_297038 16947029627812674573217 := by
  unfold tailWord_297038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354233237236191362085471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7222577265259687264455845 1354233237236191362085471)
  ·
    refine ⟨2031349855854287043128207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1354233237236191362085471 2031349855854287043128207)
    ·
      refine ⟨3047024783781430564692311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2031349855854287043128207 3047024783781430564692311)
      ·
        refine ⟨4570537175672145847038467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3047024783781430564692311 4570537175672145847038467)
        ·
          refine ⟨6855805763508218770557701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4570537175672145847038467 6855805763508218770557701)
          ·
            refine ⟨1285463580657791019479569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6855805763508218770557701 1285463580657791019479569)
            ·
              refine ⟨964097685493343264609677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285463580657791019479569 964097685493343264609677)
              ·
                refine ⟨361536632060003724228629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 964097685493343264609677 361536632060003724228629)
                ·
                  refine ⟨16947029627812674573217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 361536632060003724228629 16947029627812674573217)
                  ·
                    rfl

theorem cell23_297038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_297038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297038 prefixEnd_297038 := by exact prefixLift 297038
  have htrace : WordTrace (prefixWord ++ tailWord_297038) baseStart_297038 baseEnd_297038 := by
    simpa [prefixWord, tailWord_297038, baseEnd_297038] using wordTrace_append hprefix tailTrace_297038
  have hstable : (prefixWord ++ tailWord_297038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297038).length < 2 ^ (prefixWord ++ tailWord_297038).sum := by decide
  have hdescent : baseEnd_297038 < baseStart_297038 := by decide
  rcases family_descends (prefixWord ++ tailWord_297038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297052 : List Nat := [2, 2, 4, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_297052 : Nat := 118140960795 + 297052 * 2 ^ 59
def prefixEnd_297052 : Nat := 4983230072969 + 3 ^ 40 * 297052 * 2
def baseEnd_297052 : Nat := 152530455379477016383889

theorem tailTrace_297052 : CollatzResearch.WordTrace tailWord_297052 prefixEnd_297052 152530455379477016383889 := by
  unfold tailWord_297052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5417188259919405643846705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7222917679892540858462273 5417188259919405643846705)
  ·
    refine ⟨4062891194939554232885029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5417188259919405643846705 4062891194939554232885029)
    ·
      refine ⟨761792099051166418665943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4062891194939554232885029 761792099051166418665943)
      ·
        refine ⟨1142688148576749627998915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761792099051166418665943 1142688148576749627998915)
        ·
          refine ⟨1714032222865124441998373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142688148576749627998915 1714032222865124441998373)
          ·
            refine ⟨321381041787210832874695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1714032222865124441998373 321381041787210832874695)
            ·
              refine ⟨482071562680816249312043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321381041787210832874695 482071562680816249312043)
              ·
                refine ⟨723107344021224373968065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482071562680816249312043 723107344021224373968065)
                ·
                  refine ⟨542330508015918280476049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 723107344021224373968065 542330508015918280476049)
                  ·
                    refine ⟨406747881011938710357037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 542330508015918280476049 406747881011938710357037)
                    ·
                      refine ⟨152530455379477016383889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 406747881011938710357037 152530455379477016383889)
                      ·
                        rfl

theorem cell23_297052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_297052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297052 prefixEnd_297052 := by exact prefixLift 297052
  have htrace : WordTrace (prefixWord ++ tailWord_297052) baseStart_297052 baseEnd_297052 := by
    simpa [prefixWord, tailWord_297052, baseEnd_297052] using wordTrace_append hprefix tailTrace_297052
  have hstable : (prefixWord ++ tailWord_297052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297052).length < 2 ^ (prefixWord ++ tailWord_297052).sum := by decide
  have hdescent : baseEnd_297052 < baseStart_297052 := by decide
  rcases family_descends (prefixWord ++ tailWord_297052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297102 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_297102 : Nat := 118140960795 + 297102 * 2 ^ 59
def prefixEnd_297102 : Nat := 4983230072969 + 3 ^ 40 * 297102 * 2
def baseEnd_297102 : Nat := 50852043137400606919553

theorem tailTrace_297102 : CollatzResearch.WordTrace tailWord_297102 prefixEnd_297102 50852043137400606919553 := by
  unfold tailWord_297102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354525021207208728376695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7224133446438446551342373 1354525021207208728376695)
  ·
    refine ⟨2031787531810813092565043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1354525021207208728376695 2031787531810813092565043)
    ·
      refine ⟨3047681297716219638847565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2031787531810813092565043 3047681297716219638847565)
      ·
        refine ⟨1142880486643582364567837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3047681297716219638847565 1142880486643582364567837)
        ·
          refine ⟨428580182491343386712939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1142880486643582364567837 428580182491343386712939)
          ·
            refine ⟨642870273737015080069409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428580182491343386712939 642870273737015080069409)
            ·
              refine ⟨482152705302761310052057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 642870273737015080069409 482152705302761310052057)
              ·
                refine ⟨361614528977070982539043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482152705302761310052057 361614528977070982539043)
                ·
                  refine ⟨542421793465606473808565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361614528977070982539043 542421793465606473808565)
                  ·
                    refine ⟨50852043137400606919553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 542421793465606473808565 50852043137400606919553)
                    ·
                      rfl

theorem cell23_297102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_297102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297102 prefixEnd_297102 := by exact prefixLift 297102
  have htrace : WordTrace (prefixWord ++ tailWord_297102) baseStart_297102 baseEnd_297102 := by
    simpa [prefixWord, tailWord_297102, baseEnd_297102] using wordTrace_append hprefix tailTrace_297102
  have hstable : (prefixWord ++ tailWord_297102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297102).length < 2 ^ (prefixWord ++ tailWord_297102).sum := by decide
  have hdescent : baseEnd_297102 < baseStart_297102 := by decide
  rcases family_descends (prefixWord ++ tailWord_297102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297122 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_297122 : Nat := 118140960795 + 297122 * 2 ^ 59
def prefixEnd_297122 : Nat := 4983230072969 + 3 ^ 40 * 297122 * 2
def baseEnd_297122 : Nat := 152566399025291742508567

theorem tailTrace_297122 : CollatzResearch.WordTrace tailWord_297122 prefixEnd_297122 152566399025291742508567 := by
  unfold tailWord_297122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709232407396303310685405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7224619753056808828494413 2709232407396303310685405)
  ·
    refine ⟨1015962152773613741507027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2709232407396303310685405 1015962152773613741507027)
    ·
      refine ⟨1523943229160420612260541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1015962152773613741507027 1523943229160420612260541)
      ·
        refine ⟨571478710935157729597703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1523943229160420612260541 571478710935157729597703)
        ·
          refine ⟨857218066402736594396555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571478710935157729597703 857218066402736594396555)
          ·
            refine ⟨1285827099604104891594833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857218066402736594396555 1285827099604104891594833)
            ·
              refine ⟨964370324703078668696125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285827099604104891594833 964370324703078668696125)
              ·
                refine ⟨361638871763654500761047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 964370324703078668696125 361638871763654500761047)
                ·
                  refine ⟨542458307645481751141571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361638871763654500761047 542458307645481751141571)
                  ·
                    refine ⟨813687461468222626712357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 542458307645481751141571 813687461468222626712357)
                    ·
                      refine ⟨152566399025291742508567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 813687461468222626712357 152566399025291742508567)
                      ·
                        rfl

theorem cell23_297122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_297122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297122 prefixEnd_297122 := by exact prefixLift 297122
  have htrace : WordTrace (prefixWord ++ tailWord_297122) baseStart_297122 baseEnd_297122 := by
    simpa [prefixWord, tailWord_297122, baseEnd_297122] using wordTrace_append hprefix tailTrace_297122
  have hstable : (prefixWord ++ tailWord_297122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297122).length < 2 ^ (prefixWord ++ tailWord_297122).sum := by decide
  have hdescent : baseEnd_297122 < baseStart_297122 := by decide
  rcases family_descends (prefixWord ++ tailWord_297122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297125 : List Nat := [1, 3, 1, 2, 1, 3, 1, 5, 1, 2, 3]
def baseStart_297125 : Nat := 118140960795 + 297125 * 2 ^ 59
def prefixEnd_297125 : Nat := 4983230072969 + 3 ^ 40 * 297125 * 2
def baseEnd_297125 : Nat := 152567939467255230771053

theorem tailTrace_297125 : CollatzResearch.WordTrace tailWord_297125 prefixEnd_297125 152567939467255230771053 := by
  unfold tailWord_297125
  simp only [CollatzResearch.WordTrace]
  refine ⟨10837039048574344755100829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7224692699049563170067219 10837039048574344755100829)
  ·
    refine ⟨4063889643215379283162811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10837039048574344755100829 4063889643215379283162811)
    ·
      refine ⟨6095834464823068924744217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4063889643215379283162811 6095834464823068924744217)
      ·
        refine ⟨4571875848617301693558163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6095834464823068924744217 4571875848617301693558163)
        ·
          refine ⟨6857813772925952540337245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4571875848617301693558163 6857813772925952540337245)
          ·
            refine ⟨2571680164847232202626467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6857813772925952540337245 2571680164847232202626467)
            ·
              refine ⟨3857520247270848303939701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571680164847232202626467 3857520247270848303939701)
              ·
                refine ⟨361642523181642028494347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3857520247270848303939701 361642523181642028494347)
                ·
                  refine ⟨542463784772463042741521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 361642523181642028494347 542463784772463042741521)
                  ·
                    refine ⟨406847838579347282056141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 542463784772463042741521 406847838579347282056141)
                    ·
                      refine ⟨152567939467255230771053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 406847838579347282056141 152567939467255230771053)
                      ·
                        rfl

theorem cell23_297125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_297125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297125 prefixEnd_297125 := by exact prefixLift 297125
  have htrace : WordTrace (prefixWord ++ tailWord_297125) baseStart_297125 baseEnd_297125 := by
    simpa [prefixWord, tailWord_297125, baseEnd_297125] using wordTrace_append hprefix tailTrace_297125
  have hstable : (prefixWord ++ tailWord_297125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297125).length < 2 ^ (prefixWord ++ tailWord_297125).sum := by decide
  have hdescent : baseEnd_297125 < baseStart_297125 := by decide
  rcases family_descends (prefixWord ++ tailWord_297125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297188 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_297188 : Nat := 118140960795 + 297188 * 2 ^ 59
def prefixEnd_297188 : Nat := 4983230072969 + 3 ^ 40 * 297188 * 2
def baseEnd_297188 : Nat := 50866762916162828094421

theorem tailTrace_297188 : CollatzResearch.WordTrace tailWord_297188 prefixEnd_297188 50866762916162828094421 := by
  unfold tailWord_297188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5419668423673053257322109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7226224564897404343096145 5419668423673053257322109)
  ·
    refine ⟨2032375658877394971495791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5419668423673053257322109 2032375658877394971495791)
    ·
      refine ⟨3048563488316092457243687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032375658877394971495791 3048563488316092457243687)
      ·
        refine ⟨4572845232474138685865531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048563488316092457243687 4572845232474138685865531)
        ·
          refine ⟨6859267848711208028798297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4572845232474138685865531 6859267848711208028798297)
          ·
            refine ⟨5144450886533406021598723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6859267848711208028798297 5144450886533406021598723)
            ·
              refine ⟨7716676329800109032398085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5144450886533406021598723 7716676329800109032398085)
              ·
                refine ⟨1446876811837520443574641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7716676329800109032398085 1446876811837520443574641)
                ·
                  refine ⟨1085157608878140332680981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1446876811837520443574641 1085157608878140332680981)
                  ·
                    refine ⟨50866762916162828094421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1085157608878140332680981 50866762916162828094421)
                    ·
                      rfl

theorem cell23_297188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_297188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297188 prefixEnd_297188 := by exact prefixLift 297188
  have htrace : WordTrace (prefixWord ++ tailWord_297188) baseStart_297188 baseEnd_297188 := by
    simpa [prefixWord, tailWord_297188, baseEnd_297188] using wordTrace_append hprefix tailTrace_297188
  have hstable : (prefixWord ++ tailWord_297188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297188).length < 2 ^ (prefixWord ++ tailWord_297188).sum := by decide
  have hdescent : baseEnd_297188 < baseStart_297188 := by decide
  rcases family_descends (prefixWord ++ tailWord_297188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297189 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 2, 1, 3]
def baseStart_297189 : Nat := 118140960795 + 297189 * 2 ^ 59
def prefixEnd_297189 : Nat := 4983230072969 + 3 ^ 40 * 297189 * 2
def baseEnd_297189 : Nat := 152600802229142980370759

theorem tailTrace_297189 : CollatzResearch.WordTrace tailWord_297189 prefixEnd_297189 152600802229142980370759 := by
  unfold tailWord_297189
  simp only [CollatzResearch.WordTrace]
  refine ⟨10839373320342483685430621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7226248880228322456953747 10839373320342483685430621)
  ·
    refine ⟨4064764995128431382036483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10839373320342483685430621 4064764995128431382036483)
    ·
      refine ⟨6097147492692647073054725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4064764995128431382036483 6097147492692647073054725)
      ·
        refine ⟨1143215154879871326197761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6097147492692647073054725 1143215154879871326197761)
        ·
          refine ⟨857411366159903494648321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1143215154879871326197761 857411366159903494648321)
          ·
            refine ⟨643058524619927620986241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 857411366159903494648321 643058524619927620986241)
            ·
              refine ⟨482293893464945715739681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643058524619927620986241 482293893464945715739681)
              ·
                refine ⟨361720420098709286804761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 482293893464945715739681 361720420098709286804761)
                ·
                  refine ⟨271290315074031965103571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 361720420098709286804761 271290315074031965103571)
                  ·
                    refine ⟨406935472611047947655357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 271290315074031965103571 406935472611047947655357)
                    ·
                      refine ⟨152600802229142980370759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 406935472611047947655357 152600802229142980370759)
                      ·
                        rfl

theorem cell23_297189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_297189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297189 prefixEnd_297189 := by exact prefixLift 297189
  have htrace : WordTrace (prefixWord ++ tailWord_297189) baseStart_297189 baseEnd_297189 := by
    simpa [prefixWord, tailWord_297189, baseEnd_297189] using wordTrace_append hprefix tailTrace_297189
  have hstable : (prefixWord ++ tailWord_297189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297189).length < 2 ^ (prefixWord ++ tailWord_297189).sum := by decide
  have hdescent : baseEnd_297189 < baseStart_297189 := by decide
  rcases family_descends (prefixWord ++ tailWord_297189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297195 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 3, 4, 2]
def baseStart_297195 : Nat := 118140960795 + 297195 * 2 ^ 59
def prefixEnd_297195 : Nat := 4983230072969 + 3 ^ 40 * 297195 * 2
def baseEnd_297195 : Nat := 152603883113069956895731

theorem tailTrace_297195 : CollatzResearch.WordTrace tailWord_297195 prefixEnd_297195 152603883113069956895731 := by
  unfold tailWord_297195
  simp only [CollatzResearch.WordTrace]
  refine ⟨10839592158320746710149039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7226394772213831140099359 10839592158320746710149039)
  ·
    refine ⟨16259388237481120065223559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10839592158320746710149039 16259388237481120065223559)
    ·
      refine ⟨24389082356221680097835339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16259388237481120065223559 24389082356221680097835339)
      ·
        refine ⟨36583623534332520146753009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24389082356221680097835339 36583623534332520146753009)
        ·
          refine ⟨27437717650749390110064757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36583623534332520146753009 27437717650749390110064757)
          ·
            refine ⟨2572286029757755322818571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27437717650749390110064757 2572286029757755322818571)
            ·
              refine ⟨3858429044636632984227857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2572286029757755322818571 3858429044636632984227857)
              ·
                refine ⟨2893821783477474738170893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3858429044636632984227857 2893821783477474738170893)
                ·
                  refine ⟨1085183168804053026814085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2893821783477474738170893 1085183168804053026814085)
                  ·
                    refine ⟨203471844150759942527641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1085183168804053026814085 203471844150759942527641)
                    ·
                      refine ⟨152603883113069956895731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203471844150759942527641 152603883113069956895731)
                      ·
                        rfl

theorem cell23_297195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 4, 2].length) (baseStart_297195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297195 prefixEnd_297195 := by exact prefixLift 297195
  have htrace : WordTrace (prefixWord ++ tailWord_297195) baseStart_297195 baseEnd_297195 := by
    simpa [prefixWord, tailWord_297195, baseEnd_297195] using wordTrace_append hprefix tailTrace_297195
  have hstable : (prefixWord ++ tailWord_297195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297195).length < 2 ^ (prefixWord ++ tailWord_297195).sum := by decide
  have hdescent : baseEnd_297195 < baseStart_297195 := by decide
  rcases family_descends (prefixWord ++ tailWord_297195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297212 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 1, 4, 2]
def baseStart_297212 : Nat := 118140960795 + 297212 * 2 ^ 59
def prefixEnd_297212 : Nat := 4983230072969 + 3 ^ 40 * 297212 * 2
def baseEnd_297212 : Nat := 152612612284196390383153

theorem tailTrace_297212 : CollatzResearch.WordTrace tailWord_297212 prefixEnd_297212 152612612284196390383153 := by
  unfold tailWord_297212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5420106099629579306758945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7226808132839439075678593 5420106099629579306758945)
  ·
    refine ⟨4065079574722184480069209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5420106099629579306758945 4065079574722184480069209)
    ·
      refine ⟨3048809681041638360051907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4065079574722184480069209 3048809681041638360051907)
      ·
        refine ⟨4573214521562457540077861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048809681041638360051907 4573214521562457540077861)
        ·
          refine ⟨857477722792960788764599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4573214521562457540077861 857477722792960788764599)
          ·
            refine ⟨1286216584189441183146899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857477722792960788764599 1286216584189441183146899)
            ·
              refine ⟨1929324876284161774720349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286216584189441183146899 1929324876284161774720349)
              ·
                refine ⟨723496828606560665520131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1929324876284161774720349 723496828606560665520131)
                ·
                  refine ⟨1085245242909840998280197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 723496828606560665520131 1085245242909840998280197)
                  ·
                    refine ⟨203483483045595187177537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1085245242909840998280197 203483483045595187177537)
                    ·
                      refine ⟨152612612284196390383153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203483483045595187177537 152612612284196390383153)
                      ·
                        rfl

theorem cell23_297212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_297212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297212 prefixEnd_297212 := by exact prefixLift 297212
  have htrace : WordTrace (prefixWord ++ tailWord_297212) baseStart_297212 baseEnd_297212 := by
    simpa [prefixWord, tailWord_297212, baseEnd_297212] using wordTrace_append hprefix tailTrace_297212
  have hstable : (prefixWord ++ tailWord_297212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297212).length < 2 ^ (prefixWord ++ tailWord_297212).sum := by decide
  have hdescent : baseEnd_297212 < baseStart_297212 := by decide
  rcases family_descends (prefixWord ++ tailWord_297212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297252 : List Nat := [2, 3, 1, 3, 1, 2, 2, 4, 5]
def baseStart_297252 : Nat := 118140960795 + 297252 * 2 ^ 59
def prefixEnd_297252 : Nat := 4983230072969 + 3 ^ 40 * 297252 * 2
def baseEnd_297252 : Nat := 16959239056708470431441

theorem tailTrace_297252 : CollatzResearch.WordTrace tailWord_297252 prefixEnd_297252 16959239056708470431441 := by
  unfold tailWord_297252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5420835559557122722487005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7227780746076163629982673 5420835559557122722487005)
  ·
    refine ⟨2032813334833921020932627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5420835559557122722487005 2032813334833921020932627)
    ·
      refine ⟨3049220002250881531398941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032813334833921020932627 3049220002250881531398941)
      ·
        refine ⟨1143457500844080574274603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3049220002250881531398941 1143457500844080574274603)
        ·
          refine ⟨1715186251266120861411905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143457500844080574274603 1715186251266120861411905)
          ·
            refine ⟨1286389688449590646058929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1715186251266120861411905 1286389688449590646058929)
            ·
              refine ⟨964792266337192984544197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286389688449590646058929 964792266337192984544197)
              ·
                refine ⟨180898549938223684602037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 964792266337192984544197 180898549938223684602037)
                ·
                  refine ⟨16959239056708470431441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180898549938223684602037 16959239056708470431441)
                  ·
                    rfl

theorem cell23_297252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_297252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297252 prefixEnd_297252 := by exact prefixLift 297252
  have htrace : WordTrace (prefixWord ++ tailWord_297252) baseStart_297252 baseEnd_297252 := by
    simpa [prefixWord, tailWord_297252, baseEnd_297252] using wordTrace_append hprefix tailTrace_297252
  have hstable : (prefixWord ++ tailWord_297252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297252).length < 2 ^ (prefixWord ++ tailWord_297252).sum := by decide
  have hdescent : baseEnd_297252 < baseStart_297252 := by decide
  rcases family_descends (prefixWord ++ tailWord_297252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297415 : List Nat := [1, 1, 4, 1, 1, 5, 10]
def baseStart_297415 : Nat := 118140960795 + 297415 * 2 ^ 59
def prefixEnd_297415 : Nat := 4983230072969 + 3 ^ 40 * 297415 * 2
def baseEnd_297415 : Nat := 1885393195766161680799

theorem tailTrace_297415 : CollatzResearch.WordTrace tailWord_297415 prefixEnd_297415 1885393195766161680799 := by
  unfold tailWord_297415
  simp only [CollatzResearch.WordTrace]
  refine ⟨10847616217523724283157699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7231744145015816188771799 10847616217523724283157699)
  ·
    refine ⟨16271424326285586424736549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10847616217523724283157699 16271424326285586424736549)
    ·
      refine ⟨3050892061178547454638103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16271424326285586424736549 3050892061178547454638103)
      ·
        refine ⟨4576338091767821181957155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050892061178547454638103 4576338091767821181957155)
        ·
          refine ⟨6864507137651731772935733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4576338091767821181957155 6864507137651731772935733)
          ·
            refine ⟨643547544154849853712725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6864507137651731772935733 643547544154849853712725)
            ·
              refine ⟨1885393195766161680799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 643547544154849853712725 1885393195766161680799)
              ·
                rfl

theorem cell23_297415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 10].length) (baseStart_297415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297415 prefixEnd_297415 := by exact prefixLift 297415
  have htrace : WordTrace (prefixWord ++ tailWord_297415) baseStart_297415 baseEnd_297415 := by
    simpa [prefixWord, tailWord_297415, baseEnd_297415] using wordTrace_append hprefix tailTrace_297415
  have hstable : (prefixWord ++ tailWord_297415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297415).length < 2 ^ (prefixWord ++ tailWord_297415).sum := by decide
  have hdescent : baseEnd_297415 < baseStart_297415 := by decide
  rcases family_descends (prefixWord ++ tailWord_297415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297439 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 4]
def baseStart_297439 : Nat := 118140960795 + 297439 * 2 ^ 59
def prefixEnd_297439 : Nat := 4983230072969 + 3 ^ 40 * 297439 * 2
def baseEnd_297439 : Nat := 152729172392767002244609

theorem tailTrace_297439 : CollatzResearch.WordTrace tailWord_297439 prefixEnd_297439 152729172392767002244609 := by
  unfold tailWord_297439
  simp only [CollatzResearch.WordTrace]
  refine ⟨10848491569436776382031371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7232327712957850921354247 10848491569436776382031371)
  ·
    refine ⟨16272737354155164573047057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10848491569436776382031371 16272737354155164573047057)
    ·
      refine ⟨12204553015616373429785293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16272737354155164573047057 12204553015616373429785293)
      ·
        refine ⟨4576707380856140036169485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12204553015616373429785293 4576707380856140036169485)
        ·
          refine ⟨1716265267821052513563557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4576707380856140036169485 1716265267821052513563557)
          ·
            refine ⟨321799737716447346293167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1716265267821052513563557 321799737716447346293167)
            ·
              refine ⟨482699606574671019439751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321799737716447346293167 482699606574671019439751)
              ·
                refine ⟨724049409862006529159627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482699606574671019439751 724049409862006529159627)
                ·
                  refine ⟨1086074114793009793739441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724049409862006529159627 1086074114793009793739441)
                  ·
                    refine ⟨814555586094757345304581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1086074114793009793739441 814555586094757345304581)
                    ·
                      refine ⟨152729172392767002244609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 814555586094757345304581 152729172392767002244609)
                      ·
                        rfl

theorem cell23_297439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_297439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297439 prefixEnd_297439 := by exact prefixLift 297439
  have htrace : WordTrace (prefixWord ++ tailWord_297439) baseStart_297439 baseEnd_297439 := by
    simpa [prefixWord, tailWord_297439, baseEnd_297439] using wordTrace_append hprefix tailTrace_297439
  have hstable : (prefixWord ++ tailWord_297439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297439).length < 2 ^ (prefixWord ++ tailWord_297439).sum := by decide
  have hdescent : baseEnd_297439 < baseStart_297439 := by decide
  rcases family_descends (prefixWord ++ tailWord_297439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297476 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_297476 : Nat := 118140960795 + 297476 * 2 ^ 59
def prefixEnd_297476 : Nat := 4983230072969 + 3 ^ 40 * 297476 * 2
def baseEnd_297476 : Nat := 152748171176983357481939

theorem tailTrace_297476 : CollatzResearch.WordTrace tailWord_297476 prefixEnd_297476 152748171176983357481939 := by
  unfold tailWord_297476
  simp only [CollatzResearch.WordTrace]
  refine ⟨5424920535151365850564141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7233227380201821134085521 5424920535151365850564141)
  ·
    refine ⟨2034345200681762193961553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5424920535151365850564141 2034345200681762193961553)
    ·
      refine ⟨1525758900511321645471165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2034345200681762193961553 1525758900511321645471165)
      ·
        refine ⟨572159587691745617051687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1525758900511321645471165 572159587691745617051687)
        ·
          refine ⟨858239381537618425577531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572159587691745617051687 858239381537618425577531)
          ·
            refine ⟨1287359072306427638366297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858239381537618425577531 1287359072306427638366297)
            ·
              refine ⟨965519304229820728774723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1287359072306427638366297 965519304229820728774723)
              ·
                refine ⟨1448278956344731093162085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965519304229820728774723 1448278956344731093162085)
                ·
                  refine ⟨271552304314637079967891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1448278956344731093162085 271552304314637079967891)
                  ·
                    refine ⟨407328456471955619951837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 271552304314637079967891 407328456471955619951837)
                    ·
                      refine ⟨152748171176983357481939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 407328456471955619951837 152748171176983357481939)
                      ·
                        rfl

theorem cell23_297476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_297476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297476 prefixEnd_297476 := by exact prefixLift 297476
  have htrace : WordTrace (prefixWord ++ tailWord_297476) baseStart_297476 baseEnd_297476 := by
    simpa [prefixWord, tailWord_297476, baseEnd_297476] using wordTrace_append hprefix tailTrace_297476
  have hstable : (prefixWord ++ tailWord_297476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297476).length < 2 ^ (prefixWord ++ tailWord_297476).sum := by decide
  have hdescent : baseEnd_297476 < baseStart_297476 := by decide
  rcases family_descends (prefixWord ++ tailWord_297476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297482 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_297482 : Nat := 118140960795 + 297482 * 2 ^ 59
def prefixEnd_297482 : Nat := 4983230072969 + 3 ^ 40 * 297482 * 2
def baseEnd_297482 : Nat := 152751252060910334006911

theorem tailTrace_297482 : CollatzResearch.WordTrace tailWord_297482 prefixEnd_297482 152751252060910334006911 := by
  unfold tailWord_297482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2712514977070248681461675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7233373272187329817231133 2712514977070248681461675)
  ·
    refine ⟨4068772465605373022192513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2712514977070248681461675 4068772465605373022192513)
    ·
      refine ⟨3051579349204029766644385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4068772465605373022192513 3051579349204029766644385)
      ·
        refine ⟨2288684511903022324983289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3051579349204029766644385 2288684511903022324983289)
        ·
          refine ⟨1716513383927266743737467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2288684511903022324983289 1716513383927266743737467)
          ·
            refine ⟨2574770075890900115606201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716513383927266743737467 2574770075890900115606201)
            ·
              refine ⟨1931077556918175086704651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2574770075890900115606201 1931077556918175086704651)
              ·
                refine ⟨2896616335377262630056977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931077556918175086704651 2896616335377262630056977)
                ·
                  refine ⟨2172462251532946972542733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2896616335377262630056977 2172462251532946972542733)
                  ·
                    refine ⟨814673344324855114703525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2172462251532946972542733 814673344324855114703525)
                    ·
                      refine ⟨152751252060910334006911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 814673344324855114703525 152751252060910334006911)
                      ·
                        rfl

theorem cell23_297482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_297482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297482 prefixEnd_297482 := by exact prefixLift 297482
  have htrace : WordTrace (prefixWord ++ tailWord_297482) baseStart_297482 baseEnd_297482 := by
    simpa [prefixWord, tailWord_297482, baseEnd_297482] using wordTrace_append hprefix tailTrace_297482
  have hstable : (prefixWord ++ tailWord_297482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297482).length < 2 ^ (prefixWord ++ tailWord_297482).sum := by decide
  have hdescent : baseEnd_297482 < baseStart_297482 := by decide
  rcases family_descends (prefixWord ++ tailWord_297482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297533 : List Nat := [1, 4, 1, 3, 2, 1, 1, 4, 2, 2, 2]
def baseStart_297533 : Nat := 118140960795 + 297533 * 2 ^ 59
def prefixEnd_297533 : Nat := 4983230072969 + 3 ^ 40 * 297533 * 2
def baseEnd_297533 : Nat := 152777439574289634469177

theorem tailTrace_297533 : CollatzResearch.WordTrace tailWord_297533 prefixEnd_297533 152777439574289634469177 := by
  unfold tailWord_297533
  simp only [CollatzResearch.WordTrace]
  refine ⟨10851920031096230435953253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7234613354064153623968835 10851920031096230435953253)
  ·
    refine ⟨2034735005830543206741235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10851920031096230435953253 2034735005830543206741235)
    ·
      refine ⟨3052102508745814810111853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2034735005830543206741235 3052102508745814810111853)
      ·
        refine ⟨1144538440779680553791945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3052102508745814810111853 1144538440779680553791945)
        ·
          refine ⟨858403830584760415343959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1144538440779680553791945 858403830584760415343959)
          ·
            refine ⟨1287605745877140623015939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858403830584760415343959 1287605745877140623015939)
            ·
              refine ⟨1931408618815710934523909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287605745877140623015939 1931408618815710934523909)
              ·
                refine ⟨362139116027945800223233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1931408618815710934523909 362139116027945800223233)
                ·
                  refine ⟨271604337020959350167425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362139116027945800223233 271604337020959350167425)
                  ·
                    refine ⟨203703252765719512625569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 271604337020959350167425 203703252765719512625569)
                    ·
                      refine ⟨152777439574289634469177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203703252765719512625569 152777439574289634469177)
                      ·
                        rfl

theorem cell23_297533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_297533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297533 prefixEnd_297533 := by exact prefixLift 297533
  have htrace : WordTrace (prefixWord ++ tailWord_297533) baseStart_297533 baseEnd_297533 := by
    simpa [prefixWord, tailWord_297533, baseEnd_297533] using wordTrace_append hprefix tailTrace_297533
  have hstable : (prefixWord ++ tailWord_297533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297533).length < 2 ^ (prefixWord ++ tailWord_297533).sum := by decide
  have hdescent : baseEnd_297533 < baseStart_297533 := by decide
  rcases family_descends (prefixWord ++ tailWord_297533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297559 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 2, 5, 2]
def baseStart_297559 : Nat := 118140960795 + 297559 * 2 ^ 59
def prefixEnd_297559 : Nat := 4983230072969 + 3 ^ 40 * 297559 * 2
def baseEnd_297559 : Nat := 152790790071306532744057

theorem tailTrace_297559 : CollatzResearch.WordTrace tailWord_297559 prefixEnd_297559 152790790071306532744057 := by
  unfold tailWord_297559
  simp only [CollatzResearch.WordTrace]
  refine ⟨10852868329002036876399731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7235245552668024584266487 10852868329002036876399731)
  ·
    refine ⟨16279302493503055314599597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10852868329002036876399731 16279302493503055314599597)
    ·
      refine ⟨6104738435063645742974849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16279302493503055314599597 6104738435063645742974849)
      ·
        refine ⟨4578553826297734307231137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6104738435063645742974849 4578553826297734307231137)
        ·
          refine ⟨3433915369723300730423353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4578553826297734307231137 3433915369723300730423353)
          ·
            refine ⟨2575436527292475547817515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3433915369723300730423353 2575436527292475547817515)
            ·
              refine ⟨3863154790938713321726273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575436527292475547817515 3863154790938713321726273)
              ·
                refine ⟨2897366093204034991294705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3863154790938713321726273 2897366093204034991294705)
                ·
                  refine ⟨2173024569903026243471029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2897366093204034991294705 2173024569903026243471029)
                  ·
                    refine ⟨203721053428408710325409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2173024569903026243471029 203721053428408710325409)
                    ·
                      refine ⟨152790790071306532744057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203721053428408710325409 152790790071306532744057)
                      ·
                        rfl

theorem cell23_297559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_297559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297559 prefixEnd_297559 := by exact prefixLift 297559
  have htrace : WordTrace (prefixWord ++ tailWord_297559) baseStart_297559 baseEnd_297559 := by
    simpa [prefixWord, tailWord_297559, baseEnd_297559] using wordTrace_append hprefix tailTrace_297559
  have hstable : (prefixWord ++ tailWord_297559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297559).length < 2 ^ (prefixWord ++ tailWord_297559).sum := by decide
  have hdescent : baseEnd_297559 < baseStart_297559 := by decide
  rcases family_descends (prefixWord ++ tailWord_297559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297569 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 2, 5]
def baseStart_297569 : Nat := 118140960795 + 297569 * 2 ^ 59
def prefixEnd_297569 : Nat := 4983230072969 + 3 ^ 40 * 297569 * 2
def baseEnd_297569 : Nat := 50931974959283831206337

theorem tailTrace_297569 : CollatzResearch.WordTrace tailWord_297569 prefixEnd_297569 50931974959283831206337 := by
  unfold tailWord_297569
  simp only [CollatzResearch.WordTrace]
  refine ⟨10853233058965808584263761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7235488705977205722842507 10853233058965808584263761)
  ·
    refine ⟨8139924794224356438197821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10853233058965808584263761 8139924794224356438197821)
    ·
      refine ⟨3052471797834133664324183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8139924794224356438197821 3052471797834133664324183)
      ·
        refine ⟨4578707696751200496486275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3052471797834133664324183 4578707696751200496486275)
        ·
          refine ⟨6868061545126800744729413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4578707696751200496486275 6868061545126800744729413)
          ·
            refine ⟨1287761539711275139636765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6868061545126800744729413 1287761539711275139636765)
            ·
              refine ⟨482910577391728177363787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1287761539711275139636765 482910577391728177363787)
              ·
                refine ⟨724365866087592266045681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 482910577391728177363787 724365866087592266045681)
                ·
                  refine ⟨543274399565694199534261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 724365866087592266045681 543274399565694199534261)
                  ·
                    refine ⟨50931974959283831206337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 543274399565694199534261 50931974959283831206337)
                    ·
                      rfl

theorem cell23_297569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_297569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297569 prefixEnd_297569 := by exact prefixLift 297569
  have htrace : WordTrace (prefixWord ++ tailWord_297569) baseStart_297569 baseEnd_297569 := by
    simpa [prefixWord, tailWord_297569, baseEnd_297569] using wordTrace_append hprefix tailTrace_297569
  have hstable : (prefixWord ++ tailWord_297569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297569).length < 2 ^ (prefixWord ++ tailWord_297569).sum := by decide
  have hdescent : baseEnd_297569 < baseStart_297569 := by decide
  rcases family_descends (prefixWord ++ tailWord_297569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297646 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_297646 : Nat := 118140960795 + 297646 * 2 ^ 59
def prefixEnd_297646 : Nat := 4983230072969 + 3 ^ 40 * 297646 * 2
def baseEnd_297646 : Nat := 16981718098694188039573

theorem tailTrace_297646 : CollatzResearch.WordTrace tailWord_297646 prefixEnd_297646 16981718098694188039573 := by
  unfold tailWord_297646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357005184960856341852099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7237360986457900489877861 1357005184960856341852099)
  ·
    refine ⟨2035507777441284512778149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1357005184960856341852099 2035507777441284512778149)
    ·
      refine ⟨381657708270240846145903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2035507777441284512778149 381657708270240846145903)
      ·
        refine ⟨572486562405361269218855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381657708270240846145903 572486562405361269218855)
        ·
          refine ⟨858729843608041903828283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572486562405361269218855 858729843608041903828283)
          ·
            refine ⟨1288094765412062855742425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858729843608041903828283 1288094765412062855742425)
            ·
              refine ⟨966071074059047141806819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1288094765412062855742425 966071074059047141806819)
              ·
                refine ⟨1449106611088570712710229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966071074059047141806819 1449106611088570712710229)
                ·
                  refine ⟨16981718098694188039573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1449106611088570712710229 16981718098694188039573)
                  ·
                    rfl

theorem cell23_297646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_297646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297646 prefixEnd_297646 := by exact prefixLift 297646
  have htrace : WordTrace (prefixWord ++ tailWord_297646) baseStart_297646 baseEnd_297646 := by
    simpa [prefixWord, tailWord_297646, baseEnd_297646] using wordTrace_append hprefix tailTrace_297646
  have hstable : (prefixWord ++ tailWord_297646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297646).length < 2 ^ (prefixWord ++ tailWord_297646).sum := by decide
  have hdescent : baseEnd_297646 < baseStart_297646 := by decide
  rcases family_descends (prefixWord ++ tailWord_297646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297676 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_297676 : Nat := 118140960795 + 297676 * 2 ^ 59
def prefixEnd_297676 : Nat := 4983230072969 + 3 ^ 40 * 297676 * 2
def baseEnd_297676 : Nat := 50950289102627524993673

theorem tailTrace_297676 : CollatzResearch.WordTrace tailWord_297676 prefixEnd_297676 50950289102627524993673 := by
  unfold tailWord_297676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5428567834789082929204441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7238090446385443905605921 5428567834789082929204441)
  ·
    refine ⟨4071425876091812196903331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5428567834789082929204441 4071425876091812196903331)
    ·
      refine ⟨6107138814137718295354997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4071425876091812196903331 6107138814137718295354997)
      ·
        refine ⟨572544263825411090189531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6107138814137718295354997 572544263825411090189531)
        ·
          refine ⟨858816395738116635284297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572544263825411090189531 858816395738116635284297)
          ·
            refine ⟨644112296803587476463223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858816395738116635284297 644112296803587476463223)
            ·
              refine ⟨966168445205381214694835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644112296803587476463223 966168445205381214694835)
              ·
                refine ⟨1449252667808071822042253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966168445205381214694835 1449252667808071822042253)
                ·
                  refine ⟨543469750428026933265845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1449252667808071822042253 543469750428026933265845)
                  ·
                    refine ⟨50950289102627524993673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 543469750428026933265845 50950289102627524993673)
                    ·
                      rfl

theorem cell23_297676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_297676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297676 prefixEnd_297676 := by exact prefixLift 297676
  have htrace : WordTrace (prefixWord ++ tailWord_297676) baseStart_297676 baseEnd_297676 := by
    simpa [prefixWord, tailWord_297676, baseEnd_297676] using wordTrace_append hprefix tailTrace_297676
  have hstable : (prefixWord ++ tailWord_297676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297676).length < 2 ^ (prefixWord ++ tailWord_297676).sum := by decide
  have hdescent : baseEnd_297676 < baseStart_297676 := by decide
  rcases family_descends (prefixWord ++ tailWord_297676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297689 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 1, 6]
def baseStart_297689 : Nat := 118140960795 + 297689 * 2 ^ 59
def prefixEnd_297689 : Nat := 4983230072969 + 3 ^ 40 * 297689 * 2
def baseEnd_297689 : Nat := 50952514185463674706153

theorem tailTrace_297689 : CollatzResearch.WordTrace tailWord_297689 prefixEnd_297689 50952514185463674706153 := by
  unfold tailWord_297689
  simp only [CollatzResearch.WordTrace]
  refine ⟨10857609818531069078632121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7238406545687379385754747 10857609818531069078632121)
  ·
    refine ⟨8143207363898301808974091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10857609818531069078632121 8143207363898301808974091)
    ·
      refine ⟨12214811045847452713461137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8143207363898301808974091 12214811045847452713461137)
      ·
        refine ⟨9161108284385589535095853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12214811045847452713461137 9161108284385589535095853)
        ·
          refine ⟨3435415606644596075660945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9161108284385589535095853 3435415606644596075660945)
          ·
            refine ⟨2576561704983447056745709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3435415606644596075660945 2576561704983447056745709)
            ·
              refine ⟨966210639368792646279641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2576561704983447056745709 966210639368792646279641)
              ·
                refine ⟨724657979526594484709731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 966210639368792646279641 724657979526594484709731)
                ·
                  refine ⟨1086986969289891727064597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 724657979526594484709731 1086986969289891727064597)
                  ·
                    refine ⟨50952514185463674706153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1086986969289891727064597 50952514185463674706153)
                    ·
                      rfl

theorem cell23_297689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_297689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297689 prefixEnd_297689 := by exact prefixLift 297689
  have htrace : WordTrace (prefixWord ++ tailWord_297689) baseStart_297689 baseEnd_297689 := by
    simpa [prefixWord, tailWord_297689, baseEnd_297689] using wordTrace_append hprefix tailTrace_297689
  have hstable : (prefixWord ++ tailWord_297689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297689).length < 2 ^ (prefixWord ++ tailWord_297689).sum := by decide
  have hdescent : baseEnd_297689 < baseStart_297689 := by decide
  rcases family_descends (prefixWord ++ tailWord_297689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297713 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 3, 2, 2]
def baseStart_297713 : Nat := 118140960795 + 297713 * 2 ^ 59
def prefixEnd_297713 : Nat := 4983230072969 + 3 ^ 40 * 297713 * 2
def baseEnd_297713 : Nat := 152869866092098930218349

theorem tailTrace_297713 : CollatzResearch.WordTrace tailWord_297713 prefixEnd_297713 152869866092098930218349 := by
  unfold tailWord_297713
  simp only [CollatzResearch.WordTrace]
  refine ⟨10858485170444121177505793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7238990113629414118337195 10858485170444121177505793)
  ·
    refine ⟨8143863877833090883129345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10858485170444121177505793 8143863877833090883129345)
    ·
      refine ⟨6107897908374818162347009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8143863877833090883129345 6107897908374818162347009)
      ·
        refine ⟨4580923431281113621760257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6107897908374818162347009 4580923431281113621760257)
        ·
          refine ⟨3435692573460835216320193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4580923431281113621760257 3435692573460835216320193)
          ·
            refine ⟨2576769430095626412240145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3435692573460835216320193 2576769430095626412240145)
            ·
              refine ⟨1932577072571719809180109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576769430095626412240145 1932577072571719809180109)
              ·
                refine ⟨724716402214394928442541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1932577072571719809180109 724716402214394928442541)
                ·
                  refine ⟨271768650830398098165953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724716402214394928442541 271768650830398098165953)
                  ·
                    refine ⟨203826488122798573624465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 271768650830398098165953 203826488122798573624465)
                    ·
                      refine ⟨152869866092098930218349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203826488122798573624465 152869866092098930218349)
                      ·
                        rfl

theorem cell23_297713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_297713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297713 prefixEnd_297713 := by exact prefixLift 297713
  have htrace : WordTrace (prefixWord ++ tailWord_297713) baseStart_297713 baseEnd_297713 := by
    simpa [prefixWord, tailWord_297713, baseEnd_297713] using wordTrace_append hprefix tailTrace_297713
  have hstable : (prefixWord ++ tailWord_297713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297713).length < 2 ^ (prefixWord ++ tailWord_297713).sum := by decide
  have hdescent : baseEnd_297713 < baseStart_297713 := by decide
  rcases family_descends (prefixWord ++ tailWord_297713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297730 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_297730 : Nat := 118140960795 + 297730 * 2 ^ 59
def prefixEnd_297730 : Nat := 4983230072969 + 3 ^ 40 * 297730 * 2
def baseEnd_297730 : Nat := 152878595263225363705771

theorem tailTrace_297730 : CollatzResearch.WordTrace tailWord_297730 prefixEnd_297730 152878595263225363705771 := by
  unfold tailWord_297730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2714776302845633270218661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7239403474255022053916429 2714776302845633270218661)
  ·
    refine ⟨509020556783556238165999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2714776302845633270218661 509020556783556238165999)
    ·
      refine ⟨763530835175334357248999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509020556783556238165999 763530835175334357248999)
      ·
        refine ⟨1145296252763001535873499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 763530835175334357248999 1145296252763001535873499)
        ·
          refine ⟨1717944379144502303810249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145296252763001535873499 1717944379144502303810249)
          ·
            refine ⟨1288458284358376727857687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1717944379144502303810249 1288458284358376727857687)
            ·
              refine ⟨1932687426537565091786531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288458284358376727857687 1932687426537565091786531)
              ·
                refine ⟨2899031139806347637679797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932687426537565091786531 2899031139806347637679797)
                ·
                  refine ⟨271784169356845091032481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2899031139806347637679797 271784169356845091032481)
                  ·
                    refine ⟨203838127017633818274361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 271784169356845091032481 203838127017633818274361)
                    ·
                      refine ⟨152878595263225363705771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203838127017633818274361 152878595263225363705771)
                      ·
                        rfl

theorem cell23_297730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_297730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297730 prefixEnd_297730 := by exact prefixLift 297730
  have htrace : WordTrace (prefixWord ++ tailWord_297730) baseStart_297730 baseEnd_297730 := by
    simpa [prefixWord, tailWord_297730, baseEnd_297730] using wordTrace_append hprefix tailTrace_297730
  have hstable : (prefixWord ++ tailWord_297730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297730).length < 2 ^ (prefixWord ++ tailWord_297730).sum := by decide
  have hdescent : baseEnd_297730 < baseStart_297730 := by decide
  rcases family_descends (prefixWord ++ tailWord_297730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297736 : List Nat := [2, 1, 3, 2, 2, 3, 3, 7]
def baseStart_297736 : Nat := 118140960795 + 297736 * 2 ^ 59
def prefixEnd_297736 : Nat := 4983230072969 + 3 ^ 40 * 297736 * 2
def baseEnd_297736 : Nat := 5662284301746382971509

theorem tailTrace_297736 : CollatzResearch.WordTrace tailWord_297736 prefixEnd_297736 5662284301746382971509 := by
  unfold tailWord_297736
  simp only [CollatzResearch.WordTrace]
  refine ⟨5429662024680398052796531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7239549366240530737062041 5429662024680398052796531)
  ·
    refine ⟨8144493037020597079194797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5429662024680398052796531 8144493037020597079194797)
    ·
      refine ⟨3054184888882723904698049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8144493037020597079194797 3054184888882723904698049)
      ·
        refine ⟨2290638666662042928523537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3054184888882723904698049 2290638666662042928523537)
        ·
          refine ⟨1717978999996532196392653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2290638666662042928523537 1717978999996532196392653)
          ·
            refine ⟨644242124998699573647245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1717978999996532196392653 644242124998699573647245)
            ·
              refine ⟨241590796874512340117717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 644242124998699573647245 241590796874512340117717)
              ·
                refine ⟨5662284301746382971509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 241590796874512340117717 5662284301746382971509)
                ·
                  rfl

theorem cell23_297736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 7].length) (baseStart_297736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297736 prefixEnd_297736 := by exact prefixLift 297736
  have htrace : WordTrace (prefixWord ++ tailWord_297736) baseStart_297736 baseEnd_297736 := by
    simpa [prefixWord, tailWord_297736, baseEnd_297736] using wordTrace_append hprefix tailTrace_297736
  have hstable : (prefixWord ++ tailWord_297736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297736).length < 2 ^ (prefixWord ++ tailWord_297736).sum := by decide
  have hdescent : baseEnd_297736 < baseStart_297736 := by decide
  rcases family_descends (prefixWord ++ tailWord_297736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297757 : List Nat := [1, 4, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_297757 : Nat := 118140960795 + 297757 * 2 ^ 59
def prefixEnd_297757 : Nat := 4983230072969 + 3 ^ 40 * 297757 * 2
def baseEnd_297757 : Nat := 50964153080298919356049

theorem tailTrace_297757 : CollatzResearch.WordTrace tailWord_297757 prefixEnd_297757 50964153080298919356049 := by
  unfold tailWord_297757
  simp only [CollatzResearch.WordTrace]
  refine ⟨10860089982284716692107525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7240059988189811128071683 10860089982284716692107525)
  ·
    refine ⟨2036266871678384379770161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10860089982284716692107525 2036266871678384379770161)
    ·
      refine ⟨1527200153758788284827621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2036266871678384379770161 1527200153758788284827621)
      ·
        refine ⟨286350028829772803405179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1527200153758788284827621 286350028829772803405179)
        ·
          refine ⟨429525043244659205107769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286350028829772803405179 429525043244659205107769)
          ·
            refine ⟨322143782433494403830827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429525043244659205107769 322143782433494403830827)
            ·
              refine ⟨483215673650241605746241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322143782433494403830827 483215673650241605746241)
              ·
                refine ⟨362411755237681204309681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483215673650241605746241 362411755237681204309681)
                ·
                  refine ⟨271808816428260903232261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362411755237681204309681 271808816428260903232261)
                  ·
                    refine ⟨50964153080298919356049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 271808816428260903232261 50964153080298919356049)
                    ·
                      rfl

theorem cell23_297757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_297757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297757 prefixEnd_297757 := by exact prefixLift 297757
  have htrace : WordTrace (prefixWord ++ tailWord_297757) baseStart_297757 baseEnd_297757 := by
    simpa [prefixWord, tailWord_297757, baseEnd_297757] using wordTrace_append hprefix tailTrace_297757
  have hstable : (prefixWord ++ tailWord_297757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297757).length < 2 ^ (prefixWord ++ tailWord_297757).sum := by decide
  have hdescent : baseEnd_297757 < baseStart_297757 := by decide
  rcases family_descends (prefixWord ++ tailWord_297757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297798 : List Nat := [6, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2]
def baseStart_297798 : Nat := 118140960795 + 297798 * 2 ^ 59
def prefixEnd_297798 : Nat := 4983230072969 + 3 ^ 40 * 297798 * 2
def baseEnd_297798 : Nat := 152913511947731097655459

theorem tailTrace_297798 : CollatzResearch.WordTrace tailWord_297798 prefixEnd_297798 152913511947731097655459 := by
  unfold tailWord_297798
  simp only [CollatzResearch.WordTrace]
  refine ⟨339424542973005646698439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7241056916757453796233365 339424542973005646698439)
  ·
    refine ⟨509136814459508470047659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 339424542973005646698439 509136814459508470047659)
    ·
      refine ⟨763705221689262705071489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509136814459508470047659 763705221689262705071489)
      ·
        refine ⟨572778916266947028803617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 763705221689262705071489 572778916266947028803617)
        ·
          refine ⟨429584187200210271602713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 572778916266947028803617 429584187200210271602713)
          ·
            refine ⟨322188140400157703702035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429584187200210271602713 322188140400157703702035)
            ·
              refine ⟨483282210600236555553053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322188140400157703702035 483282210600236555553053)
              ·
                refine ⟨181230828975088708332395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 483282210600236555553053 181230828975088708332395)
                ·
                  refine ⟨271846243462633062498593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181230828975088708332395 271846243462633062498593)
                  ·
                    refine ⟨203884682596974796873945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 271846243462633062498593 203884682596974796873945)
                    ·
                      refine ⟨152913511947731097655459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 203884682596974796873945 152913511947731097655459)
                      ·
                        rfl

theorem cell23_297798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_297798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297798 prefixEnd_297798 := by exact prefixLift 297798
  have htrace : WordTrace (prefixWord ++ tailWord_297798) baseStart_297798 baseEnd_297798 := by
    simpa [prefixWord, tailWord_297798, baseEnd_297798] using wordTrace_append hprefix tailTrace_297798
  have hstable : (prefixWord ++ tailWord_297798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297798).length < 2 ^ (prefixWord ++ tailWord_297798).sum := by decide
  have hdescent : baseEnd_297798 < baseStart_297798 := by decide
  rcases family_descends (prefixWord ++ tailWord_297798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297836 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 3]
def baseStart_297836 : Nat := 118140960795 + 297836 * 2 ^ 59
def prefixEnd_297836 : Nat := 4983230072969 + 3 ^ 40 * 297836 * 2
def baseEnd_297836 : Nat := 152933024212601948980283

theorem tailTrace_297836 : CollatzResearch.WordTrace tailWord_297836 prefixEnd_297836 152933024212601948980283 := by
  unfold tailWord_297836
  simp only [CollatzResearch.WordTrace]
  refine ⟨5431485674499256592116681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7241980899332342122822241 5431485674499256592116681)
  ·
    refine ⟨4073614255874442444087511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5431485674499256592116681 4073614255874442444087511)
    ·
      refine ⟨6110421383811663666131267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4073614255874442444087511 6110421383811663666131267)
      ·
        refine ⟨9165632075717495499196901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6110421383811663666131267 9165632075717495499196901)
        ·
          refine ⟨1718556014197030406099419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9165632075717495499196901 1718556014197030406099419)
          ·
            refine ⟨2577834021295545609149129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1718556014197030406099419 2577834021295545609149129)
            ·
              refine ⟨1933375515971659206861847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2577834021295545609149129 1933375515971659206861847)
              ·
                refine ⟨2900063273957488810292771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933375515971659206861847 2900063273957488810292771)
                ·
                  refine ⟨4350094910936233215439157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900063273957488810292771 4350094910936233215439157)
                  ·
                    refine ⟨407821397900271863947421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4350094910936233215439157 407821397900271863947421)
                    ·
                      refine ⟨152933024212601948980283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 407821397900271863947421 152933024212601948980283)
                      ·
                        rfl

theorem cell23_297836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_297836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297836 prefixEnd_297836 := by exact prefixLift 297836
  have htrace : WordTrace (prefixWord ++ tailWord_297836) baseStart_297836 baseEnd_297836 := by
    simpa [prefixWord, tailWord_297836, baseEnd_297836] using wordTrace_append hprefix tailTrace_297836
  have hstable : (prefixWord ++ tailWord_297836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297836).length < 2 ^ (prefixWord ++ tailWord_297836).sum := by decide
  have hdescent : baseEnd_297836 < baseStart_297836 := by decide
  rcases family_descends (prefixWord ++ tailWord_297836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297839 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 3, 7]
def baseStart_297839 : Nat := 118140960795 + 297839 * 2 ^ 59
def prefixEnd_297839 : Nat := 4983230072969 + 3 ^ 40 * 297839 * 2
def baseEnd_297839 : Nat := 50978188218188479080923

theorem tailTrace_297839 : CollatzResearch.WordTrace tailWord_297839 prefixEnd_297839 50978188218188479080923 := by
  unfold tailWord_297839
  simp only [CollatzResearch.WordTrace]
  refine ⟨10863080767987644696592571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7242053845325096464395047 10863080767987644696592571)
  ·
    refine ⟨16294621151981467044888857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10863080767987644696592571 16294621151981467044888857)
    ·
      refine ⟨12220965863986100283666643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16294621151981467044888857 12220965863986100283666643)
      ·
        refine ⟨18331448795979150425499965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12220965863986100283666643 18331448795979150425499965)
        ·
          refine ⟨6874293298492181409562487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18331448795979150425499965 6874293298492181409562487)
          ·
            refine ⟨10311439947738272114343731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6874293298492181409562487 10311439947738272114343731)
            ·
              refine ⟨15467159921607408171515597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10311439947738272114343731 15467159921607408171515597)
              ·
                refine ⟨5800184970602778064318349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15467159921607408171515597 5800184970602778064318349)
                ·
                  refine ⟨2175069363976041774119381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5800184970602778064318349 2175069363976041774119381)
                  ·
                    refine ⟨50978188218188479080923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2175069363976041774119381 50978188218188479080923)
                    ·
                      rfl

theorem cell23_297839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_297839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297839 prefixEnd_297839 := by exact prefixLift 297839
  have htrace : WordTrace (prefixWord ++ tailWord_297839) baseStart_297839 baseEnd_297839 := by
    simpa [prefixWord, tailWord_297839, baseEnd_297839] using wordTrace_append hprefix tailTrace_297839
  have hstable : (prefixWord ++ tailWord_297839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297839).length < 2 ^ (prefixWord ++ tailWord_297839).sum := by decide
  have hdescent : baseEnd_297839 < baseStart_297839 := by decide
  rcases family_descends (prefixWord ++ tailWord_297839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297913 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 1, 4, 3]
def baseStart_297913 : Nat := 118140960795 + 297913 * 2 ^ 59
def prefixEnd_297913 : Nat := 4983230072969 + 3 ^ 40 * 297913 * 2
def baseEnd_297913 : Nat := 152972562222998147717429

theorem tailTrace_297913 : CollatzResearch.WordTrace tailWord_297913 prefixEnd_297913 152972562222998147717429 := by
  unfold tailWord_297913
  simp only [CollatzResearch.WordTrace]
  refine ⟨10865779769719555334786393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7243853179813036889857595 10865779769719555334786393)
  ·
    refine ⟨8149334827289666501089795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10865779769719555334786393 8149334827289666501089795)
    ·
      refine ⟨12224002240934499751634693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8149334827289666501089795 12224002240934499751634693)
      ·
        refine ⟨2292000420175218703431505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12224002240934499751634693 2292000420175218703431505)
        ·
          refine ⟨1719000315131414027573629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2292000420175218703431505 1719000315131414027573629)
          ·
            refine ⟨644625118174280260340111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1719000315131414027573629 644625118174280260340111)
            ·
              refine ⟨966937677261420390510167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644625118174280260340111 966937677261420390510167)
              ·
                refine ⟨1450406515892130585765251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 966937677261420390510167 1450406515892130585765251)
                ·
                  refine ⟨2175609773838195878647877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450406515892130585765251 2175609773838195878647877)
                  ·
                    refine ⟨407926832594661727246477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2175609773838195878647877 407926832594661727246477)
                    ·
                      refine ⟨152972562222998147717429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 407926832594661727246477 152972562222998147717429)
                      ·
                        rfl

theorem cell23_297913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_297913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297913 prefixEnd_297913 := by exact prefixLift 297913
  have htrace : WordTrace (prefixWord ++ tailWord_297913) baseStart_297913 baseEnd_297913 := by
    simpa [prefixWord, tailWord_297913, baseEnd_297913] using wordTrace_append hprefix tailTrace_297913
  have hstable : (prefixWord ++ tailWord_297913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297913).length < 2 ^ (prefixWord ++ tailWord_297913).sum := by decide
  have hdescent : baseEnd_297913 < baseStart_297913 := by decide
  rcases family_descends (prefixWord ++ tailWord_297913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297920 : List Nat := [2, 1, 1, 2, 3, 3, 1, 5, 1, 4]
def baseStart_297920 : Nat := 118140960795 + 297920 * 2 ^ 59
def prefixEnd_297920 : Nat := 4983230072969 + 3 ^ 40 * 297920 * 2
def baseEnd_297920 : Nat := 50992052195859873443299

theorem tailTrace_297920 : CollatzResearch.WordTrace tailWord_297920 prefixEnd_297920 50992052195859873443299 := by
  unfold tailWord_297920
  simp only [CollatzResearch.WordTrace]
  refine ⟨5433017540347097765145607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7244023387129463686860809 5433017540347097765145607)
  ·
    refine ⟨8149526310520646647718411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5433017540347097765145607 8149526310520646647718411)
    ·
      refine ⟨12224289465780969971577617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8149526310520646647718411 12224289465780969971577617)
      ·
        refine ⟨9168217099335727478683213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12224289465780969971577617 9168217099335727478683213)
        ·
          refine ⟨3438081412250897804506205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9168217099335727478683213 3438081412250897804506205)
          ·
            refine ⟨1289280529594086676689827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3438081412250897804506205 1289280529594086676689827)
            ·
              refine ⟨1933920794391130015034741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289280529594086676689827 1933920794391130015034741)
              ·
                refine ⟨181305074474168438909507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1933920794391130015034741 181305074474168438909507)
                ·
                  refine ⟨271957611711252658364261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181305074474168438909507 271957611711252658364261)
                  ·
                    refine ⟨50992052195859873443299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 271957611711252658364261 50992052195859873443299)
                    ·
                      rfl

theorem cell23_297920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 5, 1, 4].length) (baseStart_297920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297920 prefixEnd_297920 := by exact prefixLift 297920
  have htrace : WordTrace (prefixWord ++ tailWord_297920) baseStart_297920 baseEnd_297920 := by
    simpa [prefixWord, tailWord_297920, baseEnd_297920] using wordTrace_append hprefix tailTrace_297920
  have hstable : (prefixWord ++ tailWord_297920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297920).length < 2 ^ (prefixWord ++ tailWord_297920).sum := by decide
  have hdescent : baseEnd_297920 < baseStart_297920 := by decide
  rcases family_descends (prefixWord ++ tailWord_297920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297960 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 3, 1, 3]
def baseStart_297960 : Nat := 118140960795 + 297960 * 2 ^ 59
def prefixEnd_297960 : Nat := 4983230072969 + 3 ^ 40 * 297960 * 2
def baseEnd_297960 : Nat := 152996695813759463829713

theorem tailTrace_297960 : CollatzResearch.WordTrace tailWord_297960 prefixEnd_297960 152996695813759463829713 := by
  unfold tailWord_297960
  simp only [CollatzResearch.WordTrace]
  refine ⟨5433747000274641180873667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7244996000366188241164889 5433747000274641180873667)
  ·
    refine ⟨8150620500411961771310501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5433747000274641180873667 8150620500411961771310501)
    ·
      refine ⟨1528241343827242832120719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8150620500411961771310501 1528241343827242832120719)
      ·
        refine ⟨2292362015740864248181079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1528241343827242832120719 2292362015740864248181079)
        ·
          refine ⟨3438543023611296372271619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292362015740864248181079 3438543023611296372271619)
          ·
            refine ⟨5157814535416944558407429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438543023611296372271619 5157814535416944558407429)
            ·
              refine ⟨967090225390677104701393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5157814535416944558407429 967090225390677104701393)
              ·
                refine ⟨725317669043007828526045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967090225390677104701393 725317669043007828526045)
                ·
                  refine ⟨271994125891127935697267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725317669043007828526045 271994125891127935697267)
                  ·
                    refine ⟨407991188836691903545901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 271994125891127935697267 407991188836691903545901)
                    ·
                      refine ⟨152996695813759463829713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 407991188836691903545901 152996695813759463829713)
                      ·
                        rfl

theorem cell23_297960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_297960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297960 prefixEnd_297960 := by exact prefixLift 297960
  have htrace : WordTrace (prefixWord ++ tailWord_297960) baseStart_297960 baseEnd_297960 := by
    simpa [prefixWord, tailWord_297960, baseEnd_297960] using wordTrace_append hprefix tailTrace_297960
  have hstable : (prefixWord ++ tailWord_297960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297960).length < 2 ^ (prefixWord ++ tailWord_297960).sum := by decide
  have hdescent : baseEnd_297960 < baseStart_297960 := by decide
  rcases family_descends (prefixWord ++ tailWord_297960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_297976 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 3, 6]
def baseStart_297976 : Nat := 118140960795 + 297976 * 2 ^ 59
def prefixEnd_297976 : Nat := 4983230072969 + 3 ^ 40 * 297976 * 2
def baseEnd_297976 : Nat := 51001637168077133743213

theorem tailTrace_297976 : CollatzResearch.WordTrace tailWord_297976 prefixEnd_297976 51001637168077133743213 := by
  unfold tailWord_297976
  simp only [CollatzResearch.WordTrace]
  refine ⟨5434038784245658547164891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7245385045660878062886521 5434038784245658547164891)
  ·
    refine ⟨8151058176368487820747337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5434038784245658547164891 8151058176368487820747337)
    ·
      refine ⟨6113293632276365865560503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8151058176368487820747337 6113293632276365865560503)
      ·
        refine ⟨9169940448414548798340755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6113293632276365865560503 9169940448414548798340755)
        ·
          refine ⟨13754910672621823197511133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9169940448414548798340755 13754910672621823197511133)
          ·
            refine ⟨5158091502233183699066675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13754910672621823197511133 5158091502233183699066675)
            ·
              refine ⟨7737137253349775548600013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5158091502233183699066675 7737137253349775548600013)
              ·
                refine ⟨2901426470006165830725005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7737137253349775548600013 2901426470006165830725005)
                ·
                  refine ⟨1088034926252312186521877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2901426470006165830725005 1088034926252312186521877)
                  ·
                    refine ⟨51001637168077133743213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1088034926252312186521877 51001637168077133743213)
                    ·
                      rfl

theorem cell23_297976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_297976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_297976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_297976 prefixEnd_297976 := by exact prefixLift 297976
  have htrace : WordTrace (prefixWord ++ tailWord_297976) baseStart_297976 baseEnd_297976 := by
    simpa [prefixWord, tailWord_297976, baseEnd_297976] using wordTrace_append hprefix tailTrace_297976
  have hstable : (prefixWord ++ tailWord_297976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_297976).length < 2 ^ (prefixWord ++ tailWord_297976).sum := by decide
  have hdescent : baseEnd_297976 < baseStart_297976 := by decide
  rcases family_descends (prefixWord ++ tailWord_297976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298003 : List Nat := [1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 3]
def baseStart_298003 : Nat := 118140960795 + 298003 * 2 ^ 59
def prefixEnd_298003 : Nat := 4983230072969 + 3 ^ 40 * 298003 * 2
def baseEnd_298003 : Nat := 153018775481902795592015

theorem tailTrace_298003 : CollatzResearch.WordTrace tailWord_298003 prefixEnd_298003 153018775481902795592015 := by
  unfold tailWord_298003
  simp only [CollatzResearch.WordTrace]
  refine ⟨10869062339393500705562663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7246041559595667137041775 10869062339393500705562663)
  ·
    refine ⟨16303593509090251058343995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10869062339393500705562663 16303593509090251058343995)
    ·
      refine ⟨24455390263635376587515993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16303593509090251058343995 24455390263635376587515993)
      ·
        refine ⟨18341542697726532440636995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24455390263635376587515993 18341542697726532440636995)
        ·
          refine ⟨27512314046589798660955493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18341542697726532440636995 27512314046589798660955493)
          ·
            refine ⟨5158558883735587248929155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27512314046589798660955493 5158558883735587248929155)
            ·
              refine ⟨7737838325603380873393733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5158558883735587248929155 7737838325603380873393733)
              ·
                refine ⟨1450844686050633913761325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7737838325603380873393733 1450844686050633913761325)
                ·
                  refine ⟨544066757268987717660497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1450844686050633913761325 544066757268987717660497)
                  ·
                    refine ⟨408050067951740788245373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 544066757268987717660497 408050067951740788245373)
                    ·
                      refine ⟨153018775481902795592015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 408050067951740788245373 153018775481902795592015)
                      ·
                        rfl

theorem cell23_298003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 3].length) (baseStart_298003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298003 prefixEnd_298003 := by exact prefixLift 298003
  have htrace : WordTrace (prefixWord ++ tailWord_298003) baseStart_298003 baseEnd_298003 := by
    simpa [prefixWord, tailWord_298003, baseEnd_298003] using wordTrace_append hprefix tailTrace_298003
  have hstable : (prefixWord ++ tailWord_298003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298003).length < 2 ^ (prefixWord ++ tailWord_298003).sum := by decide
  have hdescent : baseEnd_298003 < baseStart_298003 := by decide
  rcases family_descends (prefixWord ++ tailWord_298003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298010 : List Nat := [3, 1, 1, 3, 1, 2, 3, 3, 2, 4]
def baseStart_298010 : Nat := 118140960795 + 298010 * 2 ^ 59
def prefixEnd_298010 : Nat := 4983230072969 + 3 ^ 40 * 298010 * 2
def baseEnd_298010 : Nat := 51007456615494756068161

theorem tailTrace_298010 : CollatzResearch.WordTrace tailWord_298010 prefixEnd_298010 51007456615494756068161 := by
  unfold tailWord_298010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717329412592035225266871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7246211766912093934044989 2717329412592035225266871)
  ·
    refine ⟨4075994118888052837900307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2717329412592035225266871 4075994118888052837900307)
    ·
      refine ⟨6113991178332079256850461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4075994118888052837900307 6113991178332079256850461)
      ·
        refine ⟨2292746691874529721318923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6113991178332079256850461 2292746691874529721318923)
        ·
          refine ⟨3439120037811794581978385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292746691874529721318923 3439120037811794581978385)
          ·
            refine ⟨2579340028358845936483789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3439120037811794581978385 2579340028358845936483789)
            ·
              refine ⟨967252510634567226181421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2579340028358845936483789 967252510634567226181421)
              ·
                refine ⟨362719691487962709818033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 967252510634567226181421 362719691487962709818033)
                ·
                  refine ⟨272039768615972032363525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362719691487962709818033 272039768615972032363525)
                  ·
                    refine ⟨51007456615494756068161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 272039768615972032363525 51007456615494756068161)
                    ·
                      rfl

theorem cell23_298010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_298010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298010 prefixEnd_298010 := by exact prefixLift 298010
  have htrace : WordTrace (prefixWord ++ tailWord_298010) baseStart_298010 baseEnd_298010 := by
    simpa [prefixWord, tailWord_298010, baseEnd_298010] using wordTrace_append hprefix tailTrace_298010
  have hstable : (prefixWord ++ tailWord_298010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298010).length < 2 ^ (prefixWord ++ tailWord_298010).sum := by decide
  have hdescent : baseEnd_298010 < baseStart_298010 := by decide
  rcases family_descends (prefixWord ++ tailWord_298010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298017 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_298017 : Nat := 118140960795 + 298017 * 2 ^ 59
def prefixEnd_298017 : Nat := 4983230072969 + 3 ^ 40 * 298017 * 2
def baseEnd_298017 : Nat := 153025964211065740816951

theorem tailTrace_298017 : CollatzResearch.WordTrace tailWord_298017 prefixEnd_298017 153025964211065740816951 := by
  unfold tailWord_298017
  simp only [CollatzResearch.WordTrace]
  refine ⟨10869572961342781096572305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7246381974228520731048203 10869572961342781096572305)
  ·
    refine ⟨8152179721007085822429229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10869572961342781096572305 8152179721007085822429229)
    ·
      refine ⟨3057067395377657183410961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8152179721007085822429229 3057067395377657183410961)
      ·
        refine ⟨2292800546533242887558221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3057067395377657183410961 2292800546533242887558221)
        ·
          refine ⟨859800204949966082834333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2292800546533242887558221 859800204949966082834333)
          ·
            refine ⟨322425076856237281062875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 859800204949966082834333 322425076856237281062875)
            ·
              refine ⟨483637615284355921594313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322425076856237281062875 483637615284355921594313)
              ·
                refine ⟨362728211463266941195735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483637615284355921594313 362728211463266941195735)
                ·
                  refine ⟨544092317194900411793603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362728211463266941195735 544092317194900411793603)
                  ·
                    refine ⟨816138475792350617690405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 544092317194900411793603 816138475792350617690405)
                    ·
                      refine ⟨153025964211065740816951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 816138475792350617690405 153025964211065740816951)
                      ·
                        rfl

theorem cell23_298017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_298017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298017 prefixEnd_298017 := by exact prefixLift 298017
  have htrace : WordTrace (prefixWord ++ tailWord_298017) baseStart_298017 baseEnd_298017 := by
    simpa [prefixWord, tailWord_298017, baseEnd_298017] using wordTrace_append hprefix tailTrace_298017
  have hstable : (prefixWord ++ tailWord_298017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298017).length < 2 ^ (prefixWord ++ tailWord_298017).sum := by decide
  have hdescent : baseEnd_298017 < baseStart_298017 := by decide
  rcases family_descends (prefixWord ++ tailWord_298017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298030 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_298030 : Nat := 118140960795 + 298030 * 2 ^ 59
def prefixEnd_298030 : Nat := 4983230072969 + 3 ^ 40 * 298030 * 2
def baseEnd_298030 : Nat := 153032639459574189954391

theorem tailTrace_298030 : CollatzResearch.WordTrace tailWord_298030 prefixEnd_298030 153032639459574189954391 := by
  unfold tailWord_298030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358755888786960539599443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7246698073530456211197029 1358755888786960539599443)
  ·
    refine ⟨2038133833180440809399165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1358755888786960539599443 2038133833180440809399165)
    ·
      refine ⟨764300187442665303524687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2038133833180440809399165 764300187442665303524687)
      ·
        refine ⟨1146450281163997955287031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764300187442665303524687 1146450281163997955287031)
        ·
          refine ⟨1719675421745996932930547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146450281163997955287031 1719675421745996932930547)
          ·
            refine ⟨2579513132618995399395821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719675421745996932930547 2579513132618995399395821)
            ·
              refine ⟨967317424732123274773433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2579513132618995399395821 967317424732123274773433)
              ·
                refine ⟨725488068549092456080075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967317424732123274773433 725488068549092456080075)
                ·
                  refine ⟨1088232102823638684120113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 725488068549092456080075 1088232102823638684120113)
                  ·
                    refine ⟨816174077117729013090085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1088232102823638684120113 816174077117729013090085)
                    ·
                      refine ⟨153032639459574189954391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 816174077117729013090085 153032639459574189954391)
                      ·
                        rfl

theorem cell23_298030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_298030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298030 prefixEnd_298030 := by exact prefixLift 298030
  have htrace : WordTrace (prefixWord ++ tailWord_298030) baseStart_298030 baseEnd_298030 := by
    simpa [prefixWord, tailWord_298030, baseEnd_298030] using wordTrace_append hprefix tailTrace_298030
  have hstable : (prefixWord ++ tailWord_298030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298030).length < 2 ^ (prefixWord ++ tailWord_298030).sum := by decide
  have hdescent : baseEnd_298030 < baseStart_298030 := by decide
  rcases family_descends (prefixWord ++ tailWord_298030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298034 : List Nat := [3, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2]
def baseStart_298034 : Nat := 118140960795 + 298034 * 2 ^ 59
def prefixEnd_298034 : Nat := 4983230072969 + 3 ^ 40 * 298034 * 2
def baseEnd_298034 : Nat := 153034693382192174304373

theorem tailTrace_298034 : CollatzResearch.WordTrace tailWord_298034 prefixEnd_298034 153034693382192174304373 := by
  unfold tailWord_298034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717548250570298249985289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7246795334854128666627437 2717548250570298249985289)
  ·
    refine ⟨2038161187927723687488967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2717548250570298249985289 2038161187927723687488967)
    ·
      refine ⟨3057241781891585531233451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2038161187927723687488967 3057241781891585531233451)
      ·
        refine ⟨4585862672837378296850177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3057241781891585531233451 4585862672837378296850177)
        ·
          refine ⟨3439397004628033722637633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4585862672837378296850177 3439397004628033722637633)
          ·
            refine ⟨2579547753471025291978225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3439397004628033722637633 2579547753471025291978225)
            ·
              refine ⟨1934660815103268968983669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2579547753471025291978225 1934660815103268968983669)
              ·
                refine ⟨181374451415931465842219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1934660815103268968983669 181374451415931465842219)
                ·
                  refine ⟨272061677123897198763329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181374451415931465842219 272061677123897198763329)
                  ·
                    refine ⟨204046257842922899072497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 272061677123897198763329 204046257842922899072497)
                    ·
                      refine ⟨153034693382192174304373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 204046257842922899072497 153034693382192174304373)
                      ·
                        rfl

theorem cell23_298034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_298034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298034 prefixEnd_298034 := by exact prefixLift 298034
  have htrace : WordTrace (prefixWord ++ tailWord_298034) baseStart_298034 baseEnd_298034 := by
    simpa [prefixWord, tailWord_298034, baseEnd_298034] using wordTrace_append hprefix tailTrace_298034
  have hstable : (prefixWord ++ tailWord_298034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298034).length < 2 ^ (prefixWord ++ tailWord_298034).sum := by decide
  have hdescent : baseEnd_298034 < baseStart_298034 := by decide
  rcases family_descends (prefixWord ++ tailWord_298034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298088 : List Nat := [2, 1, 4, 4, 2, 1, 2, 1, 1, 2, 3]
def baseStart_298088 : Nat := 118140960795 + 298088 * 2 ^ 59
def prefixEnd_298088 : Nat := 4983230072969 + 3 ^ 40 * 298088 * 2
def baseEnd_298088 : Nat := 153062421337534963029125

theorem tailTrace_298088 : CollatzResearch.WordTrace tailWord_298088 prefixEnd_298088 153062421337534963029125 := by
  unfold tailWord_298088
  simp only [CollatzResearch.WordTrace]
  refine ⟨5436081272042780111203459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7248108362723706814937945 5436081272042780111203459)
  ·
    refine ⟨8154121908064170166805189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5436081272042780111203459 8154121908064170166805189)
    ·
      refine ⟨1528897857762031906275973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8154121908064170166805189 1528897857762031906275973)
      ·
        refine ⟨286668348330380982426745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1528897857762031906275973 286668348330380982426745)
        ·
          refine ⟨215001261247785736820059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286668348330380982426745 215001261247785736820059)
          ·
            refine ⟨322501891871678605230089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215001261247785736820059 322501891871678605230089)
            ·
              refine ⟨241876418903758953922567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322501891871678605230089 241876418903758953922567)
              ·
                refine ⟨362814628355638430883851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241876418903758953922567 362814628355638430883851)
                ·
                  refine ⟨544221942533457646325777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362814628355638430883851 544221942533457646325777)
                  ·
                    refine ⟨408166456900093234744333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 544221942533457646325777 408166456900093234744333)
                    ·
                      refine ⟨153062421337534963029125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 408166456900093234744333 153062421337534963029125)
                      ·
                        rfl

theorem cell23_298088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_298088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298088 prefixEnd_298088 := by exact prefixLift 298088
  have htrace : WordTrace (prefixWord ++ tailWord_298088) baseStart_298088 baseEnd_298088 := by
    simpa [prefixWord, tailWord_298088, baseEnd_298088] using wordTrace_append hprefix tailTrace_298088
  have hstable : (prefixWord ++ tailWord_298088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298088).length < 2 ^ (prefixWord ++ tailWord_298088).sum := by decide
  have hdescent : baseEnd_298088 < baseStart_298088 := by decide
  rcases family_descends (prefixWord ++ tailWord_298088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298094 : List Nat := [4, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_298094 : Nat := 118140960795 + 298094 * 2 ^ 59
def prefixEnd_298094 : Nat := 4983230072969 + 3 ^ 40 * 298094 * 2
def baseEnd_298094 : Nat := 153065502221461939554097

theorem tailTrace_298094 : CollatzResearch.WordTrace tailWord_298094 prefixEnd_298094 153065502221461939554097 := by
  unfold tailWord_298094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1359047672757977905890667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7248254254709215498083557 1359047672757977905890667)
  ·
    refine ⟨2038571509136966858836001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1359047672757977905890667 2038571509136966858836001)
    ·
      refine ⟨1528928631852725144127001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2038571509136966858836001 1528928631852725144127001)
      ·
        refine ⟨1146696473889543858095251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1528928631852725144127001 1146696473889543858095251)
        ·
          refine ⟨1720044710834315787142877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146696473889543858095251 1720044710834315787142877)
          ·
            refine ⟨645016766562868420178579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1720044710834315787142877 645016766562868420178579)
            ·
              refine ⟨967525149844302630267869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645016766562868420178579 967525149844302630267869)
              ·
                refine ⟨362821931191613486350451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 967525149844302630267869 362821931191613486350451)
                ·
                  refine ⟨544232896787420229525677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 362821931191613486350451 544232896787420229525677)
                  ·
                    refine ⟨204087336295282586072129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 544232896787420229525677 204087336295282586072129)
                    ·
                      refine ⟨153065502221461939554097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 204087336295282586072129 153065502221461939554097)
                      ·
                        rfl

theorem cell23_298094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_298094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298094 prefixEnd_298094 := by exact prefixLift 298094
  have htrace : WordTrace (prefixWord ++ tailWord_298094) baseStart_298094 baseEnd_298094 := by
    simpa [prefixWord, tailWord_298094, baseEnd_298094] using wordTrace_append hprefix tailTrace_298094
  have hstable : (prefixWord ++ tailWord_298094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298094).length < 2 ^ (prefixWord ++ tailWord_298094).sum := by decide
  have hdescent : baseEnd_298094 < baseStart_298094 := by decide
  rcases family_descends (prefixWord ++ tailWord_298094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298103 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_298103 : Nat := 118140960795 + 298103 * 2 ^ 59
def prefixEnd_298103 : Nat := 4983230072969 + 3 ^ 40 * 298103 * 2
def baseEnd_298103 : Nat := 153070123547352404341555

theorem tailTrace_298103 : CollatzResearch.WordTrace tailWord_298103 prefixEnd_298103 153070123547352404341555 := by
  unfold tailWord_298103
  simp only [CollatzResearch.WordTrace]
  refine ⟨10872709639031217784202963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7248473092687478522801975 10872709639031217784202963)
  ·
    refine ⟨16309064458546826676304445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10872709639031217784202963 16309064458546826676304445)
    ·
      refine ⟨6115899171955060003614167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16309064458546826676304445 6115899171955060003614167)
      ·
        refine ⟨9173848757932590005421251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6115899171955060003614167 9173848757932590005421251)
        ·
          refine ⟨13760773136898885008131877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9173848757932590005421251 13760773136898885008131877)
          ·
            refine ⟨2580144963168540939024727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13760773136898885008131877 2580144963168540939024727)
            ·
              refine ⟨3870217444752811408537091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580144963168540939024727 3870217444752811408537091)
              ·
                refine ⟨5805326167129217112805637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870217444752811408537091 5805326167129217112805637)
                ·
                  refine ⟨1088498656336728208651057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5805326167129217112805637 1088498656336728208651057)
                  ·
                    refine ⟨816373992252546156488293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1088498656336728208651057 816373992252546156488293)
                    ·
                      refine ⟨153070123547352404341555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 816373992252546156488293 153070123547352404341555)
                      ·
                        rfl

theorem cell23_298103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_298103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298103 prefixEnd_298103 := by exact prefixLift 298103
  have htrace : WordTrace (prefixWord ++ tailWord_298103) baseStart_298103 baseEnd_298103 := by
    simpa [prefixWord, tailWord_298103, baseEnd_298103] using wordTrace_append hprefix tailTrace_298103
  have hstable : (prefixWord ++ tailWord_298103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298103).length < 2 ^ (prefixWord ++ tailWord_298103).sum := by decide
  have hdescent : baseEnd_298103 < baseStart_298103 := by decide
  rcases family_descends (prefixWord ++ tailWord_298103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298130 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 7]
def baseStart_298130 : Nat := 118140960795 + 298130 * 2 ^ 59
def prefixEnd_298130 : Nat := 4983230072969 + 3 ^ 40 * 298130 * 2
def baseEnd_298130 : Nat := 17009331947224866522659

theorem tailTrace_298130 : CollatzResearch.WordTrace tailWord_298130 prefixEnd_298130 17009331947224866522659 := by
  unfold tailWord_298130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718423602483350348858961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7249129606622267596957229 2718423602483350348858961)
  ·
    refine ⟨2038817701862512761644221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2718423602483350348858961 2038817701862512761644221)
    ·
      refine ⟨764556638198442285616583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2038817701862512761644221 764556638198442285616583)
      ·
        refine ⟨1146834957297663428424875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764556638198442285616583 1146834957297663428424875)
        ·
          refine ⟨1720252435946495142637313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146834957297663428424875 1720252435946495142637313)
          ·
            refine ⟨1290189326959871356977985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1720252435946495142637313 1290189326959871356977985)
            ·
              refine ⟨967641995219903517733489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290189326959871356977985 967641995219903517733489)
              ·
                refine ⟨725731496414927638300117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967641995219903517733489 725731496414927638300117)
                ·
                  refine ⟨17009331947224866522659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 725731496414927638300117 17009331947224866522659)
                  ·
                    rfl

theorem cell23_298130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_298130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298130 prefixEnd_298130 := by exact prefixLift 298130
  have htrace : WordTrace (prefixWord ++ tailWord_298130) baseStart_298130 baseEnd_298130 := by
    simpa [prefixWord, tailWord_298130, baseEnd_298130] using wordTrace_append hprefix tailTrace_298130
  have hstable : (prefixWord ++ tailWord_298130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298130).length < 2 ^ (prefixWord ++ tailWord_298130).sum := by decide
  have hdescent : baseEnd_298130 < baseStart_298130 := by decide
  rcases family_descends (prefixWord ++ tailWord_298130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298183 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_298183 : Nat := 118140960795 + 298183 * 2 ^ 59
def prefixEnd_298183 : Nat := 4983230072969 + 3 ^ 40 * 298183 * 2
def baseEnd_298183 : Nat := 153111201999712091341187

theorem tailTrace_298183 : CollatzResearch.WordTrace tailWord_298183 prefixEnd_298183 153111201999712091341187 := by
  unfold tailWord_298183
  simp only [CollatzResearch.WordTrace]
  refine ⟨10875627478741391447115203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7250418319160927631410135 10875627478741391447115203)
  ·
    refine ⟨16313441218112087170672805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10875627478741391447115203 16313441218112087170672805)
    ·
      refine ⟨3058770228396016344501151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16313441218112087170672805 3058770228396016344501151)
      ·
        refine ⟨4588155342594024516751727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058770228396016344501151 4588155342594024516751727)
        ·
          refine ⟨6882233013891036775127591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4588155342594024516751727 6882233013891036775127591)
          ·
            refine ⟨10323349520836555162691387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6882233013891036775127591 10323349520836555162691387)
            ·
              refine ⟨15485024281254832744037081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10323349520836555162691387 15485024281254832744037081)
              ·
                refine ⟨11613768210941124558027811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15485024281254832744037081 11613768210941124558027811)
                ·
                  refine ⟨17420652316411686837041717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11613768210941124558027811 17420652316411686837041717)
                  ·
                    refine ⟨1633186154663595640972661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17420652316411686837041717 1633186154663595640972661)
                    ·
                      refine ⟨153111201999712091341187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1633186154663595640972661 153111201999712091341187)
                      ·
                        rfl

theorem cell23_298183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_298183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298183 prefixEnd_298183 := by exact prefixLift 298183
  have htrace : WordTrace (prefixWord ++ tailWord_298183) baseStart_298183 baseEnd_298183 := by
    simpa [prefixWord, tailWord_298183, baseEnd_298183] using wordTrace_append hprefix tailTrace_298183
  have hstable : (prefixWord ++ tailWord_298183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298183).length < 2 ^ (prefixWord ++ tailWord_298183).sum := by decide
  have hdescent : baseEnd_298183 < baseStart_298183 := by decide
  rcases family_descends (prefixWord ++ tailWord_298183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298193 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_298193 : Nat := 118140960795 + 298193 * 2 ^ 59
def prefixEnd_298193 : Nat := 4983230072969 + 3 ^ 40 * 298193 * 2
def baseEnd_298193 : Nat := 153116336806257052216141

theorem tailTrace_298193 : CollatzResearch.WordTrace tailWord_298193 prefixEnd_298193 153116336806257052216141 := by
  unfold tailWord_298193
  simp only [CollatzResearch.WordTrace]
  refine ⟨10875992208705163154979233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7250661472470108769986155 10875992208705163154979233)
  ·
    refine ⟨8156994156528872366234425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10875992208705163154979233 8156994156528872366234425)
    ·
      refine ⟨6117745617396654274675819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8156994156528872366234425 6117745617396654274675819)
      ·
        refine ⟨9176618426094981412013729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6117745617396654274675819 9176618426094981412013729)
        ·
          refine ⟨6882463819571236059010297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9176618426094981412013729 6882463819571236059010297)
          ·
            refine ⟨5161847864678427044257723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6882463819571236059010297 5161847864678427044257723)
            ·
              refine ⟨7742771797017640566386585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5161847864678427044257723 7742771797017640566386585)
              ·
                refine ⟨5807078847763230424789939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7742771797017640566386585 5807078847763230424789939)
                ·
                  refine ⟨8710618271644845637184909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5807078847763230424789939 8710618271644845637184909)
                  ·
                    refine ⟨3266481851866817113944341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8710618271644845637184909 3266481851866817113944341)
                    ·
                      refine ⟨153116336806257052216141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3266481851866817113944341 153116336806257052216141)
                      ·
                        rfl

theorem cell23_298193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_298193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298193 prefixEnd_298193 := by exact prefixLift 298193
  have htrace : WordTrace (prefixWord ++ tailWord_298193) baseStart_298193 baseEnd_298193 := by
    simpa [prefixWord, tailWord_298193, baseEnd_298193] using wordTrace_append hprefix tailTrace_298193
  have hstable : (prefixWord ++ tailWord_298193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298193).length < 2 ^ (prefixWord ++ tailWord_298193).sum := by decide
  have hdescent : baseEnd_298193 < baseStart_298193 := by decide
  rcases family_descends (prefixWord ++ tailWord_298193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298197 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_298197 : Nat := 118140960795 + 298197 * 2 ^ 59
def prefixEnd_298197 : Nat := 4983230072969 + 3 ^ 40 * 298197 * 2
def baseEnd_298197 : Nat := 153118390728875036566123

theorem tailTrace_298197 : CollatzResearch.WordTrace tailWord_298197 prefixEnd_298197 153118390728875036566123 := by
  unfold tailWord_298197
  simp only [CollatzResearch.WordTrace]
  refine ⟨10876138100690671838124845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7250758733793781225416563 10876138100690671838124845)
  ·
    refine ⟨4078551787759001939296817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10876138100690671838124845 4078551787759001939296817)
    ·
      refine ⟨3058913840819251454472613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4078551787759001939296817 3058913840819251454472613)
      ·
        refine ⟨573546345153609647713615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3058913840819251454472613 573546345153609647713615)
        ·
          refine ⟨860319517730414471570423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 573546345153609647713615 860319517730414471570423)
          ·
            refine ⟨1290479276595621707355635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860319517730414471570423 1290479276595621707355635)
            ·
              refine ⟨1935718914893432561033453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290479276595621707355635 1935718914893432561033453)
              ·
                refine ⟨725894593085037210387545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1935718914893432561033453 725894593085037210387545)
                ·
                  refine ⟨544420944813777907790659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 725894593085037210387545 544420944813777907790659)
                  ·
                    refine ⟨816631417220666861685989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 544420944813777907790659 816631417220666861685989)
                    ·
                      refine ⟨153118390728875036566123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 816631417220666861685989 153118390728875036566123)
                      ·
                        rfl

theorem cell23_298197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_298197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298197 prefixEnd_298197 := by exact prefixLift 298197
  have htrace : WordTrace (prefixWord ++ tailWord_298197) baseStart_298197 baseEnd_298197 := by
    simpa [prefixWord, tailWord_298197, baseEnd_298197] using wordTrace_append hprefix tailTrace_298197
  have hstable : (prefixWord ++ tailWord_298197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298197).length < 2 ^ (prefixWord ++ tailWord_298197).sum := by decide
  have hdescent : baseEnd_298197 < baseStart_298197 := by decide
  rcases family_descends (prefixWord ++ tailWord_298197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298220 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 6]
def baseStart_298220 : Nat := 118140960795 + 298220 * 2 ^ 59
def prefixEnd_298220 : Nat := 4983230072969 + 3 ^ 40 * 298220 * 2
def baseEnd_298220 : Nat := 17014466753769827397613

theorem tailTrace_298220 : CollatzResearch.WordTrace tailWord_298220 prefixEnd_298220 17014466753769827397613 := by
  unfold tailWord_298220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5438488489803673383106057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7251317986404897844141409 5438488489803673383106057)
  ·
    refine ⟨4078866367352755037329543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5438488489803673383106057 4078866367352755037329543)
    ·
      refine ⟨6118299551029132555994315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4078866367352755037329543 6118299551029132555994315)
      ·
        refine ⟨9177449326543698833991473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6118299551029132555994315 9177449326543698833991473)
        ·
          refine ⟨6883086994907774125493605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9177449326543698833991473 6883086994907774125493605)
          ·
            refine ⟨1290578811545207648530051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6883086994907774125493605 1290578811545207648530051)
            ·
              refine ⟨1935868217317811472795077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290578811545207648530051 1935868217317811472795077)
              ·
                refine ⟨362975290747089651149077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1935868217317811472795077 362975290747089651149077)
                ·
                  refine ⟨17014466753769827397613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 362975290747089651149077 17014466753769827397613)
                  ·
                    rfl

theorem cell23_298220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_298220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298220 prefixEnd_298220 := by exact prefixLift 298220
  have htrace : WordTrace (prefixWord ++ tailWord_298220) baseStart_298220 baseEnd_298220 := by
    simpa [prefixWord, tailWord_298220, baseEnd_298220] using wordTrace_append hprefix tailTrace_298220
  have hstable : (prefixWord ++ tailWord_298220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298220).length < 2 ^ (prefixWord ++ tailWord_298220).sum := by decide
  have hdescent : baseEnd_298220 < baseStart_298220 := by decide
  rcases family_descends (prefixWord ++ tailWord_298220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298257 : List Nat := [1, 2, 2, 1, 1, 4, 3, 1, 1, 5, 2]
def baseStart_298257 : Nat := 118140960795 + 298257 * 2 ^ 59
def prefixEnd_298257 : Nat := 4983230072969 + 3 ^ 40 * 298257 * 2
def baseEnd_298257 : Nat := 153149199568144801815847

theorem tailTrace_298257 : CollatzResearch.WordTrace tailWord_298257 prefixEnd_298257 153149199568144801815847 := by
  unfold tailWord_298257
  simp only [CollatzResearch.WordTrace]
  refine ⟨10878326480473302085309025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7252217653648868056872683 10878326480473302085309025)
  ·
    refine ⟨8158744860354976563981769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10878326480473302085309025 8158744860354976563981769)
    ·
      refine ⟨6119058645266232422986327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8158744860354976563981769 6119058645266232422986327)
      ·
        refine ⟨9178587967899348634479491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6119058645266232422986327 9178587967899348634479491)
        ·
          refine ⟨13767881951849022951719237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9178587967899348634479491 13767881951849022951719237)
          ·
            refine ⟨2581477865971691803447357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13767881951849022951719237 2581477865971691803447357)
            ·
              refine ⟨968054199739384426292759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2581477865971691803447357 968054199739384426292759)
              ·
                refine ⟨1452081299609076639439139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968054199739384426292759 1452081299609076639439139)
                ·
                  refine ⟨2178121949413614959158709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452081299609076639439139 2178121949413614959158709)
                  ·
                    refine ⟨204198932757526402421129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2178121949413614959158709 204198932757526402421129)
                    ·
                      refine ⟨153149199568144801815847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 204198932757526402421129 153149199568144801815847)
                      ·
                        rfl

theorem cell23_298257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 5, 2].length) (baseStart_298257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298257 prefixEnd_298257 := by exact prefixLift 298257
  have htrace : WordTrace (prefixWord ++ tailWord_298257) baseStart_298257 baseEnd_298257 := by
    simpa [prefixWord, tailWord_298257, baseEnd_298257] using wordTrace_append hprefix tailTrace_298257
  have hstable : (prefixWord ++ tailWord_298257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298257).length < 2 ^ (prefixWord ++ tailWord_298257).sum := by decide
  have hdescent : baseEnd_298257 < baseStart_298257 := by decide
  rcases family_descends (prefixWord ++ tailWord_298257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298301 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_298301 : Nat := 118140960795 + 298301 * 2 ^ 59
def prefixEnd_298301 : Nat := 4983230072969 + 3 ^ 40 * 298301 * 2
def baseEnd_298301 : Nat := 51057264238980876555215

theorem tailTrace_298301 : CollatzResearch.WordTrace tailWord_298301 prefixEnd_298301 51057264238980876555215 := by
  unfold tailWord_298301
  simp only [CollatzResearch.WordTrace]
  refine ⟨10879931292313897599910757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7253287528209265066607171 10879931292313897599910757)
  ·
    refine ⟨2039987117308855799983267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10879931292313897599910757 2039987117308855799983267)
    ·
      refine ⟨3059980675963283699974901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2039987117308855799983267 3059980675963283699974901)
      ·
        refine ⟨286873188371557846872647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3059980675963283699974901 286873188371557846872647)
        ·
          refine ⟨430309782557336770308971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286873188371557846872647 430309782557336770308971)
          ·
            refine ⟨645464673836005155463457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430309782557336770308971 645464673836005155463457)
            ·
              refine ⟨484098505377003866597593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645464673836005155463457 484098505377003866597593)
              ·
                refine ⟨363073879032752899948195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484098505377003866597593 363073879032752899948195)
                ·
                  refine ⟨544610818549129349922293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363073879032752899948195 544610818549129349922293)
                  ·
                    refine ⟨51057264238980876555215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 544610818549129349922293 51057264238980876555215)
                    ·
                      rfl

theorem cell23_298301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_298301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298301 prefixEnd_298301 := by exact prefixLift 298301
  have htrace : WordTrace (prefixWord ++ tailWord_298301) baseStart_298301 baseEnd_298301 := by
    simpa [prefixWord, tailWord_298301, baseEnd_298301] using wordTrace_append hprefix tailTrace_298301
  have hstable : (prefixWord ++ tailWord_298301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298301).length < 2 ^ (prefixWord ++ tailWord_298301).sum := by decide
  have hdescent : baseEnd_298301 < baseStart_298301 := by decide
  rcases family_descends (prefixWord ++ tailWord_298301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298304 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 3, 2, 2]
def baseStart_298304 : Nat := 118140960795 + 298304 * 2 ^ 59
def prefixEnd_298304 : Nat := 4983230072969 + 3 ^ 40 * 298304 * 2
def baseEnd_298304 : Nat := 153173333158906117928131

theorem tailTrace_298304 : CollatzResearch.WordTrace tailWord_298304 prefixEnd_298304 153173333158906117928131 := by
  unfold tailWord_298304
  simp only [CollatzResearch.WordTrace]
  refine ⟨5440020355651514556134983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7253360474202019408179977 5440020355651514556134983)
  ·
    refine ⟨8160030533477271834202475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5440020355651514556134983 8160030533477271834202475)
    ·
      refine ⟨12240045800215907751303713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8160030533477271834202475 12240045800215907751303713)
      ·
        refine ⟨9180034350161930813477785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12240045800215907751303713 9180034350161930813477785)
        ·
          refine ⟨6885025762621448110108339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9180034350161930813477785 6885025762621448110108339)
          ·
            refine ⟨10327538643932172165162509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6885025762621448110108339 10327538643932172165162509)
            ·
              refine ⟨3872826991474564561935941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10327538643932172165162509 3872826991474564561935941)
              ·
                refine ⟨726155060901480855362989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3872826991474564561935941 726155060901480855362989)
                ·
                  refine ⟨272308147838055320761121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726155060901480855362989 272308147838055320761121)
                  ·
                    refine ⟨204231110878541490570841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 272308147838055320761121 204231110878541490570841)
                    ·
                      refine ⟨153173333158906117928131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 204231110878541490570841 153173333158906117928131)
                      ·
                        rfl

theorem cell23_298304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 3, 2, 2].length) (baseStart_298304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298304 prefixEnd_298304 := by exact prefixLift 298304
  have htrace : WordTrace (prefixWord ++ tailWord_298304) baseStart_298304 baseEnd_298304 := by
    simpa [prefixWord, tailWord_298304, baseEnd_298304] using wordTrace_append hprefix tailTrace_298304
  have hstable : (prefixWord ++ tailWord_298304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298304).length < 2 ^ (prefixWord ++ tailWord_298304).sum := by decide
  have hdescent : baseEnd_298304 < baseStart_298304 := by decide
  rcases family_descends (prefixWord ++ tailWord_298304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298324 : List Nat := [2, 4, 1, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_298324 : Nat := 118140960795 + 298324 * 2 ^ 59
def prefixEnd_298324 : Nat := 4983230072969 + 3 ^ 40 * 298324 * 2
def baseEnd_298324 : Nat := 153183602771996039678039

theorem tailTrace_298324 : CollatzResearch.WordTrace tailWord_298324 prefixEnd_298324 153183602771996039678039 := by
  unfold tailWord_298324
  simp only [CollatzResearch.WordTrace]
  refine ⟨5440385085615286263999013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7253846780820381685332017 5440385085615286263999013)
  ·
    refine ⟨1020072203552866174499815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5440385085615286263999013 1020072203552866174499815)
    ·
      refine ⟨1530108305329299261749723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020072203552866174499815 1530108305329299261749723)
      ·
        refine ⟨2295162457993948892624585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530108305329299261749723 2295162457993948892624585)
        ·
          refine ⟨1721371843495461669468439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2295162457993948892624585 1721371843495461669468439)
          ·
            refine ⟨2582057765243192504202659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721371843495461669468439 2582057765243192504202659)
            ·
              refine ⟨3873086647864788756303989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582057765243192504202659 3873086647864788756303989)
              ·
                refine ⟨363101873237323945903499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3873086647864788756303989 363101873237323945903499)
                ·
                  refine ⟨544652809855985918855249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363101873237323945903499 544652809855985918855249)
                  ·
                    refine ⟨408489607391989439141437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 544652809855985918855249 408489607391989439141437)
                    ·
                      refine ⟨153183602771996039678039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 408489607391989439141437 153183602771996039678039)
                      ·
                        rfl

theorem cell23_298324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_298324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298324 prefixEnd_298324 := by exact prefixLift 298324
  have htrace : WordTrace (prefixWord ++ tailWord_298324) baseStart_298324 baseEnd_298324 := by
    simpa [prefixWord, tailWord_298324, baseEnd_298324] using wordTrace_append hprefix tailTrace_298324
  have hstable : (prefixWord ++ tailWord_298324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298324).length < 2 ^ (prefixWord ++ tailWord_298324).sum := by decide
  have hdescent : baseEnd_298324 < baseStart_298324 := by decide
  rcases family_descends (prefixWord ++ tailWord_298324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298364 : List Nat := [2, 2, 2, 1, 1, 1, 5, 1, 3, 3, 2]
def baseStart_298364 : Nat := 118140960795 + 298364 * 2 ^ 59
def prefixEnd_298364 : Nat := 4983230072969 + 3 ^ 40 * 298364 * 2
def baseEnd_298364 : Nat := 153204141998175883177855

theorem tailTrace_298364 : CollatzResearch.WordTrace tailWord_298364 prefixEnd_298364 153204141998175883177855 := by
  unfold tailWord_298364
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441114545542829679727073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7254819394057106239636097 5441114545542829679727073)
  ·
    refine ⟨4080835909157122259795305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5441114545542829679727073 4080835909157122259795305)
    ·
      refine ⟨3060626931867841694846479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4080835909157122259795305 3060626931867841694846479)
      ·
        refine ⟨4590940397801762542269719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3060626931867841694846479 4590940397801762542269719)
        ·
          refine ⟨6886410596702643813404579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4590940397801762542269719 6886410596702643813404579)
          ·
            refine ⟨10329615895053965720106869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6886410596702643813404579 10329615895053965720106869)
            ·
              refine ⟨968401490161309286260019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10329615895053965720106869 968401490161309286260019)
              ·
                refine ⟨1452602235241963929390029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968401490161309286260019 1452602235241963929390029)
                ·
                  refine ⟨544725838215736473521261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1452602235241963929390029 544725838215736473521261)
                  ·
                    refine ⟨204272189330901177570473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 544725838215736473521261 204272189330901177570473)
                    ·
                      refine ⟨153204141998175883177855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 204272189330901177570473 153204141998175883177855)
                      ·
                        rfl

theorem cell23_298364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_298364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298364 prefixEnd_298364 := by exact prefixLift 298364
  have htrace : WordTrace (prefixWord ++ tailWord_298364) baseStart_298364 baseEnd_298364 := by
    simpa [prefixWord, tailWord_298364, baseEnd_298364] using wordTrace_append hprefix tailTrace_298364
  have hstable : (prefixWord ++ tailWord_298364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298364).length < 2 ^ (prefixWord ++ tailWord_298364).sum := by decide
  have hdescent : baseEnd_298364 < baseStart_298364 := by decide
  rcases family_descends (prefixWord ++ tailWord_298364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298388 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_298388 : Nat := 118140960795 + 298388 * 2 ^ 59
def prefixEnd_298388 : Nat := 4983230072969 + 3 ^ 40 * 298388 * 2
def baseEnd_298388 : Nat := 153216465533883789277745

theorem tailTrace_298388 : CollatzResearch.WordTrace tailWord_298388 prefixEnd_298388 153216465533883789277745 := by
  unfold tailWord_298388
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441552221499355729163909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7255402961999140972218545 5441552221499355729163909)
  ·
    refine ⟨1020291041531129199218233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5441552221499355729163909 1020291041531129199218233)
    ·
      refine ⟨765218281148346899413675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1020291041531129199218233 765218281148346899413675)
      ·
        refine ⟨1147827421722520349120513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 765218281148346899413675 1147827421722520349120513)
        ·
          refine ⟨860870566291890261840385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1147827421722520349120513 860870566291890261840385)
          ·
            refine ⟨645652924718917696380289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860870566291890261840385 645652924718917696380289)
            ·
              refine ⟨484239693539188272285217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645652924718917696380289 484239693539188272285217)
              ·
                refine ⟨363179770154391204213913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484239693539188272285217 363179770154391204213913)
                ·
                  refine ⟨272384827615793403160435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363179770154391204213913 272384827615793403160435)
                  ·
                    refine ⟨408577241423690104740653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 272384827615793403160435 408577241423690104740653)
                    ·
                      refine ⟨153216465533883789277745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 408577241423690104740653 153216465533883789277745)
                      ·
                        rfl

theorem cell23_298388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_298388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298388 prefixEnd_298388 := by exact prefixLift 298388
  have htrace : WordTrace (prefixWord ++ tailWord_298388) baseStart_298388 baseEnd_298388 := by
    simpa [prefixWord, tailWord_298388, baseEnd_298388] using wordTrace_append hprefix tailTrace_298388
  have hstable : (prefixWord ++ tailWord_298388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298388).length < 2 ^ (prefixWord ++ tailWord_298388).sum := by decide
  have hdescent : baseEnd_298388 < baseStart_298388 := by decide
  rcases family_descends (prefixWord ++ tailWord_298388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298394 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2]
def baseStart_298394 : Nat := 118140960795 + 298394 * 2 ^ 59
def prefixEnd_298394 : Nat := 4983230072969 + 3 ^ 40 * 298394 * 2
def baseEnd_298394 : Nat := 153219546417810765802717

theorem tailTrace_298394 : CollatzResearch.WordTrace tailWord_298394 prefixEnd_298394 153219546417810765802717 := by
  unfold tailWord_298394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2720830820244243620761559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7255548853984649655364157 2720830820244243620761559)
  ·
    refine ⟨4081246230366365431142339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2720830820244243620761559 4081246230366365431142339)
    ·
      refine ⟨6121869345549548146713509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4081246230366365431142339 6121869345549548146713509)
      ·
        refine ⟨1147850502290540277508783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6121869345549548146713509 1147850502290540277508783)
        ·
          refine ⟨1721775753435810416263175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147850502290540277508783 1721775753435810416263175)
          ·
            refine ⟨2582663630153715624394763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721775753435810416263175 2582663630153715624394763)
            ·
              refine ⟨3873995445230573436592145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582663630153715624394763 3873995445230573436592145)
              ·
                refine ⟨2905496583922930077444109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3873995445230573436592145 2905496583922930077444109)
                ·
                  refine ⟨1089561218971098779041541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2905496583922930077444109 1089561218971098779041541)
                  ·
                    refine ⟨204292728557081021070289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1089561218971098779041541 204292728557081021070289)
                    ·
                      refine ⟨153219546417810765802717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 204292728557081021070289 153219546417810765802717)
                      ·
                        rfl

theorem cell23_298394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_298394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298394 prefixEnd_298394 := by exact prefixLift 298394
  have htrace : WordTrace (prefixWord ++ tailWord_298394) baseStart_298394 baseEnd_298394 := by
    simpa [prefixWord, tailWord_298394, baseEnd_298394] using wordTrace_append hprefix tailTrace_298394
  have hstable : (prefixWord ++ tailWord_298394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298394).length < 2 ^ (prefixWord ++ tailWord_298394).sum := by decide
  have hdescent : baseEnd_298394 < baseStart_298394 := by decide
  rcases family_descends (prefixWord ++ tailWord_298394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298417 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 7]
def baseStart_298417 : Nat := 118140960795 + 298417 * 2 ^ 59
def prefixEnd_298417 : Nat := 4983230072969 + 3 ^ 40 * 298417 * 2
def baseEnd_298417 : Nat := 17025706274762686201679

theorem tailTrace_298417 : CollatzResearch.WordTrace tailWord_298417 prefixEnd_298417 17025706274762686201679 := by
  unfold tailWord_298417
  simp only [CollatzResearch.WordTrace]
  refine ⟨10884162159893649411133505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7256108106595766274089003 10884162159893649411133505)
  ·
    refine ⟨8163121619920237058350129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10884162159893649411133505 8163121619920237058350129)
    ·
      refine ⟨6122341214940177793762597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8163121619920237058350129 6122341214940177793762597)
      ·
        refine ⟨1147938977801283336330487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6122341214940177793762597 1147938977801283336330487)
        ·
          refine ⟨1721908466701925004495731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147938977801283336330487 1721908466701925004495731)
          ·
            refine ⟨2582862700052887506743597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721908466701925004495731 2582862700052887506743597)
            ·
              refine ⟨968573512519832815028849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2582862700052887506743597 968573512519832815028849)
              ·
                refine ⟨726430134389874611271637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968573512519832815028849 726430134389874611271637)
                ·
                  refine ⟨17025706274762686201679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 726430134389874611271637 17025706274762686201679)
                  ·
                    rfl

theorem cell23_298417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 7].length) (baseStart_298417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298417 prefixEnd_298417 := by exact prefixLift 298417
  have htrace : WordTrace (prefixWord ++ tailWord_298417) baseStart_298417 baseEnd_298417 := by
    simpa [prefixWord, tailWord_298417, baseEnd_298417] using wordTrace_append hprefix tailTrace_298417
  have hstable : (prefixWord ++ tailWord_298417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298417).length < 2 ^ (prefixWord ++ tailWord_298417).sum := by decide
  have hdescent : baseEnd_298417 < baseStart_298417 := by decide
  rcases family_descends (prefixWord ++ tailWord_298417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298444 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 2, 3, 3]
def baseStart_298444 : Nat := 118140960795 + 298444 * 2 ^ 59
def prefixEnd_298444 : Nat := 4983230072969 + 3 ^ 40 * 298444 * 2
def baseEnd_298444 : Nat := 153245220450535570177487

theorem tailTrace_298444 : CollatzResearch.WordTrace tailWord_298444 prefixEnd_298444 153245220450535570177487 := by
  unfold tailWord_298444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5442573465397916511183193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7256764620530555348244257 5442573465397916511183193)
  ·
    refine ⟨4081930099048437383387395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5442573465397916511183193 4081930099048437383387395)
    ·
      refine ⟨6122895148572656075081093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4081930099048437383387395 6122895148572656075081093)
      ·
        refine ⟨1148042840357373014077705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6122895148572656075081093 1148042840357373014077705)
        ·
          refine ⟨861032130268029760558279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1148042840357373014077705 861032130268029760558279)
          ·
            refine ⟨1291548195402044640837419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861032130268029760558279 1291548195402044640837419)
            ·
              refine ⟨1937322293103066961256129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291548195402044640837419 1937322293103066961256129)
              ·
                refine ⟨1452991719827300220942097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1937322293103066961256129 1452991719827300220942097)
                ·
                  refine ⟨1089743789870475165706573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1452991719827300220942097 1089743789870475165706573)
                  ·
                    refine ⟨408653921201428187139965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1089743789870475165706573 408653921201428187139965)
                    ·
                      refine ⟨153245220450535570177487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 408653921201428187139965 153245220450535570177487)
                      ·
                        rfl

theorem cell23_298444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_298444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298444 prefixEnd_298444 := by exact prefixLift 298444
  have htrace : WordTrace (prefixWord ++ tailWord_298444) baseStart_298444 baseEnd_298444 := by
    simpa [prefixWord, tailWord_298444, baseEnd_298444] using wordTrace_append hprefix tailTrace_298444
  have hstable : (prefixWord ++ tailWord_298444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298444).length < 2 ^ (prefixWord ++ tailWord_298444).sum := by decide
  have hdescent : baseEnd_298444 < baseStart_298444 := by decide
  rcases family_descends (prefixWord ++ tailWord_298444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298447 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 2, 5]
def baseStart_298447 : Nat := 118140960795 + 298447 * 2 ^ 59
def prefixEnd_298447 : Nat := 4983230072969 + 3 ^ 40 * 298447 * 2
def baseEnd_298447 : Nat := 51082253630833019479991

theorem tailTrace_298447 : CollatzResearch.WordTrace tailWord_298447 prefixEnd_298447 51082253630833019479991 := by
  unfold tailWord_298447
  simp only [CollatzResearch.WordTrace]
  refine ⟨10885256349784964534725595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7256837566523309689817063 10885256349784964534725595)
  ·
    refine ⟨16327884524677446802088393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10885256349784964534725595 16327884524677446802088393)
    ·
      refine ⟨12245913393508085101566295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16327884524677446802088393 12245913393508085101566295)
      ·
        refine ⟨18368870090262127652349443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12245913393508085101566295 18368870090262127652349443)
        ·
          refine ⟨27553305135393191478524165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18368870090262127652349443 27553305135393191478524165)
          ·
            refine ⟨5166244712886223402223281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27553305135393191478524165 5166244712886223402223281)
            ·
              refine ⟨3874683534664667551667461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5166244712886223402223281 3874683534664667551667461)
              ·
                refine ⟨726503162749625165937649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3874683534664667551667461 726503162749625165937649)
                ·
                  refine ⟨544877372062218874453237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 726503162749625165937649 544877372062218874453237)
                  ·
                    refine ⟨51082253630833019479991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 544877372062218874453237 51082253630833019479991)
                    ·
                      rfl

theorem cell23_298447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_298447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298447 prefixEnd_298447 := by exact prefixLift 298447
  have htrace : WordTrace (prefixWord ++ tailWord_298447) baseStart_298447 baseEnd_298447 := by
    simpa [prefixWord, tailWord_298447, baseEnd_298447] using wordTrace_append hprefix tailTrace_298447
  have hstable : (prefixWord ++ tailWord_298447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298447).length < 2 ^ (prefixWord ++ tailWord_298447).sum := by decide
  have hdescent : baseEnd_298447 < baseStart_298447 := by decide
  rcases family_descends (prefixWord ++ tailWord_298447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298502 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_298502 : Nat := 118140960795 + 298502 * 2 ^ 59
def prefixEnd_298502 : Nat := 4983230072969 + 3 ^ 40 * 298502 * 2
def baseEnd_298502 : Nat := 17030555814277371472469

theorem tailTrace_298502 : CollatzResearch.WordTrace tailWord_298502 prefixEnd_298502 17030555814277371472469 := by
  unfold tailWord_298502
  simp only [CollatzResearch.WordTrace]
  refine ⟨340226948893303403999305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7258174909723805951985173 340226948893303403999305)
  ·
    refine ⟨255170211669977552999479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 340226948893303403999305 255170211669977552999479)
    ·
      refine ⟨382755317504966329499219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255170211669977552999479 382755317504966329499219)
      ·
        refine ⟨574132976257449494248829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382755317504966329499219 574132976257449494248829)
        ·
          refine ⟨215299866096543560343311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 574132976257449494248829 215299866096543560343311)
          ·
            refine ⟨322949799144815340514967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215299866096543560343311 322949799144815340514967)
            ·
              refine ⟨484424698717223010772451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322949799144815340514967 484424698717223010772451)
              ·
                refine ⟨726637048075834516158677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484424698717223010772451 726637048075834516158677)
                ·
                  refine ⟨17030555814277371472469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 726637048075834516158677 17030555814277371472469)
                  ·
                    rfl

theorem cell23_298502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_298502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298502 prefixEnd_298502 := by exact prefixLift 298502
  have htrace : WordTrace (prefixWord ++ tailWord_298502) baseStart_298502 baseEnd_298502 := by
    simpa [prefixWord, tailWord_298502, baseEnd_298502] using wordTrace_append hprefix tailTrace_298502
  have hstable : (prefixWord ++ tailWord_298502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298502).length < 2 ^ (prefixWord ++ tailWord_298502).sum := by decide
  have hdescent : baseEnd_298502 < baseStart_298502 := by decide
  rcases family_descends (prefixWord ++ tailWord_298502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298504 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 4, 2, 3]
def baseStart_298504 : Nat := 118140960795 + 298504 * 2 ^ 59
def prefixEnd_298504 : Nat := 4983230072969 + 3 ^ 40 * 298504 * 2
def baseEnd_298504 : Nat := 153276029289805335427211

theorem tailTrace_298504 : CollatzResearch.WordTrace tailWord_298504 prefixEnd_298504 153276029289805335427211 := by
  unfold tailWord_298504
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443667655289231634775283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7258223540385642179700377 5443667655289231634775283)
  ·
    refine ⟨8165501482933847452162925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5443667655289231634775283 8165501482933847452162925)
    ·
      refine ⟨3062063056100192794561097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8165501482933847452162925 3062063056100192794561097)
      ·
        refine ⟨2296547292075144595920823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3062063056100192794561097 2296547292075144595920823)
        ·
          refine ⟨3444820938112716893881235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296547292075144595920823 3444820938112716893881235)
          ·
            refine ⟨5167231407169075340821853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444820938112716893881235 5167231407169075340821853)
            ·
              refine ⟨1937711777688403252808195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5167231407169075340821853 1937711777688403252808195)
              ·
                refine ⟨2906567666532604879212293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937711777688403252808195 2906567666532604879212293)
                ·
                  refine ⟨544981437474863414852305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2906567666532604879212293 544981437474863414852305)
                  ·
                    refine ⟨408736078106147561139229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 544981437474863414852305 408736078106147561139229)
                    ·
                      refine ⟨153276029289805335427211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 408736078106147561139229 153276029289805335427211)
                      ·
                        rfl

theorem cell23_298504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_298504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298504 prefixEnd_298504 := by exact prefixLift 298504
  have htrace : WordTrace (prefixWord ++ tailWord_298504) baseStart_298504 baseEnd_298504 := by
    simpa [prefixWord, tailWord_298504, baseEnd_298504] using wordTrace_append hprefix tailTrace_298504
  have hstable : (prefixWord ++ tailWord_298504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298504).length < 2 ^ (prefixWord ++ tailWord_298504).sum := by decide
  have hdescent : baseEnd_298504 < baseStart_298504 := by decide
  rcases family_descends (prefixWord ++ tailWord_298504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298524 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 6]
def baseStart_298524 : Nat := 118140960795 + 298524 * 2 ^ 59
def prefixEnd_298524 : Nat := 4983230072969 + 3 ^ 40 * 298524 * 2
def baseEnd_298524 : Nat := 17031810989210584130791

theorem tailTrace_298524 : CollatzResearch.WordTrace tailWord_298524 prefixEnd_298524 17031810989210584130791 := by
  unfold tailWord_298524
  simp only [CollatzResearch.WordTrace]
  refine ⟨5444032385253003342639313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7258709847004004456852417 5444032385253003342639313)
  ·
    refine ⟨4083024288939752506979485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5444032385253003342639313 4083024288939752506979485)
    ·
      refine ⟨1531134108352407190117307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4083024288939752506979485 1531134108352407190117307)
      ·
        refine ⟨2296701162528610785175961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1531134108352407190117307 2296701162528610785175961)
        ·
          refine ⟨1722525871896458088881971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2296701162528610785175961 1722525871896458088881971)
          ·
            refine ⟨2583788807844687133322957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722525871896458088881971 2583788807844687133322957)
            ·
              refine ⟨968920802941757674996109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2583788807844687133322957 968920802941757674996109)
              ·
                refine ⟨363345301103159128123541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 968920802941757674996109 363345301103159128123541)
                ·
                  refine ⟨17031810989210584130791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 363345301103159128123541 17031810989210584130791)
                  ·
                    rfl

theorem cell23_298524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 6].length) (baseStart_298524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298524 prefixEnd_298524 := by exact prefixLift 298524
  have htrace : WordTrace (prefixWord ++ tailWord_298524) baseStart_298524 baseEnd_298524 := by
    simpa [prefixWord, tailWord_298524, baseEnd_298524] using wordTrace_append hprefix tailTrace_298524
  have hstable : (prefixWord ++ tailWord_298524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298524).length < 2 ^ (prefixWord ++ tailWord_298524).sum := by decide
  have hdescent : baseEnd_298524 < baseStart_298524 := by decide
  rcases family_descends (prefixWord ++ tailWord_298524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298527 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_298527 : Nat := 118140960795 + 298527 * 2 ^ 59
def prefixEnd_298527 : Nat := 4983230072969 + 3 ^ 40 * 298527 * 2
def baseEnd_298527 : Nat := 153287839344858745439605

theorem tailTrace_298527 : CollatzResearch.WordTrace tailWord_298527 prefixEnd_298527 153287839344858745439605 := by
  unfold tailWord_298527
  simp only [CollatzResearch.WordTrace]
  refine ⟨10888174189495138197637835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7258782792996758798425223 10888174189495138197637835)
  ·
    refine ⟨16332261284242707296456753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10888174189495138197637835 16332261284242707296456753)
    ·
      refine ⟨12249195963182030472342565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16332261284242707296456753 12249195963182030472342565)
      ·
        refine ⟨2296724243096630713564231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12249195963182030472342565 2296724243096630713564231)
        ·
          refine ⟨3445086364644946070346347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296724243096630713564231 3445086364644946070346347)
          ·
            refine ⟨5167629546967419105519521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445086364644946070346347 5167629546967419105519521)
            ·
              refine ⟨3875722160225564329139641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5167629546967419105519521 3875722160225564329139641)
              ·
                refine ⟨2906791620169173246854731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3875722160225564329139641 2906791620169173246854731)
                ·
                  refine ⟨4360187430253759870282097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906791620169173246854731 4360187430253759870282097)
                  ·
                    refine ⟨3270140572690319902711573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4360187430253759870282097 3270140572690319902711573)
                    ·
                      refine ⟨153287839344858745439605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3270140572690319902711573 153287839344858745439605)
                      ·
                        rfl

theorem cell23_298527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_298527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298527 prefixEnd_298527 := by exact prefixLift 298527
  have htrace : WordTrace (prefixWord ++ tailWord_298527) baseStart_298527 baseEnd_298527 := by
    simpa [prefixWord, tailWord_298527, baseEnd_298527] using wordTrace_append hprefix tailTrace_298527
  have hstable : (prefixWord ++ tailWord_298527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298527).length < 2 ^ (prefixWord ++ tailWord_298527).sum := by decide
  have hdescent : baseEnd_298527 < baseStart_298527 := by decide
  rcases family_descends (prefixWord ++ tailWord_298527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298584 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 6, 4]
def baseStart_298584 : Nat := 118140960795 + 298584 * 2 ^ 59
def prefixEnd_298584 : Nat := 4983230072969 + 3 ^ 40 * 298584 * 2
def baseEnd_298584 : Nat := 51105702580721674142281

theorem tailTrace_298584 : CollatzResearch.WordTrace tailWord_298584 prefixEnd_298584 51105702580721674142281 := by
  unfold tailWord_298584
  simp only [CollatzResearch.WordTrace]
  refine ⟨5445126575144318466231403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7260168766859091288308537 5445126575144318466231403)
  ·
    refine ⟨8167689862716477699347105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5445126575144318466231403 8167689862716477699347105)
    ·
      refine ⟨6125767397037358274510329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8167689862716477699347105 6125767397037358274510329)
      ·
        refine ⟨4594325547778018705882747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6125767397037358274510329 4594325547778018705882747)
        ·
          refine ⟨6891488321667028058824121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4594325547778018705882747 6891488321667028058824121)
          ·
            refine ⟨5168616241250271044118091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6891488321667028058824121 5168616241250271044118091)
            ·
              refine ⟨7752924361875406566177137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5168616241250271044118091 7752924361875406566177137)
              ·
                refine ⟨5814693271406554924632853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7752924361875406566177137 5814693271406554924632853)
                ·
                  refine ⟨272563747097182262092165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5814693271406554924632853 272563747097182262092165)
                  ·
                    refine ⟨51105702580721674142281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 272563747097182262092165 51105702580721674142281)
                    ·
                      rfl

theorem cell23_298584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 6, 4].length) (baseStart_298584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298584 prefixEnd_298584 := by exact prefixLift 298584
  have htrace : WordTrace (prefixWord ++ tailWord_298584) baseStart_298584 baseEnd_298584 := by
    simpa [prefixWord, tailWord_298584, baseEnd_298584] using wordTrace_append hprefix tailTrace_298584
  have hstable : (prefixWord ++ tailWord_298584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298584).length < 2 ^ (prefixWord ++ tailWord_298584).sum := by decide
  have hdescent : baseEnd_298584 < baseStart_298584 := by decide
  rcases family_descends (prefixWord ++ tailWord_298584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298605 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 1, 5]
def baseStart_298605 : Nat := 118140960795 + 298605 * 2 ^ 59
def prefixEnd_298605 : Nat := 4983230072969 + 3 ^ 40 * 298605 * 2
def baseEnd_298605 : Nat := 51109296945303146754749

theorem tailTrace_298605 : CollatzResearch.WordTrace tailWord_298605 prefixEnd_298605 51109296945303146754749 := by
  unfold tailWord_298605
  simp only [CollatzResearch.WordTrace]
  refine ⟨10891019083212557518977269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7260679388808371679318179 10891019083212557518977269)
  ·
    refine ⟨1021033039051177267404119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10891019083212557518977269 1021033039051177267404119)
    ·
      refine ⟨1531549558576765901106179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1021033039051177267404119 1531549558576765901106179)
      ·
        refine ⟨2297324337865148851659269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1531549558576765901106179 2297324337865148851659269)
        ·
          refine ⟨430748313349715409686113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2297324337865148851659269 430748313349715409686113)
          ·
            refine ⟨323061235012286557264585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430748313349715409686113 323061235012286557264585)
            ·
              refine ⟨242295926259214917948439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323061235012286557264585 242295926259214917948439)
              ·
                refine ⟨363443889388822376922659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242295926259214917948439 363443889388822376922659)
                ·
                  refine ⟨545165834083233565383989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363443889388822376922659 545165834083233565383989)
                  ·
                    refine ⟨51109296945303146754749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 545165834083233565383989 51109296945303146754749)
                    ·
                      rfl

theorem cell23_298605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_298605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298605 prefixEnd_298605 := by exact prefixLift 298605
  have htrace : WordTrace (prefixWord ++ tailWord_298605) baseStart_298605 baseEnd_298605 := by
    simpa [prefixWord, tailWord_298605, baseEnd_298605] using wordTrace_append hprefix tailTrace_298605
  have hstable : (prefixWord ++ tailWord_298605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298605).length < 2 ^ (prefixWord ++ tailWord_298605).sum := by decide
  have hdescent : baseEnd_298605 < baseStart_298605 := by decide
  rcases family_descends (prefixWord ++ tailWord_298605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298608 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 1, 1, 4]
def baseStart_298608 : Nat := 118140960795 + 298608 * 2 ^ 59
def prefixEnd_298608 : Nat := 4983230072969 + 3 ^ 40 * 298608 * 2
def baseEnd_298608 : Nat := 153329431277872928526733

theorem tailTrace_298608 : CollatzResearch.WordTrace tailWord_298608 prefixEnd_298608 153329431277872928526733 := by
  unfold tailWord_298608
  simp only [CollatzResearch.WordTrace]
  refine ⟨5445564251100844515668239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7260752334801126020890985 5445564251100844515668239)
  ·
    refine ⟨8168346376651266773502359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5445564251100844515668239 8168346376651266773502359)
    ·
      refine ⟨12252519564976900160253539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8168346376651266773502359 12252519564976900160253539)
      ·
        refine ⟨18378779347465350240380309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12252519564976900160253539 18378779347465350240380309)
        ·
          refine ⟨861505281912438292517827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18378779347465350240380309 861505281912438292517827)
          ·
            refine ⟨1292257922868657438776741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 861505281912438292517827 1292257922868657438776741)
            ·
              refine ⟨242298360537873269770639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1292257922868657438776741 242298360537873269770639)
              ·
                refine ⟨363447540806809904655959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242298360537873269770639 363447540806809904655959)
                ·
                  refine ⟨545171311210214856983939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363447540806809904655959 545171311210214856983939)
                  ·
                    refine ⟨817756966815322285475909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 545171311210214856983939 817756966815322285475909)
                    ·
                      refine ⟨153329431277872928526733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 817756966815322285475909 153329431277872928526733)
                      ·
                        rfl

theorem cell23_298608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 1, 4].length) (baseStart_298608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298608 prefixEnd_298608 := by exact prefixLift 298608
  have htrace : WordTrace (prefixWord ++ tailWord_298608) baseStart_298608 baseEnd_298608 := by
    simpa [prefixWord, tailWord_298608, baseEnd_298608] using wordTrace_append hprefix tailTrace_298608
  have hstable : (prefixWord ++ tailWord_298608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298608).length < 2 ^ (prefixWord ++ tailWord_298608).sum := by decide
  have hdescent : baseEnd_298608 < baseStart_298608 := by decide
  rcases family_descends (prefixWord ++ tailWord_298608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298625 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_298625 : Nat := 118140960795 + 298625 * 2 ^ 59
def prefixEnd_298625 : Nat := 4983230072969 + 3 ^ 40 * 298625 * 2
def baseEnd_298625 : Nat := 153338160448999362014155

theorem tailTrace_298625 : CollatzResearch.WordTrace tailWord_298625 prefixEnd_298625 153338160448999362014155 := by
  unfold tailWord_298625
  simp only [CollatzResearch.WordTrace]
  refine ⟨10891748543140100934705329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7261165695426733956470219 10891748543140100934705329)
  ·
    refine ⟨8168811407355075701028997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10891748543140100934705329 8168811407355075701028997)
    ·
      refine ⟨1531652138879076693942937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8168811407355075701028997 1531652138879076693942937)
      ·
        refine ⟨1148739104159307520457203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1531652138879076693942937 1148739104159307520457203)
        ·
          refine ⟨1723108656238961280685805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148739104159307520457203 1723108656238961280685805)
          ·
            refine ⟨646165746089610480257177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1723108656238961280685805 646165746089610480257177)
            ·
              refine ⟨484624309567207860192883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646165746089610480257177 484624309567207860192883)
              ·
                refine ⟨726936464350811790289325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484624309567207860192883 726936464350811790289325)
                ·
                  refine ⟨272601174131554421358497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726936464350811790289325 272601174131554421358497)
                  ·
                    refine ⟨204450880598665816018873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 272601174131554421358497 204450880598665816018873)
                    ·
                      refine ⟨153338160448999362014155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 204450880598665816018873 153338160448999362014155)
                      ·
                        rfl

theorem cell23_298625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_298625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298625 prefixEnd_298625 := by exact prefixLift 298625
  have htrace : WordTrace (prefixWord ++ tailWord_298625) baseStart_298625 baseEnd_298625 := by
    simpa [prefixWord, tailWord_298625, baseEnd_298625] using wordTrace_append hprefix tailTrace_298625
  have hstable : (prefixWord ++ tailWord_298625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298625).length < 2 ^ (prefixWord ++ tailWord_298625).sum := by decide
  have hdescent : baseEnd_298625 < baseStart_298625 := by decide
  rcases family_descends (prefixWord ++ tailWord_298625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298638 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4]
def baseStart_298638 : Nat := 118140960795 + 298638 * 2 ^ 59
def prefixEnd_298638 : Nat := 4983230072969 + 3 ^ 40 * 298638 * 2
def baseEnd_298638 : Nat := 153344835697507811151595

theorem tailTrace_298638 : CollatzResearch.WordTrace tailWord_298638 prefixEnd_298638 153344835697507811151595 := by
  unfold tailWord_298638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1361527836511625519366071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7261481794728669436619045 1361527836511625519366071)
  ·
    refine ⟨2042291754767438279049107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1361527836511625519366071 2042291754767438279049107)
    ·
      refine ⟨3063437632151157418573661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2042291754767438279049107 3063437632151157418573661)
      ·
        refine ⟨1148789112056684031965123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3063437632151157418573661 1148789112056684031965123)
        ·
          refine ⟨1723183668085026047947685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148789112056684031965123 1723183668085026047947685)
          ·
            refine ⟨323096937765942383990191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1723183668085026047947685 323096937765942383990191)
            ·
              refine ⟨484645406648913575985287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323096937765942383990191 484645406648913575985287)
              ·
                refine ⟨726968109973370363977931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 484645406648913575985287 726968109973370363977931)
                ·
                  refine ⟨1090452164960055545966897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 726968109973370363977931 1090452164960055545966897)
                  ·
                    refine ⟨817839123720041659475173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1090452164960055545966897 817839123720041659475173)
                    ·
                      refine ⟨153344835697507811151595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 817839123720041659475173 153344835697507811151595)
                      ·
                        rfl

theorem cell23_298638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_298638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298638 prefixEnd_298638 := by exact prefixLift 298638
  have htrace : WordTrace (prefixWord ++ tailWord_298638) baseStart_298638 baseEnd_298638 := by
    simpa [prefixWord, tailWord_298638, baseEnd_298638] using wordTrace_append hprefix tailTrace_298638
  have hstable : (prefixWord ++ tailWord_298638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298638).length < 2 ^ (prefixWord ++ tailWord_298638).sum := by decide
  have hdescent : baseEnd_298638 < baseStart_298638 := by decide
  rcases family_descends (prefixWord ++ tailWord_298638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298674 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_298674 : Nat := 118140960795 + 298674 * 2 ^ 59
def prefixEnd_298674 : Nat := 4983230072969 + 3 ^ 40 * 298674 * 2
def baseEnd_298674 : Nat := 51121107000356556767143

theorem tailTrace_298674 : CollatzResearch.WordTrace tailWord_298674 prefixEnd_298674 51121107000356556767143 := by
  unfold tailWord_298674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2723383929990645575809769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7262357146641721535492717 2723383929990645575809769)
  ·
    refine ⟨2042537947492984181857327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2723383929990645575809769 2042537947492984181857327)
    ·
      refine ⟨3063806921239476272785991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2042537947492984181857327 3063806921239476272785991)
      ·
        refine ⟨4595710381859214409178987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063806921239476272785991 4595710381859214409178987)
        ·
          refine ⟨6893565572788821613768481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595710381859214409178987 6893565572788821613768481)
          ·
            refine ⟨5170174179591616210326361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6893565572788821613768481 5170174179591616210326361)
            ·
              refine ⟨3877630634693712157744771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5170174179591616210326361 3877630634693712157744771)
              ·
                refine ⟨5816445952040568236617157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877630634693712157744771 5816445952040568236617157)
                ·
                  refine ⟨1090583616007606544365717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5816445952040568236617157 1090583616007606544365717)
                  ·
                    refine ⟨51121107000356556767143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1090583616007606544365717 51121107000356556767143)
                    ·
                      rfl

theorem cell23_298674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_298674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298674 prefixEnd_298674 := by exact prefixLift 298674
  have htrace : WordTrace (prefixWord ++ tailWord_298674) baseStart_298674 baseEnd_298674 := by
    simpa [prefixWord, tailWord_298674, baseEnd_298674] using wordTrace_append hprefix tailTrace_298674
  have hstable : (prefixWord ++ tailWord_298674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298674).length < 2 ^ (prefixWord ++ tailWord_298674).sum := by decide
  have hdescent : baseEnd_298674 < baseStart_298674 := by decide
  rcases family_descends (prefixWord ++ tailWord_298674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298738 : List Nat := [3, 2, 1, 3, 1, 1, 3, 4, 5]
def baseStart_298738 : Nat := 118140960795 + 298738 * 2 ^ 59
def prefixEnd_298738 : Nat := 4983230072969 + 3 ^ 40 * 298738 * 2
def baseEnd_298738 : Nat := 17044020418106379989015

theorem tailTrace_298738 : CollatzResearch.WordTrace tailWord_298738 prefixEnd_298738 17044020418106379989015 := by
  unfold tailWord_298738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2723967497932680308392217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7263913327820480822379245 2723967497932680308392217)
  ·
    refine ⟨2042975623449510231294163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2723967497932680308392217 2042975623449510231294163)
    ·
      refine ⟨3064463435174265346941245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2042975623449510231294163 3064463435174265346941245)
      ·
        refine ⟨1149173788190349505102967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3064463435174265346941245 1149173788190349505102967)
        ·
          refine ⟨1723760682285524257654451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1149173788190349505102967 1723760682285524257654451)
          ·
            refine ⟨2585641023428286386481677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723760682285524257654451 2585641023428286386481677)
            ·
              refine ⟨969615383785607394930629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2585641023428286386481677 969615383785607394930629)
              ·
                refine ⟨181802884459801386549493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 969615383785607394930629 181802884459801386549493)
                ·
                  refine ⟨17044020418106379989015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 181802884459801386549493 17044020418106379989015)
                  ·
                    rfl

theorem cell23_298738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_298738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298738 prefixEnd_298738 := by exact prefixLift 298738
  have htrace : WordTrace (prefixWord ++ tailWord_298738) baseStart_298738 baseEnd_298738 := by
    simpa [prefixWord, tailWord_298738, baseEnd_298738] using wordTrace_append hprefix tailTrace_298738
  have hstable : (prefixWord ++ tailWord_298738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298738).length < 2 ^ (prefixWord ++ tailWord_298738).sum := by decide
  have hdescent : baseEnd_298738 < baseStart_298738 := by decide
  rcases family_descends (prefixWord ++ tailWord_298738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298744 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_298744 : Nat := 118140960795 + 298744 * 2 ^ 59
def prefixEnd_298744 : Nat := 4983230072969 + 3 ^ 40 * 298744 * 2
def baseEnd_298744 : Nat := 153399264646884396426107

theorem tailTrace_298744 : CollatzResearch.WordTrace tailWord_298744 prefixEnd_298744 153399264646884396426107 := by
  unfold tailWord_298744
  simp only [CollatzResearch.WordTrace]
  refine ⟨5448044414854492129143643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7264059219805989505524857 5448044414854492129143643)
  ·
    refine ⟨8172066622281738193715465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5448044414854492129143643 8172066622281738193715465)
    ·
      refine ⟨6129049966711303645286599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8172066622281738193715465 6129049966711303645286599)
      ·
        refine ⟨9193574950066955467929899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6129049966711303645286599 9193574950066955467929899)
        ·
          refine ⟨13790362425100433201894849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9193574950066955467929899 13790362425100433201894849)
          ·
            refine ⟨10342771818825324901421137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13790362425100433201894849 10342771818825324901421137)
            ·
              refine ⟨7757078864118993676065853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10342771818825324901421137 7757078864118993676065853)
              ·
                refine ⟨2908904574044622628524695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7757078864118993676065853 2908904574044622628524695)
                ·
                  refine ⟨4363356861066933942787043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908904574044622628524695 4363356861066933942787043)
                  ·
                    refine ⟨6545035291600400914180565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4363356861066933942787043 6545035291600400914180565)
                    ·
                      refine ⟨153399264646884396426107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6545035291600400914180565 153399264646884396426107)
                      ·
                        rfl

theorem cell23_298744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_298744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298744 prefixEnd_298744 := by exact prefixLift 298744
  have htrace : WordTrace (prefixWord ++ tailWord_298744) baseStart_298744 baseEnd_298744 := by
    simpa [prefixWord, tailWord_298744, baseEnd_298744] using wordTrace_append hprefix tailTrace_298744
  have hstable : (prefixWord ++ tailWord_298744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298744).length < 2 ^ (prefixWord ++ tailWord_298744).sum := by decide
  have hdescent : baseEnd_298744 < baseStart_298744 := by decide
  rcases family_descends (prefixWord ++ tailWord_298744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298771 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 4]
def baseStart_298771 : Nat := 118140960795 + 298771 * 2 ^ 59
def prefixEnd_298771 : Nat := 4983230072969 + 3 ^ 40 * 298771 * 2
def baseEnd_298771 : Nat := 153413128624555790788483

theorem tailTrace_298771 : CollatzResearch.WordTrace tailWord_298771 prefixEnd_298771 153413128624555790788483 := by
  unfold tailWord_298771
  simp only [CollatzResearch.WordTrace]
  refine ⟨10897073600611167869520167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7264715733740778579680111 10897073600611167869520167)
  ·
    refine ⟨16345610400916751804280251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10897073600611167869520167 16345610400916751804280251)
    ·
      refine ⟨24518415601375127706420377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16345610400916751804280251 24518415601375127706420377)
      ·
        refine ⟨18388811701031345779815283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24518415601375127706420377 18388811701031345779815283)
        ·
          refine ⟨27583217551547018669722925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18388811701031345779815283 27583217551547018669722925)
          ·
            refine ⟨10343706581830132001146097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27583217551547018669722925 10343706581830132001146097)
            ·
              refine ⟨7757779936372599000859573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10343706581830132001146097 7757779936372599000859573)
              ·
                refine ⟨727291869034931156330585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7757779936372599000859573 727291869034931156330585)
                ·
                  refine ⟨545468901776198367247939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 727291869034931156330585 545468901776198367247939)
                  ·
                    refine ⟨818203352664297550871909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 545468901776198367247939 818203352664297550871909)
                    ·
                      refine ⟨153413128624555790788483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 818203352664297550871909 153413128624555790788483)
                      ·
                        rfl

theorem cell23_298771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_298771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298771 prefixEnd_298771 := by exact prefixLift 298771
  have htrace : WordTrace (prefixWord ++ tailWord_298771) baseStart_298771 baseEnd_298771 := by
    simpa [prefixWord, tailWord_298771, baseEnd_298771] using wordTrace_append hprefix tailTrace_298771
  have hstable : (prefixWord ++ tailWord_298771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298771).length < 2 ^ (prefixWord ++ tailWord_298771).sum := by decide
  have hdescent : baseEnd_298771 < baseStart_298771 := by decide
  rcases family_descends (prefixWord ++ tailWord_298771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298821 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 2, 5, 3]
def baseStart_298821 : Nat := 118140960795 + 298821 * 2 ^ 59
def prefixEnd_298821 : Nat := 4983230072969 + 3 ^ 40 * 298821 * 2
def baseEnd_298821 : Nat := 153438802657280595163253

theorem tailTrace_298821 : CollatzResearch.WordTrace tailWord_298821 prefixEnd_298821 153438802657280595163253 := by
  unfold tailWord_298821
  simp only [CollatzResearch.WordTrace]
  refine ⟨10898897250430026408840317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7265931500286684272560211 10898897250430026408840317)
  ·
    refine ⟨4087086468911259903315119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10898897250430026408840317 4087086468911259903315119)
    ·
      refine ⟨6130629703366889854972679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4087086468911259903315119 6130629703366889854972679)
      ·
        refine ⟨9195944555050334782459019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6130629703366889854972679 9195944555050334782459019)
        ·
          refine ⟨13793916832575502173688529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9195944555050334782459019 13793916832575502173688529)
          ·
            refine ⟨10345437624431626630266397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13793916832575502173688529 10345437624431626630266397)
            ·
              refine ⟨3879539109161859986349899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10345437624431626630266397 3879539109161859986349899)
              ·
                refine ⟨5819308663742789979524849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3879539109161859986349899 5819308663742789979524849)
                ·
                  refine ⟨4364481497807092484643637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5819308663742789979524849 4364481497807092484643637)
                  ·
                    refine ⟨409170140419414920435341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4364481497807092484643637 409170140419414920435341)
                    ·
                      refine ⟨153438802657280595163253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 409170140419414920435341 153438802657280595163253)
                      ·
                        rfl

theorem cell23_298821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5, 3].length) (baseStart_298821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298821 prefixEnd_298821 := by exact prefixLift 298821
  have htrace : WordTrace (prefixWord ++ tailWord_298821) baseStart_298821 baseEnd_298821 := by
    simpa [prefixWord, tailWord_298821, baseEnd_298821] using wordTrace_append hprefix tailTrace_298821
  have hstable : (prefixWord ++ tailWord_298821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298821).length < 2 ^ (prefixWord ++ tailWord_298821).sum := by decide
  have hdescent : baseEnd_298821 < baseStart_298821 := by decide
  rcases family_descends (prefixWord ++ tailWord_298821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298862 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_298862 : Nat := 118140960795 + 298862 * 2 ^ 59
def prefixEnd_298862 : Nat := 4983230072969 + 3 ^ 40 * 298862 * 2
def baseEnd_298862 : Nat := 17051095040457214972285

theorem tailTrace_298862 : CollatzResearch.WordTrace tailWord_298862 prefixEnd_298862 17051095040457214972285 := by
  unfold tailWord_298862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1362549080410186301385355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7266928428854326940721893 1362549080410186301385355)
  ·
    refine ⟨2043823620615279452078033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1362549080410186301385355 2043823620615279452078033)
    ·
      refine ⟨1532867715461459589058525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2043823620615279452078033 1532867715461459589058525)
      ·
        refine ⟨574825393298047345896947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1532867715461459589058525 574825393298047345896947)
        ·
          refine ⟨862238089947071018845421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574825393298047345896947 862238089947071018845421)
          ·
            refine ⟨323339283730151632067033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 862238089947071018845421 323339283730151632067033)
            ·
              refine ⟨242504462797613724050275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323339283730151632067033 242504462797613724050275)
              ·
                refine ⟨363756694196420586075413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242504462797613724050275 363756694196420586075413)
                ·
                  refine ⟨17051095040457214972285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 363756694196420586075413 17051095040457214972285)
                  ·
                    rfl

theorem cell23_298862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_298862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298862 prefixEnd_298862 := by exact prefixLift 298862
  have htrace : WordTrace (prefixWord ++ tailWord_298862) baseStart_298862 baseEnd_298862 := by
    simpa [prefixWord, tailWord_298862, baseEnd_298862] using wordTrace_append hprefix tailTrace_298862
  have hstable : (prefixWord ++ tailWord_298862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298862).length < 2 ^ (prefixWord ++ tailWord_298862).sum := by decide
  have hdescent : baseEnd_298862 < baseStart_298862 := by decide
  rcases family_descends (prefixWord ++ tailWord_298862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298906 : List Nat := [3, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3]
def baseStart_298906 : Nat := 118140960795 + 298906 * 2 ^ 59
def prefixEnd_298906 : Nat := 4983230072969 + 3 ^ 40 * 298906 * 2
def baseEnd_298906 : Nat := 153482448512912762600363

theorem tailTrace_298906 : CollatzResearch.WordTrace tailWord_298906 prefixEnd_298906 153482448512912762600363 := by
  unfold tailWord_298906
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725499363780521481421143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7267998303414723950456381 2725499363780521481421143)
  ·
    refine ⟨4088249045670782222131715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2725499363780521481421143 4088249045670782222131715)
    ·
      refine ⟨6132373568506173333197573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4088249045670782222131715 6132373568506173333197573)
      ·
        refine ⟨1149820044094907499974545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6132373568506173333197573 1149820044094907499974545)
        ·
          refine ⟨862365033071180624980909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1149820044094907499974545 862365033071180624980909)
          ·
            refine ⟨323386887401692734367841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 862365033071180624980909 323386887401692734367841)
            ·
              refine ⟨242540165551269550775881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323386887401692734367841 242540165551269550775881)
              ·
                refine ⟨181905124163452163081911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242540165551269550775881 181905124163452163081911)
                ·
                  refine ⟨272857686245178244622867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181905124163452163081911 272857686245178244622867)
                  ·
                    refine ⟨409286529367767366934301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 272857686245178244622867 409286529367767366934301)
                    ·
                      refine ⟨153482448512912762600363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 409286529367767366934301 153482448512912762600363)
                      ·
                        rfl

theorem cell23_298906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_298906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298906 prefixEnd_298906 := by exact prefixLift 298906
  have htrace : WordTrace (prefixWord ++ tailWord_298906) baseStart_298906 baseEnd_298906 := by
    simpa [prefixWord, tailWord_298906, baseEnd_298906] using wordTrace_append hprefix tailTrace_298906
  have hstable : (prefixWord ++ tailWord_298906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298906).length < 2 ^ (prefixWord ++ tailWord_298906).sum := by decide
  have hdescent : baseEnd_298906 < baseStart_298906 := by decide
  rcases family_descends (prefixWord ++ tailWord_298906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298931 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 2, 7]
def baseStart_298931 : Nat := 118140960795 + 298931 * 2 ^ 59
def prefixEnd_298931 : Nat := 4983230072969 + 3 ^ 40 * 298931 * 2
def baseEnd_298931 : Nat := 51165095176425054929249

theorem tailTrace_298931 : CollatzResearch.WordTrace tailWord_298931 prefixEnd_298931 51165095176425054929249 := by
  unfold tailWord_298931
  simp only [CollatzResearch.WordTrace]
  refine ⟨10902909280031515195344647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7268606186687676796896431 10902909280031515195344647)
  ·
    refine ⟨16354363920047272793016971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10902909280031515195344647 16354363920047272793016971)
    ·
      refine ⟨24531545880070909189525457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16354363920047272793016971 24531545880070909189525457)
      ·
        refine ⟨18398659410053181892144093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24531545880070909189525457 18398659410053181892144093)
        ·
          refine ⟨6899497278769943209554035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18398659410053181892144093 6899497278769943209554035)
          ·
            refine ⟨10349245918154914814331053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6899497278769943209554035 10349245918154914814331053)
            ·
              refine ⟨3880967219308093055374145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10349245918154914814331053 3880967219308093055374145)
              ·
                refine ⟨2910725414481069791530609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3880967219308093055374145 2910725414481069791530609)
                ·
                  refine ⟨2183044060860802343647957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2910725414481069791530609 2183044060860802343647957)
                  ·
                    refine ⟨51165095176425054929249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2183044060860802343647957 51165095176425054929249)
                    ·
                      rfl

theorem cell23_298931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 7].length) (baseStart_298931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298931 prefixEnd_298931 := by exact prefixLift 298931
  have htrace : WordTrace (prefixWord ++ tailWord_298931) baseStart_298931 baseEnd_298931 := by
    simpa [prefixWord, tailWord_298931, baseEnd_298931] using wordTrace_append hprefix tailTrace_298931
  have hstable : (prefixWord ++ tailWord_298931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298931).length < 2 ^ (prefixWord ++ tailWord_298931).sum := by decide
  have hdescent : baseEnd_298931 < baseStart_298931 := by decide
  rcases family_descends (prefixWord ++ tailWord_298931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298979 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 2, 1, 3]
def baseStart_298979 : Nat := 118140960795 + 298979 * 2 ^ 59
def prefixEnd_298979 : Nat := 4983230072969 + 3 ^ 40 * 298979 * 2
def baseEnd_298979 : Nat := 153519932600690976987527

theorem tailTrace_298979 : CollatzResearch.WordTrace tailWord_298979 prefixEnd_298979 153519932600690976987527 := by
  unfold tailWord_298979
  simp only [CollatzResearch.WordTrace]
  refine ⟨10904659983857619393091991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7269773322571746262061327 10904659983857619393091991)
  ·
    refine ⟨16356989975786429089637987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10904659983857619393091991 16356989975786429089637987)
    ·
      refine ⟨24535484963679643634456981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16356989975786429089637987 24535484963679643634456981)
      ·
        refine ⟨1150100857672483295365171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24535484963679643634456981 1150100857672483295365171)
        ·
          refine ⟨1725151286508724943047757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1150100857672483295365171 1725151286508724943047757)
          ·
            refine ⟨646931732440771853642909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1725151286508724943047757 646931732440771853642909)
            ·
              refine ⟨242599399665289445116091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 646931732440771853642909 242599399665289445116091)
              ·
                refine ⟨363899099497934167674137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242599399665289445116091 363899099497934167674137)
                ·
                  refine ⟨272924324623450625755603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363899099497934167674137 272924324623450625755603)
                  ·
                    refine ⟨409386486935175938633405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 272924324623450625755603 409386486935175938633405)
                    ·
                      refine ⟨153519932600690976987527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 409386486935175938633405 153519932600690976987527)
                      ·
                        rfl

theorem cell23_298979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_298979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298979 prefixEnd_298979 := by exact prefixLift 298979
  have htrace : WordTrace (prefixWord ++ tailWord_298979) baseStart_298979 baseEnd_298979 := by
    simpa [prefixWord, tailWord_298979, baseEnd_298979] using wordTrace_append hprefix tailTrace_298979
  have hstable : (prefixWord ++ tailWord_298979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298979).length < 2 ^ (prefixWord ++ tailWord_298979).sum := by decide
  have hdescent : baseEnd_298979 < baseStart_298979 := by decide
  rcases family_descends (prefixWord ++ tailWord_298979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_298988 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 3]
def baseStart_298988 : Nat := 118140960795 + 298988 * 2 ^ 59
def prefixEnd_298988 : Nat := 4983230072969 + 3 ^ 40 * 298988 * 2
def baseEnd_298988 : Nat := 153524553926581441774985

theorem tailTrace_298988 : CollatzResearch.WordTrace tailWord_298988 prefixEnd_298988 153524553926581441774985 := by
  unfold tailWord_298988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5452494120412506965084809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7269992160550009286779745 5452494120412506965084809)
  ·
    refine ⟨4089370590309380223813607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5452494120412506965084809 4089370590309380223813607)
    ·
      refine ⟨6134055885464070335720411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4089370590309380223813607 6134055885464070335720411)
      ·
        refine ⟨9201083828196105503580617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6134055885464070335720411 9201083828196105503580617)
        ·
          refine ⟨6900812871147079127685463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9201083828196105503580617 6900812871147079127685463)
          ·
            refine ⟨10351219306720618691528195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6900812871147079127685463 10351219306720618691528195)
            ·
              refine ⟨15526828960080928037292293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10351219306720618691528195 15526828960080928037292293)
              ·
                refine ⟨2911280430015174006992305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15526828960080928037292293 2911280430015174006992305)
                ·
                  refine ⟨2183460322511380505244229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2911280430015174006992305 2183460322511380505244229)
                  ·
                    refine ⟨409398810470883844733293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2183460322511380505244229 409398810470883844733293)
                    ·
                      refine ⟨153524553926581441774985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 409398810470883844733293 153524553926581441774985)
                      ·
                        rfl

theorem cell23_298988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_298988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_298988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_298988 prefixEnd_298988 := by exact prefixLift 298988
  have htrace : WordTrace (prefixWord ++ tailWord_298988) baseStart_298988 baseEnd_298988 := by
    simpa [prefixWord, tailWord_298988, baseEnd_298988] using wordTrace_append hprefix tailTrace_298988
  have hstable : (prefixWord ++ tailWord_298988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_298988).length < 2 ^ (prefixWord ++ tailWord_298988).sum := by decide
  have hdescent : baseEnd_298988 < baseStart_298988 := by decide
  rcases family_descends (prefixWord ++ tailWord_298988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299014 : List Nat := [6, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_299014 : Nat := 118140960795 + 299014 * 2 ^ 59
def prefixEnd_299014 : Nat := 4983230072969 + 3 ^ 40 * 299014 * 2
def baseEnd_299014 : Nat := 153537904423598340049867

theorem tailTrace_299014 : CollatzResearch.WordTrace tailWord_299014 prefixEnd_299014 153537904423598340049867 := by
  unfold tailWord_299014
  simp only [CollatzResearch.WordTrace]
  refine ⟨340810516835338136581753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7270624359153880247077397 340810516835338136581753)
  ·
    refine ⟨255607887626503602436315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 340810516835338136581753 255607887626503602436315)
    ·
      refine ⟨383411831439755403654473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255607887626503602436315 383411831439755403654473)
      ·
        refine ⟨287558873579816552740855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383411831439755403654473 287558873579816552740855)
        ·
          refine ⟨431338310369724829111283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287558873579816552740855 431338310369724829111283)
          ·
            refine ⟨647007465554587243666925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431338310369724829111283 647007465554587243666925)
            ·
              refine ⟨242627799582970216375097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 647007465554587243666925 242627799582970216375097)
              ·
                refine ⟨181970849687227662281323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242627799582970216375097 181970849687227662281323)
                ·
                  refine ⟨272956274530841493421985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 181970849687227662281323 272956274530841493421985)
                  ·
                    refine ⟨204717205898131120066489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 272956274530841493421985 204717205898131120066489)
                    ·
                      refine ⟨153537904423598340049867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 204717205898131120066489 153537904423598340049867)
                      ·
                        rfl

theorem cell23_299014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_299014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299014 prefixEnd_299014 := by exact prefixLift 299014
  have htrace : WordTrace (prefixWord ++ tailWord_299014) baseStart_299014 baseEnd_299014 := by
    simpa [prefixWord, tailWord_299014, baseEnd_299014] using wordTrace_append hprefix tailTrace_299014
  have hstable : (prefixWord ++ tailWord_299014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299014).length < 2 ^ (prefixWord ++ tailWord_299014).sum := by decide
  have hdescent : baseEnd_299014 < baseStart_299014 := by decide
  rcases family_descends (prefixWord ++ tailWord_299014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299036 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_299036 : Nat := 118140960795 + 299036 * 2 ^ 59
def prefixEnd_299036 : Nat := 4983230072969 + 3 ^ 40 * 299036 * 2
def baseEnd_299036 : Nat := 153549200997997253974765

theorem tailTrace_299036 : CollatzResearch.WordTrace tailWord_299036 prefixEnd_299036 153549200997997253974765 := by
  unfold tailWord_299036
  simp only [CollatzResearch.WordTrace]
  refine ⟨5453369472325559063958481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7271159296434078751944641 5453369472325559063958481)
  ·
    refine ⟨4090027104244169297968861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5453369472325559063958481 4090027104244169297968861)
    ·
      refine ⟨1533760164091563486738323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4090027104244169297968861 1533760164091563486738323)
      ·
        refine ⟨2300640246137345230107485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1533760164091563486738323 2300640246137345230107485)
        ·
          refine ⟨862740092301504461290307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2300640246137345230107485 862740092301504461290307)
          ·
            refine ⟨1294110138452256691935461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862740092301504461290307 1294110138452256691935461)
            ·
              refine ⟨242645650959798129737899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1294110138452256691935461 242645650959798129737899)
              ·
                refine ⟨363968476439697194606849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242645650959798129737899 363968476439697194606849)
                ·
                  refine ⟨272976357329772895955137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 363968476439697194606849 272976357329772895955137)
                  ·
                    refine ⟨204732267997329671966353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 272976357329772895955137 204732267997329671966353)
                    ·
                      refine ⟨153549200997997253974765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 204732267997329671966353 153549200997997253974765)
                      ·
                        rfl

theorem cell23_299036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_299036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299036 prefixEnd_299036 := by exact prefixLift 299036
  have htrace : WordTrace (prefixWord ++ tailWord_299036) baseStart_299036 baseEnd_299036 := by
    simpa [prefixWord, tailWord_299036, baseEnd_299036] using wordTrace_append hprefix tailTrace_299036
  have hstable : (prefixWord ++ tailWord_299036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299036).length < 2 ^ (prefixWord ++ tailWord_299036).sum := by decide
  have hdescent : baseEnd_299036 < baseStart_299036 := by decide
  rcases family_descends (prefixWord ++ tailWord_299036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299088 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 4]
def baseStart_299088 : Nat := 118140960795 + 299088 * 2 ^ 59
def prefixEnd_299088 : Nat := 4983230072969 + 3 ^ 40 * 299088 * 2
def baseEnd_299088 : Nat := 153575901992031050524525

theorem tailTrace_299088 : CollatzResearch.WordTrace tailWord_299088 prefixEnd_299088 153575901992031050524525 := by
  unfold tailWord_299088
  simp only [CollatzResearch.WordTrace]
  refine ⟨5454317770231365504404959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7272423693641820672539945 5454317770231365504404959)
  ·
    refine ⟨8181476655347048256607439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5454317770231365504404959 8181476655347048256607439)
    ·
      refine ⟨12272214983020572384911159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8181476655347048256607439 12272214983020572384911159)
      ·
        refine ⟨18408322474530858577366739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12272214983020572384911159 18408322474530858577366739)
        ·
          refine ⟨27612483711796287866050109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18408322474530858577366739 27612483711796287866050109)
          ·
            refine ⟨10354681391923607949768791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27612483711796287866050109 10354681391923607949768791)
            ·
              refine ⟨15532022087885411924653187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10354681391923607949768791 15532022087885411924653187)
              ·
                refine ⟨23298033131828117886979781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15532022087885411924653187 23298033131828117886979781)
                ·
                  refine ⟨4368381212217772103808709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23298033131828117886979781 4368381212217772103808709)
                  ·
                    refine ⟨819071477290832269464133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4368381212217772103808709 819071477290832269464133)
                    ·
                      refine ⟨153575901992031050524525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 819071477290832269464133 153575901992031050524525)
                      ·
                        rfl

theorem cell23_299088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_299088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299088 prefixEnd_299088 := by exact prefixLift 299088
  have htrace : WordTrace (prefixWord ++ tailWord_299088) baseStart_299088 baseEnd_299088 := by
    simpa [prefixWord, tailWord_299088, baseEnd_299088] using wordTrace_append hprefix tailTrace_299088
  have hstable : (prefixWord ++ tailWord_299088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299088).length < 2 ^ (prefixWord ++ tailWord_299088).sum := by decide
  have hdescent : baseEnd_299088 < baseStart_299088 := by decide
  rcases family_descends (prefixWord ++ tailWord_299088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299095 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 3]
def baseStart_299095 : Nat := 118140960795 + 299095 * 2 ^ 59
def prefixEnd_299095 : Nat := 4983230072969 + 3 ^ 40 * 299095 * 2
def baseEnd_299095 : Nat := 153579496356612523136993

theorem tailTrace_299095 : CollatzResearch.WordTrace tailWord_299095 prefixEnd_299095 153579496356612523136993 := by
  unfold tailWord_299095
  simp only [CollatzResearch.WordTrace]
  refine ⟨10908890851437371204314739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7272593900958247469543159 10908890851437371204314739)
  ·
    refine ⟨16363336277156056806472109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10908890851437371204314739 16363336277156056806472109)
    ·
      refine ⟨6136251103933521302427041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16363336277156056806472109 6136251103933521302427041)
      ·
        refine ⟨4602188327950140976820281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6136251103933521302427041 4602188327950140976820281)
        ·
          refine ⟨3451641245962605732615211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4602188327950140976820281 3451641245962605732615211)
          ·
            refine ⟨5177461868943908598922817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3451641245962605732615211 5177461868943908598922817)
            ·
              refine ⟨3883096401707931449192113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5177461868943908598922817 3883096401707931449192113)
              ·
                refine ⟨2912322301280948586894085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3883096401707931449192113 2912322301280948586894085)
                ·
                  refine ⟨546060431490177860042641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2912322301280948586894085 546060431490177860042641)
                  ·
                    refine ⟨409545323617633395031981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 546060431490177860042641 409545323617633395031981)
                    ·
                      refine ⟨153579496356612523136993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 409545323617633395031981 153579496356612523136993)
                      ·
                        rfl

theorem cell23_299095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_299095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299095 prefixEnd_299095 := by exact prefixLift 299095
  have htrace : WordTrace (prefixWord ++ tailWord_299095) baseStart_299095 baseEnd_299095 := by
    simpa [prefixWord, tailWord_299095, baseEnd_299095] using wordTrace_append hprefix tailTrace_299095
  have hstable : (prefixWord ++ tailWord_299095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299095).length < 2 ^ (prefixWord ++ tailWord_299095).sum := by decide
  have hdescent : baseEnd_299095 < baseStart_299095 := by decide
  rcases family_descends (prefixWord ++ tailWord_299095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299106 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_299106 : Nat := 118140960795 + 299106 * 2 ^ 59
def prefixEnd_299106 : Nat := 4983230072969 + 3 ^ 40 * 299106 * 2
def baseEnd_299106 : Nat := 51195048214603993366481

theorem tailTrace_299106 : CollatzResearch.WordTrace tailWord_299106 prefixEnd_299106 51195048214603993366481 := by
  unfold tailWord_299106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2727323013599380020741293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7272861369598346721976781 2727323013599380020741293)
  ·
    refine ⟨1022746130099767507777985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2727323013599380020741293 1022746130099767507777985)
    ·
      refine ⟨767059597574825630833489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1022746130099767507777985 767059597574825630833489)
      ·
        refine ⟨575294698181119223125117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 767059597574825630833489 575294698181119223125117)
        ·
          refine ⟨215735511817919708671919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 575294698181119223125117 215735511817919708671919)
          ·
            refine ⟨323603267726879563007879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215735511817919708671919 323603267726879563007879)
            ·
              refine ⟨485404901590319344511819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323603267726879563007879 485404901590319344511819)
              ·
                refine ⟨728107352385479016767729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485404901590319344511819 728107352385479016767729)
                ·
                  refine ⟨546080514289109262575797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 728107352385479016767729 546080514289109262575797)
                  ·
                    refine ⟨51195048214603993366481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 546080514289109262575797 51195048214603993366481)
                    ·
                      rfl

theorem cell23_299106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_299106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299106 prefixEnd_299106 := by exact prefixLift 299106
  have htrace : WordTrace (prefixWord ++ tailWord_299106) baseStart_299106 baseEnd_299106 := by
    simpa [prefixWord, tailWord_299106, baseEnd_299106] using wordTrace_append hprefix tailTrace_299106
  have hstable : (prefixWord ++ tailWord_299106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299106).length < 2 ^ (prefixWord ++ tailWord_299106).sum := by decide
  have hdescent : baseEnd_299106 < baseStart_299106 := by decide
  rcases family_descends (prefixWord ++ tailWord_299106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299119 : List Nat := [1, 1, 2, 1, 3, 5, 2, 3, 1, 4]
def baseStart_299119 : Nat := 118140960795 + 299119 * 2 ^ 59
def prefixEnd_299119 : Nat := 4983230072969 + 3 ^ 40 * 299119 * 2
def baseEnd_299119 : Nat := 51197273297440143078961

theorem tailTrace_299119 : CollatzResearch.WordTrace tailWord_299119 prefixEnd_299119 51197273297440143078961 := by
  unfold tailWord_299119
  simp only [CollatzResearch.WordTrace]
  refine ⟨10909766203350423303188411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7273177468900282202125607 10909766203350423303188411)
  ·
    refine ⟨16364649305025634954782617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10909766203350423303188411 16364649305025634954782617)
    ·
      refine ⟨12273486978769226216086963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16364649305025634954782617 12273486978769226216086963)
      ·
        refine ⟨18410230468153839324130445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12273486978769226216086963 18410230468153839324130445)
        ·
          refine ⟨6903836425557689746548917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18410230468153839324130445 6903836425557689746548917)
          ·
            refine ⟨647234664896033413738961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6903836425557689746548917 647234664896033413738961)
            ·
              refine ⟨485425998672025060304221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647234664896033413738961 485425998672025060304221)
              ·
                refine ⟨182034749502009397614083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 485425998672025060304221 182034749502009397614083)
                ·
                  refine ⟨273052124253014096421125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182034749502009397614083 273052124253014096421125)
                  ·
                    refine ⟨51197273297440143078961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 273052124253014096421125 51197273297440143078961)
                    ·
                      rfl

theorem cell23_299119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 1, 4].length) (baseStart_299119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299119 prefixEnd_299119 := by exact prefixLift 299119
  have htrace : WordTrace (prefixWord ++ tailWord_299119) baseStart_299119 baseEnd_299119 := by
    simpa [prefixWord, tailWord_299119, baseEnd_299119] using wordTrace_append hprefix tailTrace_299119
  have hstable : (prefixWord ++ tailWord_299119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299119).length < 2 ^ (prefixWord ++ tailWord_299119).sum := by decide
  have hdescent : baseEnd_299119 < baseStart_299119 := by decide
  rcases family_descends (prefixWord ++ tailWord_299119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299132 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 6]
def baseStart_299132 : Nat := 118140960795 + 299132 * 2 ^ 59
def prefixEnd_299132 : Nat := 4983230072969 + 3 ^ 40 * 299132 * 2
def baseEnd_299132 : Nat := 17066499460092097597147

theorem tailTrace_299132 : CollatzResearch.WordTrace tailWord_299132 prefixEnd_299132 17066499460092097597147 := by
  unfold tailWord_299132
  simp only [CollatzResearch.WordTrace]
  refine ⟨5455120176151663261705825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7273493568202217682274433 5455120176151663261705825)
  ·
    refine ⟨4091340132113747446279369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5455120176151663261705825 4091340132113747446279369)
    ·
      refine ⟨3068505099085310584709527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4091340132113747446279369 3068505099085310584709527)
      ·
        refine ⟨4602757648627965877064291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3068505099085310584709527 4602757648627965877064291)
        ·
          refine ⟨6904136472941948815596437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4602757648627965877064291 6904136472941948815596437)
          ·
            refine ⟨323631397169153850731083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6904136472941948815596437 323631397169153850731083)
            ·
              refine ⟨485447095753730776096625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323631397169153850731083 485447095753730776096625)
              ·
                refine ⟨364085321815298082072469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485447095753730776096625 364085321815298082072469)
                ·
                  refine ⟨17066499460092097597147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 364085321815298082072469 17066499460092097597147)
                  ·
                    rfl

theorem cell23_299132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_299132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299132 prefixEnd_299132 := by exact prefixLift 299132
  have htrace : WordTrace (prefixWord ++ tailWord_299132) baseStart_299132 baseEnd_299132 := by
    simpa [prefixWord, tailWord_299132, baseEnd_299132] using wordTrace_append hprefix tailTrace_299132
  have hstable : (prefixWord ++ tailWord_299132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299132).length < 2 ^ (prefixWord ++ tailWord_299132).sum := by decide
  have hdescent : baseEnd_299132 < baseStart_299132 := by decide
  rcases family_descends (prefixWord ++ tailWord_299132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299192 : List Nat := [2, 1, 2, 1, 2, 1, 4, 4, 2, 4]
def baseStart_299192 : Nat := 118140960795 + 299192 * 2 ^ 59
def prefixEnd_299192 : Nat := 4983230072969 + 3 ^ 40 * 299192 * 2
def baseEnd_299192 : Nat := 51209767993366214541349

theorem tailTrace_299192 : CollatzResearch.WordTrace tailWord_299192 prefixEnd_299192 51209767993366214541349 := by
  unfold tailWord_299192
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456214366042978385297915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7274952488057304513730553 5456214366042978385297915)
  ·
    refine ⟨8184321549064467577946873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5456214366042978385297915 8184321549064467577946873)
    ·
      refine ⟨6138241161798350683460155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8184321549064467577946873 6138241161798350683460155)
      ·
        refine ⟨9207361742697526025190233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6138241161798350683460155 9207361742697526025190233)
        ·
          refine ⟨6905521307023144518892675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9207361742697526025190233 6905521307023144518892675)
          ·
            refine ⟨10358281960534716778339013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6905521307023144518892675 10358281960534716778339013)
            ·
              refine ⟨1942177867600259395938565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10358281960534716778339013 1942177867600259395938565)
              ·
                refine ⟨364158350175048636738481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1942177867600259395938565 364158350175048636738481)
                ·
                  refine ⟨273118762631286477553861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364158350175048636738481 273118762631286477553861)
                  ·
                    refine ⟨51209767993366214541349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 273118762631286477553861 51209767993366214541349)
                    ·
                      rfl

theorem cell23_299192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_299192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299192 prefixEnd_299192 := by exact prefixLift 299192
  have htrace : WordTrace (prefixWord ++ tailWord_299192) baseStart_299192 baseEnd_299192 := by
    simpa [prefixWord, tailWord_299192, baseEnd_299192] using wordTrace_append hprefix tailTrace_299192
  have hstable : (prefixWord ++ tailWord_299192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299192).length < 2 ^ (prefixWord ++ tailWord_299192).sum := by decide
  have hdescent : baseEnd_299192 < baseStart_299192 := by decide
  rcases family_descends (prefixWord ++ tailWord_299192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299229 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_299229 : Nat := 118140960795 + 299229 * 2 ^ 59
def prefixEnd_299229 : Nat := 4983230072969 + 3 ^ 40 * 299229 * 2
def baseEnd_299229 : Nat := 153648302764314998861377

theorem tailTrace_299229 : CollatzResearch.WordTrace tailWord_299229 prefixEnd_299229 153648302764314998861377 := by
  unfold tailWord_299229
  simp only [CollatzResearch.WordTrace]
  refine ⟨10913778232951912089692741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7275852155301274726461827 10913778232951912089692741)
  ·
    refine ⟨2046333418678483516817389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10913778232951912089692741 2046333418678483516817389)
    ·
      refine ⟨767375032004431318806521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2046333418678483516817389 767375032004431318806521)
      ·
        refine ⟨575531274003323489104891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 767375032004431318806521 575531274003323489104891)
        ·
          refine ⟨863296911004985233657337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575531274003323489104891 863296911004985233657337)
          ·
            refine ⟨647472683253738925243003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 863296911004985233657337 647472683253738925243003)
            ·
              refine ⟨971209024880608387864505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647472683253738925243003 971209024880608387864505)
              ·
                refine ⟨728406768660456290898379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971209024880608387864505 728406768660456290898379)
                ·
                  refine ⟨1092610152990684436347569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728406768660456290898379 1092610152990684436347569)
                  ·
                    refine ⟨819457614743013327260677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1092610152990684436347569 819457614743013327260677)
                    ·
                      refine ⟨153648302764314998861377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 819457614743013327260677 153648302764314998861377)
                      ·
                        rfl

theorem cell23_299229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_299229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299229 prefixEnd_299229 := by exact prefixLift 299229
  have htrace : WordTrace (prefixWord ++ tailWord_299229) baseStart_299229 baseEnd_299229 := by
    simpa [prefixWord, tailWord_299229, baseEnd_299229] using wordTrace_append hprefix tailTrace_299229
  have hstable : (prefixWord ++ tailWord_299229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299229).length < 2 ^ (prefixWord ++ tailWord_299229).sum := by decide
  have hdescent : baseEnd_299229 < baseStart_299229 := by decide
  rcases family_descends (prefixWord ++ tailWord_299229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299232 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 3]
def baseStart_299232 : Nat := 118140960795 + 299232 * 2 ^ 59
def prefixEnd_299232 : Nat := 4983230072969 + 3 ^ 40 * 299232 * 2
def baseEnd_299232 : Nat := 153649843206278487123863

theorem tailTrace_299232 : CollatzResearch.WordTrace tailWord_299232 prefixEnd_299232 153649843206278487123863 := by
  unfold tailWord_299232
  simp only [CollatzResearch.WordTrace]
  refine ⟨5456943825970521801025975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7275925101294029068034633 5456943825970521801025975)
  ·
    refine ⟨8185415738955782701538963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5456943825970521801025975 8185415738955782701538963)
    ·
      refine ⟨12278123608433674052308445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8185415738955782701538963 12278123608433674052308445)
      ·
        refine ⟨4604296353162627769615667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12278123608433674052308445 4604296353162627769615667)
        ·
          refine ⟨6906444529743941654423501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4604296353162627769615667 6906444529743941654423501)
          ·
            refine ⟨2589916698653978120408813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6906444529743941654423501 2589916698653978120408813)
            ·
              refine ⟨971218761995241795153305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2589916698653978120408813 971218761995241795153305)
              ·
                refine ⟨728414071496431346364979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971218761995241795153305 728414071496431346364979)
                ·
                  refine ⟨1092621107244647019547469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728414071496431346364979 1092621107244647019547469)
                  ·
                    refine ⟨409732915216742632330301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1092621107244647019547469 409732915216742632330301)
                    ·
                      refine ⟨153649843206278487123863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 409732915216742632330301 153649843206278487123863)
                      ·
                        rfl

theorem cell23_299232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 3].length) (baseStart_299232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299232 prefixEnd_299232 := by exact prefixLift 299232
  have htrace : WordTrace (prefixWord ++ tailWord_299232) baseStart_299232 baseEnd_299232 := by
    simpa [prefixWord, tailWord_299232, baseEnd_299232] using wordTrace_append hprefix tailTrace_299232
  have hstable : (prefixWord ++ tailWord_299232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299232).length < 2 ^ (prefixWord ++ tailWord_299232).sum := by decide
  have hdescent : baseEnd_299232 < baseStart_299232 := by decide
  rcases family_descends (prefixWord ++ tailWord_299232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299249 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 2, 1, 3]
def baseStart_299249 : Nat := 118140960795 + 299249 * 2 ^ 59
def prefixEnd_299249 : Nat := 4983230072969 + 3 ^ 40 * 299249 * 2
def baseEnd_299249 : Nat := 153658572377404920611285

theorem tailTrace_299249 : CollatzResearch.WordTrace tailWord_299249 prefixEnd_299249 153658572377404920611285 := by
  unfold tailWord_299249
  simp only [CollatzResearch.WordTrace]
  refine ⟨10914507692879455505420801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7276338461919637003613867 10914507692879455505420801)
  ·
    refine ⟨8185880769659591629065601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10914507692879455505420801 8185880769659591629065601)
    ·
      refine ⟨6139410577244693721799201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8185880769659591629065601 6139410577244693721799201)
      ·
        refine ⟨4604557932933520291349401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6139410577244693721799201 4604557932933520291349401)
        ·
          refine ⟨3453418449700140218512051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4604557932933520291349401 3453418449700140218512051)
          ·
            refine ⟨5180127674550210327768077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3453418449700140218512051 5180127674550210327768077)
            ·
              refine ⟨1942547877956328872913029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5180127674550210327768077 1942547877956328872913029)
              ·
                refine ⟨364227727116811663671193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1942547877956328872913029 364227727116811663671193)
                ·
                  refine ⟨273170795337608747753395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364227727116811663671193 273170795337608747753395)
                  ·
                    refine ⟨409756193006413121630093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 273170795337608747753395 409756193006413121630093)
                    ·
                      refine ⟨153658572377404920611285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 409756193006413121630093 153658572377404920611285)
                      ·
                        rfl

theorem cell23_299249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_299249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299249 prefixEnd_299249 := by exact prefixLift 299249
  have htrace : WordTrace (prefixWord ++ tailWord_299249) baseStart_299249 baseEnd_299249 := by
    simpa [prefixWord, tailWord_299249, baseEnd_299249] using wordTrace_append hprefix tailTrace_299249
  have hstable : (prefixWord ++ tailWord_299249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299249).length < 2 ^ (prefixWord ++ tailWord_299249).sum := by decide
  have hdescent : baseEnd_299249 < baseStart_299249 := by decide
  rcases family_descends (prefixWord ++ tailWord_299249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299250 : List Nat := [3, 2, 1, 3, 2, 1, 4, 2, 1, 2, 2]
def baseStart_299250 : Nat := 118140960795 + 299250 * 2 ^ 59
def prefixEnd_299250 : Nat := 4983230072969 + 3 ^ 40 * 299250 * 2
def baseEnd_299250 : Nat := 153659085858059416698781

theorem tailTrace_299250 : CollatzResearch.WordTrace tailWord_299250 prefixEnd_299250 153659085858059416698781 := by
  unfold tailWord_299250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2728636041468958169051801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7276362777250555117471469 2728636041468958169051801)
  ·
    refine ⟨2046477031101718626788851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2728636041468958169051801 2046477031101718626788851)
    ·
      refine ⟨3069715546652577940183277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2046477031101718626788851 3069715546652577940183277)
      ·
        refine ⟨1151143329994716727568729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3069715546652577940183277 1151143329994716727568729)
        ·
          refine ⟨863357497496037545676547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1151143329994716727568729 863357497496037545676547)
          ·
            refine ⟨1295036246244056318514821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863357497496037545676547 1295036246244056318514821)
            ·
              refine ⟨242819296170760559721529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1295036246244056318514821 242819296170760559721529)
              ·
                refine ⟨182114472128070419791147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242819296170760559721529 182114472128070419791147)
                ·
                  refine ⟨273171708192105629686721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182114472128070419791147 273171708192105629686721)
                  ·
                    refine ⟨204878781144079222265041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 273171708192105629686721 204878781144079222265041)
                    ·
                      refine ⟨153659085858059416698781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 204878781144079222265041 153659085858059416698781)
                      ·
                        rfl

theorem cell23_299250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_299250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299250 prefixEnd_299250 := by exact prefixLift 299250
  have htrace : WordTrace (prefixWord ++ tailWord_299250) baseStart_299250 baseEnd_299250 := by
    simpa [prefixWord, tailWord_299250, baseEnd_299250] using wordTrace_append hprefix tailTrace_299250
  have hstable : (prefixWord ++ tailWord_299250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299250).length < 2 ^ (prefixWord ++ tailWord_299250).sum := by decide
  have hdescent : baseEnd_299250 < baseStart_299250 := by decide
  rcases family_descends (prefixWord ++ tailWord_299250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299266 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_299266 : Nat := 118140960795 + 299266 * 2 ^ 59
def prefixEnd_299266 : Nat := 4983230072969 + 3 ^ 40 * 299266 * 2
def baseEnd_299266 : Nat := 153667301548531354098707

theorem tailTrace_299266 : CollatzResearch.WordTrace tailWord_299266 prefixEnd_299266 153667301548531354098707 := by
  unfold tailWord_299266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2728781933454466852197413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7276751822545244939193101 2728781933454466852197413)
  ·
    refine ⟨511646612522712534787015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2728781933454466852197413 511646612522712534787015)
    ·
      refine ⟨767469918784068802180523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511646612522712534787015 767469918784068802180523)
      ·
        refine ⟨1151204878176103203270785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767469918784068802180523 1151204878176103203270785)
        ·
          refine ⟨863403658632077402453089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1151204878176103203270785 863403658632077402453089)
          ·
            refine ⟨647552743974058051839817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 863403658632077402453089 647552743974058051839817)
            ·
              refine ⟨485664557980543538879863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 647552743974058051839817 485664557980543538879863)
              ·
                refine ⟨728496836970815308319795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 485664557980543538879863 728496836970815308319795)
                ·
                  refine ⟨1092745255456222962479693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 728496836970815308319795 1092745255456222962479693)
                  ·
                    refine ⟨409779470796083610929885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1092745255456222962479693 409779470796083610929885)
                    ·
                      refine ⟨153667301548531354098707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 409779470796083610929885 153667301548531354098707)
                      ·
                        rfl

theorem cell23_299266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_299266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299266 prefixEnd_299266 := by exact prefixLift 299266
  have htrace : WordTrace (prefixWord ++ tailWord_299266) baseStart_299266 baseEnd_299266 := by
    simpa [prefixWord, tailWord_299266, baseEnd_299266] using wordTrace_append hprefix tailTrace_299266
  have hstable : (prefixWord ++ tailWord_299266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299266).length < 2 ^ (prefixWord ++ tailWord_299266).sum := by decide
  have hdescent : baseEnd_299266 < baseStart_299266 := by decide
  rcases family_descends (prefixWord ++ tailWord_299266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299293 : List Nat := [1, 4, 2, 3, 2, 1, 1, 3, 1, 3, 2]
def baseStart_299293 : Nat := 118140960795 + 299293 * 2 ^ 59
def prefixEnd_299293 : Nat := 4983230072969 + 3 ^ 40 * 299293 * 2
def baseEnd_299293 : Nat := 153681165526202748461083

theorem tailTrace_299293 : CollatzResearch.WordTrace tailWord_299293 prefixEnd_299293 153681165526202748461083 := by
  unfold tailWord_299293
  simp only [CollatzResearch.WordTrace]
  refine ⟨10916112504720051020022533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7277408336480034013348355 10916112504720051020022533)
  ·
    refine ⟨2046771094635009566254225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10916112504720051020022533 2046771094635009566254225)
    ·
      refine ⟨1535078320976257174690669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2046771094635009566254225 1535078320976257174690669)
      ·
        refine ⟨575654370366096440509001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1535078320976257174690669 575654370366096440509001)
        ·
          refine ⟨431740777774572330381751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575654370366096440509001 431740777774572330381751)
          ·
            refine ⟨647611166661858495572627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431740777774572330381751 647611166661858495572627)
            ·
              refine ⟨971416749992787743358941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 647611166661858495572627 971416749992787743358941)
              ·
                refine ⟨364281281247295403759603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 971416749992787743358941 364281281247295403759603)
                ·
                  refine ⟨546421921870943105639405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364281281247295403759603 546421921870943105639405)
                  ·
                    refine ⟨204908220701603664614777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 546421921870943105639405 204908220701603664614777)
                    ·
                      refine ⟨153681165526202748461083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 204908220701603664614777 153681165526202748461083)
                      ·
                        rfl

theorem cell23_299293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_299293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299293 prefixEnd_299293 := by exact prefixLift 299293
  have htrace : WordTrace (prefixWord ++ tailWord_299293) baseStart_299293 baseEnd_299293 := by
    simpa [prefixWord, tailWord_299293, baseEnd_299293] using wordTrace_append hprefix tailTrace_299293
  have hstable : (prefixWord ++ tailWord_299293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299293).length < 2 ^ (prefixWord ++ tailWord_299293).sum := by decide
  have hdescent : baseEnd_299293 < baseStart_299293 := by decide
  rcases family_descends (prefixWord ++ tailWord_299293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299414 : List Nat := [5, 3, 1, 2, 1, 2, 2, 2, 5]
def baseStart_299414 : Nat := 118140960795 + 299414 * 2 ^ 59
def prefixEnd_299414 : Nat := 4983230072969 + 3 ^ 40 * 299414 * 2
def baseEnd_299414 : Nat := 17082588520599641672003

theorem tailTrace_299414 : CollatzResearch.WordTrace tailWord_299414 prefixEnd_299414 17082588520599641672003 := by
  unfold tailWord_299414
  simp only [CollatzResearch.WordTrace]
  refine ⟨682532858580105542823581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7280350491521125790118197 682532858580105542823581)
  ·
    refine ⟨255949821967539578558843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 682532858580105542823581 255949821967539578558843)
    ·
      refine ⟨383924732951309367838265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 255949821967539578558843 383924732951309367838265)
      ·
        refine ⟨287943549713482025878699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383924732951309367838265 287943549713482025878699)
        ·
          refine ⟨431915324570223038818049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287943549713482025878699 431915324570223038818049)
          ·
            refine ⟨323936493427667279113537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431915324570223038818049 323936493427667279113537)
            ·
              refine ⟨242952370070750459335153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323936493427667279113537 242952370070750459335153)
              ·
                refine ⟨182214277553062844501365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242952370070750459335153 182214277553062844501365)
                ·
                  refine ⟨17082588520599641672003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182214277553062844501365 17082588520599641672003)
                  ·
                    rfl

theorem cell23_299414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_299414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299414 prefixEnd_299414 := by exact prefixLift 299414
  have htrace : WordTrace (prefixWord ++ tailWord_299414) baseStart_299414 baseEnd_299414 := by
    simpa [prefixWord, tailWord_299414, baseEnd_299414] using wordTrace_append hprefix tailTrace_299414
  have hstable : (prefixWord ++ tailWord_299414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299414).length < 2 ^ (prefixWord ++ tailWord_299414).sum := by decide
  have hdescent : baseEnd_299414 < baseStart_299414 := by decide
  rcases family_descends (prefixWord ++ tailWord_299414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299416 : List Nat := [2, 1, 2, 5, 1, 1, 2, 2, 2, 2, 3]
def baseStart_299416 : Nat := 118140960795 + 299416 * 2 ^ 59
def prefixEnd_299416 : Nat := 4983230072969 + 3 ^ 40 * 299416 * 2
def baseEnd_299416 : Nat := 153744323646705767223017

theorem tailTrace_299416 : CollatzResearch.WordTrace tailWord_299416 prefixEnd_299416 153744323646705767223017 := by
  unfold tailWord_299416
  simp only [CollatzResearch.WordTrace]
  refine ⟨5460299341637221513375051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7280399122182962017833401 5460299341637221513375051)
  ·
    refine ⟨8190449012455832270062577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5460299341637221513375051 8190449012455832270062577)
    ·
      refine ⟨6142836759341874202546933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8190449012455832270062577 6142836759341874202546933)
      ·
        refine ⟨575890946188300706488775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6142836759341874202546933 575890946188300706488775)
        ·
          refine ⟨863836419282451059733163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575890946188300706488775 863836419282451059733163)
          ·
            refine ⟨1295754628923676589599745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863836419282451059733163 1295754628923676589599745)
            ·
              refine ⟨971815971692757442199809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1295754628923676589599745 971815971692757442199809)
              ·
                refine ⟨728861978769568081649857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971815971692757442199809 728861978769568081649857)
                ·
                  refine ⟨546646484077176061237393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 728861978769568081649857 546646484077176061237393)
                  ·
                    refine ⟨409984863057882045928045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 546646484077176061237393 409984863057882045928045)
                    ·
                      refine ⟨153744323646705767223017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 409984863057882045928045 153744323646705767223017)
                      ·
                        rfl

theorem cell23_299416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_299416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299416 prefixEnd_299416 := by exact prefixLift 299416
  have htrace : WordTrace (prefixWord ++ tailWord_299416) baseStart_299416 baseEnd_299416 := by
    simpa [prefixWord, tailWord_299416, baseEnd_299416] using wordTrace_append hprefix tailTrace_299416
  have hstable : (prefixWord ++ tailWord_299416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299416).length < 2 ^ (prefixWord ++ tailWord_299416).sum := by decide
  have hdescent : baseEnd_299416 < baseStart_299416 := by decide
  rcases family_descends (prefixWord ++ tailWord_299416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299442 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_299442 : Nat := 118140960795 + 299442 * 2 ^ 59
def prefixEnd_299442 : Nat := 4983230072969 + 3 ^ 40 * 299442 * 2
def baseEnd_299442 : Nat := 153757674143722665497897

theorem tailTrace_299442 : CollatzResearch.WordTrace tailWord_299442 prefixEnd_299442 153757674143722665497897 := by
  unfold tailWord_299442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730386745295062366799145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7281031320786832978131053 2730386745295062366799145)
  ·
    refine ⟨2047790058971296775099359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2730386745295062366799145 2047790058971296775099359)
    ·
      refine ⟨3071685088456945162649039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2047790058971296775099359 3071685088456945162649039)
      ·
        refine ⟨4607527632685417743973559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071685088456945162649039 4607527632685417743973559)
        ·
          refine ⟨6911291449028126615960339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4607527632685417743973559 6911291449028126615960339)
          ·
            refine ⟨10366937173542189923940509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6911291449028126615960339 10366937173542189923940509)
            ·
              refine ⟨3887601440078321221477691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10366937173542189923940509 3887601440078321221477691)
              ·
                refine ⟨5831402160117481832216537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3887601440078321221477691 5831402160117481832216537)
                ·
                  refine ⟨4373551620088111374162403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5831402160117481832216537 4373551620088111374162403)
                  ·
                    refine ⟨6560327430132167061243605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4373551620088111374162403 6560327430132167061243605)
                    ·
                      refine ⟨153757674143722665497897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6560327430132167061243605 153757674143722665497897)
                      ·
                        rfl

theorem cell23_299442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_299442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299442 prefixEnd_299442 := by exact prefixLift 299442
  have htrace : WordTrace (prefixWord ++ tailWord_299442) baseStart_299442 baseEnd_299442 := by
    simpa [prefixWord, tailWord_299442, baseEnd_299442] using wordTrace_append hprefix tailTrace_299442
  have hstable : (prefixWord ++ tailWord_299442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299442).length < 2 ^ (prefixWord ++ tailWord_299442).sum := by decide
  have hdescent : baseEnd_299442 < baseStart_299442 := by decide
  rcases family_descends (prefixWord ++ tailWord_299442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299449 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 3, 5]
def baseStart_299449 : Nat := 118140960795 + 299449 * 2 ^ 59
def prefixEnd_299449 : Nat := 4983230072969 + 3 ^ 40 * 299449 * 2
def baseEnd_299449 : Nat := 51253756169434712703455

theorem tailTrace_299449 : CollatzResearch.WordTrace tailWord_299449 prefixEnd_299449 51253756169434712703455 := by
  unfold tailWord_299449
  simp only [CollatzResearch.WordTrace]
  refine ⟨10921802292154889662701401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7281201528103259775134267 10921802292154889662701401)
  ·
    refine ⟨8191351719116167247026051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10921802292154889662701401 8191351719116167247026051)
    ·
      refine ⟨12287027578674250870539077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8191351719116167247026051 12287027578674250870539077)
      ·
        refine ⟨2303817671001422038226077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12287027578674250870539077 2303817671001422038226077)
        ·
          refine ⟨863931626625533264334779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2303817671001422038226077 863931626625533264334779)
          ·
            refine ⟨1295897439938299896502169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863931626625533264334779 1295897439938299896502169)
            ·
              refine ⟨971923079953724922376627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1295897439938299896502169 971923079953724922376627)
              ·
                refine ⟨1457884619930587383564941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 971923079953724922376627 1457884619930587383564941)
                ·
                  refine ⟨546706732473970268836853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1457884619930587383564941 546706732473970268836853)
                  ·
                    refine ⟨51253756169434712703455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 546706732473970268836853 51253756169434712703455)
                    ·
                      rfl

theorem cell23_299449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_299449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299449 prefixEnd_299449 := by exact prefixLift 299449
  have htrace : WordTrace (prefixWord ++ tailWord_299449) baseStart_299449 baseEnd_299449 := by
    simpa [prefixWord, tailWord_299449, baseEnd_299449] using wordTrace_append hprefix tailTrace_299449
  have hstable : (prefixWord ++ tailWord_299449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299449).length < 2 ^ (prefixWord ++ tailWord_299449).sum := by decide
  have hdescent : baseEnd_299449 < baseStart_299449 := by decide
  rcases family_descends (prefixWord ++ tailWord_299449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299463 : List Nat := [1, 1, 4, 1, 1, 4, 1, 5, 1, 1, 3]
def baseStart_299463 : Nat := 118140960795 + 299463 * 2 ^ 59
def prefixEnd_299463 : Nat := 4983230072969 + 3 ^ 40 * 299463 * 2
def baseEnd_299463 : Nat := 153768457237467083335301

theorem tailTrace_299463 : CollatzResearch.WordTrace tailWord_299463 prefixEnd_299463 153768457237467083335301 := by
  unfold tailWord_299463
  simp only [CollatzResearch.WordTrace]
  refine ⟨10922312914104170053711043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7281541942736113369140695 10922312914104170053711043)
  ·
    refine ⟨16383469371156255080566565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10922312914104170053711043 16383469371156255080566565)
    ·
      refine ⟨3071900507091797827606231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16383469371156255080566565 3071900507091797827606231)
      ·
        refine ⟨4607850760637696741409347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3071900507091797827606231 4607850760637696741409347)
        ·
          refine ⟨6911776140956545112114021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4607850760637696741409347 6911776140956545112114021)
          ·
            refine ⟨1295958026429352208521379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6911776140956545112114021 1295958026429352208521379)
            ·
              refine ⟨1943937039644028312782069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295958026429352208521379 1943937039644028312782069)
              ·
                refine ⟨182244097466627654323319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1943937039644028312782069 182244097466627654323319)
                ·
                  refine ⟨273366146199941481484979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182244097466627654323319 273366146199941481484979)
                  ·
                    refine ⟨410049219299912222227469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 273366146199941481484979 410049219299912222227469)
                    ·
                      refine ⟨153768457237467083335301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 410049219299912222227469 153768457237467083335301)
                      ·
                        rfl

theorem cell23_299463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_299463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299463 prefixEnd_299463 := by exact prefixLift 299463
  have htrace : WordTrace (prefixWord ++ tailWord_299463) baseStart_299463 baseEnd_299463 := by
    simpa [prefixWord, tailWord_299463, baseEnd_299463] using wordTrace_append hprefix tailTrace_299463
  have hstable : (prefixWord ++ tailWord_299463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299463).length < 2 ^ (prefixWord ++ tailWord_299463).sum := by decide
  have hdescent : baseEnd_299463 < baseStart_299463 := by decide
  rcases family_descends (prefixWord ++ tailWord_299463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299489 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_299489 : Nat := 118140960795 + 299489 * 2 ^ 59
def prefixEnd_299489 : Nat := 4983230072969 + 3 ^ 40 * 299489 * 2
def baseEnd_299489 : Nat := 153781807734483981610181

theorem tailTrace_299489 : CollatzResearch.WordTrace tailWord_299489 prefixEnd_299489 153781807734483981610181 := by
  unfold tailWord_299489
  simp only [CollatzResearch.WordTrace]
  refine ⟨10923261212009976494157521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7282174141339984329438347 10923261212009976494157521)
  ·
    refine ⟨8192445909007482370618141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10923261212009976494157521 8192445909007482370618141)
    ·
      refine ⟨3072167215877805888981803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8192445909007482370618141 3072167215877805888981803)
      ·
        refine ⟨4608250823816708833472705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072167215877805888981803 4608250823816708833472705)
        ·
          refine ⟨3456188117862531625104529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4608250823816708833472705 3456188117862531625104529)
          ·
            refine ⟨2592141088396898718828397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3456188117862531625104529 2592141088396898718828397)
            ·
              refine ⟨972052908148837019560649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2592141088396898718828397 972052908148837019560649)
              ·
                refine ⟨729039681111627764670487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972052908148837019560649 729039681111627764670487)
                ·
                  refine ⟨1093559521667441647005731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729039681111627764670487 1093559521667441647005731)
                  ·
                    refine ⟨1640339282501162470508597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1093559521667441647005731 1640339282501162470508597)
                    ·
                      refine ⟨153781807734483981610181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1640339282501162470508597 153781807734483981610181)
                      ·
                        rfl

theorem cell23_299489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_299489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299489 prefixEnd_299489 := by exact prefixLift 299489
  have htrace : WordTrace (prefixWord ++ tailWord_299489) baseStart_299489 baseEnd_299489 := by
    simpa [prefixWord, tailWord_299489, baseEnd_299489] using wordTrace_append hprefix tailTrace_299489
  have hstable : (prefixWord ++ tailWord_299489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299489).length < 2 ^ (prefixWord ++ tailWord_299489).sum := by decide
  have hdescent : baseEnd_299489 < baseStart_299489 := by decide
  rcases family_descends (prefixWord ++ tailWord_299489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299496 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 1, 6]
def baseStart_299496 : Nat := 118140960795 + 299496 * 2 ^ 59
def prefixEnd_299496 : Nat := 4983230072969 + 3 ^ 40 * 299496 * 2
def baseEnd_299496 : Nat := 51261800699688484740883

theorem tailTrace_299496 : CollatzResearch.WordTrace tailWord_299496 prefixEnd_299496 51261800699688484740883 := by
  unfold tailWord_299496
  simp only [CollatzResearch.WordTrace]
  refine ⟨5461758261492308344831171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7282344348656411126441561 5461758261492308344831171)
  ·
    refine ⟨8192637392238462517246757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5461758261492308344831171 8192637392238462517246757)
    ·
      refine ⟨1536119511044711721983767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8192637392238462517246757 1536119511044711721983767)
      ·
        refine ⟨2304179266567067582975651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536119511044711721983767 2304179266567067582975651)
        ·
          refine ⟨3456268899850601374463477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304179266567067582975651 3456268899850601374463477)
          ·
            refine ⟨324025209360993878855951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3456268899850601374463477 324025209360993878855951)
            ·
              refine ⟨486037814041490818283927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324025209360993878855951 486037814041490818283927)
              ·
                refine ⟨729056721062236227425891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486037814041490818283927 729056721062236227425891)
                ·
                  refine ⟨1093585081593354341138837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729056721062236227425891 1093585081593354341138837)
                  ·
                    refine ⟨51261800699688484740883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1093585081593354341138837 51261800699688484740883)
                    ·
                      rfl

theorem cell23_299496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_299496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299496 prefixEnd_299496 := by exact prefixLift 299496
  have htrace : WordTrace (prefixWord ++ tailWord_299496) baseStart_299496 baseEnd_299496 := by
    simpa [prefixWord, tailWord_299496, baseEnd_299496] using wordTrace_append hprefix tailTrace_299496
  have hstable : (prefixWord ++ tailWord_299496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299496).length < 2 ^ (prefixWord ++ tailWord_299496).sum := by decide
  have hdescent : baseEnd_299496 < baseStart_299496 := by decide
  rcases family_descends (prefixWord ++ tailWord_299496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299519 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 3]
def baseStart_299519 : Nat := 118140960795 + 299519 * 2 ^ 59
def prefixEnd_299519 : Nat := 4983230072969 + 3 ^ 40 * 299519 * 2
def baseEnd_299519 : Nat := 153797212154118864235043

theorem tailTrace_299519 : CollatzResearch.WordTrace tailWord_299519 prefixEnd_299519 153797212154118864235043 := by
  unfold tailWord_299519
  simp only [CollatzResearch.WordTrace]
  refine ⟨10924355401901291617749611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7282903601267527745166407 10924355401901291617749611)
  ·
    refine ⟨16386533102851937426624417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10924355401901291617749611 16386533102851937426624417)
    ·
      refine ⟨12289899827138953069968313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16386533102851937426624417 12289899827138953069968313)
      ·
        refine ⟨9217424870354214802476235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12289899827138953069968313 9217424870354214802476235)
        ·
          refine ⟨13826137305531322203714353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9217424870354214802476235 13826137305531322203714353)
          ·
            refine ⟨10369602979148491652785765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13826137305531322203714353 10369602979148491652785765)
            ·
              refine ⟨1944300558590342184897331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10369602979148491652785765 1944300558590342184897331)
              ·
                refine ⟨2916450837885513277345997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944300558590342184897331 2916450837885513277345997)
                ·
                  refine ⟨1093669064207067479004749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2916450837885513277345997 1093669064207067479004749)
                  ·
                    refine ⟨410125899077650304626781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1093669064207067479004749 410125899077650304626781)
                    ·
                      refine ⟨153797212154118864235043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 410125899077650304626781 153797212154118864235043)
                      ·
                        rfl

theorem cell23_299519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_299519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299519 prefixEnd_299519 := by exact prefixLift 299519
  have htrace : WordTrace (prefixWord ++ tailWord_299519) baseStart_299519 baseEnd_299519 := by
    simpa [prefixWord, tailWord_299519, baseEnd_299519] using wordTrace_append hprefix tailTrace_299519
  have hstable : (prefixWord ++ tailWord_299519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299519).length < 2 ^ (prefixWord ++ tailWord_299519).sum := by decide
  have hdescent : baseEnd_299519 < baseStart_299519 := by decide
  rcases family_descends (prefixWord ++ tailWord_299519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299533 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_299533 : Nat := 118140960795 + 299533 * 2 ^ 59
def prefixEnd_299533 : Nat := 4983230072969 + 3 ^ 40 * 299533 * 2
def baseEnd_299533 : Nat := 153804400883281809459979

theorem tailTrace_299533 : CollatzResearch.WordTrace tailWord_299533 prefixEnd_299533 153804400883281809459979 := by
  unfold tailWord_299533
  simp only [CollatzResearch.WordTrace]
  refine ⟨10924866023850572008759253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7283244015900381339172835 10924866023850572008759253)
  ·
    refine ⟨256051547433997781455295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 10924866023850572008759253 256051547433997781455295)
    ·
      refine ⟨384077321150996672182943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256051547433997781455295 384077321150996672182943)
      ·
        refine ⟨576115981726495008274415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384077321150996672182943 576115981726495008274415)
        ·
          refine ⟨864173972589742512411623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576115981726495008274415 864173972589742512411623)
          ·
            refine ⟨1296260958884613768617435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864173972589742512411623 1296260958884613768617435)
            ·
              refine ⟨1944391438326920652926153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1296260958884613768617435 1944391438326920652926153)
              ·
                refine ⟨1458293578745190489694615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1944391438326920652926153 1458293578745190489694615)
                ·
                  refine ⟨2187440368117785734541923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1458293578745190489694615 2187440368117785734541923)
                  ·
                    refine ⟨3281160552176678601812885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2187440368117785734541923 3281160552176678601812885)
                    ·
                      refine ⟨153804400883281809459979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3281160552176678601812885 153804400883281809459979)
                      ·
                        rfl

theorem cell23_299533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_299533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299533 prefixEnd_299533 := by exact prefixLift 299533
  have htrace : WordTrace (prefixWord ++ tailWord_299533) baseStart_299533 baseEnd_299533 := by
    simpa [prefixWord, tailWord_299533, baseEnd_299533] using wordTrace_append hprefix tailTrace_299533
  have hstable : (prefixWord ++ tailWord_299533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299533).length < 2 ^ (prefixWord ++ tailWord_299533).sum := by decide
  have hdescent : baseEnd_299533 < baseStart_299533 := by decide
  rcases family_descends (prefixWord ++ tailWord_299533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299553 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_299553 : Nat := 118140960795 + 299553 * 2 ^ 59
def prefixEnd_299553 : Nat := 4983230072969 + 3 ^ 40 * 299553 * 2
def baseEnd_299553 : Nat := 153814670496371731209887

theorem tailTrace_299553 : CollatzResearch.WordTrace tailWord_299553 prefixEnd_299553 153814670496371731209887 := by
  unfold tailWord_299553
  simp only [CollatzResearch.WordTrace]
  refine ⟨10925595483778115424487313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7283730322518743616324875 10925595483778115424487313)
  ·
    refine ⟨8194196612833586568365485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10925595483778115424487313 8194196612833586568365485)
    ·
      refine ⟨3072823729812594963137057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8194196612833586568365485 3072823729812594963137057)
      ·
        refine ⟨2304617797359446222352793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3072823729812594963137057 2304617797359446222352793)
        ·
          refine ⟨1728463348019584666764595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2304617797359446222352793 1728463348019584666764595)
          ·
            refine ⟨2592695022029377000146893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728463348019584666764595 2592695022029377000146893)
            ·
              refine ⟨972260633261016375055085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2592695022029377000146893 972260633261016375055085)
              ·
                refine ⟨364597737472881140645657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 972260633261016375055085 364597737472881140645657)
                ·
                  refine ⟨273448303104660855484243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364597737472881140645657 273448303104660855484243)
                  ·
                    refine ⟨410172454656991283226365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 273448303104660855484243 410172454656991283226365)
                    ·
                      refine ⟨153814670496371731209887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 410172454656991283226365 153814670496371731209887)
                      ·
                        rfl

theorem cell23_299553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_299553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299553 prefixEnd_299553 := by exact prefixLift 299553
  have htrace : WordTrace (prefixWord ++ tailWord_299553) baseStart_299553 baseEnd_299553 := by
    simpa [prefixWord, tailWord_299553, baseEnd_299553] using wordTrace_append hprefix tailTrace_299553
  have hstable : (prefixWord ++ tailWord_299553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299553).length < 2 ^ (prefixWord ++ tailWord_299553).sum := by decide
  have hdescent : baseEnd_299553 < baseStart_299553 := by decide
  rcases family_descends (prefixWord ++ tailWord_299553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299626 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_299626 : Nat := 118140960795 + 299626 * 2 ^ 59
def prefixEnd_299626 : Nat := 4983230072969 + 3 ^ 40 * 299626 * 2
def baseEnd_299626 : Nat := 153852154584149945597051

theorem tailTrace_299626 : CollatzResearch.WordTrace tailWord_299626 prefixEnd_299626 153852154584149945597051 := by
  unfold tailWord_299626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732064503128412222973683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7285505341675765927929821 2732064503128412222973683)
  ·
    refine ⟨4098096754692618334460525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2732064503128412222973683 4098096754692618334460525)
    ·
      refine ⟨1536786283009731875422697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4098096754692618334460525 1536786283009731875422697)
      ·
        refine ⟨1152589712257298906567023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1536786283009731875422697 1152589712257298906567023)
        ·
          refine ⟨1728884568385948359850535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1152589712257298906567023 1728884568385948359850535)
          ·
            refine ⟨2593326852578922539775803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728884568385948359850535 2593326852578922539775803)
            ·
              refine ⟨3889990278868383809663705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2593326852578922539775803 3889990278868383809663705)
              ·
                refine ⟨2917492709151287857247779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3889990278868383809663705 2917492709151287857247779)
                ·
                  refine ⟨4376239063726931785871669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2917492709151287857247779 4376239063726931785871669)
                  ·
                    refine ⟨410272412224399854925469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4376239063726931785871669 410272412224399854925469)
                    ·
                      refine ⟨153852154584149945597051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 410272412224399854925469 153852154584149945597051)
                      ·
                        rfl

theorem cell23_299626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_299626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299626 prefixEnd_299626 := by exact prefixLift 299626
  have htrace : WordTrace (prefixWord ++ tailWord_299626) baseStart_299626 baseEnd_299626 := by
    simpa [prefixWord, tailWord_299626, baseEnd_299626] using wordTrace_append hprefix tailTrace_299626
  have hstable : (prefixWord ++ tailWord_299626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299626).length < 2 ^ (prefixWord ++ tailWord_299626).sum := by decide
  have hdescent : baseEnd_299626 < baseStart_299626 := by decide
  rcases family_descends (prefixWord ++ tailWord_299626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299639 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_299639 : Nat := 118140960795 + 299639 * 2 ^ 59
def prefixEnd_299639 : Nat := 4983230072969 + 3 ^ 40 * 299639 * 2
def baseEnd_299639 : Nat := 153858829832658394734491

theorem tailTrace_299639 : CollatzResearch.WordTrace tailWord_299639 prefixEnd_299639 153858829832658394734491 := by
  unfold tailWord_299639
  simp only [CollatzResearch.WordTrace]
  refine ⟨10928732161466552112117971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7285821440977701408078647 10928732161466552112117971)
  ·
    refine ⟨16393098242199828168176957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10928732161466552112117971 16393098242199828168176957)
    ·
      refine ⟨6147411840824935563066359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16393098242199828168176957 6147411840824935563066359)
      ·
        refine ⟨9221117761237403344599539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6147411840824935563066359 9221117761237403344599539)
        ·
          refine ⟨13831676641856105016899309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9221117761237403344599539 13831676641856105016899309)
          ·
            refine ⟨5186878740696039381337241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13831676641856105016899309 5186878740696039381337241)
            ·
              refine ⟨3890159055522029536002931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5186878740696039381337241 3890159055522029536002931)
              ·
                refine ⟨5835238583283044304004397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3890159055522029536002931 5835238583283044304004397)
                ·
                  refine ⟨2188214468731141614001649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5835238583283044304004397 2188214468731141614001649)
                  ·
                    refine ⟨1641160851548356210501237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2188214468731141614001649 1641160851548356210501237)
                    ·
                      refine ⟨153858829832658394734491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1641160851548356210501237 153858829832658394734491)
                      ·
                        rfl

theorem cell23_299639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_299639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299639 prefixEnd_299639 := by exact prefixLift 299639
  have htrace : WordTrace (prefixWord ++ tailWord_299639) baseStart_299639 baseEnd_299639 := by
    simpa [prefixWord, tailWord_299639, baseEnd_299639] using wordTrace_append hprefix tailTrace_299639
  have hstable : (prefixWord ++ tailWord_299639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299639).length < 2 ^ (prefixWord ++ tailWord_299639).sum := by decide
  have hdescent : baseEnd_299639 < baseStart_299639 := by decide
  rcases family_descends (prefixWord ++ tailWord_299639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299689 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 8]
def baseStart_299689 : Nat := 118140960795 + 299689 * 2 ^ 59
def prefixEnd_299689 : Nat := 4983230072969 + 3 ^ 40 * 299689 * 2
def baseEnd_299689 : Nat := 17098278207264799901029

theorem tailTrace_299689 : CollatzResearch.WordTrace tailWord_299689 prefixEnd_299689 17098278207264799901029 := by
  unfold tailWord_299689
  simp only [CollatzResearch.WordTrace]
  refine ⟨10930555811285410651438121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7287037207523607100958747 10930555811285410651438121)
  ·
    refine ⟨8197916858464057988578591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10930555811285410651438121 8197916858464057988578591)
    ·
      refine ⟨12296875287696086982867887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8197916858464057988578591 12296875287696086982867887)
      ·
        refine ⟨18445312931544130474301831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12296875287696086982867887 18445312931544130474301831)
        ·
          refine ⟨27667969397316195711452747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18445312931544130474301831 27667969397316195711452747)
          ·
            refine ⟨41501954095974293567179121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27667969397316195711452747 41501954095974293567179121)
            ·
              refine ⟨31126465571980720175384341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41501954095974293567179121 31126465571980720175384341)
              ·
                refine ⟨1459053073686596258221141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31126465571980720175384341 1459053073686596258221141)
                ·
                  refine ⟨17098278207264799901029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1459053073686596258221141 17098278207264799901029)
                  ·
                    rfl

theorem cell23_299689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 8].length) (baseStart_299689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299689 prefixEnd_299689 := by exact prefixLift 299689
  have htrace : WordTrace (prefixWord ++ tailWord_299689) baseStart_299689 baseEnd_299689 := by
    simpa [prefixWord, tailWord_299689, baseEnd_299689] using wordTrace_append hprefix tailTrace_299689
  have hstable : (prefixWord ++ tailWord_299689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299689).length < 2 ^ (prefixWord ++ tailWord_299689).sum := by decide
  have hdescent : baseEnd_299689 < baseStart_299689 := by decide
  rcases family_descends (prefixWord ++ tailWord_299689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299706 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 6]
def baseStart_299706 : Nat := 118140960795 + 299706 * 2 ^ 59
def prefixEnd_299706 : Nat := 4983230072969 + 3 ^ 40 * 299706 * 2
def baseEnd_299706 : Nat := 17099248115167736955187

theorem tailTrace_299706 : CollatzResearch.WordTrace tailWord_299706 prefixEnd_299706 17099248115167736955187 := by
  unfold tailWord_299706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732793963055955638701743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7287450568149215036537981 2732793963055955638701743)
  ·
    refine ⟨4099190944583933458052615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2732793963055955638701743 4099190944583933458052615)
    ·
      refine ⟨6148786416875900187078923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4099190944583933458052615 6148786416875900187078923)
      ·
        refine ⟨9223179625313850280618385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6148786416875900187078923 9223179625313850280618385)
        ·
          refine ⟨6917384718985387710463789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9223179625313850280618385 6917384718985387710463789)
          ·
            refine ⟨2594019269619520391423921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6917384718985387710463789 2594019269619520391423921)
            ·
              refine ⟨1945514452214640293567941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2594019269619520391423921 1945514452214640293567941)
              ·
                refine ⟨364783959790245055043989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1945514452214640293567941 364783959790245055043989)
                ·
                  refine ⟨17099248115167736955187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 364783959790245055043989 17099248115167736955187)
                  ·
                    rfl

theorem cell23_299706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 6].length) (baseStart_299706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299706 prefixEnd_299706 := by exact prefixLift 299706
  have htrace : WordTrace (prefixWord ++ tailWord_299706) baseStart_299706 baseEnd_299706 := by
    simpa [prefixWord, tailWord_299706, baseEnd_299706] using wordTrace_append hprefix tailTrace_299706
  have hstable : (prefixWord ++ tailWord_299706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299706).length < 2 ^ (prefixWord ++ tailWord_299706).sum := by decide
  have hdescent : baseEnd_299706 < baseStart_299706 := by decide
  rcases family_descends (prefixWord ++ tailWord_299706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299776 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 3]
def baseStart_299776 : Nat := 118140960795 + 299776 * 2 ^ 59
def prefixEnd_299776 : Nat := 4983230072969 + 3 ^ 40 * 299776 * 2
def baseEnd_299776 : Nat := 153929176682324358721361

theorem tailTrace_299776 : CollatzResearch.WordTrace tailWord_299776 prefixEnd_299776 153929176682324358721361 := by
  unfold tailWord_299776
  simp only [CollatzResearch.WordTrace]
  refine ⟨5466864480985112254927591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7289152641313483006570121 5466864480985112254927591)
  ·
    refine ⟨8200296721477668382391387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5466864480985112254927591 8200296721477668382391387)
    ·
      refine ⟨12300445082216502573587081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8200296721477668382391387 12300445082216502573587081)
      ·
        refine ⟨9225333811662376930190311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12300445082216502573587081 9225333811662376930190311)
        ·
          refine ⟨13838000717493565395285467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9225333811662376930190311 13838000717493565395285467)
          ·
            refine ⟨20757001076240348092928201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13838000717493565395285467 20757001076240348092928201)
            ·
              refine ⟨15567750807180261069696151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20757001076240348092928201 15567750807180261069696151)
              ·
                refine ⟨23351626210770391604544227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15567750807180261069696151 23351626210770391604544227)
                ·
                  refine ⟨35027439316155587406816341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23351626210770391604544227 35027439316155587406816341)
                  ·
                    refine ⟨410477804486198289923629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35027439316155587406816341 410477804486198289923629)
                    ·
                      refine ⟨153929176682324358721361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 410477804486198289923629 153929176682324358721361)
                      ·
                        rfl

theorem cell23_299776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 3].length) (baseStart_299776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299776 prefixEnd_299776 := by exact prefixLift 299776
  have htrace : WordTrace (prefixWord ++ tailWord_299776) baseStart_299776 baseEnd_299776 := by
    simpa [prefixWord, tailWord_299776, baseEnd_299776] using wordTrace_append hprefix tailTrace_299776
  have hstable : (prefixWord ++ tailWord_299776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299776).length < 2 ^ (prefixWord ++ tailWord_299776).sum := by decide
  have hdescent : baseEnd_299776 < baseStart_299776 := by decide
  rcases family_descends (prefixWord ++ tailWord_299776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299783 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 1, 6]
def baseStart_299783 : Nat := 118140960795 + 299783 * 2 ^ 59
def prefixEnd_299783 : Nat := 4983230072969 + 3 ^ 40 * 299783 * 2
def baseEnd_299783 : Nat := 51310923682301943777943

theorem tailTrace_299783 : CollatzResearch.WordTrace tailWord_299783 prefixEnd_299783 51310923682301943777943 := by
  unfold tailWord_299783
  simp only [CollatzResearch.WordTrace]
  refine ⟨10933984272944864705360003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7289322848629909803573335 10933984272944864705360003)
  ·
    refine ⟨16400976409417297058040005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10933984272944864705360003 16400976409417297058040005)
    ·
      refine ⟨3075183076765743198382501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16400976409417297058040005 3075183076765743198382501)
      ·
        refine ⟨576596826893576849696719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3075183076765743198382501 576596826893576849696719)
        ·
          refine ⟨864895240340365274545079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576596826893576849696719 864895240340365274545079)
          ·
            refine ⟨1297342860510547911817619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864895240340365274545079 1297342860510547911817619)
            ·
              refine ⟨1946014290765821867726429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297342860510547911817619 1946014290765821867726429)
              ·
                refine ⟨729755359037183200397411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1946014290765821867726429 729755359037183200397411)
                ·
                  refine ⟨1094633038555774800596117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729755359037183200397411 1094633038555774800596117)
                  ·
                    refine ⟨51310923682301943777943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1094633038555774800596117 51310923682301943777943)
                    ·
                      rfl

theorem cell23_299783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_299783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299783 prefixEnd_299783 := by exact prefixLift 299783
  have htrace : WordTrace (prefixWord ++ tailWord_299783) baseStart_299783 baseEnd_299783 := by
    simpa [prefixWord, tailWord_299783, baseEnd_299783] using wordTrace_append hprefix tailTrace_299783
  have hstable : (prefixWord ++ tailWord_299783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299783).length < 2 ^ (prefixWord ++ tailWord_299783).sum := by decide
  have hdescent : baseEnd_299783 < baseStart_299783 := by decide
  rcases family_descends (prefixWord ++ tailWord_299783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299793 : List Nat := [1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 3]
def baseStart_299793 : Nat := 118140960795 + 299793 * 2 ^ 59
def prefixEnd_299793 : Nat := 4983230072969 + 3 ^ 40 * 299793 * 2
def baseEnd_299793 : Nat := 153937905853450792208783

theorem tailTrace_299793 : CollatzResearch.WordTrace tailWord_299793 prefixEnd_299793 153937905853450792208783 := by
  unfold tailWord_299793
  simp only [CollatzResearch.WordTrace]
  refine ⟨10934349002908636413224033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7289566001939090942149355 10934349002908636413224033)
  ·
    refine ⟨8200761752181477309918025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10934349002908636413224033 8200761752181477309918025)
    ·
      refine ⟨6150571314136107982438519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8200761752181477309918025 6150571314136107982438519)
      ·
        refine ⟨9225856971204161973657779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6150571314136107982438519 9225856971204161973657779)
        ·
          refine ⟨13838785456806242960486669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9225856971204161973657779 13838785456806242960486669)
          ·
            refine ⟨5189544546302341110182501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13838785456806242960486669 5189544546302341110182501)
            ·
              refine ⟨973039602431688958159219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5189544546302341110182501 973039602431688958159219)
              ·
                refine ⟨1459559403647533437238829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973039602431688958159219 1459559403647533437238829)
                ·
                  refine ⟨547334776367825038964561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1459559403647533437238829 547334776367825038964561)
                  ·
                    refine ⟨410501082275868779223421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 547334776367825038964561 410501082275868779223421)
                    ·
                      refine ⟨153937905853450792208783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 410501082275868779223421 153937905853450792208783)
                      ·
                        rfl

theorem cell23_299793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_299793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299793 prefixEnd_299793 := by exact prefixLift 299793
  have htrace : WordTrace (prefixWord ++ tailWord_299793) baseStart_299793 baseEnd_299793 := by
    simpa [prefixWord, tailWord_299793, baseEnd_299793] using wordTrace_append hprefix tailTrace_299793
  have hstable : (prefixWord ++ tailWord_299793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299793).length < 2 ^ (prefixWord ++ tailWord_299793).sum := by decide
  have hdescent : baseEnd_299793 < baseStart_299793 := by decide
  rcases family_descends (prefixWord ++ tailWord_299793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299807 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 1, 1, 4]
def baseStart_299807 : Nat := 118140960795 + 299807 * 2 ^ 59
def prefixEnd_299807 : Nat := 4983230072969 + 3 ^ 40 * 299807 * 2
def baseEnd_299807 : Nat := 153945094582613737433719

theorem tailTrace_299807 : CollatzResearch.WordTrace tailWord_299807 prefixEnd_299807 153945094582613737433719 := by
  unfold tailWord_299807
  simp only [CollatzResearch.WordTrace]
  refine ⟨10934859624857916804233675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7289906416571944536155783 10934859624857916804233675)
  ·
    refine ⟨16402289437286875206350513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10934859624857916804233675 16402289437286875206350513)
    ·
      refine ⟨12301717077965156404762885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16402289437286875206350513 12301717077965156404762885)
      ·
        refine ⟨2306571952118466825893041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12301717077965156404762885 2306571952118466825893041)
        ·
          refine ⟨1729928964088850119419781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2306571952118466825893041 1729928964088850119419781)
          ·
            refine ⟨324361680766659397391209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1729928964088850119419781 324361680766659397391209)
            ·
              refine ⟨243271260574994548043407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324361680766659397391209 243271260574994548043407)
              ·
                refine ⟨364906890862491822065111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243271260574994548043407 364906890862491822065111)
                ·
                  refine ⟨547360336293737733097667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 364906890862491822065111 547360336293737733097667)
                  ·
                    refine ⟨821040504440606599646501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 547360336293737733097667 821040504440606599646501)
                    ·
                      refine ⟨153945094582613737433719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 821040504440606599646501 153945094582613737433719)
                      ·
                        rfl

theorem cell23_299807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_299807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299807 prefixEnd_299807 := by exact prefixLift 299807
  have htrace : WordTrace (prefixWord ++ tailWord_299807) baseStart_299807 baseEnd_299807 := by
    simpa [prefixWord, tailWord_299807, baseEnd_299807] using wordTrace_append hprefix tailTrace_299807
  have hstable : (prefixWord ++ tailWord_299807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299807).length < 2 ^ (prefixWord ++ tailWord_299807).sum := by decide
  have hdescent : baseEnd_299807 < baseStart_299807 := by decide
  rcases family_descends (prefixWord ++ tailWord_299807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299837 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_299837 : Nat := 118140960795 + 299837 * 2 ^ 59
def prefixEnd_299837 : Nat := 4983230072969 + 3 ^ 40 * 299837 * 2
def baseEnd_299837 : Nat := 153960499002248620058581

theorem tailTrace_299837 : CollatzResearch.WordTrace tailWord_299837 prefixEnd_299837 153960499002248620058581 := by
  unfold tailWord_299837
  simp only [CollatzResearch.WordTrace]
  refine ⟨10935953814749231927825765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7290635876499487951883843 10935953814749231927825765)
  ·
    refine ⟨2050491340265480986467331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10935953814749231927825765 2050491340265480986467331)
    ·
      refine ⟨3075737010398221479700997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2050491340265480986467331 3075737010398221479700997)
      ·
        refine ⟨576700689449666527443937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3075737010398221479700997 576700689449666527443937)
        ·
          refine ⟨432525517087249895582953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 576700689449666527443937 432525517087249895582953)
          ·
            refine ⟨324394137815437421687215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432525517087249895582953 324394137815437421687215)
            ·
              refine ⟨486591206723156132530823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324394137815437421687215 486591206723156132530823)
              ·
                refine ⟨729886810084734198796235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 486591206723156132530823 729886810084734198796235)
                ·
                  refine ⟨1094830215127101298194353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 729886810084734198796235 1094830215127101298194353)
                  ·
                    refine ⟨821122661345325973645765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1094830215127101298194353 821122661345325973645765)
                    ·
                      refine ⟨153960499002248620058581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 821122661345325973645765 153960499002248620058581)
                      ·
                        rfl

theorem cell23_299837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_299837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299837 prefixEnd_299837 := by exact prefixLift 299837
  have htrace : WordTrace (prefixWord ++ tailWord_299837) baseStart_299837 baseEnd_299837 := by
    simpa [prefixWord, tailWord_299837, baseEnd_299837] using wordTrace_append hprefix tailTrace_299837
  have hstable : (prefixWord ++ tailWord_299837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299837).length < 2 ^ (prefixWord ++ tailWord_299837).sum := by decide
  have hdescent : baseEnd_299837 < baseStart_299837 := by decide
  rcases family_descends (prefixWord ++ tailWord_299837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299840 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 2, 1, 3]
def baseStart_299840 : Nat := 118140960795 + 299840 * 2 ^ 59
def prefixEnd_299840 : Nat := 4983230072969 + 3 ^ 40 * 299840 * 2
def baseEnd_299840 : Nat := 153962039444212108321067

theorem tailTrace_299840 : CollatzResearch.WordTrace tailWord_299840 prefixEnd_299840 153962039444212108321067 := by
  unfold tailWord_299840
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468031616869181720092487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7290708822492242293456649 5468031616869181720092487)
  ·
    refine ⟨8202047425303772580138731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5468031616869181720092487 8202047425303772580138731)
    ·
      refine ⟨12303071137955658870208097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8202047425303772580138731 12303071137955658870208097)
      ·
        refine ⟨9227303353466744152656073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12303071137955658870208097 9227303353466744152656073)
        ·
          refine ⟨6920477515100058114492055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9227303353466744152656073 6920477515100058114492055)
          ·
            refine ⟨10380716272650087171738083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6920477515100058114492055 10380716272650087171738083)
            ·
              refine ⟨15571074408975130757607125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10380716272650087171738083 15571074408975130757607125)
              ·
                refine ⟨364947056460354627131417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15571074408975130757607125 364947056460354627131417)
                ·
                  refine ⟨273710292345265970348563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 364947056460354627131417 273710292345265970348563)
                  ·
                    refine ⟨410565438517898955522845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 273710292345265970348563 410565438517898955522845)
                    ·
                      refine ⟨153962039444212108321067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 410565438517898955522845 153962039444212108321067)
                      ·
                        rfl

theorem cell23_299840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 2, 1, 3].length) (baseStart_299840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299840 prefixEnd_299840 := by exact prefixLift 299840
  have htrace : WordTrace (prefixWord ++ tailWord_299840) baseStart_299840 baseEnd_299840 := by
    simpa [prefixWord, tailWord_299840, baseEnd_299840] using wordTrace_append hprefix tailTrace_299840
  have hstable : (prefixWord ++ tailWord_299840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299840).length < 2 ^ (prefixWord ++ tailWord_299840).sum := by decide
  have hdescent : baseEnd_299840 < baseStart_299840 := by decide
  rcases family_descends (prefixWord ++ tailWord_299840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299856 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 1, 8]
def baseStart_299856 : Nat := 118140960795 + 299856 * 2 ^ 59
def prefixEnd_299856 : Nat := 4983230072969 + 3 ^ 40 * 299856 * 2
def baseEnd_299856 : Nat := 51323418378228015240331

theorem tailTrace_299856 : CollatzResearch.WordTrace tailWord_299856 prefixEnd_299856 51323418378228015240331 := by
  unfold tailWord_299856
  simp only [CollatzResearch.WordTrace]
  refine ⟨5468323400840199086383711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7291097867786932115178281 5468323400840199086383711)
  ·
    refine ⟨8202485101260298629575567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5468323400840199086383711 8202485101260298629575567)
    ·
      refine ⟨12303727651890447944363351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8202485101260298629575567 12303727651890447944363351)
      ·
        refine ⟨18455591477835671916545027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12303727651890447944363351 18455591477835671916545027)
        ·
          refine ⟨27683387216753507874817541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18455591477835671916545027 27683387216753507874817541)
          ·
            refine ⟨5190635103141282726528289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27683387216753507874817541 5190635103141282726528289)
            ·
              refine ⟨3892976327355962044896217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5190635103141282726528289 3892976327355962044896217)
              ·
                refine ⟨2919732245516971533672163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3892976327355962044896217 2919732245516971533672163)
                ·
                  refine ⟨4379598368275457300508245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2919732245516971533672163 4379598368275457300508245)
                  ·
                    refine ⟨51323418378228015240331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4379598368275457300508245 51323418378228015240331)
                    ·
                      rfl

theorem cell23_299856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_299856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299856 prefixEnd_299856 := by exact prefixLift 299856
  have htrace : WordTrace (prefixWord ++ tailWord_299856) baseStart_299856 baseEnd_299856 := by
    simpa [prefixWord, tailWord_299856, baseEnd_299856] using wordTrace_append hprefix tailTrace_299856
  have hstable : (prefixWord ++ tailWord_299856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299856).length < 2 ^ (prefixWord ++ tailWord_299856).sum := by decide
  have hdescent : baseEnd_299856 < baseStart_299856 := by decide
  rcases family_descends (prefixWord ++ tailWord_299856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299937 : List Nat := [1, 2, 3, 4, 1, 2, 1, 4, 5]
def baseStart_299937 : Nat := 118140960795 + 299937 * 2 ^ 59
def prefixEnd_299937 : Nat := 4983230072969 + 3 ^ 40 * 299937 * 2
def baseEnd_299937 : Nat := 17112427451966469867569

theorem tailTrace_299937 : CollatzResearch.WordTrace tailWord_299937 prefixEnd_299937 17112427451966469867569 := by
  unfold tailWord_299937
  simp only [CollatzResearch.WordTrace]
  refine ⟨10939601114386949006466065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7293067409591299337644043 10939601114386949006466065)
  ·
    refine ⟨8204700835790211754849549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10939601114386949006466065 8204700835790211754849549)
    ·
      refine ⟨3076762813421329408068581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8204700835790211754849549 3076762813421329408068581)
      ·
        refine ⟨576893027516499264012859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3076762813421329408068581 576893027516499264012859)
        ·
          refine ⟨865339541274748896019289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 576893027516499264012859 865339541274748896019289)
          ·
            refine ⟨649004655956061672014467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 865339541274748896019289 649004655956061672014467)
            ·
              refine ⟨973506983934092508021701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 649004655956061672014467 973506983934092508021701)
              ·
                refine ⟨182532559487642345254069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 973506983934092508021701 182532559487642345254069)
                ·
                  refine ⟨17112427451966469867569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182532559487642345254069 17112427451966469867569)
                  ·
                    rfl

theorem cell23_299937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 5].length) (baseStart_299937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299937 prefixEnd_299937 := by exact prefixLift 299937
  have htrace : WordTrace (prefixWord ++ tailWord_299937) baseStart_299937 baseEnd_299937 := by
    simpa [prefixWord, tailWord_299937, baseEnd_299937] using wordTrace_append hprefix tailTrace_299937
  have hstable : (prefixWord ++ tailWord_299937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299937).length < 2 ^ (prefixWord ++ tailWord_299937).sum := by decide
  have hdescent : baseEnd_299937 < baseStart_299937 := by decide
  rcases family_descends (prefixWord ++ tailWord_299937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299940 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 1, 7, 2]
def baseStart_299940 : Nat := 118140960795 + 299940 * 2 ^ 59
def prefixEnd_299940 : Nat := 4983230072969 + 3 ^ 40 * 299940 * 2
def baseEnd_299940 : Nat := 154013387509661717070607

theorem tailTrace_299940 : CollatzResearch.WordTrace tailWord_299940 prefixEnd_299940 154013387509661717070607 := by
  unfold tailWord_299940
  simp only [CollatzResearch.WordTrace]
  refine ⟨5469855266688040259412637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7293140355584053679216849 5469855266688040259412637)
  ·
    refine ⟨2051195725008015097279739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5469855266688040259412637 2051195725008015097279739)
    ·
      refine ⟨3076793587512022645919609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2051195725008015097279739 3076793587512022645919609)
      ·
        refine ⟨2307595190634016984439707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3076793587512022645919609 2307595190634016984439707)
        ·
          refine ⟨3461392785951025476659561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2307595190634016984439707 3461392785951025476659561)
          ·
            refine ⟨2596044589463269107494671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3461392785951025476659561 2596044589463269107494671)
            ·
              refine ⟨3894066884194903661242007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2596044589463269107494671 3894066884194903661242007)
              ·
                refine ⟨5841100326292355491863011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3894066884194903661242007 5841100326292355491863011)
                ·
                  refine ⟨8761650489438533237794517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5841100326292355491863011 8761650489438533237794517)
                  ·
                    refine ⟨205351183346215622760809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8761650489438533237794517 205351183346215622760809)
                    ·
                      refine ⟨154013387509661717070607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 205351183346215622760809 154013387509661717070607)
                      ·
                        rfl

theorem cell23_299940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_299940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299940 prefixEnd_299940 := by exact prefixLift 299940
  have htrace : WordTrace (prefixWord ++ tailWord_299940) baseStart_299940 baseEnd_299940 := by
    simpa [prefixWord, tailWord_299940, baseEnd_299940] using wordTrace_append hprefix tailTrace_299940
  have hstable : (prefixWord ++ tailWord_299940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299940).length < 2 ^ (prefixWord ++ tailWord_299940).sum := by decide
  have hdescent : baseEnd_299940 < baseStart_299940 := by decide
  rcases family_descends (prefixWord ++ tailWord_299940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299980 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 5, 4]
def baseStart_299980 : Nat := 118140960795 + 299980 * 2 ^ 59
def prefixEnd_299980 : Nat := 4983230072969 + 3 ^ 40 * 299980 * 2
def baseEnd_299980 : Nat := 51344642245280520190141

theorem tailTrace_299980 : CollatzResearch.WordTrace tailWord_299980 prefixEnd_299980 51344642245280520190141 := by
  unfold tailWord_299980
  simp only [CollatzResearch.WordTrace]
  refine ⟨5470584726615583675140697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7294112968820778233520929 5470584726615583675140697)
  ·
    refine ⟨4102938544961687756355523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5470584726615583675140697 4102938544961687756355523)
    ·
      refine ⟨6154407817442531634533285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4102938544961687756355523 6154407817442531634533285)
      ·
        refine ⟨1153951465770474681474991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6154407817442531634533285 1153951465770474681474991)
        ·
          refine ⟨1730927198655712022212487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153951465770474681474991 1730927198655712022212487)
          ·
            refine ⟨2596390797983568033318731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730927198655712022212487 2596390797983568033318731)
            ·
              refine ⟨3894586196975352049978097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2596390797983568033318731 3894586196975352049978097)
              ·
                refine ⟨2920939647731514037483573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3894586196975352049978097 2920939647731514037483573)
                ·
                  refine ⟨273838091974829441014085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2920939647731514037483573 273838091974829441014085)
                  ·
                    refine ⟨51344642245280520190141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 273838091974829441014085 51344642245280520190141)
                    ·
                      rfl

theorem cell23_299980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_299980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299980 prefixEnd_299980 := by exact prefixLift 299980
  have htrace : WordTrace (prefixWord ++ tailWord_299980) baseStart_299980 baseEnd_299980 := by
    simpa [prefixWord, tailWord_299980, baseEnd_299980] using wordTrace_append hprefix tailTrace_299980
  have hstable : (prefixWord ++ tailWord_299980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299980).length < 2 ^ (prefixWord ++ tailWord_299980).sum := by decide
  have hdescent : baseEnd_299980 < baseStart_299980 := by decide
  rcases family_descends (prefixWord ++ tailWord_299980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299983 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 6]
def baseStart_299983 : Nat := 118140960795 + 299983 * 2 ^ 59
def prefixEnd_299983 : Nat := 4983230072969 + 3 ^ 40 * 299983 * 2
def baseEnd_299983 : Nat := 154035467177805048832909

theorem tailTrace_299983 : CollatzResearch.WordTrace tailWord_299983 prefixEnd_299983 154035467177805048832909 := by
  unfold tailWord_299983
  simp only [CollatzResearch.WordTrace]
  refine ⟨10941278872220298862640603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7294185914813532575093735 10941278872220298862640603)
  ·
    refine ⟨16411918308330448293960905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10941278872220298862640603 16411918308330448293960905)
    ·
      refine ⟨12308938731247836220470679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16411918308330448293960905 12308938731247836220470679)
      ·
        refine ⟨18463408096871754330706019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12308938731247836220470679 18463408096871754330706019)
        ·
          refine ⟨27695112145307631496059029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18463408096871754330706019 27695112145307631496059029)
          ·
            refine ⟨1298208381811295226377767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27695112145307631496059029 1298208381811295226377767)
            ·
              refine ⟨1947312572716942839566651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298208381811295226377767 1947312572716942839566651)
              ·
                refine ⟨2920968859075414259349977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1947312572716942839566651 2920968859075414259349977)
                ·
                  refine ⟨2190726644306560694512483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2920968859075414259349977 2190726644306560694512483)
                  ·
                    refine ⟨3286089966459841041768725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2190726644306560694512483 3286089966459841041768725)
                    ·
                      refine ⟨154035467177805048832909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3286089966459841041768725 154035467177805048832909)
                      ·
                        rfl

theorem cell23_299983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_299983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299983 prefixEnd_299983 := by exact prefixLift 299983
  have htrace : WordTrace (prefixWord ++ tailWord_299983) baseStart_299983 baseEnd_299983 := by
    simpa [prefixWord, tailWord_299983, baseEnd_299983] using wordTrace_append hprefix tailTrace_299983
  have hstable : (prefixWord ++ tailWord_299983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299983).length < 2 ^ (prefixWord ++ tailWord_299983).sum := by decide
  have hdescent : baseEnd_299983 < baseStart_299983 := by decide
  rcases family_descends (prefixWord ++ tailWord_299983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_299997 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_299997 : Nat := 118140960795 + 299997 * 2 ^ 59
def prefixEnd_299997 : Nat := 4983230072969 + 3 ^ 40 * 299997 * 2
def baseEnd_299997 : Nat := 51347551968989331352615

theorem tailTrace_299997 : CollatzResearch.WordTrace tailWord_299997 prefixEnd_299997 51347551968989331352615 := by
  unfold tailWord_299997
  simp only [CollatzResearch.WordTrace]
  refine ⟨10941789494169579253650245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7294526329446386169100163 10941789494169579253650245)
  ·
    refine ⟨2051585530156796110059421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10941789494169579253650245 2051585530156796110059421)
    ·
      refine ⟨769344573808798541272283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2051585530156796110059421 769344573808798541272283)
      ·
        refine ⟨1154016860713197811908425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769344573808798541272283 1154016860713197811908425)
        ·
          refine ⟨865512645534898358931319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154016860713197811908425 865512645534898358931319)
          ·
            refine ⟨1298268968302347538396979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865512645534898358931319 1298268968302347538396979)
            ·
              refine ⟨1947403452453521307595469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298268968302347538396979 1947403452453521307595469)
              ·
                refine ⟨730276294670070490348301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1947403452453521307595469 730276294670070490348301)
                ·
                  refine ⟨273853610501276433880613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730276294670070490348301 273853610501276433880613)
                  ·
                    refine ⟨51347551968989331352615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 273853610501276433880613 51347551968989331352615)
                    ·
                      rfl

theorem cell23_299997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_299997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_299997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_299997 prefixEnd_299997 := by exact prefixLift 299997
  have htrace : WordTrace (prefixWord ++ tailWord_299997) baseStart_299997 baseEnd_299997 := by
    simpa [prefixWord, tailWord_299997, baseEnd_299997] using wordTrace_append hprefix tailTrace_299997
  have hstable : (prefixWord ++ tailWord_299997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_299997).length < 2 ^ (prefixWord ++ tailWord_299997).sum := by decide
  have hdescent : baseEnd_299997 < baseStart_299997 := by decide
  rcases family_descends (prefixWord ++ tailWord_299997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300061 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 6]
def baseStart_300061 : Nat := 118140960795 + 300061 * 2 ^ 59
def prefixEnd_300061 : Nat := 4983230072969 + 3 ^ 40 * 300061 * 2
def baseEnd_300061 : Nat := 17119502074317304850839

theorem tailTrace_300061 : CollatzResearch.WordTrace tailWord_300061 prefixEnd_300061 17119502074317304850839 := by
  unfold tailWord_300061
  simp only [CollatzResearch.WordTrace]
  refine ⟨10944123765937718183980037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7296082510625145455986691 10944123765937718183980037)
  ·
    refine ⟨2052023206113322159496257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10944123765937718183980037 2052023206113322159496257)
    ·
      refine ⟨1539017404584991619622193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2052023206113322159496257 1539017404584991619622193)
      ·
        refine ⟨1154263053438743714716645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1539017404584991619622193 1154263053438743714716645)
        ·
          refine ⟨216424322519764446509371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1154263053438743714716645 216424322519764446509371)
          ·
            refine ⟨324636483779646669764057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216424322519764446509371 324636483779646669764057)
            ·
              refine ⟨243477362834735002323043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324636483779646669764057 243477362834735002323043)
              ·
                refine ⟨365216044252102503484565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243477362834735002323043 365216044252102503484565)
                ·
                  refine ⟨17119502074317304850839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 365216044252102503484565 17119502074317304850839)
                  ·
                    rfl

theorem cell23_300061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_300061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300061 prefixEnd_300061 := by exact prefixLift 300061
  have htrace : WordTrace (prefixWord ++ tailWord_300061) baseStart_300061 baseEnd_300061 := by
    simpa [prefixWord, tailWord_300061, baseEnd_300061] using wordTrace_append hprefix tailTrace_300061
  have hstable : (prefixWord ++ tailWord_300061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300061).length < 2 ^ (prefixWord ++ tailWord_300061).sum := by decide
  have hdescent : baseEnd_300061 < baseStart_300061 := by decide
  rcases family_descends (prefixWord ++ tailWord_300061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300090 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_300090 : Nat := 118140960795 + 300090 * 2 ^ 59
def prefixEnd_300090 : Nat := 4983230072969 + 3 ^ 40 * 300090 * 2
def baseEnd_300090 : Nat := 154090409607836130194917

theorem tailTrace_300090 : CollatzResearch.WordTrace tailWord_300090 prefixEnd_300090 154090409607836130194917 := by
  unfold tailWord_300090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2736295370708164034196431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7296787655221770757857149 2736295370708164034196431)
  ·
    refine ⟨4104443056062246051294647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2736295370708164034196431 4104443056062246051294647)
    ·
      refine ⟨6156664584093369076941971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4104443056062246051294647 6156664584093369076941971)
      ·
        refine ⟨9234996876140053615412957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6156664584093369076941971 9234996876140053615412957)
        ·
          refine ⟨3463123828552520105779859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9234996876140053615412957 3463123828552520105779859)
          ·
            refine ⟨5194685742828780158669789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3463123828552520105779859 5194685742828780158669789)
            ·
              refine ⟨1948007153560792559501171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5194685742828780158669789 1948007153560792559501171)
              ·
                refine ⟨2922010730341188839251757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948007153560792559501171 2922010730341188839251757)
                ·
                  refine ⟨1095754023877945814719409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2922010730341188839251757 1095754023877945814719409)
                  ·
                    refine ⟨821815517908459361039557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1095754023877945814719409 821815517908459361039557)
                    ·
                      refine ⟨154090409607836130194917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 821815517908459361039557 154090409607836130194917)
                      ·
                        rfl

theorem cell23_300090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_300090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300090 prefixEnd_300090 := by exact prefixLift 300090
  have htrace : WordTrace (prefixWord ++ tailWord_300090) baseStart_300090 baseEnd_300090 := by
    simpa [prefixWord, tailWord_300090, baseEnd_300090] using wordTrace_append hprefix tailTrace_300090
  have hstable : (prefixWord ++ tailWord_300090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300090).length < 2 ^ (prefixWord ++ tailWord_300090).sum := by decide
  have hdescent : baseEnd_300090 < baseStart_300090 := by decide
  rcases family_descends (prefixWord ++ tailWord_300090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300127 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 3]
def baseStart_300127 : Nat := 118140960795 + 300127 * 2 ^ 59
def prefixEnd_300127 : Nat := 4983230072969 + 3 ^ 40 * 300127 * 2
def baseEnd_300127 : Nat := 154109408392052485432247

theorem tailTrace_300127 : CollatzResearch.WordTrace tailWord_300127 prefixEnd_300127 154109408392052485432247 := by
  unfold tailWord_300127
  simp only [CollatzResearch.WordTrace]
  refine ⟨10946530983698611455882635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7297687322465740970588423 10946530983698611455882635)
  ·
    refine ⟨16419796475547917183823953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10946530983698611455882635 16419796475547917183823953)
    ·
      refine ⟨12314847356660937887867965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16419796475547917183823953 12314847356660937887867965)
      ·
        refine ⟨4618067758747851707950487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12314847356660937887867965 4618067758747851707950487)
        ·
          refine ⟨6927101638121777561925731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4618067758747851707950487 6927101638121777561925731)
          ·
            refine ⟨10390652457182666342888597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6927101638121777561925731 10390652457182666342888597)
            ·
              refine ⟨487061833930437484822903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10390652457182666342888597 487061833930437484822903)
              ·
                refine ⟨730592750895656227234355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487061833930437484822903 730592750895656227234355)
                ·
                  refine ⟨1095889126343484340851533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 730592750895656227234355 1095889126343484340851533)
                  ·
                    refine ⟨410958422378806627819325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1095889126343484340851533 410958422378806627819325)
                    ·
                      refine ⟨154109408392052485432247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 410958422378806627819325 154109408392052485432247)
                      ·
                        rfl

theorem cell23_300127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_300127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300127 prefixEnd_300127 := by exact prefixLift 300127
  have htrace : WordTrace (prefixWord ++ tailWord_300127) baseStart_300127 baseEnd_300127 := by
    simpa [prefixWord, tailWord_300127, baseEnd_300127] using wordTrace_append hprefix tailTrace_300127
  have hstable : (prefixWord ++ tailWord_300127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300127).length < 2 ^ (prefixWord ++ tailWord_300127).sum := by decide
  have hdescent : baseEnd_300127 < baseStart_300127 := by decide
  rcases family_descends (prefixWord ++ tailWord_300127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300140 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_300140 : Nat := 118140960795 + 300140 * 2 ^ 59
def prefixEnd_300140 : Nat := 4983230072969 + 3 ^ 40 * 300140 * 2
def baseEnd_300140 : Nat := 154116083640560934569687

theorem tailTrace_300140 : CollatzResearch.WordTrace tailWord_300140 prefixEnd_300140 154116083640560934569687 := by
  unfold tailWord_300140
  simp only [CollatzResearch.WordTrace]
  refine ⟨5473502566325757338052937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7298003421767676450737249 5473502566325757338052937)
  ·
    refine ⟨4105126924744318003539703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5473502566325757338052937 4105126924744318003539703)
    ·
      refine ⟨6157690387116477005309555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4105126924744318003539703 6157690387116477005309555)
      ·
        refine ⟨9236535580674715507964333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6157690387116477005309555 9236535580674715507964333)
        ·
          refine ⟨3463700842753018315486625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9236535580674715507964333 3463700842753018315486625)
          ·
            refine ⟨2597775632064763736614969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3463700842753018315486625 2597775632064763736614969)
            ·
              refine ⟨1948331724048572802461227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2597775632064763736614969 1948331724048572802461227)
              ·
                refine ⟨2922497586072859203691841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1948331724048572802461227 2922497586072859203691841)
                ·
                  refine ⟨2191873189554644402768881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2922497586072859203691841 2191873189554644402768881)
                  ·
                    refine ⟨1643904892165983302076661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2191873189554644402768881 1643904892165983302076661)
                    ·
                      refine ⟨154116083640560934569687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1643904892165983302076661 154116083640560934569687)
                      ·
                        rfl

theorem cell23_300140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_300140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300140 prefixEnd_300140 := by exact prefixLift 300140
  have htrace : WordTrace (prefixWord ++ tailWord_300140) baseStart_300140 baseEnd_300140 := by
    simpa [prefixWord, tailWord_300140, baseEnd_300140] using wordTrace_append hprefix tailTrace_300140
  have hstable : (prefixWord ++ tailWord_300140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300140).length < 2 ^ (prefixWord ++ tailWord_300140).sum := by decide
  have hdescent : baseEnd_300140 < baseStart_300140 := by decide
  rcases family_descends (prefixWord ++ tailWord_300140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300160 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 2, 6]
def baseStart_300160 : Nat := 118140960795 + 300160 * 2 ^ 59
def prefixEnd_300160 : Nat := 4983230072969 + 3 ^ 40 * 300160 * 2
def baseEnd_300160 : Nat := 51375451084550285439865

theorem tailTrace_300160 : CollatzResearch.WordTrace tailWord_300160 prefixEnd_300160 51375451084550285439865 := by
  unfold tailWord_300160
  simp only [CollatzResearch.WordTrace]
  refine ⟨5473867296289529045916967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7298489728386038727889289 5473867296289529045916967)
  ·
    refine ⟨8210800944434293568875451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5473867296289529045916967 8210800944434293568875451)
    ·
      refine ⟨12316201416651440353313177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8210800944434293568875451 12316201416651440353313177)
      ·
        refine ⟨9237151062488580264984883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12316201416651440353313177 9237151062488580264984883)
        ·
          refine ⟨13855726593732870397477325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9237151062488580264984883 13855726593732870397477325)
          ·
            refine ⟨5195897472649826399053997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13855726593732870397477325 5195897472649826399053997)
            ·
              refine ⟨1948461552243684899645249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5195897472649826399053997 1948461552243684899645249)
              ·
                refine ⟨1461346164182763674733937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948461552243684899645249 1461346164182763674733937)
                ·
                  refine ⟨1096009623137072756050453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1461346164182763674733937 1096009623137072756050453)
                  ·
                    refine ⟨51375451084550285439865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1096009623137072756050453 51375451084550285439865)
                    ·
                      rfl

theorem cell23_300160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_300160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300160 prefixEnd_300160 := by exact prefixLift 300160
  have htrace : WordTrace (prefixWord ++ tailWord_300160) baseStart_300160 baseEnd_300160 := by
    simpa [prefixWord, tailWord_300160, baseEnd_300160] using wordTrace_append hprefix tailTrace_300160
  have hstable : (prefixWord ++ tailWord_300160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300160).length < 2 ^ (prefixWord ++ tailWord_300160).sum := by decide
  have hdescent : baseEnd_300160 < baseStart_300160 := by decide
  rcases family_descends (prefixWord ++ tailWord_300160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300161 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_300161 : Nat := 118140960795 + 300161 * 2 ^ 59
def prefixEnd_300161 : Nat := 4983230072969 + 3 ^ 40 * 300161 * 2
def baseEnd_300161 : Nat := 154126866734305352407091

theorem tailTrace_300161 : CollatzResearch.WordTrace tailWord_300161 prefixEnd_300161 154126866734305352407091 := by
  unfold tailWord_300161
  simp only [CollatzResearch.WordTrace]
  refine ⟨10947771065575435262620337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7298514043716956841746891 10947771065575435262620337)
  ·
    refine ⟨8210828299181576446965253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10947771065575435262620337 8210828299181576446965253)
    ·
      refine ⟨1539530306096545583805985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8210828299181576446965253 1539530306096545583805985)
      ·
        refine ⟨1154647729572409187854489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1539530306096545583805985 1154647729572409187854489)
        ·
          refine ⟨865985797179306890890867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1154647729572409187854489 865985797179306890890867)
          ·
            refine ⟨1298978695768960336336301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865985797179306890890867 1298978695768960336336301)
            ·
              refine ⟨487117010913360126126113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1298978695768960336336301 487117010913360126126113)
              ·
                refine ⟨365337758185020094594585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487117010913360126126113 365337758185020094594585)
                ·
                  refine ⟨274003318638765070945939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365337758185020094594585 274003318638765070945939)
                  ·
                    refine ⟨411004977958147606418909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274003318638765070945939 411004977958147606418909)
                    ·
                      refine ⟨154126866734305352407091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 411004977958147606418909 154126866734305352407091)
                      ·
                        rfl

theorem cell23_300161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_300161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300161 prefixEnd_300161 := by exact prefixLift 300161
  have htrace : WordTrace (prefixWord ++ tailWord_300161) baseStart_300161 baseEnd_300161 := by
    simpa [prefixWord, tailWord_300161, baseEnd_300161] using wordTrace_append hprefix tailTrace_300161
  have hstable : (prefixWord ++ tailWord_300161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300161).length < 2 ^ (prefixWord ++ tailWord_300161).sum := by decide
  have hdescent : baseEnd_300161 < baseStart_300161 := by decide
  rcases family_descends (prefixWord ++ tailWord_300161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300178 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_300178 : Nat := 118140960795 + 300178 * 2 ^ 59
def prefixEnd_300178 : Nat := 4983230072969 + 3 ^ 40 * 300178 * 2
def baseEnd_300178 : Nat := 154135595905431785894513

theorem tailTrace_300178 : CollatzResearch.WordTrace tailWord_300178 prefixEnd_300178 154135595905431785894513 := by
  unfold tailWord_300178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2737097776628461791497297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7298927404342564777326125 2737097776628461791497297)
  ·
    refine ⟨2052823332471346343622973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2737097776628461791497297 2052823332471346343622973)
    ·
      refine ⟨769808749676754878858615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2052823332471346343622973 769808749676754878858615)
      ·
        refine ⟨1154713124515132318287923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769808749676754878858615 1154713124515132318287923)
        ·
          refine ⟨1732069686772698477431885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1154713124515132318287923 1732069686772698477431885)
          ·
            refine ⟨649526132539761929036957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1732069686772698477431885 649526132539761929036957)
            ·
              refine ⟨243572299702410723388859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 649526132539761929036957 243572299702410723388859)
              ·
                refine ⟨365358449553616085083289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243572299702410723388859 365358449553616085083289)
                ·
                  refine ⟨274018837165212063812467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365358449553616085083289 274018837165212063812467)
                  ·
                    refine ⟨411028255747818095718701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274018837165212063812467 411028255747818095718701)
                    ·
                      refine ⟨154135595905431785894513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 411028255747818095718701 154135595905431785894513)
                      ·
                        rfl

theorem cell23_300178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_300178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300178 prefixEnd_300178 := by exact prefixLift 300178
  have htrace : WordTrace (prefixWord ++ tailWord_300178) baseStart_300178 baseEnd_300178 := by
    simpa [prefixWord, tailWord_300178, baseEnd_300178] using wordTrace_append hprefix tailTrace_300178
  have hstable : (prefixWord ++ tailWord_300178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300178).length < 2 ^ (prefixWord ++ tailWord_300178).sum := by decide
  have hdescent : baseEnd_300178 < baseStart_300178 := by decide
  rcases family_descends (prefixWord ++ tailWord_300178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300224 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 7]
def baseStart_300224 : Nat := 118140960795 + 300224 * 2 ^ 59
def prefixEnd_300224 : Nat := 4983230072969 + 3 ^ 40 * 300224 * 2
def baseEnd_300224 : Nat := 17128801779504289546589

theorem tailTrace_300224 : CollatzResearch.WordTrace tailWord_300224 prefixEnd_300224 17128801779504289546589 := by
  unfold tailWord_300224
  simp only [CollatzResearch.WordTrace]
  refine ⟨5475034432173598511081863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7300045909564798014775817 5475034432173598511081863)
  ·
    refine ⟨8212551648260397766622795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5475034432173598511081863 8212551648260397766622795)
    ·
      refine ⟨12318827472390596649934193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8212551648260397766622795 12318827472390596649934193)
      ·
        refine ⟨9239120604292947487450645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12318827472390596649934193 9239120604292947487450645)
        ·
          refine ⟨433083778326231913474249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9239120604292947487450645 433083778326231913474249)
          ·
            refine ⟨324812833744673935105687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433083778326231913474249 324812833744673935105687)
            ·
              refine ⟨487219250617010902658531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324812833744673935105687 487219250617010902658531)
              ·
                refine ⟨730828875925516353987797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487219250617010902658531 730828875925516353987797)
                ·
                  refine ⟨17128801779504289546589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 730828875925516353987797 17128801779504289546589)
                  ·
                    rfl

theorem cell23_300224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 7].length) (baseStart_300224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300224 prefixEnd_300224 := by exact prefixLift 300224
  have htrace : WordTrace (prefixWord ++ tailWord_300224) baseStart_300224 baseEnd_300224 := by
    simpa [prefixWord, tailWord_300224, baseEnd_300224] using wordTrace_append hprefix tailTrace_300224
  have hstable : (prefixWord ++ tailWord_300224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300224).length < 2 ^ (prefixWord ++ tailWord_300224).sum := by decide
  have hdescent : baseEnd_300224 < baseStart_300224 := by decide
  rcases family_descends (prefixWord ++ tailWord_300224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300297 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 6]
def baseStart_300297 : Nat := 118140960795 + 300297 * 2 ^ 59
def prefixEnd_300297 : Nat := 4983230072969 + 3 ^ 40 * 300297 * 2
def baseEnd_300297 : Nat := 17132966678146313367385

theorem tailTrace_300297 : CollatzResearch.WordTrace tailWord_300297 prefixEnd_300297 17132966678146313367385 := by
  unfold tailWord_300297
  simp only [CollatzResearch.WordTrace]
  refine ⟨10952731393082730489571145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7301820928721820326380763 10952731393082730489571145)
  ·
    refine ⟨8214548544812047867178359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10952731393082730489571145 8214548544812047867178359)
    ·
      refine ⟨12321822817218071800767539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8214548544812047867178359 12321822817218071800767539)
      ·
        refine ⟨18482734225827107701151309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12321822817218071800767539 18482734225827107701151309)
        ·
          refine ⟨6931025334685165387931741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18482734225827107701151309 6931025334685165387931741)
          ·
            refine ⟨2599134500506937020474403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6931025334685165387931741 2599134500506937020474403)
            ·
              refine ⟨3898701750760405530711605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2599134500506937020474403 3898701750760405530711605)
              ·
                refine ⟨365503289133788018504213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3898701750760405530711605 365503289133788018504213)
                ·
                  refine ⟨17132966678146313367385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 365503289133788018504213 17132966678146313367385)
                  ·
                    rfl

theorem cell23_300297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 6].length) (baseStart_300297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300297 prefixEnd_300297 := by exact prefixLift 300297
  have htrace : WordTrace (prefixWord ++ tailWord_300297) baseStart_300297 baseEnd_300297 := by
    simpa [prefixWord, tailWord_300297, baseEnd_300297] using wordTrace_append hprefix tailTrace_300297
  have hstable : (prefixWord ++ tailWord_300297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300297).length < 2 ^ (prefixWord ++ tailWord_300297).sum := by decide
  have hdescent : baseEnd_300297 < baseStart_300297 := by decide
  rcases family_descends (prefixWord ++ tailWord_300297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300341 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_300341 : Nat := 118140960795 + 300341 * 2 ^ 59
def prefixEnd_300341 : Nat := 4983230072969 + 3 ^ 40 * 300341 * 2
def baseEnd_300341 : Nat := 154219293252114648156263

theorem tailTrace_300341 : CollatzResearch.WordTrace tailWord_300341 prefixEnd_300341 154219293252114648156263 := by
  unfold tailWord_300341
  simp only [CollatzResearch.WordTrace]
  refine ⟨10954336204923326004172877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7302890803282217336115251 10954336204923326004172877)
  ·
    refine ⟨4107876076846247251564829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10954336204923326004172877 4107876076846247251564829)
    ·
      refine ⟨1540453528817342719336811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4107876076846247251564829 1540453528817342719336811)
      ·
        refine ⟨2310680293226014079005217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540453528817342719336811 2310680293226014079005217)
        ·
          refine ⟨1733010219919510559253913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2310680293226014079005217 1733010219919510559253913)
          ·
            refine ⟨1299757664939632919440435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733010219919510559253913 1299757664939632919440435)
            ·
              refine ⟨1949636497409449379160653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299757664939632919440435 1949636497409449379160653)
              ·
                refine ⟨731113686528543517185245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1949636497409449379160653 731113686528543517185245)
                ·
                  refine ⟨274167632448203818944467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731113686528543517185245 274167632448203818944467)
                  ·
                    refine ⟨411251448672305728416701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274167632448203818944467 411251448672305728416701)
                    ·
                      refine ⟨154219293252114648156263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 411251448672305728416701 154219293252114648156263)
                      ·
                        rfl

theorem cell23_300341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_300341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300341 prefixEnd_300341 := by exact prefixLift 300341
  have htrace : WordTrace (prefixWord ++ tailWord_300341) baseStart_300341 baseEnd_300341 := by
    simpa [prefixWord, tailWord_300341, baseEnd_300341] using wordTrace_append hprefix tailTrace_300341
  have hstable : (prefixWord ++ tailWord_300341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300341).length < 2 ^ (prefixWord ++ tailWord_300341).sum := by decide
  have hdescent : baseEnd_300341 < baseStart_300341 := by decide
  rcases family_descends (prefixWord ++ tailWord_300341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300375 : List Nat := [1, 1, 3, 2, 3, 4, 1, 3, 1, 1, 3]
def baseStart_300375 : Nat := 118140960795 + 300375 * 2 ^ 59
def prefixEnd_300375 : Nat := 4983230072969 + 3 ^ 40 * 300375 * 2
def baseEnd_300375 : Nat := 154236751594367515131107

theorem tailTrace_300375 : CollatzResearch.WordTrace tailWord_300375 prefixEnd_300375 154236751594367515131107 := by
  unfold tailWord_300375
  simp only [CollatzResearch.WordTrace]
  refine ⟨10955576286800149810910579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7303717524533433207273719 10955576286800149810910579)
  ·
    refine ⟨16433364430200224716365869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10955576286800149810910579 16433364430200224716365869)
    ·
      refine ⟨6162511661325084268637201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16433364430200224716365869 6162511661325084268637201)
      ·
        refine ⟨4621883745993813201477901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6162511661325084268637201 4621883745993813201477901)
        ·
          refine ⟨1733206404747679950554213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4621883745993813201477901 1733206404747679950554213)
          ·
            refine ⟨324976200890189990728915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1733206404747679950554213 324976200890189990728915)
            ·
              refine ⟨487464301335284986093373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324976200890189990728915 487464301335284986093373)
              ·
                refine ⟨182799113000731869785015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 487464301335284986093373 182799113000731869785015)
                ·
                  refine ⟨274198669501097804677523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182799113000731869785015 274198669501097804677523)
                  ·
                    refine ⟨411298004251646707016285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274198669501097804677523 411298004251646707016285)
                    ·
                      refine ⟨154236751594367515131107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 411298004251646707016285 154236751594367515131107)
                      ·
                        rfl

theorem cell23_300375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_300375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300375 prefixEnd_300375 := by exact prefixLift 300375
  have htrace : WordTrace (prefixWord ++ tailWord_300375) baseStart_300375 baseEnd_300375 := by
    simpa [prefixWord, tailWord_300375, baseEnd_300375] using wordTrace_append hprefix tailTrace_300375
  have hstable : (prefixWord ++ tailWord_300375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300375).length < 2 ^ (prefixWord ++ tailWord_300375).sum := by decide
  have hdescent : baseEnd_300375 < baseStart_300375 := by decide
  rcases family_descends (prefixWord ++ tailWord_300375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300384 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 5]
def baseStart_300384 : Nat := 118140960795 + 300384 * 2 ^ 59
def prefixEnd_300384 : Nat := 4983230072969 + 3 ^ 40 * 300384 * 2
def baseEnd_300384 : Nat := 154241372920257979918565

theorem tailTrace_300384 : CollatzResearch.WordTrace tailWord_300384 prefixEnd_300384 154241372920257979918565 := by
  unfold tailWord_300384
  simp only [CollatzResearch.WordTrace]
  refine ⟨5477952271883772173994103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7303936362511696231992137 5477952271883772173994103)
  ·
    refine ⟨8216928407825658260991155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5477952271883772173994103 8216928407825658260991155)
    ·
      refine ⟨12325392611738487391486733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8216928407825658260991155 12325392611738487391486733)
      ·
        refine ⟨4622022229401932771807525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12325392611738487391486733 4622022229401932771807525)
        ·
          refine ⟨866629168012862394713911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4622022229401932771807525 866629168012862394713911)
          ·
            refine ⟨1299943752019293592070867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866629168012862394713911 1299943752019293592070867)
            ·
              refine ⟨1949915628028940388106301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299943752019293592070867 1949915628028940388106301)
              ·
                refine ⟨731218360510852645539863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1949915628028940388106301 731218360510852645539863)
                ·
                  refine ⟨1096827540766278968309795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731218360510852645539863 1096827540766278968309795)
                  ·
                    refine ⟨1645241311149418452464693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1096827540766278968309795 1645241311149418452464693)
                    ·
                      refine ⟨154241372920257979918565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1645241311149418452464693 154241372920257979918565)
                      ·
                        rfl

theorem cell23_300384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_300384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300384 prefixEnd_300384 := by exact prefixLift 300384
  have htrace : WordTrace (prefixWord ++ tailWord_300384) baseStart_300384 baseEnd_300384 := by
    simpa [prefixWord, tailWord_300384, baseEnd_300384] using wordTrace_append hprefix tailTrace_300384
  have hstable : (prefixWord ++ tailWord_300384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300384).length < 2 ^ (prefixWord ++ tailWord_300384).sum := by decide
  have hdescent : baseEnd_300384 < baseStart_300384 := by decide
  rcases family_descends (prefixWord ++ tailWord_300384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300387 : List Nat := [1, 1, 1, 5, 2, 2, 11]
def baseStart_300387 : Nat := 118140960795 + 300387 * 2 ^ 59
def prefixEnd_300387 : Nat := 4983230072969 + 3 ^ 40 * 300387 * 2
def baseEnd_300387 : Nat := 1904233498299030471371

theorem tailTrace_300387 : CollatzResearch.WordTrace tailWord_300387 prefixEnd_300387 1904233498299030471371 := by
  unfold tailWord_300387
  simp only [CollatzResearch.WordTrace]
  refine ⟨10956013962756675860347415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7304009308504450573564943 10956013962756675860347415)
  ·
    refine ⟨16434020944135013790521123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10956013962756675860347415 16434020944135013790521123)
    ·
      refine ⟨24651031416202520685781685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16434020944135013790521123 24651031416202520685781685)
      ·
        refine ⟨2311034195268986314292033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24651031416202520685781685 2311034195268986314292033)
        ·
          refine ⟨1733275646451739735719025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2311034195268986314292033 1733275646451739735719025)
          ·
            refine ⟨1299956734838804801789269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733275646451739735719025 1299956734838804801789269)
            ·
              refine ⟨1904233498299030471371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1299956734838804801789269 1904233498299030471371)
              ·
                rfl

theorem cell23_300387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 11].length) (baseStart_300387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300387 prefixEnd_300387 := by exact prefixLift 300387
  have htrace : WordTrace (prefixWord ++ tailWord_300387) baseStart_300387 baseEnd_300387 := by
    simpa [prefixWord, tailWord_300387, baseEnd_300387] using wordTrace_append hprefix tailTrace_300387
  have hstable : (prefixWord ++ tailWord_300387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300387).length < 2 ^ (prefixWord ++ tailWord_300387).sum := by decide
  have hdescent : baseEnd_300387 < baseStart_300387 := by decide
  rcases family_descends (prefixWord ++ tailWord_300387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300392 : List Nat := [2, 1, 4, 2, 3, 1, 3, 2, 1, 1, 3]
def baseStart_300392 : Nat := 118140960795 + 300392 * 2 ^ 59
def prefixEnd_300392 : Nat := 4983230072969 + 3 ^ 40 * 300392 * 2
def baseEnd_300392 : Nat := 154245480765493948618529

theorem tailTrace_300392 : CollatzResearch.WordTrace tailWord_300392 prefixEnd_300392 154245480765493948618529 := by
  unfold tailWord_300392
  simp only [CollatzResearch.WordTrace]
  refine ⟨5478098163869280857139715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7304130885159041142852953 5478098163869280857139715)
  ·
    refine ⟨8217147245803921285709573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5478098163869280857139715 8217147245803921285709573)
    ·
      refine ⟨1540715108588235241070545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8217147245803921285709573 1540715108588235241070545)
      ·
        refine ⟨1155536331441176430802909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1540715108588235241070545 1155536331441176430802909)
        ·
          refine ⟨433326124290441161551091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1155536331441176430802909 433326124290441161551091)
          ·
            refine ⟨649989186435661742326637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433326124290441161551091 649989186435661742326637)
            ·
              refine ⟨243745944913373153372489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 649989186435661742326637 243745944913373153372489)
              ·
                refine ⟨182809458685029865029367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 243745944913373153372489 182809458685029865029367)
                ·
                  refine ⟨274214188027544797544051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 182809458685029865029367 274214188027544797544051)
                  ·
                    refine ⟨411321282041317196316077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274214188027544797544051 411321282041317196316077)
                    ·
                      refine ⟨154245480765493948618529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 411321282041317196316077 154245480765493948618529)
                      ·
                        rfl

theorem cell23_300392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_300392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300392 prefixEnd_300392 := by exact prefixLift 300392
  have htrace : WordTrace (prefixWord ++ tailWord_300392) baseStart_300392 baseEnd_300392 := by
    simpa [prefixWord, tailWord_300392, baseEnd_300392] using wordTrace_append hprefix tailTrace_300392
  have hstable : (prefixWord ++ tailWord_300392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300392).length < 2 ^ (prefixWord ++ tailWord_300392).sum := by decide
  have hdescent : baseEnd_300392 < baseStart_300392 := by decide
  rcases family_descends (prefixWord ++ tailWord_300392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300407 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_300407 : Nat := 118140960795 + 300407 * 2 ^ 59
def prefixEnd_300407 : Nat := 4983230072969 + 3 ^ 40 * 300407 * 2
def baseEnd_300407 : Nat := 154253182975311389930959

theorem tailTrace_300407 : CollatzResearch.WordTrace tailWord_300407 prefixEnd_300407 154253182975311389930959 := by
  unfold tailWord_300407
  simp only [CollatzResearch.WordTrace]
  refine ⟨10956743422684219276075475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7304495615122812850716983 10956743422684219276075475)
  ·
    refine ⟨16435115134026328914113213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10956743422684219276075475 16435115134026328914113213)
    ·
      refine ⟨6163168175259873342792455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16435115134026328914113213 6163168175259873342792455)
      ·
        refine ⟨9244752262889810014188683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6163168175259873342792455 9244752262889810014188683)
        ·
          refine ⟨13867128394334715021283025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9244752262889810014188683 13867128394334715021283025)
          ·
            refine ⟨10400346295751036265962269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13867128394334715021283025 10400346295751036265962269)
            ·
              refine ⟨3900129860906638599735851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10400346295751036265962269 3900129860906638599735851)
              ·
                refine ⟨5850194791359957899603777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3900129860906638599735851 5850194791359957899603777)
                ·
                  refine ⟨4387646093519968424702833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5850194791359957899603777 4387646093519968424702833)
                  ·
                    refine ⟨3290734570139976318527125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4387646093519968424702833 3290734570139976318527125)
                    ·
                      refine ⟨154253182975311389930959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3290734570139976318527125 154253182975311389930959)
                      ·
                        rfl

theorem cell23_300407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_300407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300407 prefixEnd_300407 := by exact prefixLift 300407
  have htrace : WordTrace (prefixWord ++ tailWord_300407) baseStart_300407 baseEnd_300407 := by
    simpa [prefixWord, tailWord_300407, baseEnd_300407] using wordTrace_append hprefix tailTrace_300407
  have hstable : (prefixWord ++ tailWord_300407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300407).length < 2 ^ (prefixWord ++ tailWord_300407).sum := by decide
  have hdescent : baseEnd_300407 < baseStart_300407 := by decide
  rcases family_descends (prefixWord ++ tailWord_300407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300448 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 2, 1, 3]
def baseStart_300448 : Nat := 118140960795 + 300448 * 2 ^ 59
def prefixEnd_300448 : Nat := 4983230072969 + 3 ^ 40 * 300448 * 2
def baseEnd_300448 : Nat := 154274235682145729518271

theorem tailTrace_300448 : CollatzResearch.WordTrace tailWord_300448 prefixEnd_300448 154274235682145729518271 := by
  unfold tailWord_300448
  simp only [CollatzResearch.WordTrace]
  refine ⟨5479119407767841639158999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7305492543690455518878665 5479119407767841639158999)
  ·
    refine ⟨8218679111651762458738499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5479119407767841639158999 8218679111651762458738499)
    ·
      refine ⟨12328018667477643688107749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8218679111651762458738499 12328018667477643688107749)
      ·
        refine ⟨2311503500152058191520203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12328018667477643688107749 2311503500152058191520203)
        ·
          refine ⟨3467255250228087287280305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311503500152058191520203 3467255250228087287280305)
          ·
            refine ⟨2600441437671065465460229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3467255250228087287280305 2600441437671065465460229)
            ·
              refine ⟨487582769563324774773793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2600441437671065465460229 487582769563324774773793)
              ·
                refine ⟨365687077172493581080345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487582769563324774773793 365687077172493581080345)
                ·
                  refine ⟨274265307879370185810259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365687077172493581080345 274265307879370185810259)
                  ·
                    refine ⟨411397961819055278715389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274265307879370185810259 411397961819055278715389)
                    ·
                      refine ⟨154274235682145729518271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 411397961819055278715389 154274235682145729518271)
                      ·
                        rfl

theorem cell23_300448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_300448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300448 prefixEnd_300448 := by exact prefixLift 300448
  have htrace : WordTrace (prefixWord ++ tailWord_300448) baseStart_300448 baseEnd_300448 := by
    simpa [prefixWord, tailWord_300448, baseEnd_300448] using wordTrace_append hprefix tailTrace_300448
  have hstable : (prefixWord ++ tailWord_300448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300448).length < 2 ^ (prefixWord ++ tailWord_300448).sum := by decide
  have hdescent : baseEnd_300448 < baseStart_300448 := by decide
  rcases family_descends (prefixWord ++ tailWord_300448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300488 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 4, 2, 2]
def baseStart_300488 : Nat := 118140960795 + 300488 * 2 ^ 59
def prefixEnd_300488 : Nat := 4983230072969 + 3 ^ 40 * 300488 * 2
def baseEnd_300488 : Nat := 154294774908325573018087

theorem tailTrace_300488 : CollatzResearch.WordTrace tailWord_300488 prefixEnd_300488 154294774908325573018087 := by
  unfold tailWord_300488
  simp only [CollatzResearch.WordTrace]
  refine ⟨5479848867695385054887059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7306465156927180073182745 5479848867695385054887059)
  ·
    refine ⟨8219773301543077582330589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5479848867695385054887059 8219773301543077582330589)
    ·
      refine ⟨3082414988078654093373971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8219773301543077582330589 3082414988078654093373971)
      ·
        refine ⟨4623622482117981140060957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3082414988078654093373971 4623622482117981140060957)
        ·
          refine ⟨1733858430794242927522859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4623622482117981140060957 1733858430794242927522859)
          ·
            refine ⟨2600787646191364391284289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733858430794242927522859 2600787646191364391284289)
            ·
              refine ⟨1950590734643523293463217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2600787646191364391284289 1950590734643523293463217)
              ·
                refine ⟨1462943050982642470097413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950590734643523293463217 1462943050982642470097413)
                ·
                  refine ⟨274301822059245463143265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1462943050982642470097413 274301822059245463143265)
                  ·
                    refine ⟨205726366544434097357449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 274301822059245463143265 205726366544434097357449)
                    ·
                      refine ⟨154294774908325573018087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 205726366544434097357449 154294774908325573018087)
                      ·
                        rfl

theorem cell23_300488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_300488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300488 prefixEnd_300488 := by exact prefixLift 300488
  have htrace : WordTrace (prefixWord ++ tailWord_300488) baseStart_300488 baseEnd_300488 := by
    simpa [prefixWord, tailWord_300488, baseEnd_300488] using wordTrace_append hprefix tailTrace_300488
  have hstable : (prefixWord ++ tailWord_300488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300488).length < 2 ^ (prefixWord ++ tailWord_300488).sum := by decide
  have hdescent : baseEnd_300488 < baseStart_300488 := by decide
  rcases family_descends (prefixWord ++ tailWord_300488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300492 : List Nat := [2, 2, 1, 4, 2, 3, 2, 1, 1, 3, 2]
def baseStart_300492 : Nat := 118140960795 + 300492 * 2 ^ 59
def prefixEnd_300492 : Nat := 4983230072969 + 3 ^ 40 * 300492 * 2
def baseEnd_300492 : Nat := 154296828830943557368069

theorem tailTrace_300492 : CollatzResearch.WordTrace tailWord_300492 prefixEnd_300492 154296828830943557368069 := by
  unfold tailWord_300492
  simp only [CollatzResearch.WordTrace]
  refine ⟨5479921813688139396459865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7306562418250852528613153 5479921813688139396459865)
  ·
    refine ⟨4109941360266104547344899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5479921813688139396459865 4109941360266104547344899)
    ·
      refine ⟨6164912040399156821017349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4109941360266104547344899 6164912040399156821017349)
      ·
        refine ⟨1155921007574841903940753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6164912040399156821017349 1155921007574841903940753)
        ·
          refine ⟨866940755681131427955565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1155921007574841903940753 866940755681131427955565)
          ·
            refine ⟨325102783380424285483337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 866940755681131427955565 325102783380424285483337)
            ·
              refine ⟨243827087535318214112503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325102783380424285483337 243827087535318214112503)
              ·
                refine ⟨365740631302977321168755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243827087535318214112503 365740631302977321168755)
                ·
                  refine ⟨548610946954465981753133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365740631302977321168755 548610946954465981753133)
                  ·
                    refine ⟨205729105107924743157425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 548610946954465981753133 205729105107924743157425)
                    ·
                      refine ⟨154296828830943557368069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 205729105107924743157425 154296828830943557368069)
                      ·
                        rfl

theorem cell23_300492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_300492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300492 prefixEnd_300492 := by exact prefixLift 300492
  have htrace : WordTrace (prefixWord ++ tailWord_300492) baseStart_300492 baseEnd_300492 := by
    simpa [prefixWord, tailWord_300492, baseEnd_300492] using wordTrace_append hprefix tailTrace_300492
  have hstable : (prefixWord ++ tailWord_300492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300492).length < 2 ^ (prefixWord ++ tailWord_300492).sum := by decide
  have hdescent : baseEnd_300492 < baseStart_300492 := by decide
  rcases family_descends (prefixWord ++ tailWord_300492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300505 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 2, 2, 2]
def baseStart_300505 : Nat := 118140960795 + 300505 * 2 ^ 59
def prefixEnd_300505 : Nat := 4983230072969 + 3 ^ 40 * 300505 * 2
def baseEnd_300505 : Nat := 154303504079452006505509

theorem tailTrace_300505 : CollatzResearch.WordTrace tailWord_300505 prefixEnd_300505 154303504079452006505509 := by
  unfold tailWord_300505
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960317776329182013142969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7306878517552788008761979 10960317776329182013142969)
  ·
    refine ⟨8220238332246886509857227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10960317776329182013142969 8220238332246886509857227)
    ·
      refine ⟨12330357498370329764785841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8220238332246886509857227 12330357498370329764785841)
      ·
        refine ⟨9247768123777747323589381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12330357498370329764785841 9247768123777747323589381)
        ·
          refine ⟨1733956523208327623173009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9247768123777747323589381 1733956523208327623173009)
          ·
            refine ⟨1300467392406245717379757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733956523208327623173009 1300467392406245717379757)
            ·
              refine ⟨487675272152342144017409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1300467392406245717379757 487675272152342144017409)
              ·
                refine ⟨365756454114256608013057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487675272152342144017409 365756454114256608013057)
                ·
                  refine ⟨274317340585692456009793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365756454114256608013057 274317340585692456009793)
                  ·
                    refine ⟨205738005439269342007345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 274317340585692456009793 205738005439269342007345)
                    ·
                      refine ⟨154303504079452006505509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 205738005439269342007345 154303504079452006505509)
                      ·
                        rfl

theorem cell23_300505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 2, 2, 2].length) (baseStart_300505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300505 prefixEnd_300505 := by exact prefixLift 300505
  have htrace : WordTrace (prefixWord ++ tailWord_300505) baseStart_300505 baseEnd_300505 := by
    simpa [prefixWord, tailWord_300505, baseEnd_300505] using wordTrace_append hprefix tailTrace_300505
  have hstable : (prefixWord ++ tailWord_300505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300505).length < 2 ^ (prefixWord ++ tailWord_300505).sum := by decide
  have hdescent : baseEnd_300505 < baseStart_300505 := by decide
  rcases family_descends (prefixWord ++ tailWord_300505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300511 : List Nat := [1, 1, 2, 3, 3, 1, 1, 6, 5]
def baseStart_300511 : Nat := 118140960795 + 300511 * 2 ^ 59
def prefixEnd_300511 : Nat := 4983230072969 + 3 ^ 40 * 300511 * 2
def baseEnd_300511 : Nat := 17145176107042109225609

theorem tailTrace_300511 : CollatzResearch.WordTrace tailWord_300511 prefixEnd_300511 17145176107042109225609 := by
  unfold tailWord_300511
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960536614307445037861387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7307024409538296691907591 10960536614307445037861387)
  ·
    refine ⟨16440804921461167556792081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10960536614307445037861387 16440804921461167556792081)
    ·
      refine ⟨12330603691095875667594061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16440804921461167556792081 12330603691095875667594061)
      ·
        refine ⟨4623976384160953375347773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12330603691095875667594061 4623976384160953375347773)
        ·
          refine ⟨1733991144060357515755415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4623976384160953375347773 1733991144060357515755415)
          ·
            refine ⟨2600986716090536273633123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1733991144060357515755415 2600986716090536273633123)
            ·
              refine ⟨3901480074135804410449685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2600986716090536273633123 3901480074135804410449685)
              ·
                refine ⟨182881878475115831739829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3901480074135804410449685 182881878475115831739829)
                ·
                  refine ⟨17145176107042109225609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182881878475115831739829 17145176107042109225609)
                  ·
                    rfl

theorem cell23_300511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 5].length) (baseStart_300511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300511 prefixEnd_300511 := by exact prefixLift 300511
  have htrace : WordTrace (prefixWord ++ tailWord_300511) baseStart_300511 baseEnd_300511 := by
    simpa [prefixWord, tailWord_300511, baseEnd_300511] using wordTrace_append hprefix tailTrace_300511
  have hstable : (prefixWord ++ tailWord_300511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300511).length < 2 ^ (prefixWord ++ tailWord_300511).sum := by decide
  have hdescent : baseEnd_300511 < baseStart_300511 := by decide
  rcases family_descends (prefixWord ++ tailWord_300511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300522 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_300522 : Nat := 118140960795 + 300522 * 2 ^ 59
def prefixEnd_300522 : Nat := 4983230072969 + 3 ^ 40 * 300522 * 2
def baseEnd_300522 : Nat := 154312233250578439992931

theorem tailTrace_300522 : CollatzResearch.WordTrace tailWord_300522 prefixEnd_300522 154312233250578439992931 := by
  unfold tailWord_300522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740234454316898479127955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7307291878178395944341213 2740234454316898479127955)
  ·
    refine ⟨4110351681475347718691933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2740234454316898479127955 4110351681475347718691933)
    ·
      refine ⟨1541381880553255394509475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4110351681475347718691933 1541381880553255394509475)
      ·
        refine ⟨2312072820829883091764213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541381880553255394509475 2312072820829883091764213)
        ·
          refine ⟨216756826952801539852895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2312072820829883091764213 216756826952801539852895)
          ·
            refine ⟨325135240429202309779343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216756826952801539852895 325135240429202309779343)
            ·
              refine ⟨487702860643803464669015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325135240429202309779343 487702860643803464669015)
              ·
                refine ⟨731554290965705197003523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 487702860643803464669015 731554290965705197003523)
                ·
                  refine ⟨1097331436448557795505285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 731554290965705197003523 1097331436448557795505285)
                  ·
                    refine ⟨205749644334104586657241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097331436448557795505285 205749644334104586657241)
                    ·
                      refine ⟨154312233250578439992931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 205749644334104586657241 154312233250578439992931)
                      ·
                        rfl

theorem cell23_300522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_300522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300522 prefixEnd_300522 := by exact prefixLift 300522
  have htrace : WordTrace (prefixWord ++ tailWord_300522) baseStart_300522 baseEnd_300522 := by
    simpa [prefixWord, tailWord_300522, baseEnd_300522] using wordTrace_append hprefix tailTrace_300522
  have hstable : (prefixWord ++ tailWord_300522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300522).length < 2 ^ (prefixWord ++ tailWord_300522).sum := by decide
  have hdescent : baseEnd_300522 < baseStart_300522 := by decide
  rcases family_descends (prefixWord ++ tailWord_300522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300524 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_300524 : Nat := 118140960795 + 300524 * 2 ^ 59
def prefixEnd_300524 : Nat := 4983230072969 + 3 ^ 40 * 300524 * 2
def baseEnd_300524 : Nat := 51437753403962477389307

theorem tailTrace_300524 : CollatzResearch.WordTrace tailWord_300524 prefixEnd_300524 51437753403962477389307 := by
  unfold tailWord_300524
  simp only [CollatzResearch.WordTrace]
  refine ⟨5480505381630174129042313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7307340508840232172056417 5480505381630174129042313)
  ·
    refine ⟨4110379036222630596781735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5480505381630174129042313 4110379036222630596781735)
    ·
      refine ⟨6165568554333945895172603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4110379036222630596781735 6165568554333945895172603)
      ·
        refine ⟨9248352831500918842758905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6165568554333945895172603 9248352831500918842758905)
        ·
          refine ⟨6936264623625689132069179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9248352831500918842758905 6936264623625689132069179)
          ·
            refine ⟨10404396935438533698103769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6936264623625689132069179 10404396935438533698103769)
            ·
              refine ⟨7803297701578900273577827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10404396935438533698103769 7803297701578900273577827)
              ·
                refine ⟨11704946552368350410366741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7803297701578900273577827 11704946552368350410366741)
                ·
                  refine ⟨548669369642266425485941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11704946552368350410366741 548669369642266425485941)
                  ·
                    refine ⟨51437753403962477389307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 548669369642266425485941 51437753403962477389307)
                    ·
                      rfl

theorem cell23_300524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_300524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300524 prefixEnd_300524 := by exact prefixLift 300524
  have htrace : WordTrace (prefixWord ++ tailWord_300524) baseStart_300524 baseEnd_300524 := by
    simpa [prefixWord, tailWord_300524, baseEnd_300524] using wordTrace_append hprefix tailTrace_300524
  have hstable : (prefixWord ++ tailWord_300524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300524).length < 2 ^ (prefixWord ++ tailWord_300524).sum := by decide
  have hdescent : baseEnd_300524 < baseStart_300524 := by decide
  rcases family_descends (prefixWord ++ tailWord_300524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300545 : List Nat := [1, 2, 4, 1, 4, 2, 1, 3, 5]
def baseStart_300545 : Nat := 118140960795 + 300545 * 2 ^ 59
def prefixEnd_300545 : Nat := 4983230072969 + 3 ^ 40 * 300545 * 2
def baseEnd_300545 : Nat := 17147115922847983333925

theorem tailTrace_300545 : CollatzResearch.WordTrace tailWord_300545 prefixEnd_300545 17147115922847983333925 := by
  unfold tailWord_300545
  simp only [CollatzResearch.WordTrace]
  refine ⟨10961776696184268844599089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7307851130789512563066059 10961776696184268844599089)
  ·
    refine ⟨8221332522138201633449317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10961776696184268844599089 8221332522138201633449317)
    ·
      refine ⟨1541499847900912806271747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8221332522138201633449317 1541499847900912806271747)
      ·
        refine ⟨2312249771851369209407621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541499847900912806271747 2312249771851369209407621)
        ·
          refine ⟨433546832222131726763929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2312249771851369209407621 433546832222131726763929)
          ·
            refine ⟨325160124166598795072947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433546832222131726763929 325160124166598795072947)
            ·
              refine ⟨487740186249898192609421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325160124166598795072947 487740186249898192609421)
              ·
                refine ⟨182902569843711822228533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 487740186249898192609421 182902569843711822228533)
                ·
                  refine ⟨17147115922847983333925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182902569843711822228533 17147115922847983333925)
                  ·
                    rfl

theorem cell23_300545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 5].length) (baseStart_300545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300545 prefixEnd_300545 := by exact prefixLift 300545
  have htrace : WordTrace (prefixWord ++ tailWord_300545) baseStart_300545 baseEnd_300545 := by
    simpa [prefixWord, tailWord_300545, baseEnd_300545] using wordTrace_append hprefix tailTrace_300545
  have hstable : (prefixWord ++ tailWord_300545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300545).length < 2 ^ (prefixWord ++ tailWord_300545).sum := by decide
  have hdescent : baseEnd_300545 < baseStart_300545 := by decide
  rcases family_descends (prefixWord ++ tailWord_300545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300558 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_300558 : Nat := 118140960795 + 300558 * 2 ^ 59
def prefixEnd_300558 : Nat := 4983230072969 + 3 ^ 40 * 300558 * 2
def baseEnd_300558 : Nat := 51443572851380099714255

theorem tailTrace_300558 : CollatzResearch.WordTrace tailWord_300558 prefixEnd_300558 51443572851380099714255 := by
  unfold tailWord_300558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370281355642146508102791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7308167230091448043214885 1370281355642146508102791)
  ·
    refine ⟨2055422033463219762154187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1370281355642146508102791 2055422033463219762154187)
    ·
      refine ⟨3083133050194829643231281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2055422033463219762154187 3083133050194829643231281)
      ·
        refine ⟨2312349787646122232423461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3083133050194829643231281 2312349787646122232423461)
        ·
          refine ⟨433565585183647918579399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2312349787646122232423461 433565585183647918579399)
          ·
            refine ⟨650348377775471877869099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433565585183647918579399 650348377775471877869099)
            ·
              refine ⟨975522566663207816803649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650348377775471877869099 975522566663207816803649)
              ·
                refine ⟨731641924997405862602737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975522566663207816803649 731641924997405862602737)
                ·
                  refine ⟨548731443748054396952053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 731641924997405862602737 548731443748054396952053)
                  ·
                    refine ⟨51443572851380099714255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 548731443748054396952053 51443572851380099714255)
                    ·
                      rfl

theorem cell23_300558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_300558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300558 prefixEnd_300558 := by exact prefixLift 300558
  have htrace : WordTrace (prefixWord ++ tailWord_300558) baseStart_300558 baseEnd_300558 := by
    simpa [prefixWord, tailWord_300558, baseEnd_300558] using wordTrace_append hprefix tailTrace_300558
  have hstable : (prefixWord ++ tailWord_300558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300558).length < 2 ^ (prefixWord ++ tailWord_300558).sum := by decide
  have hdescent : baseEnd_300558 < baseStart_300558 := by decide
  rcases family_descends (prefixWord ++ tailWord_300558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300561 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_300561 : Nat := 118140960795 + 300561 * 2 ^ 59
def prefixEnd_300561 : Nat := 4983230072969 + 3 ^ 40 * 300561 * 2
def baseEnd_300561 : Nat := 154332258996103787405251

theorem tailTrace_300561 : CollatzResearch.WordTrace tailWord_300561 prefixEnd_300561 154332258996103787405251 := by
  unfold tailWord_300561
  simp only [CollatzResearch.WordTrace]
  refine ⟨10962360264126303577181537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7308240176084202384787691 10962360264126303577181537)
  ·
    refine ⟨8221770198094727682886153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10962360264126303577181537 8221770198094727682886153)
    ·
      refine ⟨6166327648571045762164615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8221770198094727682886153 6166327648571045762164615)
      ·
        refine ⟨9249491472856568643246923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6166327648571045762164615 9249491472856568643246923)
        ·
          refine ⟨13874237209284852964870385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9249491472856568643246923 13874237209284852964870385)
          ·
            refine ⟨10405677906963639723652789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13874237209284852964870385 10405677906963639723652789)
            ·
              refine ⟨975532303777841224092449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10405677906963639723652789 975532303777841224092449)
              ·
                refine ⟨731649227833380918069337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975532303777841224092449 731649227833380918069337)
                ·
                  refine ⟨548736920875035688552003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 731649227833380918069337 548736920875035688552003)
                  ·
                    refine ⟨823105381312553532828005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 548736920875035688552003 823105381312553532828005)
                    ·
                      refine ⟨154332258996103787405251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 823105381312553532828005 154332258996103787405251)
                      ·
                        rfl

theorem cell23_300561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_300561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300561 prefixEnd_300561 := by exact prefixLift 300561
  have htrace : WordTrace (prefixWord ++ tailWord_300561) baseStart_300561 baseEnd_300561 := by
    simpa [prefixWord, tailWord_300561, baseEnd_300561] using wordTrace_append hprefix tailTrace_300561
  have hstable : (prefixWord ++ tailWord_300561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300561).length < 2 ^ (prefixWord ++ tailWord_300561).sum := by decide
  have hdescent : baseEnd_300561 < baseStart_300561 := by decide
  rcases family_descends (prefixWord ++ tailWord_300561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300578 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_300578 : Nat := 118140960795 + 300578 * 2 ^ 59
def prefixEnd_300578 : Nat := 4983230072969 + 3 ^ 40 * 300578 * 2
def baseEnd_300578 : Nat := 154340988167230220892673

theorem tailTrace_300578 : CollatzResearch.WordTrace tailWord_300578 prefixEnd_300578 154340988167230220892673 := by
  unfold tailWord_300578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2740745076266178870137597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7308653536709810320366925 2740745076266178870137597)
  ·
    refine ⟨1027779403599817076301599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2740745076266178870137597 1027779403599817076301599)
    ·
      refine ⟨1541669105399725614452399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1027779403599817076301599 1541669105399725614452399)
      ·
        refine ⟨2312503658099588421678599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541669105399725614452399 2312503658099588421678599)
        ·
          refine ⟨3468755487149382632517899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2312503658099588421678599 3468755487149382632517899)
          ·
            refine ⟨5203133230724073948776849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3468755487149382632517899 5203133230724073948776849)
            ·
              refine ⟨3902349923043055461582637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5203133230724073948776849 3902349923043055461582637)
              ·
                refine ⟨1463381221141145798093489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3902349923043055461582637 1463381221141145798093489)
                ·
                  refine ⟨1097535915855859348570117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1463381221141145798093489 1097535915855859348570117)
                  ·
                    refine ⟨205787984222973627856897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1097535915855859348570117 205787984222973627856897)
                    ·
                      refine ⟨154340988167230220892673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 205787984222973627856897 154340988167230220892673)
                      ·
                        rfl

theorem cell23_300578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_300578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300578 prefixEnd_300578 := by exact prefixLift 300578
  have htrace : WordTrace (prefixWord ++ tailWord_300578) baseStart_300578 baseEnd_300578 := by
    simpa [prefixWord, tailWord_300578, baseEnd_300578] using wordTrace_append hprefix tailTrace_300578
  have hstable : (prefixWord ++ tailWord_300578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300578).length < 2 ^ (prefixWord ++ tailWord_300578).sum := by decide
  have hdescent : baseEnd_300578 < baseStart_300578 := by decide
  rcases family_descends (prefixWord ++ tailWord_300578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300581 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 6, 2, 3]
def baseStart_300581 : Nat := 118140960795 + 300581 * 2 ^ 59
def prefixEnd_300581 : Nat := 4983230072969 + 3 ^ 40 * 300581 * 2
def baseEnd_300581 : Nat := 154342528609193709155159

theorem tailTrace_300581 : CollatzResearch.WordTrace tailWord_300581 prefixEnd_300581 154342528609193709155159 := by
  unfold tailWord_300581
  simp only [CollatzResearch.WordTrace]
  refine ⟨10963089724053846992909597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7308726482702564661939731 10963089724053846992909597)
  ·
    refine ⟨4111158646520192622341099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10963089724053846992909597 4111158646520192622341099)
    ·
      refine ⟨6166737969780288933511649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4111158646520192622341099 6166737969780288933511649)
      ·
        refine ⟨4625053477335216700133737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6166737969780288933511649 4625053477335216700133737)
        ·
          refine ⟨3468790108001412525100303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4625053477335216700133737 3468790108001412525100303)
          ·
            refine ⟨5203185162002118787650455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3468790108001412525100303 5203185162002118787650455)
            ·
              refine ⟨7804777743003178181475683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5203185162002118787650455 7804777743003178181475683)
              ·
                refine ⟨11707166614504767272213525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7804777743003178181475683 11707166614504767272213525)
                ·
                  refine ⟨548773435054910965885009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11707166614504767272213525 548773435054910965885009)
                  ·
                    refine ⟨411580076291183224413757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 548773435054910965885009 411580076291183224413757)
                    ·
                      refine ⟨154342528609193709155159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 411580076291183224413757 154342528609193709155159)
                      ·
                        rfl

theorem cell23_300581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_300581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300581 prefixEnd_300581 := by exact prefixLift 300581
  have htrace : WordTrace (prefixWord ++ tailWord_300581) baseStart_300581 baseEnd_300581 := by
    simpa [prefixWord, tailWord_300581, baseEnd_300581] using wordTrace_append hprefix tailTrace_300581
  have hstable : (prefixWord ++ tailWord_300581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300581).length < 2 ^ (prefixWord ++ tailWord_300581).sum := by decide
  have hdescent : baseEnd_300581 < baseStart_300581 := by decide
  rcases family_descends (prefixWord ++ tailWord_300581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300631 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 3, 5]
def baseStart_300631 : Nat := 118140960795 + 300631 * 2 ^ 59
def prefixEnd_300631 : Nat := 4983230072969 + 3 ^ 40 * 300631 * 2
def baseEnd_300631 : Nat := 51456067547306171176643

theorem tailTrace_300631 : CollatzResearch.WordTrace tailWord_300631 prefixEnd_300631 51456067547306171176643 := by
  unfold tailWord_300631
  simp only [CollatzResearch.WordTrace]
  refine ⟨10964913373872705532229747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7309942249248470354819831 10964913373872705532229747)
  ·
    refine ⟨16447370060809058298344621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10964913373872705532229747 16447370060809058298344621)
    ·
      refine ⟨6167763772803396861879233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16447370060809058298344621 6167763772803396861879233)
      ·
        refine ⟨4625822829602547646409425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6167763772803396861879233 4625822829602547646409425)
        ·
          refine ⟨3469367122201910734807069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4625822829602547646409425 3469367122201910734807069)
          ·
            refine ⟨1301012670825716525552651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3469367122201910734807069 1301012670825716525552651)
            ·
              refine ⟨1951519006238574788328977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301012670825716525552651 1951519006238574788328977)
              ·
                refine ⟨1463639254678931091246733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1951519006238574788328977 1463639254678931091246733)
                ·
                  refine ⟨548864720504599159217525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1463639254678931091246733 548864720504599159217525)
                  ·
                    refine ⟨51456067547306171176643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 548864720504599159217525 51456067547306171176643)
                    ·
                      rfl

theorem cell23_300631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_300631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300631 prefixEnd_300631 := by exact prefixLift 300631
  have htrace : WordTrace (prefixWord ++ tailWord_300631) baseStart_300631 baseEnd_300631 := by
    simpa [prefixWord, tailWord_300631, baseEnd_300631] using wordTrace_append hprefix tailTrace_300631
  have hstable : (prefixWord ++ tailWord_300631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300631).length < 2 ^ (prefixWord ++ tailWord_300631).sum := by decide
  have hdescent : baseEnd_300631 < baseStart_300631 := by decide
  rcases family_descends (prefixWord ++ tailWord_300631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300645 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 3, 1, 3]
def baseStart_300645 : Nat := 118140960795 + 300645 * 2 ^ 59
def prefixEnd_300645 : Nat := 4983230072969 + 3 ^ 40 * 300645 * 2
def baseEnd_300645 : Nat := 154375391371081458754865

theorem tailTrace_300645 : CollatzResearch.WordTrace tailWord_300645 prefixEnd_300645 154375391371081458754865 := by
  unfold tailWord_300645
  simp only [CollatzResearch.WordTrace]
  refine ⟨10965423995821985923239389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7310282663881323948826259 10965423995821985923239389)
  ·
    refine ⟨4112033998433244721214771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10965423995821985923239389 4112033998433244721214771)
    ·
      refine ⟨6168050997649867081822157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4112033998433244721214771 6168050997649867081822157)
      ·
        refine ⟨2313019124118700155683309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6168050997649867081822157 2313019124118700155683309)
        ·
          refine ⟨867382171544512558381241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2313019124118700155683309 867382171544512558381241)
          ·
            refine ⟨650536628658384418785931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 867382171544512558381241 650536628658384418785931)
            ·
              refine ⟨975804942987576628178897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 650536628658384418785931 975804942987576628178897)
              ·
                refine ⟨731853707240682471134173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975804942987576628178897 731853707240682471134173)
                ·
                  refine ⟨274445140215255926675315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731853707240682471134173 274445140215255926675315)
                  ·
                    refine ⟨411667710322883890012973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274445140215255926675315 411667710322883890012973)
                    ·
                      refine ⟨154375391371081458754865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 411667710322883890012973 154375391371081458754865)
                      ·
                        rfl

theorem cell23_300645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_300645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300645 prefixEnd_300645 := by exact prefixLift 300645
  have htrace : WordTrace (prefixWord ++ tailWord_300645) baseStart_300645 baseEnd_300645 := by
    simpa [prefixWord, tailWord_300645, baseEnd_300645] using wordTrace_append hprefix tailTrace_300645
  have hstable : (prefixWord ++ tailWord_300645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300645).length < 2 ^ (prefixWord ++ tailWord_300645).sum := by decide
  have hdescent : baseEnd_300645 < baseStart_300645 := by decide
  rcases family_descends (prefixWord ++ tailWord_300645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300648 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 3, 5]
def baseStart_300648 : Nat := 118140960795 + 300648 * 2 ^ 59
def prefixEnd_300648 : Nat := 4983230072969 + 3 ^ 40 * 300648 * 2
def baseEnd_300648 : Nat := 51458977271014982339117

theorem tailTrace_300648 : CollatzResearch.WordTrace tailWord_300648 prefixEnd_300648 51458977271014982339117 := by
  unfold tailWord_300648
  simp only [CollatzResearch.WordTrace]
  refine ⟨5482766707405558717799299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7310355609874078290399065 5482766707405558717799299)
  ·
    refine ⟨8224150061108338076698949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5482766707405558717799299 8224150061108338076698949)
    ·
      refine ⟨1542028136457813389381053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8224150061108338076698949 1542028136457813389381053)
      ·
        refine ⟨578260551171680021017895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1542028136457813389381053 578260551171680021017895)
        ·
          refine ⟨867390826757520031526843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578260551171680021017895 867390826757520031526843)
          ·
            refine ⟨1301086240136280047290265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867390826757520031526843 1301086240136280047290265)
            ·
              refine ⟨975814680102210035467699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301086240136280047290265 975814680102210035467699)
              ·
                refine ⟨1463722020153315053201549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 975814680102210035467699 1463722020153315053201549)
                ·
                  refine ⟨548895757557493144950581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1463722020153315053201549 548895757557493144950581)
                  ·
                    refine ⟨51458977271014982339117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 548895757557493144950581 51458977271014982339117)
                    ·
                      rfl

theorem cell23_300648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_300648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300648 prefixEnd_300648 := by exact prefixLift 300648
  have htrace : WordTrace (prefixWord ++ tailWord_300648) baseStart_300648 baseEnd_300648 := by
    simpa [prefixWord, tailWord_300648, baseEnd_300648] using wordTrace_append hprefix tailTrace_300648
  have hstable : (prefixWord ++ tailWord_300648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300648).length < 2 ^ (prefixWord ++ tailWord_300648).sum := by decide
  have hdescent : baseEnd_300648 < baseStart_300648 := by decide
  rcases family_descends (prefixWord ++ tailWord_300648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300681 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 4]
def baseStart_300681 : Nat := 118140960795 + 300681 * 2 ^ 59
def prefixEnd_300681 : Nat := 4983230072969 + 3 ^ 40 * 300681 * 2
def baseEnd_300681 : Nat := 154393876674643317904699

theorem tailTrace_300681 : CollatzResearch.WordTrace tailWord_300681 prefixEnd_300681 154393876674643317904699 := by
  unfold tailWord_300681
  simp only [CollatzResearch.WordTrace]
  refine ⟨10966737023691564071549897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7311158015794376047699931 10966737023691564071549897)
  ·
    refine ⟨8225052767768673053662423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10966737023691564071549897 8225052767768673053662423)
    ·
      refine ⟨12337579151653009580493635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8225052767768673053662423 12337579151653009580493635)
      ·
        refine ⟨18506368727479514370740453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12337579151653009580493635 18506368727479514370740453)
        ·
          refine ⟨3469944136402408944513835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18506368727479514370740453 3469944136402408944513835)
          ·
            refine ⟨5204916204603613416770753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469944136402408944513835 5204916204603613416770753)
            ·
              refine ⟨3903687153452710062578065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5204916204603613416770753 3903687153452710062578065)
              ·
                refine ⟨2927765365089532546933549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3903687153452710062578065 2927765365089532546933549)
                ·
                  refine ⟨1097912011908574705100081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2927765365089532546933549 1097912011908574705100081)
                  ·
                    refine ⟨823434008931431028825061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1097912011908574705100081 823434008931431028825061)
                    ·
                      refine ⟨154393876674643317904699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 823434008931431028825061 154393876674643317904699)
                      ·
                        rfl

theorem cell23_300681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_300681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300681 prefixEnd_300681 := by exact prefixLift 300681
  have htrace : WordTrace (prefixWord ++ tailWord_300681) baseStart_300681 baseEnd_300681 := by
    simpa [prefixWord, tailWord_300681, baseEnd_300681] using wordTrace_append hprefix tailTrace_300681
  have hstable : (prefixWord ++ tailWord_300681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300681).length < 2 ^ (prefixWord ++ tailWord_300681).sum := by decide
  have hdescent : baseEnd_300681 < baseStart_300681 := by decide
  rcases family_descends (prefixWord ++ tailWord_300681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300702 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_300702 : Nat := 118140960795 + 300702 * 2 ^ 59
def prefixEnd_300702 : Nat := 4983230072969 + 3 ^ 40 * 300702 * 2
def baseEnd_300702 : Nat := 154404659768387735742103

theorem tailTrace_300702 : CollatzResearch.WordTrace tailWord_300702 prefixEnd_300702 154404659768387735742103 := by
  unfold tailWord_300702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370937869576935582258045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7311668637743656438709573 1370937869576935582258045)
  ·
    refine ⟨514101701091350843346767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1370937869576935582258045 514101701091350843346767)
    ·
      refine ⟨771152551637026265020151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 514101701091350843346767 771152551637026265020151)
      ·
        refine ⟨1156728827455539397530227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771152551637026265020151 1156728827455539397530227)
        ·
          refine ⟨1735093241183309096295341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156728827455539397530227 1735093241183309096295341)
          ·
            refine ⟨650659965443740911110753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1735093241183309096295341 650659965443740911110753)
            ·
              refine ⟨487994974082805683333065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650659965443740911110753 487994974082805683333065)
              ·
                refine ⟨365996230562104262499799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 487994974082805683333065 365996230562104262499799)
                ·
                  refine ⟨548994345843156393749699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365996230562104262499799 548994345843156393749699)
                  ·
                    refine ⟨823491518764734590624549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 548994345843156393749699 823491518764734590624549)
                    ·
                      refine ⟨154404659768387735742103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 823491518764734590624549 154404659768387735742103)
                      ·
                        rfl

theorem cell23_300702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_300702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300702 prefixEnd_300702 := by exact prefixLift 300702
  have htrace : WordTrace (prefixWord ++ tailWord_300702) baseStart_300702 baseEnd_300702 := by
    simpa [prefixWord, tailWord_300702, baseEnd_300702] using wordTrace_append hprefix tailTrace_300702
  have hstable : (prefixWord ++ tailWord_300702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300702).length < 2 ^ (prefixWord ++ tailWord_300702).sum := by decide
  have hdescent : baseEnd_300702 < baseStart_300702 := by decide
  rcases family_descends (prefixWord ++ tailWord_300702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300705 : List Nat := [1, 2, 3, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_300705 : Nat := 118140960795 + 300705 * 2 ^ 59
def prefixEnd_300705 : Nat := 4983230072969 + 3 ^ 40 * 300705 * 2
def baseEnd_300705 : Nat := 154406200210351224004589

theorem tailTrace_300705 : CollatzResearch.WordTrace tailWord_300705 prefixEnd_300705 154406200210351224004589 := by
  unfold tailWord_300705
  simp only [CollatzResearch.WordTrace]
  refine ⟨10967612375604616170423569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7311741583736410780282379 10967612375604616170423569)
  ·
    refine ⟨8225709281703462127817677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10967612375604616170423569 8225709281703462127817677)
    ·
      refine ⟨3084640980638798297931629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8225709281703462127817677 3084640980638798297931629)
      ·
        refine ⟨1156740367739549361724361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3084640980638798297931629 1156740367739549361724361)
        ·
          refine ⟨867555275804662021293271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1156740367739549361724361 867555275804662021293271)
          ·
            refine ⟨1301332913706993031939907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867555275804662021293271 1301332913706993031939907)
            ·
              refine ⟨1951999370560489547909861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301332913706993031939907 1951999370560489547909861)
              ·
                refine ⟨365999881980091790233099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1951999370560489547909861 365999881980091790233099)
                ·
                  refine ⟨548999822970137685349649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 365999881980091790233099 548999822970137685349649)
                  ·
                    refine ⟨411749867227603264012237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 548999822970137685349649 411749867227603264012237)
                    ·
                      refine ⟨154406200210351224004589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 411749867227603264012237 154406200210351224004589)
                      ·
                        rfl

theorem cell23_300705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_300705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300705 prefixEnd_300705 := by exact prefixLift 300705
  have htrace : WordTrace (prefixWord ++ tailWord_300705) baseStart_300705 baseEnd_300705 := by
    simpa [prefixWord, tailWord_300705, baseEnd_300705] using wordTrace_append hprefix tailTrace_300705
  have hstable : (prefixWord ++ tailWord_300705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300705).length < 2 ^ (prefixWord ++ tailWord_300705).sum := by decide
  have hdescent : baseEnd_300705 < baseStart_300705 := by decide
  rcases family_descends (prefixWord ++ tailWord_300705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300708 : List Nat := [2, 3, 1, 2, 2, 2, 4, 7]
def baseStart_300708 : Nat := 118140960795 + 300708 * 2 ^ 59
def prefixEnd_300708 : Nat := 4983230072969 + 3 ^ 40 * 300708 * 2
def baseEnd_300708 : Nat := 5718805209344989343225

theorem tailTrace_300708 : CollatzResearch.WordTrace tailWord_300708 prefixEnd_300708 5718805209344989343225 := by
  unfold tailWord_300708
  simp only [CollatzResearch.WordTrace]
  refine ⟨5483860897296873841391389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7311814529729165121855185 5483860897296873841391389)
  ·
    refine ⟨2056447836486327690521771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5483860897296873841391389 2056447836486327690521771)
    ·
      refine ⟨3084671754729491535782657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2056447836486327690521771 3084671754729491535782657)
      ·
        refine ⟨2313503816047118651836993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3084671754729491535782657 2313503816047118651836993)
        ·
          refine ⟨1735127862035338988877745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2313503816047118651836993 1735127862035338988877745)
          ·
            refine ⟨1301345896526504241658309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1735127862035338988877745 1301345896526504241658309)
            ·
              refine ⟨244002355598719545310933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1301345896526504241658309 244002355598719545310933)
              ·
                refine ⟨5718805209344989343225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 244002355598719545310933 5718805209344989343225)
                ·
                  rfl

theorem cell23_300708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 7].length) (baseStart_300708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300708 prefixEnd_300708 := by exact prefixLift 300708
  have htrace : WordTrace (prefixWord ++ tailWord_300708) baseStart_300708 baseEnd_300708 := by
    simpa [prefixWord, tailWord_300708, baseEnd_300708] using wordTrace_append hprefix tailTrace_300708
  have hstable : (prefixWord ++ tailWord_300708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300708).length < 2 ^ (prefixWord ++ tailWord_300708).sum := by decide
  have hdescent : baseEnd_300708 < baseStart_300708 := by decide
  rcases family_descends (prefixWord ++ tailWord_300708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300725 : List Nat := [1, 3, 3, 3, 3, 1, 9]
def baseStart_300725 : Nat := 118140960795 + 300725 * 2 ^ 59
def prefixEnd_300725 : Nat := 4983230072969 + 3 ^ 40 * 300725 * 2
def baseEnd_300725 : Nat := 1906376170659767231537

theorem tailTrace_300725 : CollatzResearch.WordTrace tailWord_300725 prefixEnd_300725 1906376170659767231537 := by
  unfold tailWord_300725
  simp only [CollatzResearch.WordTrace]
  refine ⟨10968341835532159586151629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7312227890354773057434419 10968341835532159586151629)
  ·
    refine ⟨4113128188324559844806861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10968341835532159586151629 4113128188324559844806861)
    ·
      refine ⟨1542423070621709941802573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4113128188324559844806861 1542423070621709941802573)
      ·
        refine ⟨578408651483141228175965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1542423070621709941802573 578408651483141228175965)
        ·
          refine ⟨216903244306177960565987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 578408651483141228175965 216903244306177960565987)
          ·
            refine ⟨325354866459266940848981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216903244306177960565987 325354866459266940848981)
            ·
              refine ⟨1906376170659767231537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 325354866459266940848981 1906376170659767231537)
              ·
                rfl

theorem cell23_300725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 9].length) (baseStart_300725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300725 prefixEnd_300725 := by exact prefixLift 300725
  have htrace : WordTrace (prefixWord ++ tailWord_300725) baseStart_300725 baseEnd_300725 := by
    simpa [prefixWord, tailWord_300725, baseEnd_300725] using wordTrace_append hprefix tailTrace_300725
  have hstable : (prefixWord ++ tailWord_300725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300725).length < 2 ^ (prefixWord ++ tailWord_300725).sum := by decide
  have hdescent : baseEnd_300725 < baseStart_300725 := by decide
  rcases family_descends (prefixWord ++ tailWord_300725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300735 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 2, 1, 3]
def baseStart_300735 : Nat := 118140960795 + 300735 * 2 ^ 59
def prefixEnd_300735 : Nat := 4983230072969 + 3 ^ 40 * 300735 * 2
def baseEnd_300735 : Nat := 154421604629986106629451

theorem tailTrace_300735 : CollatzResearch.WordTrace tailWord_300735 prefixEnd_300735 154421604629986106629451 := by
  unfold tailWord_300735
  simp only [CollatzResearch.WordTrace]
  refine ⟨10968706565495931294015659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7312471043663954196010439 10968706565495931294015659)
  ·
    refine ⟨16453059848243896941023489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10968706565495931294015659 16453059848243896941023489)
    ·
      refine ⟨12339794886182922705767617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16453059848243896941023489 12339794886182922705767617)
      ·
        refine ⟨9254846164637192029325713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12339794886182922705767617 9254846164637192029325713)
        ·
          refine ⟨6941134623477894021994285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9254846164637192029325713 6941134623477894021994285)
          ·
            refine ⟨2602925483804210258247857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6941134623477894021994285 2602925483804210258247857)
            ·
              refine ⟨1952194112853157693685893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2602925483804210258247857 1952194112853157693685893)
              ·
                refine ⟨366036396159967067566105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1952194112853157693685893 366036396159967067566105)
                ·
                  refine ⟨274527297119975300674579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366036396159967067566105 274527297119975300674579)
                  ·
                    refine ⟨411790945679962951011869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274527297119975300674579 411790945679962951011869)
                    ·
                      refine ⟨154421604629986106629451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 411790945679962951011869 154421604629986106629451)
                      ·
                        rfl

theorem cell23_300735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_300735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300735 prefixEnd_300735 := by exact prefixLift 300735
  have htrace : WordTrace (prefixWord ++ tailWord_300735) baseStart_300735 baseEnd_300735 := by
    simpa [prefixWord, tailWord_300735, baseEnd_300735] using wordTrace_append hprefix tailTrace_300735
  have hstable : (prefixWord ++ tailWord_300735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300735).length < 2 ^ (prefixWord ++ tailWord_300735).sum := by decide
  have hdescent : baseEnd_300735 < baseStart_300735 := by decide
  rcases family_descends (prefixWord ++ tailWord_300735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300741 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_300741 : Nat := 118140960795 + 300741 * 2 ^ 59
def prefixEnd_300741 : Nat := 4983230072969 + 3 ^ 40 * 300741 * 2
def baseEnd_300741 : Nat := 154424685513913083154423

theorem tailTrace_300741 : CollatzResearch.WordTrace tailWord_300741 prefixEnd_300741 154424685513913083154423 := by
  unfold tailWord_300741
  simp only [CollatzResearch.WordTrace]
  refine ⟨10968925403474194318734077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7312616935649462879156051 10968925403474194318734077)
  ·
    refine ⟨4113347026302822869525279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10968925403474194318734077 4113347026302822869525279)
    ·
      refine ⟨6170020539454234304287919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4113347026302822869525279 6170020539454234304287919)
      ·
        refine ⟨9255030809181351456431879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6170020539454234304287919 9255030809181351456431879)
        ·
          refine ⟨13882546213772027184647819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9255030809181351456431879 13882546213772027184647819)
          ·
            refine ⟨20823819320658040776971729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13882546213772027184647819 20823819320658040776971729)
            ·
              refine ⟨15617864490493530582728797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20823819320658040776971729 15617864490493530582728797)
              ·
                refine ⟨5856699183935073968523299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15617864490493530582728797 5856699183935073968523299)
                ·
                  refine ⟨8785048775902610952784949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5856699183935073968523299 8785048775902610952784949)
                  ·
                    refine ⟨823598322740869776823589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8785048775902610952784949 823598322740869776823589)
                    ·
                      refine ⟨154424685513913083154423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 823598322740869776823589 154424685513913083154423)
                      ·
                        rfl

theorem cell23_300741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_300741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300741 prefixEnd_300741 := by exact prefixLift 300741
  have htrace : WordTrace (prefixWord ++ tailWord_300741) baseStart_300741 baseEnd_300741 := by
    simpa [prefixWord, tailWord_300741, baseEnd_300741] using wordTrace_append hprefix tailTrace_300741
  have hstable : (prefixWord ++ tailWord_300741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300741).length < 2 ^ (prefixWord ++ tailWord_300741).sum := by decide
  have hdescent : baseEnd_300741 < baseStart_300741 := by decide
  rcases family_descends (prefixWord ++ tailWord_300741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300742 : List Nat := [6, 1, 2, 1, 1, 2, 2, 8]
def baseStart_300742 : Nat := 118140960795 + 300742 * 2 ^ 59
def prefixEnd_300742 : Nat := 4983230072969 + 3 ^ 40 * 300742 * 2
def baseEnd_300742 : Nat := 5719451814613614045997

theorem tailTrace_300742 : CollatzResearch.WordTrace tailWord_300742 prefixEnd_300742 5719451814613614045997 := by
  unfold tailWord_300742
  simp only [CollatzResearch.WordTrace]
  refine ⟨342780058639705359047515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7312641250980380993013653 342780058639705359047515)
  ·
    refine ⟨514170087959558038571273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342780058639705359047515 514170087959558038571273)
    ·
      refine ⟨385627565969668528928455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 514170087959558038571273 385627565969668528928455)
      ·
        refine ⟨578441348954502793392683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 385627565969668528928455 578441348954502793392683)
        ·
          refine ⟨867662023431754190089025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 578441348954502793392683 867662023431754190089025)
          ·
            refine ⟨650746517573815642566769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 867662023431754190089025 650746517573815642566769)
            ·
              refine ⟨488059888180361731925077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650746517573815642566769 488059888180361731925077)
              ·
                refine ⟨5719451814613614045997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 488059888180361731925077 5719451814613614045997)
                ·
                  rfl

theorem cell23_300742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_300742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300742 prefixEnd_300742 := by exact prefixLift 300742
  have htrace : WordTrace (prefixWord ++ tailWord_300742) baseStart_300742 baseEnd_300742 := by
    simpa [prefixWord, tailWord_300742, baseEnd_300742] using wordTrace_append hprefix tailTrace_300742
  have hstable : (prefixWord ++ tailWord_300742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300742).length < 2 ^ (prefixWord ++ tailWord_300742).sum := by decide
  have hdescent : baseEnd_300742 < baseStart_300742 := by decide
  rcases family_descends (prefixWord ++ tailWord_300742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300751 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 2, 6]
def baseStart_300751 : Nat := 118140960795 + 300751 * 2 ^ 59
def prefixEnd_300751 : Nat := 4983230072969 + 3 ^ 40 * 300751 * 2
def baseEnd_300751 : Nat := 51476606773486014676459

theorem tailTrace_300751 : CollatzResearch.WordTrace tailWord_300751 prefixEnd_300751 51476606773486014676459 := by
  unfold tailWord_300751
  simp only [CollatzResearch.WordTrace]
  refine ⟨10969290133437966026598107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7312860088958644017732071 10969290133437966026598107)
  ·
    refine ⟨16453935200156949039897161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10969290133437966026598107 16453935200156949039897161)
    ·
      refine ⟨12340451400117711779922871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16453935200156949039897161 12340451400117711779922871)
      ·
        refine ⟨18510677100176567669884307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12340451400117711779922871 18510677100176567669884307)
        ·
          refine ⟨27766015650264851504826461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18510677100176567669884307 27766015650264851504826461)
          ·
            refine ⟨10412255868849319314309923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27766015650264851504826461 10412255868849319314309923)
            ·
              refine ⟨15618383803273978971464885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10412255868849319314309923 15618383803273978971464885)
              ·
                refine ⟨1464223481556935528574833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15618383803273978971464885 1464223481556935528574833)
                ·
                  refine ⟨1098167611167701646431125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1464223481556935528574833 1098167611167701646431125)
                  ·
                    refine ⟨51476606773486014676459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1098167611167701646431125 51476606773486014676459)
                    ·
                      rfl

theorem cell23_300751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_300751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300751 prefixEnd_300751 := by exact prefixLift 300751
  have htrace : WordTrace (prefixWord ++ tailWord_300751) baseStart_300751 baseEnd_300751 := by
    simpa [prefixWord, tailWord_300751, baseEnd_300751] using wordTrace_append hprefix tailTrace_300751
  have hstable : (prefixWord ++ tailWord_300751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300751).length < 2 ^ (prefixWord ++ tailWord_300751).sum := by decide
  have hdescent : baseEnd_300751 < baseStart_300751 := by decide
  rcases family_descends (prefixWord ++ tailWord_300751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300762 : List Nat := [3, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2]
def baseStart_300762 : Nat := 118140960795 + 300762 * 2 ^ 59
def prefixEnd_300762 : Nat := 4983230072969 + 3 ^ 40 * 300762 * 2
def baseEnd_300762 : Nat := 154435468607657500991827

theorem tailTrace_300762 : CollatzResearch.WordTrace tailWord_300762 prefixEnd_300762 154435468607657500991827 := by
  unfold tailWord_300762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2742422834099528726312135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7313127557598743270165693 2742422834099528726312135)
  ·
    refine ⟨4113634251149293089468203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2742422834099528726312135 4113634251149293089468203)
    ·
      refine ⟨6170451376723939634202305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4113634251149293089468203 6170451376723939634202305)
      ·
        refine ⟨4627838532542954725651729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6170451376723939634202305 4627838532542954725651729)
        ·
          refine ⟨3470878899407216044238797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4627838532542954725651729 3470878899407216044238797)
          ·
            refine ⟨1301579587277706016589549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3470878899407216044238797 1301579587277706016589549)
            ·
              refine ⟨488092345229139756221081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1301579587277706016589549 488092345229139756221081)
              ·
                refine ⟨366069258921854817165811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 488092345229139756221081 366069258921854817165811)
                ·
                  refine ⟨549103888382782225748717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366069258921854817165811 549103888382782225748717)
                  ·
                    refine ⟨205913958143543334655769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549103888382782225748717 205913958143543334655769)
                    ·
                      refine ⟨154435468607657500991827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 205913958143543334655769 154435468607657500991827)
                      ·
                        rfl

theorem cell23_300762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_300762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300762 prefixEnd_300762 := by exact prefixLift 300762
  have htrace : WordTrace (prefixWord ++ tailWord_300762) baseStart_300762 baseEnd_300762 := by
    simpa [prefixWord, tailWord_300762, baseEnd_300762] using wordTrace_append hprefix tailTrace_300762
  have hstable : (prefixWord ++ tailWord_300762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300762).length < 2 ^ (prefixWord ++ tailWord_300762).sum := by decide
  have hdescent : baseEnd_300762 < baseStart_300762 := by decide
  rcases family_descends (prefixWord ++ tailWord_300762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300778 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_300778 : Nat := 118140960795 + 300778 * 2 ^ 59
def prefixEnd_300778 : Nat := 4983230072969 + 3 ^ 40 * 300778 * 2
def baseEnd_300778 : Nat := 154443684298129438391753

theorem tailTrace_300778 : CollatzResearch.WordTrace tailWord_300778 prefixEnd_300778 154443684298129438391753 := by
  unfold tailWord_300778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2742568726085037409457747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7313516602893433091887325 2742568726085037409457747)
  ·
    refine ⟨4113853089127556114186621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2742568726085037409457747 4113853089127556114186621)
    ·
      refine ⟨1542694908422833542819983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4113853089127556114186621 1542694908422833542819983)
      ·
        refine ⟨2314042362634250314229975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542694908422833542819983 2314042362634250314229975)
        ·
          refine ⟨3471063543951375471344963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314042362634250314229975 3471063543951375471344963)
          ·
            refine ⟨5206595315927063207017445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3471063543951375471344963 5206595315927063207017445)
            ·
              refine ⟨976236621736324351315771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5206595315927063207017445 976236621736324351315771)
              ·
                refine ⟨1464354932604486526973657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976236621736324351315771 1464354932604486526973657)
                ·
                  refine ⟨1098266199453364895230243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1464354932604486526973657 1098266199453364895230243)
                  ·
                    refine ⟨1647399299180047342845365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1098266199453364895230243 1647399299180047342845365)
                    ·
                      refine ⟨154443684298129438391753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1647399299180047342845365 154443684298129438391753)
                      ·
                        rfl

theorem cell23_300778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_300778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300778 prefixEnd_300778 := by exact prefixLift 300778
  have htrace : WordTrace (prefixWord ++ tailWord_300778) baseStart_300778 baseEnd_300778 := by
    simpa [prefixWord, tailWord_300778, baseEnd_300778] using wordTrace_append hprefix tailTrace_300778
  have hstable : (prefixWord ++ tailWord_300778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300778).length < 2 ^ (prefixWord ++ tailWord_300778).sum := by decide
  have hdescent : baseEnd_300778 < baseStart_300778 := by decide
  rcases family_descends (prefixWord ++ tailWord_300778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300791 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_300791 : Nat := 118140960795 + 300791 * 2 ^ 59
def prefixEnd_300791 : Nat := 4983230072969 + 3 ^ 40 * 300791 * 2
def baseEnd_300791 : Nat := 154450359546637887529193

theorem tailTrace_300791 : CollatzResearch.WordTrace tailWord_300791 prefixEnd_300791 154450359546637887529193 := by
  unfold tailWord_300791
  simp only [CollatzResearch.WordTrace]
  refine ⟨10970749053293052858054227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7313832702195368572036151 10970749053293052858054227)
  ·
    refine ⟨16456123579939579287081341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10970749053293052858054227 16456123579939579287081341)
    ·
      refine ⟨6171046342477342232655503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16456123579939579287081341 6171046342477342232655503)
      ·
        refine ⟨9256569513716013348983255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6171046342477342232655503 9256569513716013348983255)
        ·
          refine ⟨13884854270574020023474883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9256569513716013348983255 13884854270574020023474883)
          ·
            refine ⟨20827281405861030035212325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13884854270574020023474883 20827281405861030035212325)
            ·
              refine ⟨3905115263598943131602311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20827281405861030035212325 3905115263598943131602311)
              ·
                refine ⟨5857672895398414697403467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3905115263598943131602311 5857672895398414697403467)
                ·
                  refine ⟨8786509343097622046105201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5857672895398414697403467 8786509343097622046105201)
                  ·
                    refine ⟨6589882007323216534578901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8786509343097622046105201 6589882007323216534578901)
                    ·
                      refine ⟨154450359546637887529193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 6589882007323216534578901 154450359546637887529193)
                      ·
                        rfl

theorem cell23_300791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_300791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300791 prefixEnd_300791 := by exact prefixLift 300791
  have htrace : WordTrace (prefixWord ++ tailWord_300791) baseStart_300791 baseEnd_300791 := by
    simpa [prefixWord, tailWord_300791, baseEnd_300791] using wordTrace_append hprefix tailTrace_300791
  have hstable : (prefixWord ++ tailWord_300791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300791).length < 2 ^ (prefixWord ++ tailWord_300791).sum := by decide
  have hdescent : baseEnd_300791 < baseStart_300791 := by decide
  rcases family_descends (prefixWord ++ tailWord_300791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300828 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_300828 : Nat := 118140960795 + 300828 * 2 ^ 59
def prefixEnd_300828 : Nat := 4983230072969 + 3 ^ 40 * 300828 * 2
def baseEnd_300828 : Nat := 51489786110284747588841

theorem tailTrace_300828 : CollatzResearch.WordTrace tailWord_300828 prefixEnd_300828 51489786110284747588841 := by
  unfold tailWord_300828
  simp only [CollatzResearch.WordTrace]
  refine ⟨5486049277079504088575569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7314732369439338784767425 5486049277079504088575569)
  ·
    refine ⟨4114536957809628066431677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5486049277079504088575569 4114536957809628066431677)
    ·
      refine ⟨1542951359178610524911879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4114536957809628066431677 1542951359178610524911879)
      ·
        refine ⟨2314427038767915787367819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542951359178610524911879 2314427038767915787367819)
        ·
          refine ⟨3471640558151873681051729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314427038767915787367819 3471640558151873681051729)
          ·
            refine ⟨2603730418613905260788797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3471640558151873681051729 2603730418613905260788797)
            ·
              refine ⟨976398906980214472795799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2603730418613905260788797 976398906980214472795799)
              ·
                refine ⟨1464598360470321709193699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976398906980214472795799 1464598360470321709193699)
                ·
                  refine ⟨2196897540705482563790549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464598360470321709193699 2196897540705482563790549)
                  ·
                    refine ⟨51489786110284747588841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2196897540705482563790549 51489786110284747588841)
                    ·
                      rfl

theorem cell23_300828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_300828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300828 prefixEnd_300828 := by exact prefixLift 300828
  have htrace : WordTrace (prefixWord ++ tailWord_300828) baseStart_300828 baseEnd_300828 := by
    simpa [prefixWord, tailWord_300828, baseEnd_300828] using wordTrace_append hprefix tailTrace_300828
  have hstable : (prefixWord ++ tailWord_300828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300828).length < 2 ^ (prefixWord ++ tailWord_300828).sum := by decide
  have hdescent : baseEnd_300828 < baseStart_300828 := by decide
  rcases family_descends (prefixWord ++ tailWord_300828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300830 : List Nat := [4, 3, 2, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_300830 : Nat := 118140960795 + 300830 * 2 ^ 59
def prefixEnd_300830 : Nat := 4983230072969 + 3 ^ 40 * 300830 * 2
def baseEnd_300830 : Nat := 154470385292163234941515

theorem tailTrace_300830 : CollatzResearch.WordTrace tailWord_300830 prefixEnd_300830 154470385292163234941515 := by
  unfold tailWord_300830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1371521437518970314840493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7314781000101175012482629 1371521437518970314840493)
  ·
    refine ⟨514320539069613868065185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1371521437518970314840493 514320539069613868065185)
    ·
      refine ⟨385740404302210401048889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 514320539069613868065185 385740404302210401048889)
      ·
        refine ⟨289305303226657800786667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385740404302210401048889 289305303226657800786667)
        ·
          refine ⟨433957954839986701180001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289305303226657800786667 433957954839986701180001)
          ·
            refine ⟨325468466129990025885001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 433957954839986701180001 325468466129990025885001)
            ·
              refine ⟨244101349597492519413751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325468466129990025885001 244101349597492519413751)
              ·
                refine ⟨366152024396238779120627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244101349597492519413751 366152024396238779120627)
                ·
                  refine ⟨549228036594358168680941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366152024396238779120627 549228036594358168680941)
                  ·
                    refine ⟨205960513722884313255353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549228036594358168680941 205960513722884313255353)
                    ·
                      refine ⟨154470385292163234941515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 205960513722884313255353 154470385292163234941515)
                      ·
                        rfl

theorem cell23_300830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_300830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300830 prefixEnd_300830 := by exact prefixLift 300830
  have htrace : WordTrace (prefixWord ++ tailWord_300830) baseStart_300830 baseEnd_300830 := by
    simpa [prefixWord, tailWord_300830, baseEnd_300830] using wordTrace_append hprefix tailTrace_300830
  have hstable : (prefixWord ++ tailWord_300830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300830).length < 2 ^ (prefixWord ++ tailWord_300830).sum := by decide
  have hdescent : baseEnd_300830 < baseStart_300830 := by decide
  rcases family_descends (prefixWord ++ tailWord_300830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300885 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_300885 : Nat := 118140960795 + 300885 * 2 ^ 59
def prefixEnd_300885 : Nat := 4983230072969 + 3 ^ 40 * 300885 * 2
def baseEnd_300885 : Nat := 154498626728160519753761

theorem tailTrace_300885 : CollatzResearch.WordTrace tailWord_300885 prefixEnd_300885 154498626728160519753761 := by
  unfold tailWord_300885
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974177514952506911976109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7316118343301671274650739 10974177514952506911976109)
  ·
    refine ⟨4115316568107190091991041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10974177514952506911976109 4115316568107190091991041)
    ·
      refine ⟨3086487426080392568993281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4115316568107190091991041 3086487426080392568993281)
      ·
        refine ⟨2314865569560294426744961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3086487426080392568993281 2314865569560294426744961)
        ·
          refine ⟨1736149177170220820058721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2314865569560294426744961 1736149177170220820058721)
          ·
            refine ⟨1302111882877665615044041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1736149177170220820058721 1302111882877665615044041)
            ·
              refine ⟨976583912158249211283031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302111882877665615044041 976583912158249211283031)
              ·
                refine ⟨1464875868237373816924547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976583912158249211283031 1464875868237373816924547)
                ·
                  refine ⟨2197313802356060725386821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1464875868237373816924547 2197313802356060725386821)
                  ·
                    refine ⟨411996337941761386010029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2197313802356060725386821 411996337941761386010029)
                    ·
                      refine ⟨154498626728160519753761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 411996337941761386010029 154498626728160519753761)
                      ·
                        rfl

theorem cell23_300885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_300885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300885 prefixEnd_300885 := by exact prefixLift 300885
  have htrace : WordTrace (prefixWord ++ tailWord_300885) baseStart_300885 baseEnd_300885 := by
    simpa [prefixWord, tailWord_300885, baseEnd_300885] using wordTrace_append hprefix tailTrace_300885
  have hstable : (prefixWord ++ tailWord_300885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300885).length < 2 ^ (prefixWord ++ tailWord_300885).sum := by decide
  have hdescent : baseEnd_300885 < baseStart_300885 := by decide
  rcases family_descends (prefixWord ++ tailWord_300885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300932 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_300932 : Nat := 118140960795 + 300932 * 2 ^ 59
def prefixEnd_300932 : Nat := 4983230072969 + 3 ^ 40 * 300932 * 2
def baseEnd_300932 : Nat := 154522760318921835866045

theorem tailTrace_300932 : CollatzResearch.WordTrace tailWord_300932 prefixEnd_300932 154522760318921835866045 := by
  unfold tailWord_300932
  simp only [CollatzResearch.WordTrace]
  refine ⟨5487945872891116969468525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7317261163854822625958033 5487945872891116969468525)
  ·
    refine ⟨2057979702334168863550697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5487945872891116969468525 2057979702334168863550697)
    ·
      refine ⟨1543484776750626647663023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2057979702334168863550697 1543484776750626647663023)
      ·
        refine ⟨2315227165125939971494535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543484776750626647663023 2315227165125939971494535)
        ·
          refine ⟨3472840747688909957241803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2315227165125939971494535 3472840747688909957241803)
          ·
            refine ⟨5209261121533364935862705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3472840747688909957241803 5209261121533364935862705)
            ·
              refine ⟨3906945841150023701897029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5209261121533364935862705 3906945841150023701897029)
              ·
                refine ⟨732552345215629444105693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3906945841150023701897029 732552345215629444105693)
                ·
                  refine ⟨274707129455861041539635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732552345215629444105693 274707129455861041539635)
                  ·
                    refine ⟨412060694183791562309453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274707129455861041539635 412060694183791562309453)
                    ·
                      refine ⟨154522760318921835866045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 412060694183791562309453 154522760318921835866045)
                      ·
                        rfl

theorem cell23_300932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_300932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300932 prefixEnd_300932 := by exact prefixLift 300932
  have htrace : WordTrace (prefixWord ++ tailWord_300932) baseStart_300932 baseEnd_300932 := by
    simpa [prefixWord, tailWord_300932, baseEnd_300932] using wordTrace_append hprefix tailTrace_300932
  have hstable : (prefixWord ++ tailWord_300932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300932).length < 2 ^ (prefixWord ++ tailWord_300932).sum := by decide
  have hdescent : baseEnd_300932 < baseStart_300932 := by decide
  rcases family_descends (prefixWord ++ tailWord_300932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300949 : List Nat := [1, 3, 2, 1, 1, 3, 2, 5, 1, 1, 3]
def baseStart_300949 : Nat := 118140960795 + 300949 * 2 ^ 59
def prefixEnd_300949 : Nat := 4983230072969 + 3 ^ 40 * 300949 * 2
def baseEnd_300949 : Nat := 154531489490048269353467

theorem tailTrace_300949 : CollatzResearch.WordTrace tailWord_300949 prefixEnd_300949 154531489490048269353467 := by
  unfold tailWord_300949
  simp only [CollatzResearch.WordTrace]
  refine ⟨10976511786720645842305901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7317674524480430561537267 10976511786720645842305901)
  ·
    refine ⟨4116191920020242190864713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10976511786720645842305901 4116191920020242190864713)
    ·
      refine ⟨3087143940015181643148535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4116191920020242190864713 3087143940015181643148535)
      ·
        refine ⟨4630715910022772464722803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3087143940015181643148535 4630715910022772464722803)
        ·
          refine ⟨6946073865034158697084205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4630715910022772464722803 6946073865034158697084205)
          ·
            refine ⟨2604777699387809511406577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6946073865034158697084205 2604777699387809511406577)
            ·
              refine ⟨1953583274540857133554933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2604777699387809511406577 1953583274540857133554933)
              ·
                refine ⟨183148431988205356270775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1953583274540857133554933 183148431988205356270775)
                ·
                  refine ⟨274722647982308034406163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183148431988205356270775 274722647982308034406163)
                  ·
                    refine ⟨412083971973462051609245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 274722647982308034406163 412083971973462051609245)
                    ·
                      refine ⟨154531489490048269353467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 412083971973462051609245 154531489490048269353467)
                      ·
                        rfl

theorem cell23_300949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_300949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300949 prefixEnd_300949 := by exact prefixLift 300949
  have htrace : WordTrace (prefixWord ++ tailWord_300949) baseStart_300949 baseEnd_300949 := by
    simpa [prefixWord, tailWord_300949, baseEnd_300949] using wordTrace_append hprefix tailTrace_300949
  have hstable : (prefixWord ++ tailWord_300949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300949).length < 2 ^ (prefixWord ++ tailWord_300949).sum := by decide
  have hdescent : baseEnd_300949 < baseStart_300949 := by decide
  rcases family_descends (prefixWord ++ tailWord_300949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300965 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 4, 4]
def baseStart_300965 : Nat := 118140960795 + 300965 * 2 ^ 59
def prefixEnd_300965 : Nat := 4983230072969 + 3 ^ 40 * 300965 * 2
def baseEnd_300965 : Nat := 51513235060173402251131

theorem tailTrace_300965 : CollatzResearch.WordTrace tailWord_300965 prefixEnd_300965 51513235060173402251131 := by
  unfold tailWord_300965
  simp only [CollatzResearch.WordTrace]
  refine ⟨10977095354662680574888349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7318063569775120383258899 10977095354662680574888349)
  ·
    refine ⟨4116410757998505215583131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10977095354662680574888349 4116410757998505215583131)
    ·
      refine ⟨6174616136997757823374697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4116410757998505215583131 6174616136997757823374697)
      ·
        refine ⟨4630962102748318367531023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6174616136997757823374697 4630962102748318367531023)
        ·
          refine ⟨6946443154122477551296535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4630962102748318367531023 6946443154122477551296535)
          ·
            refine ⟨10419664731183716326944803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6946443154122477551296535 10419664731183716326944803)
            ·
              refine ⟨15629497096775574490417205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10419664731183716326944803 15629497096775574490417205)
              ·
                refine ⟨1465265352822710108476613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15629497096775574490417205 1465265352822710108476613)
                ·
                  refine ⟨274737253654258145339365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1465265352822710108476613 274737253654258145339365)
                  ·
                    refine ⟨51513235060173402251131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 274737253654258145339365 51513235060173402251131)
                    ·
                      rfl

theorem cell23_300965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_300965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300965 prefixEnd_300965 := by exact prefixLift 300965
  have htrace : WordTrace (prefixWord ++ tailWord_300965) baseStart_300965 baseEnd_300965 := by
    simpa [prefixWord, tailWord_300965, baseEnd_300965] using wordTrace_append hprefix tailTrace_300965
  have hstable : (prefixWord ++ tailWord_300965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300965).length < 2 ^ (prefixWord ++ tailWord_300965).sum := by decide
  have hdescent : baseEnd_300965 < baseStart_300965 := by decide
  rcases family_descends (prefixWord ++ tailWord_300965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300975 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 3]
def baseStart_300975 : Nat := 118140960795 + 300975 * 2 ^ 59
def prefixEnd_300975 : Nat := 4983230072969 + 3 ^ 40 * 300975 * 2
def baseEnd_300975 : Nat := 154544839987065167628347

theorem tailTrace_300975 : CollatzResearch.WordTrace tailWord_300975 prefixEnd_300975 154544839987065167628347 := by
  unfold tailWord_300975
  simp only [CollatzResearch.WordTrace]
  refine ⟨10977460084626452282752379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7318306723084301521834919 10977460084626452282752379)
  ·
    refine ⟨16466190126939678424128569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10977460084626452282752379 16466190126939678424128569)
    ·
      refine ⟨12349642595204758818096427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16466190126939678424128569 12349642595204758818096427)
      ·
        refine ⟨18524463892807138227144641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12349642595204758818096427 18524463892807138227144641)
        ·
          refine ⟨13893347919605353670358481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18524463892807138227144641 13893347919605353670358481)
          ·
            refine ⟨10420010939704015252768861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13893347919605353670358481 10420010939704015252768861)
            ·
              refine ⟨3907504102389005719788323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10420010939704015252768861 3907504102389005719788323)
              ·
                refine ⟨5861256153583508579682485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3907504102389005719788323 5861256153583508579682485)
                ·
                  refine ⟨549492764398453929345233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5861256153583508579682485 549492764398453929345233)
                  ·
                    refine ⟨412119573298840447008925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 549492764398453929345233 412119573298840447008925)
                    ·
                      refine ⟨154544839987065167628347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 412119573298840447008925 154544839987065167628347)
                      ·
                        rfl

theorem cell23_300975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 3].length) (baseStart_300975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300975 prefixEnd_300975 := by exact prefixLift 300975
  have htrace : WordTrace (prefixWord ++ tailWord_300975) baseStart_300975 baseEnd_300975 := by
    simpa [prefixWord, tailWord_300975, baseEnd_300975] using wordTrace_append hprefix tailTrace_300975
  have hstable : (prefixWord ++ tailWord_300975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300975).length < 2 ^ (prefixWord ++ tailWord_300975).sum := by decide
  have hdescent : baseEnd_300975 < baseStart_300975 := by decide
  rcases family_descends (prefixWord ++ tailWord_300975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300989 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 5, 2, 2]
def baseStart_300989 : Nat := 118140960795 + 300989 * 2 ^ 59
def prefixEnd_300989 : Nat := 4983230072969 + 3 ^ 40 * 300989 * 2
def baseEnd_300989 : Nat := 154552028716228112853283

theorem tailTrace_300989 : CollatzResearch.WordTrace tailWord_300989 prefixEnd_300989 154552028716228112853283 := by
  unfold tailWord_300989
  simp only [CollatzResearch.WordTrace]
  refine ⟨10977970706575732673762021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7318647137717155115841347 10977970706575732673762021)
  ·
    refine ⟨2058369507482949876330379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10977970706575732673762021 2058369507482949876330379)
    ·
      refine ⟨3087554261224424814495569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2058369507482949876330379 3087554261224424814495569)
      ·
        refine ⟨2315665695918318610871677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3087554261224424814495569 2315665695918318610871677)
        ·
          refine ⟨868374635969369479076879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2315665695918318610871677 868374635969369479076879)
          ·
            refine ⟨1302561953954054218615319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868374635969369479076879 1302561953954054218615319)
            ·
              refine ⟨1953842930931081327922979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1302561953954054218615319 1953842930931081327922979)
              ·
                refine ⟨2930764396396621991884469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1953842930931081327922979 2930764396396621991884469)
                ·
                  refine ⟨274759162162183311739169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2930764396396621991884469 274759162162183311739169)
                  ·
                    refine ⟨206069371621637483804377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 274759162162183311739169 206069371621637483804377)
                    ·
                      refine ⟨154552028716228112853283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 206069371621637483804377 154552028716228112853283)
                      ·
                        rfl

theorem cell23_300989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_300989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300989 prefixEnd_300989 := by exact prefixLift 300989
  have htrace : WordTrace (prefixWord ++ tailWord_300989) baseStart_300989 baseEnd_300989 := by
    simpa [prefixWord, tailWord_300989, baseEnd_300989] using wordTrace_append hprefix tailTrace_300989
  have hstable : (prefixWord ++ tailWord_300989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300989).length < 2 ^ (prefixWord ++ tailWord_300989).sum := by decide
  have hdescent : baseEnd_300989 < baseStart_300989 := by decide
  rcases family_descends (prefixWord ++ tailWord_300989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_300992 : List Nat := [2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 3]
def baseStart_300992 : Nat := 118140960795 + 300992 * 2 ^ 59
def prefixEnd_300992 : Nat := 4983230072969 + 3 ^ 40 * 300992 * 2
def baseEnd_300992 : Nat := 154553569158191601115769

theorem tailTrace_300992 : CollatzResearch.WordTrace tailWord_300992 prefixEnd_300992 154553569158191601115769 := by
  unfold tailWord_300992
  simp only [CollatzResearch.WordTrace]
  refine ⟨5489040062782432093060615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7318720083709909457414153 5489040062782432093060615)
  ·
    refine ⟨8233560094173648139590923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5489040062782432093060615 8233560094173648139590923)
    ·
      refine ⟨12350340141260472209386385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8233560094173648139590923 12350340141260472209386385)
      ·
        refine ⟨9262755105945354157039789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12350340141260472209386385 9262755105945354157039789)
        ·
          refine ⟨3473533164729507808889921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9262755105945354157039789 3473533164729507808889921)
          ·
            refine ⟨2605149873547130856667441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3473533164729507808889921 2605149873547130856667441)
            ·
              refine ⟨1953862405160348142500581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2605149873547130856667441 1953862405160348142500581)
              ·
                refine ⟨366349200967565276718859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1953862405160348142500581 366349200967565276718859)
                ·
                  refine ⟨549523801451347915078289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366349200967565276718859 549523801451347915078289)
                  ·
                    refine ⟨412142851088510936308717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 549523801451347915078289 412142851088510936308717)
                    ·
                      refine ⟨154553569158191601115769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 412142851088510936308717 154553569158191601115769)
                      ·
                        rfl

theorem cell23_300992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 3].length) (baseStart_300992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_300992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_300992 prefixEnd_300992 := by exact prefixLift 300992
  have htrace : WordTrace (prefixWord ++ tailWord_300992) baseStart_300992 baseEnd_300992 := by
    simpa [prefixWord, tailWord_300992, baseEnd_300992] using wordTrace_append hprefix tailTrace_300992
  have hstable : (prefixWord ++ tailWord_300992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_300992).length < 2 ^ (prefixWord ++ tailWord_300992).sum := by decide
  have hdescent : baseEnd_300992 < baseStart_300992 := by decide
  rcases family_descends (prefixWord ++ tailWord_300992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301046 : List Nat := [5, 1, 1, 1, 5, 1, 2, 7]
def baseStart_301046 : Nat := 118140960795 + 301046 * 2 ^ 59
def prefixEnd_301046 : Nat := 4983230072969 + 3 ^ 40 * 301046 * 2
def baseEnd_301046 : Nat := 5725233226427199623723

theorem tailTrace_301046 : CollatzResearch.WordTrace tailWord_301046 prefixEnd_301046 5725233226427199623723 := by
  unfold tailWord_301046
  simp only [CollatzResearch.WordTrace]
  refine ⟨686253104210576963036687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7320033111579487605724661 686253104210576963036687)
  ·
    refine ⟨1029379656315865444555031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 686253104210576963036687 1029379656315865444555031)
    ·
      refine ⟨1544069484473798166832547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029379656315865444555031 1544069484473798166832547)
      ·
        refine ⟨2316104226710697250248821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544069484473798166832547 2316104226710697250248821)
        ·
          refine ⟨217134771254127867210827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2316104226710697250248821 217134771254127867210827)
          ·
            refine ⟨325702156881191800816241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217134771254127867210827 325702156881191800816241)
            ·
              refine ⟨244276617660893850612181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325702156881191800816241 244276617660893850612181)
              ·
                refine ⟨5725233226427199623723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 244276617660893850612181 5725233226427199623723)
                ·
                  rfl

theorem cell23_301046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_301046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301046 prefixEnd_301046 := by exact prefixLift 301046
  have htrace : WordTrace (prefixWord ++ tailWord_301046) baseStart_301046 baseEnd_301046 := by
    simpa [prefixWord, tailWord_301046, baseEnd_301046] using wordTrace_append hprefix tailTrace_301046
  have hstable : (prefixWord ++ tailWord_301046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301046).length < 2 ^ (prefixWord ++ tailWord_301046).sum := by decide
  have hdescent : baseEnd_301046 < baseStart_301046 := by decide
  rcases family_descends (prefixWord ++ tailWord_301046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301049 : List Nat := [1, 2, 1, 3, 1, 4, 1, 4, 1, 3, 2]
def baseStart_301049 : Nat := 118140960795 + 301049 * 2 ^ 59
def prefixEnd_301049 : Nat := 4983230072969 + 3 ^ 40 * 301049 * 2
def baseEnd_301049 : Nat := 154582837555497878103007

theorem tailTrace_301049 : CollatzResearch.WordTrace tailWord_301049 prefixEnd_301049 154582837555497878103007 := by
  unfold tailWord_301049
  simp only [CollatzResearch.WordTrace]
  refine ⟨10980159086358362920946201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7320106057572241947297467 10980159086358362920946201)
  ·
    refine ⟨8235119314768772190709651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10980159086358362920946201 8235119314768772190709651)
    ·
      refine ⟨12352678972153158286064477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8235119314768772190709651 12352678972153158286064477)
      ·
        refine ⟨4632254614557434357274179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12352678972153158286064477 4632254614557434357274179)
        ·
          refine ⟨6948381921836151535911269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4632254614557434357274179 6948381921836151535911269)
          ·
            refine ⟨1302821610344278412983363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6948381921836151535911269 1302821610344278412983363)
            ·
              refine ⟨1954232415516417619475045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1302821610344278412983363 1954232415516417619475045)
              ·
                refine ⟨366418577909328303651571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1954232415516417619475045 366418577909328303651571)
                ·
                  refine ⟨549627866863992455477357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366418577909328303651571 549627866863992455477357)
                  ·
                    refine ⟨206110450073997170804009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 549627866863992455477357 206110450073997170804009)
                    ·
                      refine ⟨154582837555497878103007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 206110450073997170804009 154582837555497878103007)
                      ·
                        rfl

theorem cell23_301049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_301049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301049 prefixEnd_301049 := by exact prefixLift 301049
  have htrace : WordTrace (prefixWord ++ tailWord_301049) baseStart_301049 baseEnd_301049 := by
    simpa [prefixWord, tailWord_301049, baseEnd_301049] using wordTrace_append hprefix tailTrace_301049
  have hstable : (prefixWord ++ tailWord_301049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301049).length < 2 ^ (prefixWord ++ tailWord_301049).sum := by decide
  have hdescent : baseEnd_301049 < baseStart_301049 := by decide
  rcases family_descends (prefixWord ++ tailWord_301049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301065 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 3, 6, 3]
def baseStart_301065 : Nat := 118140960795 + 301065 * 2 ^ 59
def prefixEnd_301065 : Nat := 4983230072969 + 3 ^ 40 * 301065 * 2
def baseEnd_301065 : Nat := 154591053245969815502933

theorem tailTrace_301065 : CollatzResearch.WordTrace tailWord_301065 prefixEnd_301065 154591053245969815502933 := by
  unfold tailWord_301065
  simp only [CollatzResearch.WordTrace]
  refine ⟨10980742654300397653528649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7320495102866931769019099 10980742654300397653528649)
  ·
    refine ⟨8235556990725298240146487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10980742654300397653528649 8235556990725298240146487)
    ·
      refine ⟨12353335486087947360219731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8235556990725298240146487 12353335486087947360219731)
      ·
        refine ⟨18530003229131921040329597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12353335486087947360219731 18530003229131921040329597)
        ·
          refine ⟨6948751210924470390123599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18530003229131921040329597 6948751210924470390123599)
          ·
            refine ⟨10423126816386705585185399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6948751210924470390123599 10423126816386705585185399)
            ·
              refine ⟨15634690224580058377778099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10423126816386705585185399 15634690224580058377778099)
              ·
                refine ⟨23452035336870087566667149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15634690224580058377778099 23452035336870087566667149)
                ·
                  refine ⟨8794513251326282837500181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23452035336870087566667149 8794513251326282837500181)
                  ·
                    refine ⟨412242808655919508007821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8794513251326282837500181 412242808655919508007821)
                    ·
                      refine ⟨154591053245969815502933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 412242808655919508007821 154591053245969815502933)
                      ·
                        rfl

theorem cell23_301065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6, 3].length) (baseStart_301065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301065 prefixEnd_301065 := by exact prefixLift 301065
  have htrace : WordTrace (prefixWord ++ tailWord_301065) baseStart_301065 baseEnd_301065 := by
    simpa [prefixWord, tailWord_301065, baseEnd_301065] using wordTrace_append hprefix tailTrace_301065
  have hstable : (prefixWord ++ tailWord_301065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301065).length < 2 ^ (prefixWord ++ tailWord_301065).sum := by decide
  have hdescent : baseEnd_301065 < baseStart_301065 := by decide
  rcases family_descends (prefixWord ++ tailWord_301065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301075 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 4]
def baseStart_301075 : Nat := 118140960795 + 301075 * 2 ^ 59
def prefixEnd_301075 : Nat := 4983230072969 + 3 ^ 40 * 301075 * 2
def baseEnd_301075 : Nat := 154596188052514776377887

theorem tailTrace_301075 : CollatzResearch.WordTrace tailWord_301075 prefixEnd_301075 154596188052514776377887 := by
  unfold tailWord_301075
  simp only [CollatzResearch.WordTrace]
  refine ⟨10981107384264169361392679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7320738256176112907595119 10981107384264169361392679)
  ·
    refine ⟨16471661076396254042089019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10981107384264169361392679 16471661076396254042089019)
    ·
      refine ⟨24707491614594381063133529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16471661076396254042089019 24707491614594381063133529)
      ·
        refine ⟨18530618710945785797350147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24707491614594381063133529 18530618710945785797350147)
        ·
          refine ⟨27795928066418678696025221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18530618710945785797350147 27795928066418678696025221)
          ·
            refine ⟨5211736512453502255504729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27795928066418678696025221 5211736512453502255504729)
            ·
              refine ⟨3908802384340126691628547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5211736512453502255504729 3908802384340126691628547)
              ·
                refine ⟨5863203576510190037442821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3908802384340126691628547 5863203576510190037442821)
                ·
                  refine ⟨1099350670595660632020529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5863203576510190037442821 1099350670595660632020529)
                  ·
                    refine ⟨824513002946745474015397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1099350670595660632020529 824513002946745474015397)
                    ·
                      refine ⟨154596188052514776377887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 824513002946745474015397 154596188052514776377887)
                      ·
                        rfl

theorem cell23_301075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_301075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301075 prefixEnd_301075 := by exact prefixLift 301075
  have htrace : WordTrace (prefixWord ++ tailWord_301075) baseStart_301075 baseEnd_301075 := by
    simpa [prefixWord, tailWord_301075, baseEnd_301075] using wordTrace_append hprefix tailTrace_301075
  have hstable : (prefixWord ++ tailWord_301075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301075).length < 2 ^ (prefixWord ++ tailWord_301075).sum := by decide
  have hdescent : baseEnd_301075 < baseStart_301075 := by decide
  rcases family_descends (prefixWord ++ tailWord_301075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301115 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 6, 5]
def baseStart_301115 : Nat := 118140960795 + 301115 * 2 ^ 59
def prefixEnd_301115 : Nat := 4983230072969 + 3 ^ 40 * 301115 * 2
def baseEnd_301115 : Nat := 51538909092898206625901

theorem tailTrace_301115 : CollatzResearch.WordTrace tailWord_301115 prefixEnd_301115 51538909092898206625901 := by
  unfold tailWord_301115
  simp only [CollatzResearch.WordTrace]
  refine ⟨10982566304119256192848799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7321710869412837461899199 10982566304119256192848799)
  ·
    refine ⟨16473849456178884289273199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10982566304119256192848799 16473849456178884289273199)
    ·
      refine ⟨24710774184268326433909799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16473849456178884289273199 24710774184268326433909799)
      ·
        refine ⟨37066161276402489650864699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24710774184268326433909799 37066161276402489650864699)
        ·
          refine ⟨55599241914603734476297049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37066161276402489650864699 55599241914603734476297049)
          ·
            refine ⟨41699431435952800857222787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55599241914603734476297049 41699431435952800857222787)
            ·
              refine ⟨62549147153929201285834181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41699431435952800857222787 62549147153929201285834181)
              ·
                refine ⟨11727965091361725241093909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62549147153929201285834181 11727965091361725241093909)
                ·
                  refine ⟨549748363657580870676277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 11727965091361725241093909 549748363657580870676277)
                  ·
                    refine ⟨51538909092898206625901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 549748363657580870676277 51538909092898206625901)
                    ·
                      rfl

theorem cell23_301115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 5].length) (baseStart_301115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301115 prefixEnd_301115 := by exact prefixLift 301115
  have htrace : WordTrace (prefixWord ++ tailWord_301115) baseStart_301115 baseEnd_301115 := by
    simpa [prefixWord, tailWord_301115, baseEnd_301115] using wordTrace_append hprefix tailTrace_301115
  have hstable : (prefixWord ++ tailWord_301115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301115).length < 2 ^ (prefixWord ++ tailWord_301115).sum := by decide
  have hdescent : baseEnd_301115 < baseStart_301115 := by decide
  rcases family_descends (prefixWord ++ tailWord_301115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301132 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_301132 : Nat := 118140960795 + 301132 * 2 ^ 59
def prefixEnd_301132 : Nat := 4983230072969 + 3 ^ 40 * 301132 * 2
def baseEnd_301132 : Nat := 51541818816607017788375

theorem tailTrace_301132 : CollatzResearch.WordTrace tailWord_301132 prefixEnd_301132 51541818816607017788375 := by
  unfold tailWord_301132
  simp only [CollatzResearch.WordTrace]
  refine ⟨5491593172528834048108825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7322124230038445397478433 5491593172528834048108825)
  ·
    refine ⟨4118694879396625536081619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5491593172528834048108825 4118694879396625536081619)
    ·
      refine ⟨6178042319094938304122429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4118694879396625536081619 6178042319094938304122429)
      ·
        refine ⟨2316765869660601864045911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6178042319094938304122429 2316765869660601864045911)
        ·
          refine ⟨3475148804490902796068867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316765869660601864045911 3475148804490902796068867)
          ·
            refine ⟨5212723206736354194103301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475148804490902796068867 5212723206736354194103301)
            ·
              refine ⟨977385601263066411394369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5212723206736354194103301 977385601263066411394369)
              ·
                refine ⟨733039200947299808545777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977385601263066411394369 733039200947299808545777)
                ·
                  refine ⟨549779400710474856409333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 733039200947299808545777 549779400710474856409333)
                  ·
                    refine ⟨51541818816607017788375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 549779400710474856409333 51541818816607017788375)
                    ·
                      rfl

theorem cell23_301132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_301132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301132 prefixEnd_301132 := by exact prefixLift 301132
  have htrace : WordTrace (prefixWord ++ tailWord_301132) baseStart_301132 baseEnd_301132 := by
    simpa [prefixWord, tailWord_301132, baseEnd_301132] using wordTrace_append hprefix tailTrace_301132
  have hstable : (prefixWord ++ tailWord_301132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301132).length < 2 ^ (prefixWord ++ tailWord_301132).sum := by decide
  have hdescent : baseEnd_301132 < baseStart_301132 := by decide
  rcases family_descends (prefixWord ++ tailWord_301132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301212 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_301212 : Nat := 118140960795 + 301212 * 2 ^ 59
def prefixEnd_301212 : Nat := 4983230072969 + 3 ^ 40 * 301212 * 2
def baseEnd_301212 : Nat := 154666534902180740364757

theorem tailTrace_301212 : CollatzResearch.WordTrace tailWord_301212 prefixEnd_301212 154666534902180740364757 := by
  unfold tailWord_301212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5493052092383920879564945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7324069456511894506086593 5493052092383920879564945)
  ·
    refine ⟨4119789069287940659673709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5493052092383920879564945 4119789069287940659673709)
    ·
      refine ⟨1544920900982977747377641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4119789069287940659673709 1544920900982977747377641)
      ·
        refine ⟨1158690675737233310533231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1544920900982977747377641 1158690675737233310533231)
        ·
          refine ⟨1738036013605849965799847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158690675737233310533231 1738036013605849965799847)
          ·
            refine ⟨2607054020408774948699771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738036013605849965799847 2607054020408774948699771)
            ·
              refine ⟨3910581030613162423049657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2607054020408774948699771 3910581030613162423049657)
              ·
                refine ⟨2932935772959871817287243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3910581030613162423049657 2932935772959871817287243)
                ·
                  refine ⟨4399403659439807725930865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2932935772959871817287243 4399403659439807725930865)
                  ·
                    refine ⟨3299552744579855794448149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4399403659439807725930865 3299552744579855794448149)
                    ·
                      refine ⟨154666534902180740364757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3299552744579855794448149 154666534902180740364757)
                      ·
                        rfl

theorem cell23_301212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_301212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301212 prefixEnd_301212 := by exact prefixLift 301212
  have htrace : WordTrace (prefixWord ++ tailWord_301212) baseStart_301212 baseEnd_301212 := by
    simpa [prefixWord, tailWord_301212, baseEnd_301212] using wordTrace_append hprefix tailTrace_301212
  have hstable : (prefixWord ++ tailWord_301212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301212).length < 2 ^ (prefixWord ++ tailWord_301212).sum := by decide
  have hdescent : baseEnd_301212 < baseStart_301212 := by decide
  rcases family_descends (prefixWord ++ tailWord_301212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301239 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 1, 5]
def baseStart_301239 : Nat := 118140960795 + 301239 * 2 ^ 59
def prefixEnd_301239 : Nat := 4983230072969 + 3 ^ 40 * 301239 * 2
def baseEnd_301239 : Nat := 51560132959950711575711

theorem tailTrace_301239 : CollatzResearch.WordTrace tailWord_301239 prefixEnd_301239 51560132959950711575711 := by
  unfold tailWord_301239
  simp only [CollatzResearch.WordTrace]
  refine ⟨10987088955670025370362771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7324725970446683580241847 10987088955670025370362771)
  ·
    refine ⟨16480633433505038055544157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10987088955670025370362771 16480633433505038055544157)
    ·
      refine ⟨6180237537564389270829059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16480633433505038055544157 6180237537564389270829059)
      ·
        refine ⟨9270356306346583906243589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6180237537564389270829059 9270356306346583906243589)
        ·
          refine ⟨1738191807439984482420673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9270356306346583906243589 1738191807439984482420673)
          ·
            refine ⟨1303643855579988361815505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1738191807439984482420673 1303643855579988361815505)
            ·
              refine ⟨977732891684991271361629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1303643855579988361815505 977732891684991271361629)
              ·
                refine ⟨366649834381871726760611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 977732891684991271361629 366649834381871726760611)
                ·
                  refine ⟨549974751572807590140917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 366649834381871726760611 549974751572807590140917)
                  ·
                    refine ⟨51560132959950711575711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 549974751572807590140917 51560132959950711575711)
                    ·
                      rfl

theorem cell23_301239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_301239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301239 prefixEnd_301239 := by exact prefixLift 301239
  have htrace : WordTrace (prefixWord ++ tailWord_301239) baseStart_301239 baseEnd_301239 := by
    simpa [prefixWord, tailWord_301239, baseEnd_301239] using wordTrace_append hprefix tailTrace_301239
  have hstable : (prefixWord ++ tailWord_301239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301239).length < 2 ^ (prefixWord ++ tailWord_301239).sum := by decide
  have hdescent : baseEnd_301239 < baseStart_301239 := by decide
  rcases family_descends (prefixWord ++ tailWord_301239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301260 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 6]
def baseStart_301260 : Nat := 118140960795 + 301260 * 2 ^ 59
def prefixEnd_301260 : Nat := 4983230072969 + 3 ^ 40 * 301260 * 2
def baseEnd_301260 : Nat := 17187909108177394729393

theorem tailTrace_301260 : CollatzResearch.WordTrace tailWord_301260 prefixEnd_301260 17187909108177394729393 := by
  unfold tailWord_301260
  simp only [CollatzResearch.WordTrace]
  refine ⟨5493927444296972978438617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7325236592395963971251489 5493927444296972978438617)
  ·
    refine ⟨4120445583222729733828963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5493927444296972978438617 4120445583222729733828963)
    ·
      refine ⟨6180668374834094600743445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4120445583222729733828963 6180668374834094600743445)
      ·
        refine ⟨289718830070348184409849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6180668374834094600743445 289718830070348184409849)
        ·
          refine ⟨217289122552761138307387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289718830070348184409849 217289122552761138307387)
          ·
            refine ⟨325933683829141707461081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217289122552761138307387 325933683829141707461081)
            ·
              refine ⟨244450262871856280595811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325933683829141707461081 244450262871856280595811)
              ·
                refine ⟨366675394307784420893717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244450262871856280595811 366675394307784420893717)
                ·
                  refine ⟨17187909108177394729393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 366675394307784420893717 17187909108177394729393)
                  ·
                    rfl

theorem cell23_301260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 6].length) (baseStart_301260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301260 prefixEnd_301260 := by exact prefixLift 301260
  have htrace : WordTrace (prefixWord ++ tailWord_301260) baseStart_301260 baseEnd_301260 := by
    simpa [prefixWord, tailWord_301260, baseEnd_301260] using wordTrace_append hprefix tailTrace_301260
  have hstable : (prefixWord ++ tailWord_301260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301260).length < 2 ^ (prefixWord ++ tailWord_301260).sum := by decide
  have hdescent : baseEnd_301260 < baseStart_301260 := by decide
  rcases family_descends (prefixWord ++ tailWord_301260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301312 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 2, 7]
def baseStart_301312 : Nat := 118140960795 + 301312 * 2 ^ 59
def prefixEnd_301312 : Nat := 4983230072969 + 3 ^ 40 * 301312 * 2
def baseEnd_301312 : Nat := 51572627655876783038099

theorem tailTrace_301312 : CollatzResearch.WordTrace tailWord_301312 prefixEnd_301312 51572627655876783038099 := by
  unfold tailWord_301312
  simp only [CollatzResearch.WordTrace]
  refine ⟨5494875742202779418885095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7326500989603705891846793 5494875742202779418885095)
  ·
    refine ⟨8242313613304169128327643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5494875742202779418885095 8242313613304169128327643)
    ·
      refine ⟨12363470419956253692491465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8242313613304169128327643 12363470419956253692491465)
      ·
        refine ⟨9272602814967190269368599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12363470419956253692491465 9272602814967190269368599)
        ·
          refine ⟨13908904222450785404052899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9272602814967190269368599 13908904222450785404052899)
          ·
            refine ⟨20863356333676178106079349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13908904222450785404052899 20863356333676178106079349)
            ·
              refine ⟨1955939656282141697444939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20863356333676178106079349 1955939656282141697444939)
              ·
                refine ⟨2933909484423212546167409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955939656282141697444939 2933909484423212546167409)
                ·
                  refine ⟨2200432113317409409625557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2933909484423212546167409 2200432113317409409625557)
                  ·
                    refine ⟨51572627655876783038099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2200432113317409409625557 51572627655876783038099)
                    ·
                      rfl

theorem cell23_301312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_301312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301312 prefixEnd_301312 := by exact prefixLift 301312
  have htrace : WordTrace (prefixWord ++ tailWord_301312) baseStart_301312 baseEnd_301312 := by
    simpa [prefixWord, tailWord_301312, baseEnd_301312] using wordTrace_append hprefix tailTrace_301312
  have hstable : (prefixWord ++ tailWord_301312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301312).length < 2 ^ (prefixWord ++ tailWord_301312).sum := by decide
  have hdescent : baseEnd_301312 < baseStart_301312 := by decide
  rcases family_descends (prefixWord ++ tailWord_301312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301316 : List Nat := [2, 3, 2, 2, 3, 2, 1, 8]
def baseStart_301316 : Nat := 118140960795 + 301316 * 2 ^ 59
def prefixEnd_301316 : Nat := 4983230072969 + 3 ^ 40 * 301316 * 2
def baseEnd_301316 : Nat := 5730368032972160498677

theorem tailTrace_301316 : CollatzResearch.WordTrace tailWord_301316 prefixEnd_301316 5730368032972160498677 := by
  unfold tailWord_301316
  simp only [CollatzResearch.WordTrace]
  refine ⟨5494948688195533760457901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7326598250927378347277201 5494948688195533760457901)
  ·
    refine ⟨2060605758073325160171713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5494948688195533760457901 2060605758073325160171713)
    ·
      refine ⟨1545454318554993870128785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2060605758073325160171713 1545454318554993870128785)
      ·
        refine ⟨1159090738916245402596589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1545454318554993870128785 1159090738916245402596589)
        ·
          refine ⟨434659027093592025973721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1159090738916245402596589 434659027093592025973721)
          ·
            refine ⟨325994270320194019480291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434659027093592025973721 325994270320194019480291)
            ·
              refine ⟨488991405480291029220437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325994270320194019480291 488991405480291029220437)
              ·
                refine ⟨5730368032972160498677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 488991405480291029220437 5730368032972160498677)
                ·
                  rfl

theorem cell23_301316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 8].length) (baseStart_301316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301316 prefixEnd_301316 := by exact prefixLift 301316
  have htrace : WordTrace (prefixWord ++ tailWord_301316) baseStart_301316 baseEnd_301316 := by
    simpa [prefixWord, tailWord_301316, baseEnd_301316] using wordTrace_append hprefix tailTrace_301316
  have hstable : (prefixWord ++ tailWord_301316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301316).length < 2 ^ (prefixWord ++ tailWord_301316).sum := by decide
  have hdescent : baseEnd_301316 < baseStart_301316 := by decide
  rcases family_descends (prefixWord ++ tailWord_301316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301326 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_301326 : Nat := 118140960795 + 301326 * 2 ^ 59
def prefixEnd_301326 : Nat := 4983230072969 + 3 ^ 40 * 301326 * 2
def baseEnd_301326 : Nat := 154725071696793294339233

theorem tailTrace_301326 : CollatzResearch.WordTrace tailWord_301326 prefixEnd_301326 154725071696793294339233 := by
  unfold tailWord_301326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373782763294354903597479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7326841404236559485853221 1373782763294354903597479)
  ·
    refine ⟨2060674144941532355396219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1373782763294354903597479 2060674144941532355396219)
    ·
      refine ⟨3091011217412298533094329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2060674144941532355396219 3091011217412298533094329)
      ·
        refine ⟨2318258413059223899820747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3091011217412298533094329 2318258413059223899820747)
        ·
          refine ⟨3477387619588835849731121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318258413059223899820747 3477387619588835849731121)
          ·
            refine ⟨2608040714691626887298341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3477387619588835849731121 2608040714691626887298341)
            ·
              refine ⟨489007634004680041368439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2608040714691626887298341 489007634004680041368439)
              ·
                refine ⟨733511451007020062052659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489007634004680041368439 733511451007020062052659)
                ·
                  refine ⟨1100267176510530093078989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 733511451007020062052659 1100267176510530093078989)
                  ·
                    refine ⟨412600191191448784904621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1100267176510530093078989 412600191191448784904621)
                    ·
                      refine ⟨154725071696793294339233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 412600191191448784904621 154725071696793294339233)
                      ·
                        rfl

theorem cell23_301326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_301326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301326 prefixEnd_301326 := by exact prefixLift 301326
  have htrace : WordTrace (prefixWord ++ tailWord_301326) baseStart_301326 baseEnd_301326 := by
    simpa [prefixWord, tailWord_301326, baseEnd_301326] using wordTrace_append hprefix tailTrace_301326
  have hstable : (prefixWord ++ tailWord_301326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301326).length < 2 ^ (prefixWord ++ tailWord_301326).sum := by decide
  have hdescent : baseEnd_301326 < baseStart_301326 := by decide
  rcases family_descends (prefixWord ++ tailWord_301326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301336 : List Nat := [2, 1, 2, 3, 1, 2, 1, 3, 3, 3, 2]
def baseStart_301336 : Nat := 118140960795 + 301336 * 2 ^ 59
def prefixEnd_301336 : Nat := 4983230072969 + 3 ^ 40 * 301336 * 2
def baseEnd_301336 : Nat := 154730206503338255214187

theorem tailTrace_301336 : CollatzResearch.WordTrace tailWord_301336 prefixEnd_301336 154730206503338255214187 := by
  unfold tailWord_301336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5495313418159305468321931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7327084557545740624429241 5495313418159305468321931)
  ·
    refine ⟨8242970127238958202482897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5495313418159305468321931 8242970127238958202482897)
    ·
      refine ⟨6182227595429218651862173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8242970127238958202482897 6182227595429218651862173)
      ·
        refine ⟨2318335348285956994448315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6182227595429218651862173 2318335348285956994448315)
        ·
          refine ⟨3477503022428935491672473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318335348285956994448315 3477503022428935491672473)
          ·
            refine ⟨2608127266821701618754355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3477503022428935491672473 2608127266821701618754355)
            ·
              refine ⟨3912190900232552428131533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2608127266821701618754355 3912190900232552428131533)
              ·
                refine ⟨1467071587587207160549325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3912190900232552428131533 1467071587587207160549325)
                ·
                  refine ⟨550151845345202685205997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1467071587587207160549325 550151845345202685205997)
                  ·
                    refine ⟨206306942004451006952249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 550151845345202685205997 206306942004451006952249)
                    ·
                      refine ⟨154730206503338255214187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 206306942004451006952249 154730206503338255214187)
                      ·
                        rfl

theorem cell23_301336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 3, 3, 2].length) (baseStart_301336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301336 prefixEnd_301336 := by exact prefixLift 301336
  have htrace : WordTrace (prefixWord ++ tailWord_301336) baseStart_301336 baseEnd_301336 := by
    simpa [prefixWord, tailWord_301336, baseEnd_301336] using wordTrace_append hprefix tailTrace_301336
  have hstable : (prefixWord ++ tailWord_301336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301336).length < 2 ^ (prefixWord ++ tailWord_301336).sum := by decide
  have hdescent : baseEnd_301336 < baseStart_301336 := by decide
  rcases family_descends (prefixWord ++ tailWord_301336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301377 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_301377 : Nat := 118140960795 + 301377 * 2 ^ 59
def prefixEnd_301377 : Nat := 4983230072969 + 3 ^ 40 * 301377 * 2
def baseEnd_301377 : Nat := 154751259210172594801499

theorem tailTrace_301377 : CollatzResearch.WordTrace tailWord_301377 prefixEnd_301377 154751259210172594801499 := by
  unfold tailWord_301377
  simp only [CollatzResearch.WordTrace]
  refine ⟨10992122229170074938886385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7328081486113383292590923 10992122229170074938886385)
  ·
    refine ⟨8244091671877556204164789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10992122229170074938886385 8244091671877556204164789)
    ·
      refine ⟨772883594238520894140449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8244091671877556204164789 772883594238520894140449)
      ·
        refine ⟨579662695678890670605337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 772883594238520894140449 579662695678890670605337)
        ·
          refine ⟨434747021759168002954003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 579662695678890670605337 434747021759168002954003)
          ·
            refine ⟨652120532638752004431005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434747021759168002954003 652120532638752004431005)
            ·
              refine ⟨244545199739532001661627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 652120532638752004431005 244545199739532001661627)
              ·
                refine ⟨366817799609298002492441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244545199739532001661627 366817799609298002492441)
                ·
                  refine ⟨275113349706973501869331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366817799609298002492441 275113349706973501869331)
                  ·
                    refine ⟨412670024560460252803997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 275113349706973501869331 412670024560460252803997)
                    ·
                      refine ⟨154751259210172594801499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 412670024560460252803997 154751259210172594801499)
                      ·
                        rfl

theorem cell23_301377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_301377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301377 prefixEnd_301377 := by exact prefixLift 301377
  have htrace : WordTrace (prefixWord ++ tailWord_301377) baseStart_301377 baseEnd_301377 := by
    simpa [prefixWord, tailWord_301377, baseEnd_301377] using wordTrace_append hprefix tailTrace_301377
  have hstable : (prefixWord ++ tailWord_301377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301377).length < 2 ^ (prefixWord ++ tailWord_301377).sum := by decide
  have hdescent : baseEnd_301377 < baseStart_301377 := by decide
  rcases family_descends (prefixWord ++ tailWord_301377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301379 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 4]
def baseStart_301379 : Nat := 118140960795 + 301379 * 2 ^ 59
def prefixEnd_301379 : Nat := 4983230072969 + 3 ^ 40 * 301379 * 2
def baseEnd_301379 : Nat := 154752286171481586976489

theorem tailTrace_301379 : CollatzResearch.WordTrace tailWord_301379 prefixEnd_301379 154752286171481586976489 := by
  unfold tailWord_301379
  simp only [CollatzResearch.WordTrace]
  refine ⟨10992195175162829280459191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7328130116775219520306127 10992195175162829280459191)
  ·
    refine ⟨16488292762744243920688787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10992195175162829280459191 16488292762744243920688787)
    ·
      refine ⟨24732439144116365881033181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16488292762744243920688787 24732439144116365881033181)
      ·
        refine ⟨9274664679043637205387443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24732439144116365881033181 9274664679043637205387443)
        ·
          refine ⟨13911997018565455808081165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9274664679043637205387443 13911997018565455808081165)
          ·
            refine ⟨5216998881962045928030437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13911997018565455808081165 5216998881962045928030437)
            ·
              refine ⟨978187290367883611505707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5216998881962045928030437 978187290367883611505707)
              ·
                refine ⟨1467280935551825417258561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978187290367883611505707 1467280935551825417258561)
                ·
                  refine ⟨1100460701663869062943921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1467280935551825417258561 1100460701663869062943921)
                  ·
                    refine ⟨825345526247901797207941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1100460701663869062943921 825345526247901797207941)
                    ·
                      refine ⟨154752286171481586976489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 825345526247901797207941 154752286171481586976489)
                      ·
                        rfl

theorem cell23_301379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_301379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301379 prefixEnd_301379 := by exact prefixLift 301379
  have htrace : WordTrace (prefixWord ++ tailWord_301379) baseStart_301379 baseEnd_301379 := by
    simpa [prefixWord, tailWord_301379, baseEnd_301379] using wordTrace_append hprefix tailTrace_301379
  have hstable : (prefixWord ++ tailWord_301379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301379).length < 2 ^ (prefixWord ++ tailWord_301379).sum := by decide
  have hdescent : baseEnd_301379 < baseStart_301379 := by decide
  rcases family_descends (prefixWord ++ tailWord_301379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301419 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 2, 5]
def baseStart_301419 : Nat := 118140960795 + 301419 * 2 ^ 59
def prefixEnd_301419 : Nat := 4983230072969 + 3 ^ 40 * 301419 * 2
def baseEnd_301419 : Nat := 51590941799220476825435

theorem tailTrace_301419 : CollatzResearch.WordTrace tailWord_301419 prefixEnd_301419 51590941799220476825435 := by
  unfold tailWord_301419
  simp only [CollatzResearch.WordTrace]
  refine ⟨10993654095017916111915311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7329102730011944074610207 10993654095017916111915311)
  ·
    refine ⟨16490481142526874167872967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10993654095017916111915311 16490481142526874167872967)
    ·
      refine ⟨24735721713790311251809451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16490481142526874167872967 24735721713790311251809451)
      ·
        refine ⟨37103582570685466877714177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24735721713790311251809451 37103582570685466877714177)
        ·
          refine ⟨27827686928014100158285633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37103582570685466877714177 27827686928014100158285633)
          ·
            refine ⟨20870765196010575118714225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27827686928014100158285633 20870765196010575118714225)
            ·
              refine ⟨15653073897007931339035669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20870765196010575118714225 15653073897007931339035669)
              ·
                refine ⟨733737838922246781517297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15653073897007931339035669 733737838922246781517297)
                ·
                  refine ⟨550303379191685086137973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 733737838922246781517297 550303379191685086137973)
                  ·
                    refine ⟨51590941799220476825435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 550303379191685086137973 51590941799220476825435)
                    ·
                      rfl

theorem cell23_301419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 5].length) (baseStart_301419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301419 prefixEnd_301419 := by exact prefixLift 301419
  have htrace : WordTrace (prefixWord ++ tailWord_301419) baseStart_301419 baseEnd_301419 := by
    simpa [prefixWord, tailWord_301419, baseEnd_301419] using wordTrace_append hprefix tailTrace_301419
  have hstable : (prefixWord ++ tailWord_301419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301419).length < 2 ^ (prefixWord ++ tailWord_301419).sum := by decide
  have hdescent : baseEnd_301419 < baseStart_301419 := by decide
  rcases family_descends (prefixWord ++ tailWord_301419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301519 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_301519 : Nat := 118140960795 + 301519 * 2 ^ 59
def prefixEnd_301519 : Nat := 4983230072969 + 3 ^ 40 * 301519 * 2
def baseEnd_301519 : Nat := 154824173463111039225845

theorem tailTrace_301519 : CollatzResearch.WordTrace tailWord_301519 prefixEnd_301519 154824173463111039225845 := by
  unfold tailWord_301519
  simp only [CollatzResearch.WordTrace]
  refine ⟨10997301394655633190555611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7331534263103755460370407 10997301394655633190555611)
  ·
    refine ⟨16495952091983449785833417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10997301394655633190555611 16495952091983449785833417)
    ·
      refine ⟨12371964068987587339375063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16495952091983449785833417 12371964068987587339375063)
      ·
        refine ⟨18557946103481381009062595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12371964068987587339375063 18557946103481381009062595)
        ·
          refine ⟨27836919155222071513593893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18557946103481381009062595 27836919155222071513593893)
          ·
            refine ⟨5219422341604138408798855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27836919155222071513593893 5219422341604138408798855)
            ·
              refine ⟨7829133512406207613198283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5219422341604138408798855 7829133512406207613198283)
              ·
                refine ⟨11743700268609311419797425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7829133512406207613198283 11743700268609311419797425)
                ·
                  refine ⟨8807775201456983564848069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11743700268609311419797425 8807775201456983564848069)
                  ·
                    refine ⟨1651457850273184418409013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8807775201456983564848069 1651457850273184418409013)
                    ·
                      refine ⟨154824173463111039225845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1651457850273184418409013 154824173463111039225845)
                      ·
                        rfl

theorem cell23_301519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_301519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301519 prefixEnd_301519 := by exact prefixLift 301519
  have htrace : WordTrace (prefixWord ++ tailWord_301519) baseStart_301519 baseEnd_301519 := by
    simpa [prefixWord, tailWord_301519, baseEnd_301519] using wordTrace_append hprefix tailTrace_301519
  have hstable : (prefixWord ++ tailWord_301519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301519).length < 2 ^ (prefixWord ++ tailWord_301519).sum := by decide
  have hdescent : baseEnd_301519 < baseStart_301519 := by decide
  rcases family_descends (prefixWord ++ tailWord_301519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301576 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_301576 : Nat := 118140960795 + 301576 * 2 ^ 59
def prefixEnd_301576 : Nat := 4983230072969 + 3 ^ 40 * 301576 * 2
def baseEnd_301576 : Nat := 154853441860417316213083

theorem tailTrace_301576 : CollatzResearch.WordTrace tailWord_301576 prefixEnd_301576 154853441860417316213083 := by
  unfold tailWord_301576
  simp only [CollatzResearch.WordTrace]
  refine ⟨5499690177724565962690291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7332920236966087950253721 5499690177724565962690291)
  ·
    refine ⟨8249535266586848944035437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5499690177724565962690291 8249535266586848944035437)
    ·
      refine ⟨3093575724970068354013289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8249535266586848944035437 3093575724970068354013289)
      ·
        refine ⟨2320181793727551265509967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3093575724970068354013289 2320181793727551265509967)
        ·
          refine ⟨3480272690591326898264951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2320181793727551265509967 3480272690591326898264951)
          ·
            refine ⟨5220409035886990347397427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480272690591326898264951 5220409035886990347397427)
            ·
              refine ⟨7830613553830485521096141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5220409035886990347397427 7830613553830485521096141)
              ·
                refine ⟨2936480082686432070411053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7830613553830485521096141 2936480082686432070411053)
                ·
                  refine ⟨1101180031007412026404145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2936480082686432070411053 1101180031007412026404145)
                  ·
                    refine ⟨825885023255559019803109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1101180031007412026404145 825885023255559019803109)
                    ·
                      refine ⟨154853441860417316213083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 825885023255559019803109 154853441860417316213083)
                      ·
                        rfl

theorem cell23_301576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_301576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301576 prefixEnd_301576 := by exact prefixLift 301576
  have htrace : WordTrace (prefixWord ++ tailWord_301576) baseStart_301576 baseEnd_301576 := by
    simpa [prefixWord, tailWord_301576, baseEnd_301576] using wordTrace_append hprefix tailTrace_301576
  have hstable : (prefixWord ++ tailWord_301576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301576).length < 2 ^ (prefixWord ++ tailWord_301576).sum := by decide
  have hdescent : baseEnd_301576 < baseStart_301576 := by decide
  rcases family_descends (prefixWord ++ tailWord_301576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301591 : List Nat := [1, 1, 3, 6, 1, 1, 3, 2, 1, 1, 3]
def baseStart_301591 : Nat := 118140960795 + 301591 * 2 ^ 59
def prefixEnd_301591 : Nat := 4983230072969 + 3 ^ 40 * 301591 * 2
def baseEnd_301591 : Nat := 154861144070234757525515

theorem tailTrace_301591 : CollatzResearch.WordTrace tailWord_301591 prefixEnd_301591 154861144070234757525515 := by
  unfold tailWord_301591
  simp only [CollatzResearch.WordTrace]
  refine ⟨10999927450394789487176627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7333284966929859658117751 10999927450394789487176627)
  ·
    refine ⟨16499891175592184230764941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10999927450394789487176627 16499891175592184230764941)
    ·
      refine ⟨6187459190847069086536853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16499891175592184230764941 6187459190847069086536853)
      ·
        refine ⟨290037149570956363431415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6187459190847069086536853 290037149570956363431415)
        ·
          refine ⟨435055724356434545147123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290037149570956363431415 435055724356434545147123)
          ·
            refine ⟨652583586534651817720685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435055724356434545147123 652583586534651817720685)
            ·
              refine ⟨244718844950494431645257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 652583586534651817720685 244718844950494431645257)
              ·
                refine ⟨183539133712870823733943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244718844950494431645257 183539133712870823733943)
                ·
                  refine ⟨275308700569306235600915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183539133712870823733943 275308700569306235600915)
                  ·
                    refine ⟨412963050853959353401373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 275308700569306235600915 412963050853959353401373)
                    ·
                      refine ⟨154861144070234757525515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 412963050853959353401373 154861144070234757525515)
                      ·
                        rfl

theorem cell23_301591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_301591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301591 prefixEnd_301591 := by exact prefixLift 301591
  have htrace : WordTrace (prefixWord ++ tailWord_301591) baseStart_301591 baseEnd_301591 := by
    simpa [prefixWord, tailWord_301591, baseEnd_301591] using wordTrace_append hprefix tailTrace_301591
  have hstable : (prefixWord ++ tailWord_301591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301591).length < 2 ^ (prefixWord ++ tailWord_301591).sum := by decide
  have hdescent : baseEnd_301591 < baseStart_301591 := by decide
  rcases family_descends (prefixWord ++ tailWord_301591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301597 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_301597 : Nat := 118140960795 + 301597 * 2 ^ 59
def prefixEnd_301597 : Nat := 4983230072969 + 3 ^ 40 * 301597 * 2
def baseEnd_301597 : Nat := 154864224954161734050487

theorem tailTrace_301597 : CollatzResearch.WordTrace tailWord_301597 prefixEnd_301597 154864224954161734050487 := by
  unfold tailWord_301597
  simp only [CollatzResearch.WordTrace]
  refine ⟨11000146288373052511895045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7333430858915368341263363 11000146288373052511895045)
  ·
    refine ⟨2062527429069947345980321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11000146288373052511895045 2062527429069947345980321)
    ·
      refine ⟨1546895571802460509485241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2062527429069947345980321 1546895571802460509485241)
      ·
        refine ⟨1160171678851845382113931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1546895571802460509485241 1160171678851845382113931)
        ·
          refine ⟨1740257518277768073170897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160171678851845382113931 1740257518277768073170897)
          ·
            refine ⟨1305193138708326054878173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1740257518277768073170897 1305193138708326054878173)
            ·
              refine ⟨489447427015622270579315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1305193138708326054878173 489447427015622270579315)
              ·
                refine ⟨734171140523433405868973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489447427015622270579315 734171140523433405868973)
                ·
                  refine ⟨275314177696287527200865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 734171140523433405868973 275314177696287527200865)
                  ·
                    refine ⟨206485633272215645400649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 275314177696287527200865 206485633272215645400649)
                    ·
                      refine ⟨154864224954161734050487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 206485633272215645400649 154864224954161734050487)
                      ·
                        rfl

theorem cell23_301597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_301597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301597 prefixEnd_301597 := by exact prefixLift 301597
  have htrace : WordTrace (prefixWord ++ tailWord_301597) baseStart_301597 baseEnd_301597 := by
    simpa [prefixWord, tailWord_301597, baseEnd_301597] using wordTrace_append hprefix tailTrace_301597
  have hstable : (prefixWord ++ tailWord_301597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301597).length < 2 ^ (prefixWord ++ tailWord_301597).sum := by decide
  have hdescent : baseEnd_301597 < baseStart_301597 := by decide
  rcases family_descends (prefixWord ++ tailWord_301597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301614 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_301614 : Nat := 118140960795 + 301614 * 2 ^ 59
def prefixEnd_301614 : Nat := 4983230072969 + 3 ^ 40 * 301614 * 2
def baseEnd_301614 : Nat := 154872954125288167537909

theorem tailTrace_301614 : CollatzResearch.WordTrace tailWord_301614 prefixEnd_301614 154872954125288167537909 := by
  unfold tailWord_301614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1375095791163933051907987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7333844219540976276842597 1375095791163933051907987)
  ·
    refine ⟨2062643686745899577861981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1375095791163933051907987 2062643686745899577861981)
    ·
      refine ⟨773491382529712341698243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2062643686745899577861981 773491382529712341698243)
      ·
        refine ⟨1160237073794568512547365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773491382529712341698243 1160237073794568512547365)
        ·
          refine ⟨217544451336481596102631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1160237073794568512547365 217544451336481596102631)
          ·
            refine ⟨326316677004722394153947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217544451336481596102631 326316677004722394153947)
            ·
              refine ⟨489475015507083591230921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326316677004722394153947 489475015507083591230921)
              ·
                refine ⟨367106261630312693423191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489475015507083591230921 367106261630312693423191)
                ·
                  refine ⟨550659392445469040134787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367106261630312693423191 550659392445469040134787)
                  ·
                    refine ⟨825989088668203560202181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 550659392445469040134787 825989088668203560202181)
                    ·
                      refine ⟨154872954125288167537909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 825989088668203560202181 154872954125288167537909)
                      ·
                        rfl

theorem cell23_301614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_301614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301614 prefixEnd_301614 := by exact prefixLift 301614
  have htrace : WordTrace (prefixWord ++ tailWord_301614) baseStart_301614 baseEnd_301614 := by
    simpa [prefixWord, tailWord_301614, baseEnd_301614] using wordTrace_append hprefix tailTrace_301614
  have hstable : (prefixWord ++ tailWord_301614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301614).length < 2 ^ (prefixWord ++ tailWord_301614).sum := by decide
  have hdescent : baseEnd_301614 < baseStart_301614 := by decide
  rcases family_descends (prefixWord ++ tailWord_301614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301640 : List Nat := [2, 1, 3, 1, 1, 1, 1, 7, 1, 3, 2]
def baseStart_301640 : Nat := 118140960795 + 301640 * 2 ^ 59
def prefixEnd_301640 : Nat := 4983230072969 + 3 ^ 40 * 301640 * 2
def baseEnd_301640 : Nat := 154886304622305065812789

theorem tailTrace_301640 : CollatzResearch.WordTrace tailWord_301640 prefixEnd_301640 154886304622305065812789 := by
  unfold tailWord_301640
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500857313608635427855187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7334476418144847237140249 5500857313608635427855187)
  ·
    refine ⟨8251285970412953141782781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5500857313608635427855187 8251285970412953141782781)
    ·
      refine ⟨3094232238904857428168543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8251285970412953141782781 3094232238904857428168543)
      ·
        refine ⟨4641348358357286142252815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3094232238904857428168543 4641348358357286142252815)
        ·
          refine ⟨6962022537535929213379223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641348358357286142252815 6962022537535929213379223)
          ·
            refine ⟨10443033806303893820068835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6962022537535929213379223 10443033806303893820068835)
            ·
              refine ⟨15664550709455840730103253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10443033806303893820068835 15664550709455840730103253)
              ·
                refine ⟨367137907252871267111795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15664550709455840730103253 367137907252871267111795)
                ·
                  refine ⟨550706860879306900667693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 367137907252871267111795 550706860879306900667693)
                  ·
                    refine ⟨206515072829740087750385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 550706860879306900667693 206515072829740087750385)
                    ·
                      refine ⟨154886304622305065812789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 206515072829740087750385 154886304622305065812789)
                      ·
                        rfl

theorem cell23_301640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_301640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301640 prefixEnd_301640 := by exact prefixLift 301640
  have htrace : WordTrace (prefixWord ++ tailWord_301640) baseStart_301640 baseEnd_301640 := by
    simpa [prefixWord, tailWord_301640, baseEnd_301640] using wordTrace_append hprefix tailTrace_301640
  have hstable : (prefixWord ++ tailWord_301640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301640).length < 2 ^ (prefixWord ++ tailWord_301640).sum := by decide
  have hdescent : baseEnd_301640 < baseStart_301640 := by decide
  rcases family_descends (prefixWord ++ tailWord_301640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301656 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_301656 : Nat := 118140960795 + 301656 * 2 ^ 59
def prefixEnd_301656 : Nat := 4983230072969 + 3 ^ 40 * 301656 * 2
def baseEnd_301656 : Nat := 154894520312777003212715

theorem tailTrace_301656 : CollatzResearch.WordTrace tailWord_301656 prefixEnd_301656 154894520312777003212715 := by
  unfold tailWord_301656
  simp only [CollatzResearch.WordTrace]
  refine ⟨5501149097579652794146411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7334865463439537058861881 5501149097579652794146411)
  ·
    refine ⟨8251723646369479191219617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5501149097579652794146411 8251723646369479191219617)
    ·
      refine ⟨6188792734777109393414713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8251723646369479191219617 6188792734777109393414713)
      ·
        refine ⟨4641594551082832045061035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6188792734777109393414713 4641594551082832045061035)
        ·
          refine ⟨6962391826624248067591553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641594551082832045061035 6962391826624248067591553)
          ·
            refine ⟨5221793869968186050693665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6962391826624248067591553 5221793869968186050693665)
            ·
              refine ⟨3916345402476139538020249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5221793869968186050693665 3916345402476139538020249)
              ·
                refine ⟨2937259051857104653515187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3916345402476139538020249 2937259051857104653515187)
                ·
                  refine ⟨4405888577785656980272781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2937259051857104653515187 4405888577785656980272781)
                  ·
                    refine ⟨1652208216669621367602293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4405888577785656980272781 1652208216669621367602293)
                    ·
                      refine ⟨154894520312777003212715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1652208216669621367602293 154894520312777003212715)
                      ·
                        rfl

theorem cell23_301656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_301656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301656 prefixEnd_301656 := by exact prefixLift 301656
  have htrace : WordTrace (prefixWord ++ tailWord_301656) baseStart_301656 baseEnd_301656 := by
    simpa [prefixWord, tailWord_301656, baseEnd_301656] using wordTrace_append hprefix tailTrace_301656
  have hstable : (prefixWord ++ tailWord_301656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301656).length < 2 ^ (prefixWord ++ tailWord_301656).sum := by decide
  have hdescent : baseEnd_301656 < baseStart_301656 := by decide
  rcases family_descends (prefixWord ++ tailWord_301656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301676 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 9]
def baseStart_301676 : Nat := 118140960795 + 301676 * 2 ^ 59
def prefixEnd_301676 : Nat := 4983230072969 + 3 ^ 40 * 301676 * 2
def baseEnd_301676 : Nat := 17211643325096324995847

theorem tailTrace_301676 : CollatzResearch.WordTrace tailWord_301676 prefixEnd_301676 17211643325096324995847 := by
  unfold tailWord_301676
  simp only [CollatzResearch.WordTrace]
  refine ⟨5501513827543424502010441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7335351770057899336013921 5501513827543424502010441)
  ·
    refine ⟨4126135370657568376507831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5501513827543424502010441 4126135370657568376507831)
    ·
      refine ⟨6189203055986352564761747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4126135370657568376507831 6189203055986352564761747)
      ·
        refine ⟨9283804583979528847142621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6189203055986352564761747 9283804583979528847142621)
        ·
          refine ⟨3481426718992323317678483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9283804583979528847142621 3481426718992323317678483)
          ·
            refine ⟨5222140078488484976517725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3481426718992323317678483 5222140078488484976517725)
            ·
              refine ⟨1958302529433181866194147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5222140078488484976517725 1958302529433181866194147)
              ·
                refine ⟨2937453794149772799291221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958302529433181866194147 2937453794149772799291221)
                ·
                  refine ⟨17211643325096324995847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2937453794149772799291221 17211643325096324995847)
                  ·
                    rfl

theorem cell23_301676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_301676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301676 prefixEnd_301676 := by exact prefixLift 301676
  have htrace : WordTrace (prefixWord ++ tailWord_301676) baseStart_301676 baseEnd_301676 := by
    simpa [prefixWord, tailWord_301676, baseEnd_301676] using wordTrace_append hprefix tailTrace_301676
  have hstable : (prefixWord ++ tailWord_301676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301676).length < 2 ^ (prefixWord ++ tailWord_301676).sum := by decide
  have hdescent : baseEnd_301676 < baseStart_301676 := by decide
  rcases family_descends (prefixWord ++ tailWord_301676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301703 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_301703 : Nat := 118140960795 + 301703 * 2 ^ 59
def prefixEnd_301703 : Nat := 4983230072969 + 3 ^ 40 * 301703 * 2
def baseEnd_301703 : Nat := 154918653903538319324999

theorem tailTrace_301703 : CollatzResearch.WordTrace tailWord_301703 prefixEnd_301703 154918653903538319324999 := by
  unfold tailWord_301703
  simp only [CollatzResearch.WordTrace]
  refine ⟨11004012425989032615253763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7336008283992688410169175 11004012425989032615253763)
  ·
    refine ⟨16506018638983548922880645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11004012425989032615253763 16506018638983548922880645)
    ·
      refine ⟨3094878494809415423040121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16506018638983548922880645 3094878494809415423040121)
      ·
        refine ⟨2321158871107061567280091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3094878494809415423040121 2321158871107061567280091)
        ·
          refine ⟨3481738306660592350920137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2321158871107061567280091 3481738306660592350920137)
          ·
            refine ⟨2611303729995444263190103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3481738306660592350920137 2611303729995444263190103)
            ·
              refine ⟨3916955594993166394785155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2611303729995444263190103 3916955594993166394785155)
              ·
                refine ⟨5875433392489749592177733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3916955594993166394785155 5875433392489749592177733)
                ·
                  refine ⟨1101643761091828048533325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5875433392489749592177733 1101643761091828048533325)
                  ·
                    refine ⟨413116410409435518199997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1101643761091828048533325 413116410409435518199997)
                    ·
                      refine ⟨154918653903538319324999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 413116410409435518199997 154918653903538319324999)
                      ·
                        rfl

theorem cell23_301703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_301703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301703 prefixEnd_301703 := by exact prefixLift 301703
  have htrace : WordTrace (prefixWord ++ tailWord_301703) baseStart_301703 baseEnd_301703 := by
    simpa [prefixWord, tailWord_301703, baseEnd_301703] using wordTrace_append hprefix tailTrace_301703
  have hstable : (prefixWord ++ tailWord_301703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301703).length < 2 ^ (prefixWord ++ tailWord_301703).sum := by decide
  have hdescent : baseEnd_301703 < baseStart_301703 := by decide
  rcases family_descends (prefixWord ++ tailWord_301703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301710 : List Nat := [4, 1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_301710 : Nat := 118140960795 + 301710 * 2 ^ 59
def prefixEnd_301710 : Nat := 4983230072969 + 3 ^ 40 * 301710 * 2
def baseEnd_301710 : Nat := 17213583140902199104163

theorem tailTrace_301710 : CollatzResearch.WordTrace tailWord_301710 prefixEnd_301710 17213583140902199104163 := by
  unfold tailWord_301710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1375533467120459101344823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7336178491309115207172389 1375533467120459101344823)
  ·
    refine ⟨2063300200680688652017235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1375533467120459101344823 2063300200680688652017235)
    ·
      refine ⟨3094950301021032978025853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2063300200680688652017235 3094950301021032978025853)
      ·
        refine ⟨1160606362882887366759695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3094950301021032978025853 1160606362882887366759695)
        ·
          refine ⟨1740909544324331050139543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160606362882887366759695 1740909544324331050139543)
          ·
            refine ⟨2611364316486496575209315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740909544324331050139543 2611364316486496575209315)
            ·
              refine ⟨3917046474729744862813973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2611364316486496575209315 3917046474729744862813973)
              ·
                refine ⟨183611553502956790444405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3917046474729744862813973 183611553502956790444405)
                ·
                  refine ⟨17213583140902199104163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183611553502956790444405 17213583140902199104163)
                  ·
                    rfl

theorem cell23_301710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_301710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301710 prefixEnd_301710 := by exact prefixLift 301710
  have htrace : WordTrace (prefixWord ++ tailWord_301710) baseStart_301710 baseEnd_301710 := by
    simpa [prefixWord, tailWord_301710, baseEnd_301710] using wordTrace_append hprefix tailTrace_301710
  have hstable : (prefixWord ++ tailWord_301710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301710).length < 2 ^ (prefixWord ++ tailWord_301710).sum := by decide
  have hdescent : baseEnd_301710 < baseStart_301710 := by decide
  rcases family_descends (prefixWord ++ tailWord_301710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301743 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 4]
def baseStart_301743 : Nat := 118140960795 + 301743 * 2 ^ 59
def prefixEnd_301743 : Nat := 4983230072969 + 3 ^ 40 * 301743 * 2
def baseEnd_301743 : Nat := 154939193129718162824815

theorem tailTrace_301743 : CollatzResearch.WordTrace tailWord_301743 prefixEnd_301743 154939193129718162824815 := by
  unfold tailWord_301743
  simp only [CollatzResearch.WordTrace]
  refine ⟨11005471345844119446709883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7336980897229412964473255 11005471345844119446709883)
  ·
    refine ⟨16508207018766179170064825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11005471345844119446709883 16508207018766179170064825)
    ·
      refine ⟨12381155264074634377548619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16508207018766179170064825 12381155264074634377548619)
      ·
        refine ⟨18571732896111951566322929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12381155264074634377548619 18571732896111951566322929)
        ·
          refine ⟨13928799672083963674742197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18571732896111951566322929 13928799672083963674742197)
          ·
            refine ⟨1305824969257871594507081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13928799672083963674742197 1305824969257871594507081)
            ·
              refine ⟨979368726943403695880311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1305824969257871594507081 979368726943403695880311)
              ·
                refine ⟨1469053090415105543820467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979368726943403695880311 1469053090415105543820467)
                ·
                  refine ⟨2203579635622658315730701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1469053090415105543820467 2203579635622658315730701)
                  ·
                    refine ⟨826342363358496868399013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2203579635622658315730701 826342363358496868399013)
                    ·
                      refine ⟨154939193129718162824815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 826342363358496868399013 154939193129718162824815)
                      ·
                        rfl

theorem cell23_301743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_301743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301743 prefixEnd_301743 := by exact prefixLift 301743
  have htrace : WordTrace (prefixWord ++ tailWord_301743) baseStart_301743 baseEnd_301743 := by
    simpa [prefixWord, tailWord_301743, baseEnd_301743] using wordTrace_append hprefix tailTrace_301743
  have hstable : (prefixWord ++ tailWord_301743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301743).length < 2 ^ (prefixWord ++ tailWord_301743).sum := by decide
  have hdescent : baseEnd_301743 < baseStart_301743 := by decide
  rcases family_descends (prefixWord ++ tailWord_301743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301760 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 4]
def baseStart_301760 : Nat := 118140960795 + 301760 * 2 ^ 59
def prefixEnd_301760 : Nat := 4983230072969 + 3 ^ 40 * 301760 * 2
def baseEnd_301760 : Nat := 154947922300844596312237

theorem tailTrace_301760 : CollatzResearch.WordTrace tailWord_301760 prefixEnd_301760 154947922300844596312237 := by
  unfold tailWord_301760
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503045693391265675039367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7337394257855020900052489 5503045693391265675039367)
  ·
    refine ⟨8254568540086898512559051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5503045693391265675039367 8254568540086898512559051)
    ·
      refine ⟨12381852810130347768838577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8254568540086898512559051 12381852810130347768838577)
      ·
        refine ⟨9286389607597760826628933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12381852810130347768838577 9286389607597760826628933)
        ·
          refine ⟨1741198051424580154992925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9286389607597760826628933 1741198051424580154992925)
          ·
            refine ⟨652949269284217558122347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1741198051424580154992925 652949269284217558122347)
            ·
              refine ⟨979423903926326337183521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 652949269284217558122347 979423903926326337183521)
              ·
                refine ⟨734567927944744752887641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 979423903926326337183521 734567927944744752887641)
                ·
                  refine ⟨550925945958558564665731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 734567927944744752887641 550925945958558564665731)
                  ·
                    refine ⟨826388918937837846998597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 550925945958558564665731 826388918937837846998597)
                    ·
                      refine ⟨154947922300844596312237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 826388918937837846998597 154947922300844596312237)
                      ·
                        rfl

theorem cell23_301760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_301760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301760 prefixEnd_301760 := by exact prefixLift 301760
  have htrace : WordTrace (prefixWord ++ tailWord_301760) baseStart_301760 baseEnd_301760 := by
    simpa [prefixWord, tailWord_301760, baseEnd_301760] using wordTrace_append hprefix tailTrace_301760
  have hstable : (prefixWord ++ tailWord_301760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301760).length < 2 ^ (prefixWord ++ tailWord_301760).sum := by decide
  have hdescent : baseEnd_301760 < baseStart_301760 := by decide
  rcases family_descends (prefixWord ++ tailWord_301760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301761 : List Nat := [1, 2, 6, 2, 1, 1, 3, 2, 5]
def baseStart_301761 : Nat := 118140960795 + 301761 * 2 ^ 59
def prefixEnd_301761 : Nat := 4983230072969 + 3 ^ 40 * 301761 * 2
def baseEnd_301761 : Nat := 17216492864611010266637

theorem tailTrace_301761 : CollatzResearch.WordTrace tailWord_301761 prefixEnd_301761 17216492864611010266637 := by
  unfold tailWord_301761
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006127859778908520865137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7337418573185939013910091 11006127859778908520865137)
  ·
    refine ⟨8254595894834181390648853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11006127859778908520865137 8254595894834181390648853)
    ·
      refine ⟨386934182570352252686665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8254595894834181390648853 386934182570352252686665)
      ·
        refine ⟨290200636927764189514999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386934182570352252686665 290200636927764189514999)
        ·
          refine ⟨435300955391646284272499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290200636927764189514999 435300955391646284272499)
          ·
            refine ⟨652951433087469426408749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435300955391646284272499 652951433087469426408749)
            ·
              refine ⟨244856787407801034903281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 652951433087469426408749 244856787407801034903281)
              ·
                refine ⟨183642590555850776177461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244856787407801034903281 183642590555850776177461)
                ·
                  refine ⟨17216492864611010266637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183642590555850776177461 17216492864611010266637)
                  ·
                    rfl

theorem cell23_301761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 5].length) (baseStart_301761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301761 prefixEnd_301761 := by exact prefixLift 301761
  have htrace : WordTrace (prefixWord ++ tailWord_301761) baseStart_301761 baseEnd_301761 := by
    simpa [prefixWord, tailWord_301761, baseEnd_301761] using wordTrace_append hprefix tailTrace_301761
  have hstable : (prefixWord ++ tailWord_301761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301761).length < 2 ^ (prefixWord ++ tailWord_301761).sum := by decide
  have hdescent : baseEnd_301761 < baseStart_301761 := by decide
  rcases family_descends (prefixWord ++ tailWord_301761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301797 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 2, 2, 3]
def baseStart_301797 : Nat := 118140960795 + 301797 * 2 ^ 59
def prefixEnd_301797 : Nat := 4983230072969 + 3 ^ 40 * 301797 * 2
def baseEnd_301797 : Nat := 154966921085060951549567

theorem tailTrace_301797 : CollatzResearch.WordTrace tailWord_301797 prefixEnd_301797 154966921085060951549567 := by
  unfold tailWord_301797
  simp only [CollatzResearch.WordTrace]
  refine ⟨11007440887648486669175645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7338293925098991112783763 11007440887648486669175645)
  ·
    refine ⟨4127790332868182500940867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11007440887648486669175645 4127790332868182500940867)
    ·
      refine ⟨6191685499302273751411301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4127790332868182500940867 6191685499302273751411301)
      ·
        refine ⟨1160941031119176328389619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6191685499302273751411301 1160941031119176328389619)
        ·
          refine ⟨1741411546678764492584429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160941031119176328389619 1741411546678764492584429)
          ·
            refine ⟨653029330004536684719161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1741411546678764492584429 653029330004536684719161)
            ·
              refine ⟨489771997503402513539371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 653029330004536684719161 489771997503402513539371)
              ·
                refine ⟨734657996255103770309057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489771997503402513539371 734657996255103770309057)
                ·
                  refine ⟨550993497191327827731793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 734657996255103770309057 550993497191327827731793)
                  ·
                    refine ⟨413245122893495870798845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 550993497191327827731793 413245122893495870798845)
                    ·
                      refine ⟨154966921085060951549567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 413245122893495870798845 154966921085060951549567)
                      ·
                        rfl

theorem cell23_301797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_301797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301797 prefixEnd_301797 := by exact prefixLift 301797
  have htrace : WordTrace (prefixWord ++ tailWord_301797) baseStart_301797 baseEnd_301797 := by
    simpa [prefixWord, tailWord_301797, baseEnd_301797] using wordTrace_append hprefix tailTrace_301797
  have hstable : (prefixWord ++ tailWord_301797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301797).length < 2 ^ (prefixWord ++ tailWord_301797).sum := by decide
  have hdescent : baseEnd_301797 < baseStart_301797 := by decide
  rcases family_descends (prefixWord ++ tailWord_301797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301850 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_301850 : Nat := 118140960795 + 301850 * 2 ^ 59
def prefixEnd_301850 : Nat := 4983230072969 + 3 ^ 40 * 301850 * 2
def baseEnd_301850 : Nat := 154994135559749244186823

theorem tailTrace_301850 : CollatzResearch.WordTrace tailWord_301850 prefixEnd_301850 154994135559749244186823 := by
  unfold tailWord_301850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2752343489114119180213751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7339582637637651147236669 2752343489114119180213751)
  ·
    refine ⟨4128515233671178770320627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2752343489114119180213751 4128515233671178770320627)
    ·
      refine ⟨6192772850506768155480941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4128515233671178770320627 6192772850506768155480941)
      ·
        refine ⟨2322289818940038058305353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6192772850506768155480941 2322289818940038058305353)
        ·
          refine ⟨1741717364205028543729015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2322289818940038058305353 1741717364205028543729015)
          ·
            refine ⟨2612576046307542815593523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741717364205028543729015 2612576046307542815593523)
            ·
              refine ⟨3918864069461314223390285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612576046307542815593523 3918864069461314223390285)
              ·
                refine ⟨1469574026047992833771357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3918864069461314223390285 1469574026047992833771357)
                ·
                  refine ⟨551090259767997312664259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1469574026047992833771357 551090259767997312664259)
                  ·
                    refine ⟨826635389651995968996389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 551090259767997312664259 826635389651995968996389)
                    ·
                      refine ⟨154994135559749244186823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 826635389651995968996389 154994135559749244186823)
                      ·
                        rfl

theorem cell23_301850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_301850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301850 prefixEnd_301850 := by exact prefixLift 301850
  have htrace : WordTrace (prefixWord ++ tailWord_301850) baseStart_301850 baseEnd_301850 := by
    simpa [prefixWord, tailWord_301850, baseEnd_301850] using wordTrace_append hprefix tailTrace_301850
  have hstable : (prefixWord ++ tailWord_301850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301850).length < 2 ^ (prefixWord ++ tailWord_301850).sum := by decide
  have hdescent : baseEnd_301850 < baseStart_301850 := by decide
  rcases family_descends (prefixWord ++ tailWord_301850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_301873 : List Nat := [1, 2, 2, 3, 2, 1, 12]
def baseStart_301873 : Nat := 118140960795 + 301873 * 2 ^ 59
def prefixEnd_301873 : Nat := 4983230072969 + 3 ^ 40 * 301873 * 2
def baseEnd_301873 : Nat := 1913653649565464866657

theorem tailTrace_301873 : CollatzResearch.WordTrace tailWord_301873 prefixEnd_301873 1913653649565464866657 := by
  unfold tailWord_301873
  simp only [CollatzResearch.WordTrace]
  refine ⟨11010212835373151648942273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7340141890248767765961515 11010212835373151648942273)
  ·
    refine ⟨8257659626529863736706705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11010212835373151648942273 8257659626529863736706705)
    ·
      refine ⟨6193244719897397802530029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8257659626529863736706705 6193244719897397802530029)
      ·
        refine ⟨2322466769961524175948761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6193244719897397802530029 2322466769961524175948761)
        ·
          refine ⟨1741850077471143131961571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2322466769961524175948761 1741850077471143131961571)
          ·
            refine ⟨2612775116206714697942357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741850077471143131961571 2612775116206714697942357)
            ·
              refine ⟨1913653649565464866657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 2612775116206714697942357 1913653649565464866657)
              ·
                rfl

theorem cell23_301873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 12].length) (baseStart_301873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_301873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_301873 prefixEnd_301873 := by exact prefixLift 301873
  have htrace : WordTrace (prefixWord ++ tailWord_301873) baseStart_301873 baseEnd_301873 := by
    simpa [prefixWord, tailWord_301873, baseEnd_301873] using wordTrace_append hprefix tailTrace_301873
  have hstable : (prefixWord ++ tailWord_301873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_301873).length < 2 ^ (prefixWord ++ tailWord_301873).sum := by decide
  have hdescent : baseEnd_301873 < baseStart_301873 := by decide
  rcases family_descends (prefixWord ++ tailWord_301873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
