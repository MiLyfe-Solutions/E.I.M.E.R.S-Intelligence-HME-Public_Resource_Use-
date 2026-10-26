import V185TrunkScan23Chunk0795

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4707080 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_4707080 : Nat := 118140960795 + 4707080 * 2 ^ 59
def prefixEnd_4707080 : Nat := 4983230072969 + 3 ^ 40 * 4707080 * 2
def baseEnd_4707080 : Nat := 2416994519165548761552539

theorem tailTrace_4707080 : CollatzResearch.WordTrace tailWord_4707080 prefixEnd_4707080 2416994519165548761552539 := by
  unfold tailWord_4707080
  simp only [CollatzResearch.WordTrace]
  refine ⟨85840655893530270053471347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114454207858040360071295129 85840655893530270053471347)
  ·
    refine ⟨128760983840295405080207021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85840655893530270053471347 128760983840295405080207021)
    ·
      refine ⟨48285368940110776905077633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128760983840295405080207021 48285368940110776905077633)
      ·
        refine ⟨36214026705083082678808225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48285368940110776905077633 36214026705083082678808225)
        ·
          refine ⟨27160520028812312009106169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36214026705083082678808225 27160520028812312009106169)
          ·
            refine ⟨20370390021609234006829627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27160520028812312009106169 20370390021609234006829627)
            ·
              refine ⟨30555585032413851010244441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20370390021609234006829627 30555585032413851010244441)
              ·
                refine ⟨22916688774310388257683331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30555585032413851010244441 22916688774310388257683331)
                ·
                  refine ⟨34375033161465582386524997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22916688774310388257683331 34375033161465582386524997)
                  ·
                    refine ⟨6445318717774796697473437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34375033161465582386524997 6445318717774796697473437)
                    ·
                      refine ⟨2416994519165548761552539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445318717774796697473437 2416994519165548761552539)
                      ·
                        rfl

theorem cell23_4707080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_4707080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707080 prefixEnd_4707080 := by exact prefixLift 4707080
  have htrace : WordTrace (prefixWord ++ tailWord_4707080) baseStart_4707080 baseEnd_4707080 := by
    simpa [prefixWord, tailWord_4707080, baseEnd_4707080] using wordTrace_append hprefix tailTrace_4707080
  have hstable : (prefixWord ++ tailWord_4707080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707080).length < 2 ^ (prefixWord ++ tailWord_4707080).sum := by decide
  have hdescent : baseEnd_4707080 < baseStart_4707080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707104 : List Nat := [2, 1, 1, 5, 1, 2, 3, 3, 1, 4]
def baseStart_4707104 : Nat := 118140960795 + 4707104 * 2 ^ 59
def prefixEnd_4707104 : Nat := 4983230072969 + 3 ^ 40 * 4707104 * 2
def baseEnd_4707104 : Nat := 805668947567085555884143

theorem tailTrace_4707104 : CollatzResearch.WordTrace tailWord_4707104 prefixEnd_4707104 805668947567085555884143 := by
  unfold tailWord_4707104
  simp only [CollatzResearch.WordTrace]
  refine ⟨85841093569486796102908183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114454791425982394803877577 85841093569486796102908183)
  ·
    refine ⟨128761640354230194154362275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85841093569486796102908183 128761640354230194154362275)
    ·
      refine ⟨193142460531345291231543413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128761640354230194154362275 193142460531345291231543413)
      ·
        refine ⟨18107105674813621052957195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193142460531345291231543413 18107105674813621052957195)
        ·
          refine ⟨27160658512220431579435793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18107105674813621052957195 27160658512220431579435793)
          ·
            refine ⟨20370493884165323684576845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27160658512220431579435793 20370493884165323684576845)
            ·
              refine ⟨7638935206561996381716317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20370493884165323684576845 7638935206561996381716317)
              ·
                refine ⟨2864600702460748643143619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7638935206561996381716317 2864600702460748643143619)
                ·
                  refine ⟨4296901053691122964715429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864600702460748643143619 4296901053691122964715429)
                  ·
                    refine ⟨805668947567085555884143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4296901053691122964715429 805668947567085555884143)
                    ·
                      rfl

theorem cell23_4707104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 1, 4].length) (baseStart_4707104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707104 prefixEnd_4707104 := by exact prefixLift 4707104
  have htrace : WordTrace (prefixWord ++ tailWord_4707104) baseStart_4707104 baseEnd_4707104 := by
    simpa [prefixWord, tailWord_4707104, baseEnd_4707104] using wordTrace_append hprefix tailTrace_4707104
  have hstable : (prefixWord ++ tailWord_4707104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707104).length < 2 ^ (prefixWord ++ tailWord_4707104).sum := by decide
  have hdescent : baseEnd_4707104 < baseStart_4707104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707154 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_4707154 : Nat := 118140960795 + 4707154 * 2 ^ 59
def prefixEnd_4707154 : Nat := 4983230072969 + 3 ^ 40 * 4707154 * 2
def baseEnd_4707154 : Nat := 2417032516733981472027199

theorem tailTrace_4707154 : CollatzResearch.WordTrace tailWord_4707154 prefixEnd_4707154 2417032516733981472027199 := by
  unfold tailWord_4707154
  simp only [CollatzResearch.WordTrace]
  refine ⟨42921002697198112686284129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114456007192528300496757677 42921002697198112686284129)
  ·
    refine ⟨32190752022898584514713097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42921002697198112686284129 32190752022898584514713097)
    ·
      refine ⟨24143064017173938386034823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32190752022898584514713097 24143064017173938386034823)
      ·
        refine ⟨36214596025760907579052235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24143064017173938386034823 36214596025760907579052235)
        ·
          refine ⟨54321894038641361368578353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36214596025760907579052235 54321894038641361368578353)
          ·
            refine ⟨40741420528981021026433765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54321894038641361368578353 40741420528981021026433765)
            ·
              refine ⟨7639016349183941442456331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40741420528981021026433765 7639016349183941442456331)
              ·
                refine ⟨11458524523775912163684497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7639016349183941442456331 11458524523775912163684497)
                ·
                  refine ⟨8593893392831934122763373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11458524523775912163684497 8593893392831934122763373)
                  ·
                    refine ⟨3222710022311975296036265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8593893392831934122763373 3222710022311975296036265)
                    ·
                      refine ⟨2417032516733981472027199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3222710022311975296036265 2417032516733981472027199)
                      ·
                        rfl

theorem cell23_4707154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_4707154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707154 prefixEnd_4707154 := by exact prefixLift 4707154
  have htrace : WordTrace (prefixWord ++ tailWord_4707154) baseStart_4707154 baseEnd_4707154 := by
    simpa [prefixWord, tailWord_4707154, baseEnd_4707154] using wordTrace_append hprefix tailTrace_4707154
  have hstable : (prefixWord ++ tailWord_4707154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707154).length < 2 ^ (prefixWord ++ tailWord_4707154).sum := by decide
  have hdescent : baseEnd_4707154 < baseStart_4707154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707160 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 6, 4]
def baseStart_4707160 : Nat := 118140960795 + 4707160 * 2 ^ 59
def prefixEnd_4707160 : Nat := 4983230072969 + 3 ^ 40 * 4707160 * 2
def baseEnd_4707160 : Nat := 805678532539302816184057

theorem tailTrace_4707160 : CollatzResearch.WordTrace tailWord_4707160 prefixEnd_4707160 805678532539302816184057 := by
  unfold tailWord_4707160
  simp only [CollatzResearch.WordTrace]
  refine ⟨85842114813385356884927467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114456153084513809179903289 85842114813385356884927467)
  ·
    refine ⟨128763172220078035327391201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85842114813385356884927467 128763172220078035327391201)
    ·
      refine ⟨96572379165058526495543401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128763172220078035327391201 96572379165058526495543401)
      ·
        refine ⟨72429284373793894871657551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96572379165058526495543401 72429284373793894871657551)
        ·
          refine ⟨108643926560690842307486327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72429284373793894871657551 108643926560690842307486327)
          ·
            refine ⟨162965889841036263461229491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108643926560690842307486327 162965889841036263461229491)
            ·
              refine ⟨244448834761554395191844237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162965889841036263461229491 244448834761554395191844237)
              ·
                refine ⟨91668313035582898196941589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244448834761554395191844237 91668313035582898196941589)
                ·
                  refine ⟨4296952173542948352981637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91668313035582898196941589 4296952173542948352981637)
                  ·
                    refine ⟨805678532539302816184057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4296952173542948352981637 805678532539302816184057)
                    ·
                      rfl

theorem cell23_4707160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_4707160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707160 prefixEnd_4707160 := by exact prefixLift 4707160
  have htrace : WordTrace (prefixWord ++ tailWord_4707160) baseStart_4707160 baseEnd_4707160 := by
    simpa [prefixWord, tailWord_4707160, baseEnd_4707160] using wordTrace_append hprefix tailTrace_4707160
  have hstable : (prefixWord ++ tailWord_4707160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707160).length < 2 ^ (prefixWord ++ tailWord_4707160).sum := by decide
  have hdescent : baseEnd_4707160 < baseStart_4707160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707180 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_4707180 : Nat := 118140960795 + 4707180 * 2 ^ 59
def prefixEnd_4707180 : Nat := 4983230072969 + 3 ^ 40 * 4707180 * 2
def baseEnd_4707180 : Nat := 2417045867230998370302079

theorem tailTrace_4707180 : CollatzResearch.WordTrace tailWord_4707180 prefixEnd_4707180 2417045867230998370302079 := by
  unfold tailWord_4707180
  simp only [CollatzResearch.WordTrace]
  refine ⟨85842479543349128592791497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114456639391132171457055329 85842479543349128592791497)
  ·
    refine ⟨64381859657511846444593623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85842479543349128592791497 64381859657511846444593623)
    ·
      refine ⟨96572789486267769666890435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64381859657511846444593623 96572789486267769666890435)
      ·
        refine ⟨144859184229401654500335653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96572789486267769666890435 144859184229401654500335653)
        ·
          refine ⟨27161097043012810218812935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144859184229401654500335653 27161097043012810218812935)
          ·
            refine ⟨40741645564519215328219403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27161097043012810218812935 40741645564519215328219403)
            ·
              refine ⟨61112468346778822992329105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40741645564519215328219403 61112468346778822992329105)
              ·
                refine ⟨45834351260084117244246829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61112468346778822992329105 45834351260084117244246829)
                ·
                  refine ⟨17187881722531543966592561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45834351260084117244246829 17187881722531543966592561)
                  ·
                    refine ⟨12890911291898657974944421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17187881722531543966592561 12890911291898657974944421)
                    ·
                      refine ⟨2417045867230998370302079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12890911291898657974944421 2417045867230998370302079)
                      ·
                        rfl

theorem cell23_4707180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_4707180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707180 prefixEnd_4707180 := by exact prefixLift 4707180
  have htrace : WordTrace (prefixWord ++ tailWord_4707180) baseStart_4707180 baseEnd_4707180 := by
    simpa [prefixWord, tailWord_4707180, baseEnd_4707180] using wordTrace_append hprefix tailTrace_4707180
  have hstable : (prefixWord ++ tailWord_4707180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707180).length < 2 ^ (prefixWord ++ tailWord_4707180).sum := by decide
  have hdescent : baseEnd_4707180 < baseStart_4707180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707207 : List Nat := [1, 1, 4, 2, 3, 2, 3, 7]
def baseStart_4707207 : Nat := 118140960795 + 4707207 * 2 ^ 59
def prefixEnd_4707207 : Nat := 4983230072969 + 3 ^ 40 * 4707207 * 2
def baseEnd_4707207 : Nat := 89520730785506287580165

theorem tailTrace_4707207 : CollatzResearch.WordTrace tailWord_4707207 prefixEnd_4707207 89520730785506287580165 := by
  unfold tailWord_4707207
  simp only [CollatzResearch.WordTrace]
  refine ⟨171685943857600440796815875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114457295905066960531210583 171685943857600440796815875)
  ·
    refine ⟨257528915786400661195223813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171685943857600440796815875 257528915786400661195223813)
    ·
      refine ⟨48286671709950123974104465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257528915786400661195223813 48286671709950123974104465)
      ·
        refine ⟨36215003782462592980578349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48286671709950123974104465 36215003782462592980578349)
        ·
          refine ⟨13580626418423472367716881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36215003782462592980578349 13580626418423472367716881)
          ·
            refine ⟨10185469813817604275787661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13580626418423472367716881 10185469813817604275787661)
            ·
              refine ⟨3819551180181601603420373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10185469813817604275787661 3819551180181601603420373)
              ·
                refine ⟨89520730785506287580165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3819551180181601603420373 89520730785506287580165)
                ·
                  rfl

theorem cell23_4707207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 7].length) (baseStart_4707207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707207 prefixEnd_4707207 := by exact prefixLift 4707207
  have htrace : WordTrace (prefixWord ++ tailWord_4707207) baseStart_4707207 baseEnd_4707207 := by
    simpa [prefixWord, tailWord_4707207, baseEnd_4707207] using wordTrace_append hprefix tailTrace_4707207
  have hstable : (prefixWord ++ tailWord_4707207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707207).length < 2 ^ (prefixWord ++ tailWord_4707207).sum := by decide
  have hdescent : baseEnd_4707207 < baseStart_4707207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707217 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 4, 1, 3]
def baseStart_4707217 : Nat := 118140960795 + 4707217 * 2 ^ 59
def prefixEnd_4707217 : Nat := 4983230072969 + 3 ^ 40 * 4707217 * 2
def baseEnd_4707217 : Nat := 2417064866015214725539409

theorem tailTrace_4707217 : CollatzResearch.WordTrace tailWord_4707217 prefixEnd_4707217 2417064866015214725539409 := by
  unfold tailWord_4707217
  simp only [CollatzResearch.WordTrace]
  refine ⟨171686308587564212504679905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114457539058376141669786603 171686308587564212504679905)
  ·
    refine ⟨128764731440673159378509929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171686308587564212504679905 128764731440673159378509929)
    ·
      refine ⟨96573548580504869533882447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128764731440673159378509929 96573548580504869533882447)
      ·
        refine ⟨144860322870757304300823671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96573548580504869533882447 144860322870757304300823671)
        ·
          refine ⟨217290484306135956451235507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144860322870757304300823671 217290484306135956451235507)
          ·
            refine ⟨325935726459203934676853261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217290484306135956451235507 325935726459203934676853261)
            ·
              refine ⟨122225897422201475503819973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 325935726459203934676853261 122225897422201475503819973)
              ·
                refine ⟨22917355766662776656966245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122225897422201475503819973 22917355766662776656966245)
                ·
                  refine ⟨4297004206249270623181171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22917355766662776656966245 4297004206249270623181171)
                  ·
                    refine ⟨6445506309373905934771757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4297004206249270623181171 6445506309373905934771757)
                    ·
                      refine ⟨2417064866015214725539409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445506309373905934771757 2417064866015214725539409)
                      ·
                        rfl

theorem cell23_4707217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_4707217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707217 prefixEnd_4707217 := by exact prefixLift 4707217
  have htrace : WordTrace (prefixWord ++ tailWord_4707217) baseStart_4707217 baseEnd_4707217 := by
    simpa [prefixWord, tailWord_4707217, baseEnd_4707217] using wordTrace_append hprefix tailTrace_4707217
  have hstable : (prefixWord ++ tailWord_4707217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707217).length < 2 ^ (prefixWord ++ tailWord_4707217).sum := by decide
  have hdescent : baseEnd_4707217 < baseStart_4707217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707218 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_4707218 : Nat := 118140960795 + 4707218 * 2 ^ 59
def prefixEnd_4707218 : Nat := 4983230072969 + 3 ^ 40 * 4707218 * 2
def baseEnd_4707218 : Nat := 2417065379495869221626905

theorem tailTrace_4707218 : CollatzResearch.WordTrace tailWord_4707218 prefixEnd_4707218 2417065379495869221626905 := by
  unfold tailWord_4707218
  simp only [CollatzResearch.WordTrace]
  refine ⟨42921586265140147418866577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114457563373707059783644205 42921586265140147418866577)
  ·
    refine ⟨32191189698855110564149933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42921586265140147418866577 32191189698855110564149933)
    ·
      refine ⟨12071696137070666461556225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32191189698855110564149933 12071696137070666461556225)
      ·
        refine ⟨9053772102802999846167169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12071696137070666461556225 9053772102802999846167169)
        ·
          refine ⟨6790329077102249884625377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9053772102802999846167169 6790329077102249884625377)
          ·
            refine ⟨5092746807826687413469033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6790329077102249884625377 5092746807826687413469033)
            ·
              refine ⟨3819560105870015560101775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5092746807826687413469033 3819560105870015560101775)
              ·
                refine ⟨5729340158805023340152663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3819560105870015560101775 5729340158805023340152663)
                ·
                  refine ⟨8594010238207535010228995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5729340158805023340152663 8594010238207535010228995)
                  ·
                    refine ⟨12891015357311302515343493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8594010238207535010228995 12891015357311302515343493)
                    ·
                      refine ⟨2417065379495869221626905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12891015357311302515343493 2417065379495869221626905)
                      ·
                        rfl

theorem cell23_4707218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_4707218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707218 prefixEnd_4707218 := by exact prefixLift 4707218
  have htrace : WordTrace (prefixWord ++ tailWord_4707218) baseStart_4707218 baseEnd_4707218 := by
    simpa [prefixWord, tailWord_4707218, baseEnd_4707218] using wordTrace_append hprefix tailTrace_4707218
  have hstable : (prefixWord ++ tailWord_4707218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707218).length < 2 ^ (prefixWord ++ tailWord_4707218).sum := by decide
  have hdescent : baseEnd_4707218 < baseStart_4707218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707221 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 1, 2, 3]
def baseStart_4707221 : Nat := 118140960795 + 4707221 * 2 ^ 59
def prefixEnd_4707221 : Nat := 4983230072969 + 3 ^ 40 * 4707221 * 2
def baseEnd_4707221 : Nat := 2417066919937832709889391

theorem tailTrace_4707221 : CollatzResearch.WordTrace tailWord_4707221 prefixEnd_4707221 2417066919937832709889391 := by
  unfold tailWord_4707221
  simp only [CollatzResearch.WordTrace]
  refine ⟨171686454479549721187825517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114457636319699814125217011 171686454479549721187825517)
  ·
    refine ⟨64382420429831145445434569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171686454479549721187825517 64382420429831145445434569)
    ·
      refine ⟨48286815322373359084075927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64382420429831145445434569 48286815322373359084075927)
      ·
        refine ⟨72430222983560038626113891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48286815322373359084075927 72430222983560038626113891)
        ·
          refine ⟨108645334475340057939170837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72430222983560038626113891 108645334475340057939170837)
          ·
            refine ⟨5092750053531565215898633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108645334475340057939170837 5092750053531565215898633)
            ·
              refine ⟨3819562540148673911923975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5092750053531565215898633 3819562540148673911923975)
              ·
                refine ⟨5729343810223010867885963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3819562540148673911923975 5729343810223010867885963)
                ·
                  refine ⟨8594015715334516301828945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5729343810223010867885963 8594015715334516301828945)
                  ·
                    refine ⟨6445511786500887226371709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8594015715334516301828945 6445511786500887226371709)
                    ·
                      refine ⟨2417066919937832709889391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445511786500887226371709 2417066919937832709889391)
                      ·
                        rfl

theorem cell23_4707221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_4707221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707221 prefixEnd_4707221 := by exact prefixLift 4707221
  have htrace : WordTrace (prefixWord ++ tailWord_4707221) baseStart_4707221 baseEnd_4707221 := by
    simpa [prefixWord, tailWord_4707221, baseEnd_4707221] using wordTrace_append hprefix tailTrace_4707221
  have hstable : (prefixWord ++ tailWord_4707221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707221).length < 2 ^ (prefixWord ++ tailWord_4707221).sum := by decide
  have hdescent : baseEnd_4707221 < baseStart_4707221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707228 : List Nat := [2, 2, 3, 3, 3, 1, 1, 2, 2, 4]
def baseStart_4707228 : Nat := 118140960795 + 4707228 * 2 ^ 59
def prefixEnd_4707228 : Nat := 4983230072969 + 3 ^ 40 * 4707228 * 2
def baseEnd_4707228 : Nat := 805690171434138060833953

theorem tailTrace_4707228 : CollatzResearch.WordTrace tailWord_4707228 prefixEnd_4707228 805690171434138060833953 := by
  unfold tailWord_4707228
  simp only [CollatzResearch.WordTrace]
  refine ⟨85843354895262180691665169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114457806527016240922220225 85843354895262180691665169)
  ·
    refine ⟨64382516171446635518748877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85843354895262180691665169 64382516171446635518748877)
    ·
      refine ⟨24143443564292488319530829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64382516171446635518748877 24143443564292488319530829)
      ·
        refine ⟨9053791336609683119824061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24143443564292488319530829 9053791336609683119824061)
        ·
          refine ⟨3395171751228631169934023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9053791336609683119824061 3395171751228631169934023)
          ·
            refine ⟨5092757626842946754901035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395171751228631169934023 5092757626842946754901035)
            ·
              refine ⟨7639136440264420132351553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5092757626842946754901035 7639136440264420132351553)
              ·
                refine ⟨5729352330198315099263665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7639136440264420132351553 5729352330198315099263665)
                ·
                  refine ⟨4297014247648736324447749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5729352330198315099263665 4297014247648736324447749)
                  ·
                    refine ⟨805690171434138060833953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4297014247648736324447749 805690171434138060833953)
                    ·
                      rfl

theorem cell23_4707228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_4707228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707228 prefixEnd_4707228 := by exact prefixLift 4707228
  have htrace : WordTrace (prefixWord ++ tailWord_4707228) baseStart_4707228 baseEnd_4707228 := by
    simpa [prefixWord, tailWord_4707228, baseEnd_4707228] using wordTrace_append hprefix tailTrace_4707228
  have hstable : (prefixWord ++ tailWord_4707228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707228).length < 2 ^ (prefixWord ++ tailWord_4707228).sum := by decide
  have hdescent : baseEnd_4707228 < baseStart_4707228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707300 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_4707300 : Nat := 118140960795 + 4707300 * 2 ^ 59
def prefixEnd_4707300 : Nat := 4983230072969 + 3 ^ 40 * 4707300 * 2
def baseEnd_4707300 : Nat := 2417107484909537900801527

theorem tailTrace_4707300 : CollatzResearch.WordTrace tailWord_4707300 prefixEnd_4707300 2417107484909537900801527 := by
  unfold tailWord_4707300
  simp only [CollatzResearch.WordTrace]
  refine ⟨85844667923131758839975677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114459557230842345119967569 85844667923131758839975677)
  ·
    refine ⟨32191750471174409564990879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85844667923131758839975677 32191750471174409564990879)
    ·
      refine ⟨48287625706761614347486319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32191750471174409564990879 48287625706761614347486319)
      ·
        refine ⟨72431438560142421521229479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48287625706761614347486319 72431438560142421521229479)
        ·
          refine ⟨108647157840213632281844219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72431438560142421521229479 108647157840213632281844219)
          ·
            refine ⟨162970736760320448422766329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108647157840213632281844219 162970736760320448422766329)
            ·
              refine ⟨122228052570240336317074747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162970736760320448422766329 122228052570240336317074747)
              ·
                refine ⟨183342078855360504475612121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122228052570240336317074747 183342078855360504475612121)
                ·
                  refine ⟨137506559141520378356709091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183342078855360504475612121 137506559141520378356709091)
                  ·
                    refine ⟨206259838712280567535063637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137506559141520378356709091 206259838712280567535063637)
                    ·
                      refine ⟨2417107484909537900801527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 206259838712280567535063637 2417107484909537900801527)
                      ·
                        rfl

theorem cell23_4707300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_4707300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707300 prefixEnd_4707300 := by exact prefixLift 4707300
  have htrace : WordTrace (prefixWord ++ tailWord_4707300) baseStart_4707300 baseEnd_4707300 := by
    simpa [prefixWord, tailWord_4707300, baseEnd_4707300] using wordTrace_append hprefix tailTrace_4707300
  have hstable : (prefixWord ++ tailWord_4707300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707300).length < 2 ^ (prefixWord ++ tailWord_4707300).sum := by decide
  have hdescent : baseEnd_4707300 < baseStart_4707300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707320 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_4707320 : Nat := 118140960795 + 4707320 * 2 ^ 59
def prefixEnd_4707320 : Nat := 4983230072969 + 3 ^ 40 * 4707320 * 2
def baseEnd_4707320 : Nat := 2417117754522627822551435

theorem tailTrace_4707320 : CollatzResearch.WordTrace tailWord_4707320 prefixEnd_4707320 2417117754522627822551435 := by
  unfold tailWord_4707320
  simp only [CollatzResearch.WordTrace]
  refine ⟨85845032653095530547839707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114460043537460707397119609 85845032653095530547839707)
  ·
    refine ⟨128767548979643295821759561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85845032653095530547839707 128767548979643295821759561)
    ·
      refine ⟨96575661734732471866319671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128767548979643295821759561 96575661734732471866319671)
      ·
        refine ⟨144863492602098707799479507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96575661734732471866319671 144863492602098707799479507)
        ·
          refine ⟨217295238903148061699219261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144863492602098707799479507 217295238903148061699219261)
          ·
            refine ⟨81485714588680523137207223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217295238903148061699219261 81485714588680523137207223)
            ·
              refine ⟨122228571883020784705810835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81485714588680523137207223 122228571883020784705810835)
              ·
                refine ⟨183342857824531177058716253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122228571883020784705810835 183342857824531177058716253)
                ·
                  refine ⟨68753571684199191397018595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183342857824531177058716253 68753571684199191397018595)
                  ·
                    refine ⟨103130357526298787095527893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68753571684199191397018595 103130357526298787095527893)
                    ·
                      refine ⟨2417117754522627822551435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103130357526298787095527893 2417117754522627822551435)
                      ·
                        rfl

theorem cell23_4707320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_4707320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707320 prefixEnd_4707320 := by exact prefixLift 4707320
  have htrace : WordTrace (prefixWord ++ tailWord_4707320) baseStart_4707320 baseEnd_4707320 := by
    simpa [prefixWord, tailWord_4707320, baseEnd_4707320] using wordTrace_append hprefix tailTrace_4707320
  have hstable : (prefixWord ++ tailWord_4707320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707320).length < 2 ^ (prefixWord ++ tailWord_4707320).sum := by decide
  have hdescent : baseEnd_4707320 < baseStart_4707320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707384 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 1, 4, 3]
def baseStart_4707384 : Nat := 118140960795 + 4707384 * 2 ^ 59
def prefixEnd_4707384 : Nat := 4983230072969 + 3 ^ 40 * 4707384 * 2
def baseEnd_4707384 : Nat := 2417150617284515572151141

theorem tailTrace_4707384 : CollatzResearch.WordTrace tailWord_4707384 prefixEnd_4707384 2417150617284515572151141 := by
  unfold tailWord_4707384
  simp only [CollatzResearch.WordTrace]
  refine ⟨85846199788979600013004603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114461599718639466684006137 85846199788979600013004603)
  ·
    refine ⟨128769299683469400019506905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85846199788979600013004603 128769299683469400019506905)
    ·
      refine ⟨96576974762602050014630179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128769299683469400019506905 96576974762602050014630179)
      ·
        refine ⟨144865462143903075021945269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96576974762602050014630179 144865462143903075021945269)
        ·
          refine ⟨13581137075990913283307369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144865462143903075021945269 13581137075990913283307369)
          ·
            refine ⟨10185852806993184962480527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13581137075990913283307369 10185852806993184962480527)
            ·
              refine ⟨15278779210489777443720791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10185852806993184962480527 15278779210489777443720791)
              ·
                refine ⟨22918168815734666165581187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15278779210489777443720791 22918168815734666165581187)
                ·
                  refine ⟨34377253223601999248371781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22918168815734666165581187 34377253223601999248371781)
                  ·
                    refine ⟨6445734979425374859069709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34377253223601999248371781 6445734979425374859069709)
                    ·
                      refine ⟨2417150617284515572151141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445734979425374859069709 2417150617284515572151141)
                      ·
                        rfl

theorem cell23_4707384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_4707384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707384 prefixEnd_4707384 := by exact prefixLift 4707384
  have htrace : WordTrace (prefixWord ++ tailWord_4707384) baseStart_4707384 baseEnd_4707384 := by
    simpa [prefixWord, tailWord_4707384, baseEnd_4707384] using wordTrace_append hprefix tailTrace_4707384
  have hstable : (prefixWord ++ tailWord_4707384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707384).length < 2 ^ (prefixWord ++ tailWord_4707384).sum := by decide
  have hdescent : baseEnd_4707384 < baseStart_4707384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707398 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_4707398 : Nat := 118140960795 + 4707398 * 2 ^ 59
def prefixEnd_4707398 : Nat := 4983230072969 + 3 ^ 40 * 4707398 * 2
def baseEnd_4707398 : Nat := 2417157806013678517376077

theorem tailTrace_4707398 : CollatzResearch.WordTrace tailWord_4707398 prefixEnd_4707398 2417157806013678517376077 := by
  unfold tailWord_4707398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5365403443747140013031839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114461940133272320278012565 5365403443747140013031839)
  ·
    refine ⟨8048105165620710019547759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5365403443747140013031839 8048105165620710019547759)
    ·
      refine ⟨12072157748431065029321639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8048105165620710019547759 12072157748431065029321639)
      ·
        refine ⟨18108236622646597543982459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12072157748431065029321639 18108236622646597543982459)
        ·
          refine ⟨27162354933969896315973689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18108236622646597543982459 27162354933969896315973689)
          ·
            refine ⟨20371766200477422236980267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27162354933969896315973689 20371766200477422236980267)
            ·
              refine ⟨30557649300716133355470401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20371766200477422236980267 30557649300716133355470401)
              ·
                refine ⟨22918236975537100016602801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30557649300716133355470401 22918236975537100016602801)
                ·
                  refine ⟨17188677731652825012452101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22918236975537100016602801 17188677731652825012452101)
                  ·
                    refine ⟨3222877074684904689834769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17188677731652825012452101 3222877074684904689834769)
                    ·
                      refine ⟨2417157806013678517376077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3222877074684904689834769 2417157806013678517376077)
                      ·
                        rfl

theorem cell23_4707398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_4707398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707398 prefixEnd_4707398 := by exact prefixLift 4707398
  have htrace : WordTrace (prefixWord ++ tailWord_4707398) baseStart_4707398 baseEnd_4707398 := by
    simpa [prefixWord, tailWord_4707398, baseEnd_4707398] using wordTrace_append hprefix tailTrace_4707398
  have hstable : (prefixWord ++ tailWord_4707398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707398).length < 2 ^ (prefixWord ++ tailWord_4707398).sum := by decide
  have hdescent : baseEnd_4707398 < baseStart_4707398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707417 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 3, 5]
def baseStart_4707417 : Nat := 118140960795 + 4707417 * 2 ^ 59
def prefixEnd_4707417 : Nat := 4983230072969 + 3 ^ 40 * 4707417 * 2
def baseEnd_4707417 : Nat := 805722520715371314346163

theorem tailTrace_4707417 : CollatzResearch.WordTrace tailWord_4707417 prefixEnd_4707417 805722520715371314346163 := by
  unfold tailWord_4707417
  simp only [CollatzResearch.WordTrace]
  refine ⟨171693603186839646661960505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114462402124559764441307003 171693603186839646661960505)
  ·
    refine ⟨128770202390129734996470379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171693603186839646661960505 128770202390129734996470379)
    ·
      refine ⟨193155303585194602494705569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128770202390129734996470379 193155303585194602494705569)
      ·
        refine ⟨144866477688895951871029177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193155303585194602494705569 144866477688895951871029177)
        ·
          refine ⟨108649858266671963903271883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144866477688895951871029177 108649858266671963903271883)
          ·
            refine ⟨162974787400007945854907825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108649858266671963903271883 162974787400007945854907825)
            ·
              refine ⟨122231090550005959391180869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162974787400007945854907825 122231090550005959391180869)
              ·
                refine ⟨22918329478126117385846413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122231090550005959391180869 22918329478126117385846413)
                ·
                  refine ⟨8594373554297294019692405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22918329478126117385846413 8594373554297294019692405)
                  ·
                    refine ⟨805722520715371314346163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8594373554297294019692405 805722520715371314346163)
                    ·
                      rfl

theorem cell23_4707417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_4707417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707417 prefixEnd_4707417 := by exact prefixLift 4707417
  have htrace : WordTrace (prefixWord ++ tailWord_4707417) baseStart_4707417 baseEnd_4707417 := by
    simpa [prefixWord, tailWord_4707417, baseEnd_4707417] using wordTrace_append hprefix tailTrace_4707417
  have hstable : (prefixWord ++ tailWord_4707417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707417).length < 2 ^ (prefixWord ++ tailWord_4707417).sum := by decide
  have hdescent : baseEnd_4707417 < baseStart_4707417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707424 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 3, 5, 2]
def baseStart_4707424 : Nat := 118140960795 + 4707424 * 2 ^ 59
def prefixEnd_4707424 : Nat := 4983230072969 + 3 ^ 40 * 4707424 * 2
def baseEnd_4707424 : Nat := 2417171156510695415650957

theorem tailTrace_4707424 : CollatzResearch.WordTrace tailWord_4707424 prefixEnd_4707424 2417171156510695415650957 := by
  unfold tailWord_4707424
  simp only [CollatzResearch.WordTrace]
  refine ⟨85846929248907143428732663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114462572331876191238310217 85846929248907143428732663)
  ·
    refine ⟨128770393873360715143098995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85846929248907143428732663 128770393873360715143098995)
    ·
      refine ⟨193155590810041072714648493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128770393873360715143098995 193155590810041072714648493)
      ·
        refine ⟨72433346553765402267993185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193155590810041072714648493 72433346553765402267993185)
        ·
          refine ⟨54325009915324051700994889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72433346553765402267993185 54325009915324051700994889)
          ·
            refine ⟨40743757436493038775746167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54325009915324051700994889 40743757436493038775746167)
            ·
              refine ⟨61115636154739558163619251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40743757436493038775746167 61115636154739558163619251)
              ·
                refine ⟨91673454232109337245428877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61115636154739558163619251 91673454232109337245428877)
                ·
                  refine ⟨34377545337041001467035829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91673454232109337245428877 34377545337041001467035829)
                  ·
                    refine ⟨3222894875347593887534609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34377545337041001467035829 3222894875347593887534609)
                    ·
                      refine ⟨2417171156510695415650957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3222894875347593887534609 2417171156510695415650957)
                      ·
                        rfl

theorem cell23_4707424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_4707424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707424 prefixEnd_4707424 := by exact prefixLift 4707424
  have htrace : WordTrace (prefixWord ++ tailWord_4707424) baseStart_4707424 baseEnd_4707424 := by
    simpa [prefixWord, tailWord_4707424, baseEnd_4707424] using wordTrace_append hprefix tailTrace_4707424
  have hstable : (prefixWord ++ tailWord_4707424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707424).length < 2 ^ (prefixWord ++ tailWord_4707424).sum := by decide
  have hdescent : baseEnd_4707424 < baseStart_4707424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707431 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_4707431 : Nat := 118140960795 + 4707431 * 2 ^ 59
def prefixEnd_4707431 : Nat := 4983230072969 + 3 ^ 40 * 4707431 * 2
def baseEnd_4707431 : Nat := 2417174750875276888263425

theorem tailTrace_4707431 : CollatzResearch.WordTrace tailWord_4707431 prefixEnd_4707431 2417174750875276888263425 := by
  unfold tailWord_4707431
  simp only [CollatzResearch.WordTrace]
  refine ⟨171694113808788927052970147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114462742539192618035313431 171694113808788927052970147)
  ·
    refine ⟨257541170713183390579455221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171694113808788927052970147 257541170713183390579455221)
    ·
      refine ⟨24144484754360942866823927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 257541170713183390579455221 24144484754360942866823927)
      ·
        refine ⟨36216727131541414300235891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24144484754360942866823927 36216727131541414300235891)
        ·
          refine ⟨54325090697312121450353837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36216727131541414300235891 54325090697312121450353837)
          ·
            refine ⟨20371909011492045543882689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54325090697312121450353837 20371909011492045543882689)
            ·
              refine ⟨15278931758619034157912017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20371909011492045543882689 15278931758619034157912017)
              ·
                refine ⟨11459198818964275618434013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15278931758619034157912017 11459198818964275618434013)
                ·
                  refine ⟨4297199557111603356912755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11459198818964275618434013 4297199557111603356912755)
                  ·
                    refine ⟨6445799335667405035369133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4297199557111603356912755 6445799335667405035369133)
                    ·
                      refine ⟨2417174750875276888263425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445799335667405035369133 2417174750875276888263425)
                      ·
                        rfl

theorem cell23_4707431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_4707431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707431 prefixEnd_4707431 := by exact prefixLift 4707431
  have htrace : WordTrace (prefixWord ++ tailWord_4707431) baseStart_4707431 baseEnd_4707431 := by
    simpa [prefixWord, tailWord_4707431, baseEnd_4707431] using wordTrace_append hprefix tailTrace_4707431
  have hstable : (prefixWord ++ tailWord_4707431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707431).length < 2 ^ (prefixWord ++ tailWord_4707431).sum := by decide
  have hdescent : baseEnd_4707431 < baseStart_4707431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707447 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 3, 6]
def baseStart_4707447 : Nat := 118140960795 + 4707447 * 2 ^ 59
def prefixEnd_4707447 : Nat := 4983230072969 + 3 ^ 40 * 4707447 * 2
def baseEnd_4707447 : Nat := 805727655521916275221117

theorem tailTrace_4707447 : CollatzResearch.WordTrace tailWord_4707447 prefixEnd_4707447 805727655521916275221117 := by
  unfold tailWord_4707447
  simp only [CollatzResearch.WordTrace]
  refine ⟨171694697376730961785552595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114463131584487307857035063 171694697376730961785552595)
  ·
    refine ⟨257542046065096442678328893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171694697376730961785552595 257542046065096442678328893)
    ·
      refine ⟨96578267274411166004373335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257542046065096442678328893 96578267274411166004373335)
      ·
        refine ⟨144867400911616749006560003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96578267274411166004373335 144867400911616749006560003)
        ·
          refine ⟨217301101367425123509840005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144867400911616749006560003 217301101367425123509840005)
          ·
            refine ⟨40743956506392210658095001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217301101367425123509840005 40743956506392210658095001)
            ·
              refine ⟨30557967379794157993571251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40743956506392210658095001 30557967379794157993571251)
              ·
                refine ⟨45836951069691236990356877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30557967379794157993571251 45836951069691236990356877)
                ·
                  refine ⟨17188856651134213871383829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45836951069691236990356877 17188856651134213871383829)
                  ·
                    refine ⟨805727655521916275221117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17188856651134213871383829 805727655521916275221117)
                    ·
                      rfl

theorem cell23_4707447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_4707447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707447 prefixEnd_4707447 := by exact prefixLift 4707447
  have htrace : WordTrace (prefixWord ++ tailWord_4707447) baseStart_4707447 baseEnd_4707447 := by
    simpa [prefixWord, tailWord_4707447, baseEnd_4707447] using wordTrace_append hprefix tailTrace_4707447
  have hstable : (prefixWord ++ tailWord_4707447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707447).length < 2 ^ (prefixWord ++ tailWord_4707447).sum := by decide
  have hdescent : baseEnd_4707447 < baseStart_4707447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707448 : List Nat := [2, 1, 2, 1, 1, 1, 7, 3, 1, 1, 3]
def baseStart_4707448 : Nat := 118140960795 + 4707448 * 2 ^ 59
def prefixEnd_4707448 : Nat := 4983230072969 + 3 ^ 40 * 4707448 * 2
def baseEnd_4707448 : Nat := 2417183480046403321750847

theorem tailTrace_4707448 : CollatzResearch.WordTrace tailWord_4707448 prefixEnd_4707448 2417183480046403321750847 := by
  unfold tailWord_4707448
  simp only [CollatzResearch.WordTrace]
  refine ⟨85847366924863669478169499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114463155899818225970892665 85847366924863669478169499)
  ·
    refine ⟨128771050387295504217254249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85847366924863669478169499 128771050387295504217254249)
    ·
      refine ⟨96578287790471628162940687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128771050387295504217254249 96578287790471628162940687)
      ·
        refine ⟨144867431685707442244411031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96578287790471628162940687 144867431685707442244411031)
        ·
          refine ⟨217301147528561163366616547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144867431685707442244411031 217301147528561163366616547)
          ·
            refine ⟨325951721292841745049924821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217301147528561163366616547 325951721292841745049924821)
            ·
              refine ⟨7639493467800978399607613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 325951721292841745049924821 7639493467800978399607613)
              ·
                refine ⟨2864810050425366899852855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7639493467800978399607613 2864810050425366899852855)
                ·
                  refine ⟨4297215075638050349779283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864810050425366899852855 4297215075638050349779283)
                  ·
                    refine ⟨6445822613457075524668925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4297215075638050349779283 6445822613457075524668925)
                    ·
                      refine ⟨2417183480046403321750847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445822613457075524668925 2417183480046403321750847)
                      ·
                        rfl

theorem cell23_4707448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3, 1, 1, 3].length) (baseStart_4707448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707448 prefixEnd_4707448 := by exact prefixLift 4707448
  have htrace : WordTrace (prefixWord ++ tailWord_4707448) baseStart_4707448 baseEnd_4707448 := by
    simpa [prefixWord, tailWord_4707448, baseEnd_4707448] using wordTrace_append hprefix tailTrace_4707448
  have hstable : (prefixWord ++ tailWord_4707448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707448).length < 2 ^ (prefixWord ++ tailWord_4707448).sum := by decide
  have hdescent : baseEnd_4707448 < baseStart_4707448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707465 : List Nat := [1, 2, 1, 1, 4, 4, 3, 2, 1, 1, 3]
def baseStart_4707465 : Nat := 118140960795 + 4707465 * 2 ^ 59
def prefixEnd_4707465 : Nat := 4983230072969 + 3 ^ 40 * 4707465 * 2
def baseEnd_4707465 : Nat := 2417192209217529755238269

theorem tailTrace_4707465 : CollatzResearch.WordTrace tailWord_4707465 prefixEnd_4707465 2417192209217529755238269 := by
  unfold tailWord_4707465
  simp only [CollatzResearch.WordTrace]
  refine ⟨171695353890665750859707849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114463569260443833906471899 171695353890665750859707849)
  ·
    refine ⟨128771515417999313144780887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171695353890665750859707849 128771515417999313144780887)
    ·
      refine ⟨193157273126998969717171331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128771515417999313144780887 193157273126998969717171331)
      ·
        refine ⟨289735909690498454575756997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193157273126998969717171331 289735909690498454575756997)
        ·
          refine ⟨54325483066968460232954437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 289735909690498454575756997 54325483066968460232954437)
          ·
            refine ⟨10186028075056586293678957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54325483066968460232954437 10186028075056586293678957)
            ·
              refine ⟨3819760528146219860129609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10186028075056586293678957 3819760528146219860129609)
              ·
                refine ⟨2864820396109664895097207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3819760528146219860129609 2864820396109664895097207)
                ·
                  refine ⟨4297230594164497342645811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2864820396109664895097207 4297230594164497342645811)
                  ·
                    refine ⟨6445845891246746013968717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4297230594164497342645811 6445845891246746013968717)
                    ·
                      refine ⟨2417192209217529755238269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445845891246746013968717 2417192209217529755238269)
                      ·
                        rfl

theorem cell23_4707465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 2, 1, 1, 3].length) (baseStart_4707465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707465 prefixEnd_4707465 := by exact prefixLift 4707465
  have htrace : WordTrace (prefixWord ++ tailWord_4707465) baseStart_4707465 baseEnd_4707465 := by
    simpa [prefixWord, tailWord_4707465, baseEnd_4707465] using wordTrace_append hprefix tailTrace_4707465
  have hstable : (prefixWord ++ tailWord_4707465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707465).length < 2 ^ (prefixWord ++ tailWord_4707465).sum := by decide
  have hdescent : baseEnd_4707465 < baseStart_4707465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707484 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_4707484 : Nat := 118140960795 + 4707484 * 2 ^ 59
def prefixEnd_4707484 : Nat := 4983230072969 + 3 ^ 40 * 4707484 * 2
def baseEnd_4707484 : Nat := 2417201965349965180900681

theorem tailTrace_4707484 : CollatzResearch.WordTrace tailWord_4707484 prefixEnd_4707484 2417201965349965180900681 := by
  unfold tailWord_4707484
  simp only [CollatzResearch.WordTrace]
  refine ⟨85848023438798458552324753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114464031251731278069766337 85848023438798458552324753)
  ·
    refine ⟨64386017579098843914243565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85848023438798458552324753 64386017579098843914243565)
    ·
      refine ⟨24144756592162066467841337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64386017579098843914243565 24144756592162066467841337)
      ·
        refine ⟨18108567444121549850881003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24144756592162066467841337 18108567444121549850881003)
        ·
          refine ⟨27162851166182324776321505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18108567444121549850881003 27162851166182324776321505)
          ·
            refine ⟨20372138374636743582241129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27162851166182324776321505 20372138374636743582241129)
            ·
              refine ⟨15279103780977557686680847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20372138374636743582241129 15279103780977557686680847)
              ·
                refine ⟨22918655671466336530021271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15279103780977557686680847 22918655671466336530021271)
                ·
                  refine ⟨34377983507199504795031907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22918655671466336530021271 34377983507199504795031907)
                  ·
                    refine ⟨51566975260799257192547861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34377983507199504795031907 51566975260799257192547861)
                    ·
                      refine ⟨2417201965349965180900681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51566975260799257192547861 2417201965349965180900681)
                      ·
                        rfl

theorem cell23_4707484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_4707484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707484 prefixEnd_4707484 := by exact prefixLift 4707484
  have htrace : WordTrace (prefixWord ++ tailWord_4707484) baseStart_4707484 baseEnd_4707484 := by
    simpa [prefixWord, tailWord_4707484, baseEnd_4707484] using wordTrace_append hprefix tailTrace_4707484
  have hstable : (prefixWord ++ tailWord_4707484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707484).length < 2 ^ (prefixWord ++ tailWord_4707484).sum := by decide
  have hdescent : baseEnd_4707484 < baseStart_4707484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707504 : List Nat := [2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 3]
def baseStart_4707504 : Nat := 118140960795 + 4707504 * 2 ^ 59
def prefixEnd_4707504 : Nat := 4983230072969 + 3 ^ 40 * 4707504 * 2
def baseEnd_4707504 : Nat := 2417212234963055102650589

theorem tailTrace_4707504 : CollatzResearch.WordTrace tailWord_4707504 prefixEnd_4707504 2417212234963055102650589 := by
  unfold tailWord_4707504
  simp only [CollatzResearch.WordTrace]
  refine ⟨85848388168762230260188783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114464517558349640346918377 85848388168762230260188783)
  ·
    refine ⟨128772582253143345390283175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85848388168762230260188783 128772582253143345390283175)
    ·
      refine ⟨193158873379715018085424763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128772582253143345390283175 193158873379715018085424763)
      ·
        refine ⟨289738310069572527128137145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193158873379715018085424763 289738310069572527128137145)
        ·
          refine ⟨217303732552179395346102859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289738310069572527128137145 217303732552179395346102859)
          ·
            refine ⟨325955598828269093019154289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217303732552179395346102859 325955598828269093019154289)
            ·
              refine ⟨244466699121201819764365717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325955598828269093019154289 244466699121201819764365717)
              ·
                refine ⟨11459376521306335301454643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 244466699121201819764365717 11459376521306335301454643)
                ·
                  refine ⟨17189064781959502952181965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11459376521306335301454643 17189064781959502952181965)
                  ·
                    refine ⟨6445899293234813607068237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17189064781959502952181965 6445899293234813607068237)
                    ·
                      refine ⟨2417212234963055102650589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445899293234813607068237 2417212234963055102650589)
                      ·
                        rfl

theorem cell23_4707504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 3].length) (baseStart_4707504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707504 prefixEnd_4707504 := by exact prefixLift 4707504
  have htrace : WordTrace (prefixWord ++ tailWord_4707504) baseStart_4707504 baseEnd_4707504 := by
    simpa [prefixWord, tailWord_4707504, baseEnd_4707504] using wordTrace_append hprefix tailTrace_4707504
  have hstable : (prefixWord ++ tailWord_4707504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707504).length < 2 ^ (prefixWord ++ tailWord_4707504).sum := by decide
  have hdescent : baseEnd_4707504 < baseStart_4707504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707538 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_4707538 : Nat := 118140960795 + 4707538 * 2 ^ 59
def prefixEnd_4707538 : Nat := 4983230072969 + 3 ^ 40 * 4707538 * 2
def baseEnd_4707538 : Nat := 2417229693305307969625433

theorem tailTrace_4707538 : CollatzResearch.WordTrace tailWord_4707538 prefixEnd_4707538 2417229693305307969625433 := by
  unfold tailWord_4707538
  simp only [CollatzResearch.WordTrace]
  refine ⟨42924504104850321081778817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114465344279600856218076845 42924504104850321081778817)
  ·
    refine ⟨32193378078637740811334113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42924504104850321081778817 32193378078637740811334113)
    ·
      refine ⟨24145033558978305608500585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32193378078637740811334113 24145033558978305608500585)
      ·
        refine ⟨18108775169233729206375439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24145033558978305608500585 18108775169233729206375439)
        ·
          refine ⟨27163162753850593809563159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18108775169233729206375439 27163162753850593809563159)
          ·
            refine ⟨40744744130775890714344739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27163162753850593809563159 40744744130775890714344739)
            ·
              refine ⟨61117116196163836071517109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40744744130775890714344739 61117116196163836071517109)
              ·
                refine ⟨5729729643390359631704729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61117116196163836071517109 5729729643390359631704729)
                ·
                  refine ⟨4297297232542769723778547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5729729643390359631704729 4297297232542769723778547)
                  ·
                    refine ⟨6445945848814154585667821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4297297232542769723778547 6445945848814154585667821)
                    ·
                      refine ⟨2417229693305307969625433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6445945848814154585667821 2417229693305307969625433)
                      ·
                        rfl

theorem cell23_4707538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_4707538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707538 prefixEnd_4707538 := by exact prefixLift 4707538
  have htrace : WordTrace (prefixWord ++ tailWord_4707538) baseStart_4707538 baseEnd_4707538 := by
    simpa [prefixWord, tailWord_4707538, baseEnd_4707538] using wordTrace_append hprefix tailTrace_4707538
  have hstable : (prefixWord ++ tailWord_4707538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707538).length < 2 ^ (prefixWord ++ tailWord_4707538).sum := by decide
  have hdescent : baseEnd_4707538 < baseStart_4707538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707565 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_4707565 : Nat := 118140960795 + 4707565 * 2 ^ 59
def prefixEnd_4707565 : Nat := 4983230072969 + 3 ^ 40 * 4707565 * 2
def baseEnd_4707565 : Nat := 2417243557282979363987809

theorem tailTrace_4707565 : CollatzResearch.WordTrace tailWord_4707565 prefixEnd_4707565 2417243557282979363987809 := by
  unfold tailWord_4707565
  simp only [CollatzResearch.WordTrace]
  refine ⟨171699001190303467938348149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114466000793535645292232099 171699001190303467938348149)
  ·
    refine ⟨16096781361590950119220139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171699001190303467938348149 16096781361590950119220139)
    ·
      refine ⟨24145172042386425178830209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16096781361590950119220139 24145172042386425178830209)
      ·
        refine ⟨18108879031789818884122657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24145172042386425178830209 18108879031789818884122657)
        ·
          refine ⟨13581659273842364163091993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18108879031789818884122657 13581659273842364163091993)
          ·
            refine ⟨10186244455381773122318995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13581659273842364163091993 10186244455381773122318995)
            ·
              refine ⟨15279366683072659683478493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10186244455381773122318995 15279366683072659683478493)
              ·
                refine ⟨5729762506152247381304435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15279366683072659683478493 5729762506152247381304435)
                ·
                  refine ⟨8594643759228371071956653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5729762506152247381304435 8594643759228371071956653)
                  ·
                    refine ⟨3222991409710639151983745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8594643759228371071956653 3222991409710639151983745)
                    ·
                      refine ⟨2417243557282979363987809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3222991409710639151983745 2417243557282979363987809)
                      ·
                        rfl

theorem cell23_4707565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_4707565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707565 prefixEnd_4707565 := by exact prefixLift 4707565
  have htrace : WordTrace (prefixWord ++ tailWord_4707565) baseStart_4707565 baseEnd_4707565 := by
    simpa [prefixWord, tailWord_4707565, baseEnd_4707565] using wordTrace_append hprefix tailTrace_4707565
  have hstable : (prefixWord ++ tailWord_4707565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707565).length < 2 ^ (prefixWord ++ tailWord_4707565).sum := by decide
  have hdescent : baseEnd_4707565 < baseStart_4707565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707578 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2]
def baseStart_4707578 : Nat := 118140960795 + 4707578 * 2 ^ 59
def prefixEnd_4707578 : Nat := 4983230072969 + 3 ^ 40 * 4707578 * 2
def baseEnd_4707578 : Nat := 2417250232531487813125249

theorem tailTrace_4707578 : CollatzResearch.WordTrace tailWord_4707578 prefixEnd_4707578 2417250232531487813125249 := by
  unfold tailWord_4707578
  simp only [CollatzResearch.WordTrace]
  refine ⟨42924868834814092789642847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114466316892837580772380925 42924868834814092789642847)
  ·
    refine ⟨64387303252221139184464271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42924868834814092789642847 64387303252221139184464271)
    ·
      refine ⟨96580954878331708776696407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64387303252221139184464271 96580954878331708776696407)
      ·
        refine ⟨144871432317497563165044611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96580954878331708776696407 144871432317497563165044611)
        ·
          refine ⟨217307148476246344747566917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144871432317497563165044611 217307148476246344747566917)
          ·
            refine ⟨40745090339296189640168797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217307148476246344747566917 40745090339296189640168797)
            ·
              refine ⟨15279408877236071115063299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40745090339296189640168797 15279408877236071115063299)
              ·
                refine ⟨22919113315854106672594949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15279408877236071115063299 22919113315854106672594949)
                ·
                  refine ⟨4297333746722645001111553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22919113315854106672594949 4297333746722645001111553)
                  ·
                    refine ⟨3223000310041983750833665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4297333746722645001111553 3223000310041983750833665)
                    ·
                      refine ⟨2417250232531487813125249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3223000310041983750833665 2417250232531487813125249)
                      ·
                        rfl

theorem cell23_4707578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2].length) (baseStart_4707578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707578 prefixEnd_4707578 := by exact prefixLift 4707578
  have htrace : WordTrace (prefixWord ++ tailWord_4707578) baseStart_4707578 baseEnd_4707578 := by
    simpa [prefixWord, tailWord_4707578, baseEnd_4707578] using wordTrace_append hprefix tailTrace_4707578
  have hstable : (prefixWord ++ tailWord_4707578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707578).length < 2 ^ (prefixWord ++ tailWord_4707578).sum := by decide
  have hdescent : baseEnd_4707578 < baseStart_4707578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707651 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 1, 6, 2]
def baseStart_4707651 : Nat := 118140960795 + 4707651 * 2 ^ 59
def prefixEnd_4707651 : Nat := 4983230072969 + 3 ^ 40 * 4707651 * 2
def baseEnd_4707651 : Nat := 2417287716619266027512413

theorem tailTrace_4707651 : CollatzResearch.WordTrace tailWord_4707651 prefixEnd_4707651 2417287716619266027512413 := by
  unfold tailWord_4707651
  simp only [CollatzResearch.WordTrace]
  refine ⟨171702137867991904625978807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114468091911994603083985871 171702137867991904625978807)
  ·
    refine ⟨257553206801987856938968211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171702137867991904625978807 257553206801987856938968211)
    ·
      refine ⟨386329810202981785408452317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257553206801987856938968211 386329810202981785408452317)
      ·
        refine ⟨144873678826118169528169619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 386329810202981785408452317 144873678826118169528169619)
        ·
          refine ⟨217310518239177254292254429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144873678826118169528169619 217310518239177254292254429)
          ·
            refine ⟨81491444339691470359595411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217310518239177254292254429 81491444339691470359595411)
            ·
              refine ⟨122237166509537205539393117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81491444339691470359595411 122237166509537205539393117)
              ·
                refine ⟨45838937441076452077272419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122237166509537205539393117 45838937441076452077272419)
                ·
                  refine ⟨68758406161614678115908629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45838937441076452077272419 68758406161614678115908629)
                  ·
                    refine ⟨3223050288825688036683217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68758406161614678115908629 3223050288825688036683217)
                    ·
                      refine ⟨2417287716619266027512413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3223050288825688036683217 2417287716619266027512413)
                      ·
                        rfl

theorem cell23_4707651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 6, 2].length) (baseStart_4707651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707651 prefixEnd_4707651 := by exact prefixLift 4707651
  have htrace : WordTrace (prefixWord ++ tailWord_4707651) baseStart_4707651 baseEnd_4707651 := by
    simpa [prefixWord, tailWord_4707651, baseEnd_4707651] using wordTrace_append hprefix tailTrace_4707651
  have hstable : (prefixWord ++ tailWord_4707651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707651).length < 2 ^ (prefixWord ++ tailWord_4707651).sum := by decide
  have hdescent : baseEnd_4707651 < baseStart_4707651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707668 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_4707668 : Nat := 118140960795 + 4707668 * 2 ^ 59
def prefixEnd_4707668 : Nat := 4983230072969 + 3 ^ 40 * 4707668 * 2
def baseEnd_4707668 : Nat := 2417296445790392460999835

theorem tailTrace_4707668 : CollatzResearch.WordTrace tailWord_4707668 prefixEnd_4707668 2417296445790392460999835 := by
  unfold tailWord_4707668
  simp only [CollatzResearch.WordTrace]
  refine ⟨85851378954465158264673829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114468505272620211019565105 85851378954465158264673829)
  ·
    refine ⟨16097133553962217174626343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85851378954465158264673829 16097133553962217174626343)
    ·
      refine ⟨24145700330943325761939515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16097133553962217174626343 24145700330943325761939515)
      ·
        refine ⟨36218550496414988642909273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24145700330943325761939515 36218550496414988642909273)
        ·
          refine ⟨27163912872311241482181955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36218550496414988642909273 27163912872311241482181955)
          ·
            refine ⟨40745869308466862223272933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27163912872311241482181955 40745869308466862223272933)
            ·
              refine ⟨7639850495337536666863675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40745869308466862223272933 7639850495337536666863675)
              ·
                refine ⟨11459775743006305000295513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7639850495337536666863675 11459775743006305000295513)
                ·
                  refine ⟨8594831807254728750221635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11459775743006305000295513 8594831807254728750221635)
                  ·
                    refine ⟨12892247710882093125332453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8594831807254728750221635 12892247710882093125332453)
                    ·
                      refine ⟨2417296445790392460999835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12892247710882093125332453 2417296445790392460999835)
                      ·
                        rfl

theorem cell23_4707668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_4707668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707668 prefixEnd_4707668 := by exact prefixLift 4707668
  have htrace : WordTrace (prefixWord ++ tailWord_4707668) baseStart_4707668 baseEnd_4707668 := by
    simpa [prefixWord, tailWord_4707668, baseEnd_4707668] using wordTrace_append hprefix tailTrace_4707668
  have hstable : (prefixWord ++ tailWord_4707668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707668).length < 2 ^ (prefixWord ++ tailWord_4707668).sum := by decide
  have hdescent : baseEnd_4707668 < baseStart_4707668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707674 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 10]
def baseStart_4707674 : Nat := 118140960795 + 4707674 * 2 ^ 59
def prefixEnd_4707674 : Nat := 4983230072969 + 3 ^ 40 * 4707674 * 2
def baseEnd_4707674 : Nat := 268588836297146604169423

theorem tailTrace_4707674 : CollatzResearch.WordTrace tailWord_4707674 prefixEnd_4707674 268588836297146604169423 := by
  unfold tailWord_4707674
  simp only [CollatzResearch.WordTrace]
  refine ⟨42925744186727144888516519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114468651164605719702710717 42925744186727144888516519)
  ·
    refine ⟨64388616280090717332774779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42925744186727144888516519 64388616280090717332774779)
    ·
      refine ⟨96582924420136075999162169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64388616280090717332774779 96582924420136075999162169)
      ·
        refine ⟨72437193315102056999371627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96582924420136075999162169 72437193315102056999371627)
        ·
          refine ⟨108655789972653085499057441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72437193315102056999371627 108655789972653085499057441)
          ·
            refine ⟨81491842479489814124293081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108655789972653085499057441 81491842479489814124293081)
            ·
              refine ⟨61118881859617360593219811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81491842479489814124293081 61118881859617360593219811)
              ·
                refine ⟨91678322789426040889829717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61118881859617360593219811 91678322789426040889829717)
                ·
                  refine ⟨268588836297146604169423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 91678322789426040889829717 268588836297146604169423)
                  ·
                    rfl

theorem cell23_4707674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 10].length) (baseStart_4707674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707674 prefixEnd_4707674 := by exact prefixLift 4707674
  have htrace : WordTrace (prefixWord ++ tailWord_4707674) baseStart_4707674 baseEnd_4707674 := by
    simpa [prefixWord, tailWord_4707674, baseEnd_4707674] using wordTrace_append hprefix tailTrace_4707674
  have hstable : (prefixWord ++ tailWord_4707674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707674).length < 2 ^ (prefixWord ++ tailWord_4707674).sum := by decide
  have hdescent : baseEnd_4707674 < baseStart_4707674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707738 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 1, 5]
def baseStart_4707738 : Nat := 118140960795 + 4707738 * 2 ^ 59
def prefixEnd_4707738 : Nat := 4983230072969 + 3 ^ 40 * 4707738 * 2
def baseEnd_4707738 : Nat := 805777463145402395708171

theorem tailTrace_4707738 : CollatzResearch.WordTrace tailWord_4707738 prefixEnd_4707738 805777463145402395708171 := by
  unfold tailWord_4707738
  simp only [CollatzResearch.WordTrace]
  refine ⟨42926327754669179621098967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114470207345784478989597245 42926327754669179621098967)
  ·
    refine ⟨64389491632003769431648451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42926327754669179621098967 64389491632003769431648451)
    ·
      refine ⟨96584237448005654147472677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64389491632003769431648451 96584237448005654147472677)
      ·
        refine ⟨18109544521501060152651127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96584237448005654147472677 18109544521501060152651127)
        ·
          refine ⟨27164316782251590228976691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18109544521501060152651127 27164316782251590228976691)
          ·
            refine ⟨40746475173377385343465037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27164316782251590228976691 40746475173377385343465037)
            ·
              refine ⟨15279928190016519503799389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40746475173377385343465037 15279928190016519503799389)
              ·
                refine ⟨5729973071256194813924771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15279928190016519503799389 5729973071256194813924771)
                ·
                  refine ⟨8594959606884292220887157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5729973071256194813924771 8594959606884292220887157)
                  ·
                    refine ⟨805777463145402395708171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8594959606884292220887157 805777463145402395708171)
                    ·
                      rfl

theorem cell23_4707738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_4707738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707738 prefixEnd_4707738 := by exact prefixLift 4707738
  have htrace : WordTrace (prefixWord ++ tailWord_4707738) baseStart_4707738 baseEnd_4707738 := by
    simpa [prefixWord, tailWord_4707738, baseEnd_4707738] using wordTrace_append hprefix tailTrace_4707738
  have hstable : (prefixWord ++ tailWord_4707738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707738).length < 2 ^ (prefixWord ++ tailWord_4707738).sum := by decide
  have hdescent : baseEnd_4707738 < baseStart_4707738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707742 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_4707742 : Nat := 118140960795 + 4707742 * 2 ^ 59
def prefixEnd_4707742 : Nat := 4983230072969 + 3 ^ 40 * 4707742 * 2
def baseEnd_4707742 : Nat := 268592715928758352386055

theorem tailTrace_4707742 : CollatzResearch.WordTrace tailWord_4707742 prefixEnd_4707742 268592715928758352386055 := by
  unfold tailWord_4707742
  simp only [CollatzResearch.WordTrace]
  refine ⟨21463182113832778395942685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114470304607108151445027653 21463182113832778395942685)
  ·
    refine ⟨8048693292687291898478507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21463182113832778395942685 8048693292687291898478507)
    ·
      refine ⟨12073039939030937847717761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8048693292687291898478507 12073039939030937847717761)
      ·
        refine ⟨9054779954273203385788321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12073039939030937847717761 9054779954273203385788321)
        ·
          refine ⟨6791084965704902539341241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9054779954273203385788321 6791084965704902539341241)
          ·
            refine ⟨5093313724278676904505931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6791084965704902539341241 5093313724278676904505931)
            ·
              refine ⟨7639970586418015356758897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093313724278676904505931 7639970586418015356758897)
              ·
                refine ⟨5729977939813511517569173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7639970586418015356758897 5729977939813511517569173)
                ·
                  refine ⟨268592715928758352386055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5729977939813511517569173 268592715928758352386055)
                  ·
                    rfl

theorem cell23_4707742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_4707742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707742 prefixEnd_4707742 := by exact prefixLift 4707742
  have htrace : WordTrace (prefixWord ++ tailWord_4707742) baseStart_4707742 baseEnd_4707742 := by
    simpa [prefixWord, tailWord_4707742, baseEnd_4707742] using wordTrace_append hprefix tailTrace_4707742
  have hstable : (prefixWord ++ tailWord_4707742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707742).length < 2 ^ (prefixWord ++ tailWord_4707742).sum := by decide
  have hdescent : baseEnd_4707742 < baseStart_4707742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707768 : List Nat := [2, 1, 2, 1, 2, 2, 2, 5, 2, 4]
def baseStart_4707768 : Nat := 118140960795 + 4707768 * 2 ^ 59
def prefixEnd_4707768 : Nat := 4983230072969 + 3 ^ 40 * 4707768 * 2
def baseEnd_4707768 : Nat := 805782597951947356583125

theorem tailTrace_4707768 : CollatzResearch.WordTrace tailWord_4707768 prefixEnd_4707768 805782597951947356583125 := by
  unfold tailWord_4707768
  simp only [CollatzResearch.WordTrace]
  refine ⟨85853202604284016803993979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114470936805712022405325305 85853202604284016803993979)
  ·
    refine ⟨128779803906426025205990969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85853202604284016803993979 128779803906426025205990969)
    ·
      refine ⟨96584852929819518904493227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128779803906426025205990969 96584852929819518904493227)
      ·
        refine ⟨144877279394729278356739841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96584852929819518904493227 144877279394729278356739841)
        ·
          refine ⟨108657959546046958767554881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144877279394729278356739841 108657959546046958767554881)
          ·
            refine ⟨81493469659535219075666161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108657959546046958767554881 81493469659535219075666161)
            ·
              refine ⟨61120102244651414306749621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81493469659535219075666161 61120102244651414306749621)
              ·
                refine ⟨5730009585436070091257777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61120102244651414306749621 5730009585436070091257777)
                ·
                  refine ⟨4297507189077052568443333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5730009585436070091257777 4297507189077052568443333)
                  ·
                    refine ⟨805782597951947356583125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4297507189077052568443333 805782597951947356583125)
                    ·
                      rfl

theorem cell23_4707768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_4707768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707768 prefixEnd_4707768 := by exact prefixLift 4707768
  have htrace : WordTrace (prefixWord ++ tailWord_4707768) baseStart_4707768 baseEnd_4707768 := by
    simpa [prefixWord, tailWord_4707768, baseEnd_4707768] using wordTrace_append hprefix tailTrace_4707768
  have hstable : (prefixWord ++ tailWord_4707768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707768).length < 2 ^ (prefixWord ++ tailWord_4707768).sum := by decide
  have hdescent : baseEnd_4707768 < baseStart_4707768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707798 : List Nat := [5, 2, 1, 1, 1, 2, 11]
def baseStart_4707798 : Nat := 118140960795 + 4707798 * 2 ^ 59
def prefixEnd_4707798 : Nat := 4983230072969 + 3 ^ 40 * 4707798 * 2
def baseEnd_4707798 : Nat := 29843990102166382128077

theorem tailTrace_4707798 : CollatzResearch.WordTrace tailWord_4707798 prefixEnd_4707798 29843990102166382128077 := by
  unfold tailWord_4707798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10731718712403709295723753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114471666265639565821053365 10731718712403709295723753)
  ·
    refine ⟨8048789034302781971792815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10731718712403709295723753 8048789034302781971792815)
    ·
      refine ⟨12073183551454172957689223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8048789034302781971792815 12073183551454172957689223)
      ·
        refine ⟨18109775327181259436533835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12073183551454172957689223 18109775327181259436533835)
        ·
          refine ⟨27164662990771889154800753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18109775327181259436533835 27164662990771889154800753)
          ·
            refine ⟨20373497243078916866100565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27164662990771889154800753 20373497243078916866100565)
            ·
              refine ⟨29843990102166382128077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20373497243078916866100565 29843990102166382128077)
              ·
                rfl

theorem cell23_4707798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 11].length) (baseStart_4707798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707798 prefixEnd_4707798 := by exact prefixLift 4707798
  have htrace : WordTrace (prefixWord ++ tailWord_4707798) baseStart_4707798 baseEnd_4707798 := by
    simpa [prefixWord, tailWord_4707798, baseEnd_4707798] using wordTrace_append hprefix tailTrace_4707798
  have hstable : (prefixWord ++ tailWord_4707798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707798).length < 2 ^ (prefixWord ++ tailWord_4707798).sum := by decide
  have hdescent : baseEnd_4707798 < baseStart_4707798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707829 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4707829 : Nat := 118140960795 + 4707829 * 2 ^ 59
def prefixEnd_4707829 : Nat := 4983230072969 + 3 ^ 40 * 4707829 * 2
def baseEnd_4707829 : Nat := 2417379116175766331086595

theorem tailTrace_4707829 : CollatzResearch.WordTrace tailWord_4707829 prefixEnd_4707829 2417379116175766331086595 := by
  unfold tailWord_4707829
  simp only [CollatzResearch.WordTrace]
  refine ⟨171708630061347041025958541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114472420040898027350639027 171708630061347041025958541)
  ·
    refine ⟨64390736273005140384734453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171708630061347041025958541 64390736273005140384734453)
    ·
      refine ⟨6036631525594231911068855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64390736273005140384734453 6036631525594231911068855)
      ·
        refine ⟨9054947288391347866603283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6036631525594231911068855 9054947288391347866603283)
        ·
          refine ⟨13582420932587021799904925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9054947288391347866603283 13582420932587021799904925)
          ·
            refine ⟨5093407849720133174964347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13582420932587021799904925 5093407849720133174964347)
            ·
              refine ⟨7640111774580199762446521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093407849720133174964347 7640111774580199762446521)
              ·
                refine ⟨5730083830935149821834891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7640111774580199762446521 5730083830935149821834891)
                ·
                  refine ⟨8595125746402724732752337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5730083830935149821834891 8595125746402724732752337)
                  ·
                    refine ⟨6446344309802043549564253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8595125746402724732752337 6446344309802043549564253)
                    ·
                      refine ⟨2417379116175766331086595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6446344309802043549564253 2417379116175766331086595)
                      ·
                        rfl

theorem cell23_4707829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4707829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707829 prefixEnd_4707829 := by exact prefixLift 4707829
  have htrace : WordTrace (prefixWord ++ tailWord_4707829) baseStart_4707829 baseEnd_4707829 := by
    simpa [prefixWord, tailWord_4707829, baseEnd_4707829] using wordTrace_append hprefix tailTrace_4707829
  have hstable : (prefixWord ++ tailWord_4707829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707829).length < 2 ^ (prefixWord ++ tailWord_4707829).sum := by decide
  have hdescent : baseEnd_4707829 < baseStart_4707829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707831 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_4707831 : Nat := 118140960795 + 4707831 * 2 ^ 59
def prefixEnd_4707831 : Nat := 4983230072969 + 3 ^ 40 * 4707831 * 2
def baseEnd_4707831 : Nat := 2417380143137075323261585

theorem tailTrace_4707831 : CollatzResearch.WordTrace tailWord_4707831 prefixEnd_4707831 2417380143137075323261585 := by
  unfold tailWord_4707831
  simp only [CollatzResearch.WordTrace]
  refine ⟨171708703007339795367531347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114472468671559863578354231 171708703007339795367531347)
  ·
    refine ⟨257563054511009693051297021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171708703007339795367531347 257563054511009693051297021)
    ·
      refine ⟨96586145441628634894236383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257563054511009693051297021 96586145441628634894236383)
      ·
        refine ⟨144879218162442952341354575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96586145441628634894236383 144879218162442952341354575)
        ·
          refine ⟨217318827243664428512031863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144879218162442952341354575 217318827243664428512031863)
          ·
            refine ⟨325978240865496642768047795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217318827243664428512031863 325978240865496642768047795)
            ·
              refine ⟨488967361298244964152071693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325978240865496642768047795 488967361298244964152071693)
              ·
                refine ⟨183362760486841861557026885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 488967361298244964152071693 183362760486841861557026885)
                ·
                  refine ⟨34380517591282849041942541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183362760486841861557026885 34380517591282849041942541)
                  ·
                    refine ⟨12892694096731068390728453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34380517591282849041942541 12892694096731068390728453)
                    ·
                      refine ⟨2417380143137075323261585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12892694096731068390728453 2417380143137075323261585)
                      ·
                        rfl

theorem cell23_4707831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_4707831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707831 prefixEnd_4707831 := by exact prefixLift 4707831
  have htrace : WordTrace (prefixWord ++ tailWord_4707831) baseStart_4707831 baseEnd_4707831 := by
    simpa [prefixWord, tailWord_4707831, baseEnd_4707831] using wordTrace_append hprefix tailTrace_4707831
  have hstable : (prefixWord ++ tailWord_4707831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707831).length < 2 ^ (prefixWord ++ tailWord_4707831).sum := by decide
  have hdescent : baseEnd_4707831 < baseStart_4707831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707842 : List Nat := [3, 4, 1, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_4707842 : Nat := 118140960795 + 4707842 * 2 ^ 59
def prefixEnd_4707842 : Nat := 4983230072969 + 3 ^ 40 * 4707842 * 2
def baseEnd_4707842 : Nat := 2417385791424274780224035

theorem tailTrace_4707842 : CollatzResearch.WordTrace tailWord_4707842 prefixEnd_4707842 2417385791424274780224035 := by
  unfold tailWord_4707842
  simp only [CollatzResearch.WordTrace]
  refine ⟨42927276052574986061545445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114472736140199962830787853 42927276052574986061545445)
  ·
    refine ⟨8048864259857809886539771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42927276052574986061545445 8048864259857809886539771)
    ·
      refine ⟨12073296389786714829809657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8048864259857809886539771 12073296389786714829809657)
      ·
        refine ⟨9054972292340036122357243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12073296389786714829809657 9054972292340036122357243)
        ·
          refine ⟨13582458438510054183535865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9054972292340036122357243 13582458438510054183535865)
          ·
            refine ⟨10186843828882540637651899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13582458438510054183535865 10186843828882540637651899)
            ·
              refine ⟨15280265743323810956477849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10186843828882540637651899 15280265743323810956477849)
              ·
                refine ⟨11460199307492858217358387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15280265743323810956477849 11460199307492858217358387)
                ·
                  refine ⟨17190298961239287326037581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11460199307492858217358387 17190298961239287326037581)
                  ·
                    refine ⟨6446362110464732747264093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17190298961239287326037581 6446362110464732747264093)
                    ·
                      refine ⟨2417385791424274780224035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6446362110464732747264093 2417385791424274780224035)
                      ·
                        rfl

theorem cell23_4707842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_4707842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707842 prefixEnd_4707842 := by exact prefixLift 4707842
  have htrace : WordTrace (prefixWord ++ tailWord_4707842) baseStart_4707842 baseEnd_4707842 := by
    simpa [prefixWord, tailWord_4707842, baseEnd_4707842] using wordTrace_append hprefix tailTrace_4707842
  have hstable : (prefixWord ++ tailWord_4707842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707842).length < 2 ^ (prefixWord ++ tailWord_4707842).sum := by decide
  have hdescent : baseEnd_4707842 < baseStart_4707842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707846 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_4707846 : Nat := 118140960795 + 4707846 * 2 ^ 59
def prefixEnd_4707846 : Nat := 4983230072969 + 3 ^ 40 * 4707846 * 2
def baseEnd_4707846 : Nat := 2417387845346892764574017

theorem tailTrace_4707846 : CollatzResearch.WordTrace tailWord_4707846 prefixEnd_4707846 2417387845346892764574017 := by
  unfold tailWord_4707846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5365914065696420404041481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114472833401523635286218261 5365914065696420404041481)
  ·
    refine ⟨4024435549272315303031111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5365914065696420404041481 4024435549272315303031111)
    ·
      refine ⟨6036653323908472954546667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4024435549272315303031111 6036653323908472954546667)
      ·
        refine ⟨9054979985862709431820001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6036653323908472954546667 9054979985862709431820001)
        ·
          refine ⟨6791234989397032073865001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9054979985862709431820001 6791234989397032073865001)
          ·
            refine ⟨5093426242047774055398751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6791234989397032073865001 5093426242047774055398751)
            ·
              refine ⟨7640139363071661083098127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093426242047774055398751 7640139363071661083098127)
              ·
                refine ⟨11460209044607491624647191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7640139363071661083098127 11460209044607491624647191)
                ·
                  refine ⟨17190313566911237436970787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11460209044607491624647191 17190313566911237436970787)
                  ·
                    refine ⟨25785470350366856155456181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17190313566911237436970787 25785470350366856155456181)
                    ·
                      refine ⟨2417387845346892764574017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25785470350366856155456181 2417387845346892764574017)
                      ·
                        rfl

theorem cell23_4707846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_4707846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707846 prefixEnd_4707846 := by exact prefixLift 4707846
  have htrace : WordTrace (prefixWord ++ tailWord_4707846) baseStart_4707846 baseEnd_4707846 := by
    simpa [prefixWord, tailWord_4707846, baseEnd_4707846] using wordTrace_append hprefix tailTrace_4707846
  have hstable : (prefixWord ++ tailWord_4707846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707846).length < 2 ^ (prefixWord ++ tailWord_4707846).sum := by decide
  have hdescent : baseEnd_4707846 < baseStart_4707846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707860 : List Nat := [2, 4, 3, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_4707860 : Nat := 118140960795 + 4707860 * 2 ^ 59
def prefixEnd_4707860 : Nat := 4983230072969 + 3 ^ 40 * 4707860 * 2
def baseEnd_4707860 : Nat := 2417395034076055709798953

theorem tailTrace_4707860 : CollatzResearch.WordTrace tailWord_4707860 prefixEnd_4707860 2417395034076055709798953 := by
  unfold tailWord_4707860
  simp only [CollatzResearch.WordTrace]
  refine ⟨85854880362117366660168517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114473173816156488880224689 85854880362117366660168517)
  ·
    refine ⟨16097790067897006248781597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85854880362117366660168517 16097790067897006248781597)
    ·
      refine ⟨6036671275461377343293099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16097790067897006248781597 6036671275461377343293099)
      ·
        refine ⟨9055006913192066014939649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6036671275461377343293099 9055006913192066014939649)
        ·
          refine ⟨6791255184894049511204737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9055006913192066014939649 6791255184894049511204737)
          ·
            refine ⟨5093441388670537133403553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6791255184894049511204737 5093441388670537133403553)
            ·
              refine ⟨3820081041502902850052665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5093441388670537133403553 3820081041502902850052665)
              ·
                refine ⟨2865060781127177137539499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3820081041502902850052665 2865060781127177137539499)
                ·
                  refine ⟨4297591171690765706309249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2865060781127177137539499 4297591171690765706309249)
                  ·
                    refine ⟨3223193378768074279731937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4297591171690765706309249 3223193378768074279731937)
                    ·
                      refine ⟨2417395034076055709798953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3223193378768074279731937 2417395034076055709798953)
                      ·
                        rfl

theorem cell23_4707860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_4707860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707860 prefixEnd_4707860 := by exact prefixLift 4707860
  have htrace : WordTrace (prefixWord ++ tailWord_4707860) baseStart_4707860 baseEnd_4707860 := by
    simpa [prefixWord, tailWord_4707860, baseEnd_4707860] using wordTrace_append hprefix tailTrace_4707860
  have hstable : (prefixWord ++ tailWord_4707860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707860).length < 2 ^ (prefixWord ++ tailWord_4707860).sum := by decide
  have hdescent : baseEnd_4707860 < baseStart_4707860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707868 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_4707868 : Nat := 118140960795 + 4707868 * 2 ^ 59
def prefixEnd_4707868 : Nat := 4983230072969 + 3 ^ 40 * 4707868 * 2
def baseEnd_4707868 : Nat := 2417399141921291678498915

theorem tailTrace_4707868 : CollatzResearch.WordTrace tailWord_4707868 prefixEnd_4707868 2417399141921291678498915 := by
  unfold tailWord_4707868
  simp only [CollatzResearch.WordTrace]
  refine ⟨85855026254102875343314129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114473368338803833791085505 85855026254102875343314129)
  ·
    refine ⟨64391269690577156507485597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85855026254102875343314129 64391269690577156507485597)
    ·
      refine ⟨24146726133966433690307099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64391269690577156507485597 24146726133966433690307099)
      ·
        refine ⟨36220089200949650535460649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24146726133966433690307099 36220089200949650535460649)
        ·
          refine ⟨27165066900712237901595487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36220089200949650535460649 27165066900712237901595487)
          ·
            refine ⟨40747600351068356852393231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27165066900712237901595487 40747600351068356852393231)
            ·
              refine ⟨61121400526602535278589847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40747600351068356852393231 61121400526602535278589847)
              ·
                refine ⟨91682100789903802917884771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61121400526602535278589847 91682100789903802917884771)
                ·
                  refine ⟨137523151184855704376827157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91682100789903802917884771 137523151184855704376827157)
                  ·
                    refine ⟨6446397711790111142663773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 137523151184855704376827157 6446397711790111142663773)
                    ·
                      refine ⟨2417399141921291678498915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6446397711790111142663773 2417399141921291678498915)
                      ·
                        rfl

theorem cell23_4707868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_4707868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707868 prefixEnd_4707868 := by exact prefixLift 4707868
  have htrace : WordTrace (prefixWord ++ tailWord_4707868) baseStart_4707868 baseEnd_4707868 := by
    simpa [prefixWord, tailWord_4707868, baseEnd_4707868] using wordTrace_append hprefix tailTrace_4707868
  have hstable : (prefixWord ++ tailWord_4707868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707868).length < 2 ^ (prefixWord ++ tailWord_4707868).sum := by decide
  have hdescent : baseEnd_4707868 < baseStart_4707868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707882 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_4707882 : Nat := 118140960795 + 4707882 * 2 ^ 59
def prefixEnd_4707882 : Nat := 4983230072969 + 3 ^ 40 * 4707882 * 2
def baseEnd_4707882 : Nat := 2417406330650454623723851

theorem tailTrace_4707882 : CollatzResearch.WordTrace tailWord_4707882 prefixEnd_4707882 2417406330650454623723851 := by
  unfold tailWord_4707882
  simp only [CollatzResearch.WordTrace]
  refine ⟨42927640782538757769409475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114473708753436687385091933 42927640782538757769409475)
  ·
    refine ⟨64391461173808136654114213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42927640782538757769409475 64391461173808136654114213)
    ·
      refine ⟨12073398970089025622646415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64391461173808136654114213 12073398970089025622646415)
      ·
        refine ⟨18110098455133538433969623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12073398970089025622646415 18110098455133538433969623)
        ·
          refine ⟨27165147682700307650954435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18110098455133538433969623 27165147682700307650954435)
          ·
            refine ⟨40747721524050461476431653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27165147682700307650954435 40747721524050461476431653)
            ·
              refine ⟨7640197785759461526830935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40747721524050461476431653 7640197785759461526830935)
              ·
                refine ⟨11460296678639192290246403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7640197785759461526830935 11460296678639192290246403)
                ·
                  refine ⟨17190445017958788435369605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11460296678639192290246403 17190445017958788435369605)
                  ·
                    refine ⟨3223208440867272831631801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17190445017958788435369605 3223208440867272831631801)
                    ·
                      refine ⟨2417406330650454623723851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3223208440867272831631801 2417406330650454623723851)
                      ·
                        rfl

theorem cell23_4707882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_4707882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707882 prefixEnd_4707882 := by exact prefixLift 4707882
  have htrace : WordTrace (prefixWord ++ tailWord_4707882) baseStart_4707882 baseEnd_4707882 := by
    simpa [prefixWord, tailWord_4707882, baseEnd_4707882] using wordTrace_append hprefix tailTrace_4707882
  have hstable : (prefixWord ++ tailWord_4707882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707882).length < 2 ^ (prefixWord ++ tailWord_4707882).sum := by decide
  have hdescent : baseEnd_4707882 < baseStart_4707882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707898 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3]
def baseStart_4707898 : Nat := 118140960795 + 4707898 * 2 ^ 59
def prefixEnd_4707898 : Nat := 4983230072969 + 3 ^ 40 * 4707898 * 2
def baseEnd_4707898 : Nat := 2417414546340926561123777

theorem tailTrace_4707898 : CollatzResearch.WordTrace tailWord_4707898 prefixEnd_4707898 2417414546340926561123777 := by
  unfold tailWord_4707898
  simp only [CollatzResearch.WordTrace]
  refine ⟨42927786674524266452555087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114474097798731377206813565 42927786674524266452555087)
  ·
    refine ⟨64391680011786399678832631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42927786674524266452555087 64391680011786399678832631)
    ·
      refine ⟨96587520017679599518248947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64391680011786399678832631 96587520017679599518248947)
      ·
        refine ⟨144881280026519399277373421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96587520017679599518248947 144881280026519399277373421)
        ·
          refine ⟨54330480009944774729015033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144881280026519399277373421 54330480009944774729015033)
          ·
            refine ⟨40747860007458581046761275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54330480009944774729015033 40747860007458581046761275)
            ·
              refine ⟨61121790011187871570141913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40747860007458581046761275 61121790011187871570141913)
              ·
                refine ⟨45841342508390903677606435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61121790011187871570141913 45841342508390903677606435)
                ·
                  refine ⟨68762013762586355516409653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45841342508390903677606435 68762013762586355516409653)
                  ·
                    refine ⟨6446438790242470829663405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68762013762586355516409653 6446438790242470829663405)
                    ·
                      refine ⟨2417414546340926561123777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6446438790242470829663405 2417414546340926561123777)
                      ·
                        rfl

theorem cell23_4707898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_4707898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707898 prefixEnd_4707898 := by exact prefixLift 4707898
  have htrace : WordTrace (prefixWord ++ tailWord_4707898) baseStart_4707898 baseEnd_4707898 := by
    simpa [prefixWord, tailWord_4707898, baseEnd_4707898] using wordTrace_append hprefix tailTrace_4707898
  have hstable : (prefixWord ++ tailWord_4707898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707898).length < 2 ^ (prefixWord ++ tailWord_4707898).sum := by decide
  have hdescent : baseEnd_4707898 < baseStart_4707898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707918 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_4707918 : Nat := 118140960795 + 4707918 * 2 ^ 59
def prefixEnd_4707918 : Nat := 4983230072969 + 3 ^ 40 * 4707918 * 2
def baseEnd_4707918 : Nat := 805808271984672160957895

theorem tailTrace_4707918 : CollatzResearch.WordTrace tailWord_4707918 prefixEnd_4707918 805808271984672160957895 := by
  unfold tailWord_4707918
  simp only [CollatzResearch.WordTrace]
  refine ⟨21463984519753076153243551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114474584105349739483965605 21463984519753076153243551)
  ·
    refine ⟨32195976779629614229865327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21463984519753076153243551 32195976779629614229865327)
    ·
      refine ⟨48293965169444421344797991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32195976779629614229865327 48293965169444421344797991)
      ·
        refine ⟨72440947754166632017196987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48293965169444421344797991 72440947754166632017196987)
        ·
          refine ⟨108661421631249948025795481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72440947754166632017196987 108661421631249948025795481)
          ·
            refine ⟨81496066223437461019346611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108661421631249948025795481 81496066223437461019346611)
            ·
              refine ⟨122244099335156191529019917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81496066223437461019346611 122244099335156191529019917)
              ·
                refine ⟨45841537250683571823382469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122244099335156191529019917 45841537250683571823382469)
                ·
                  refine ⟨8595288234503169716884213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45841537250683571823382469 8595288234503169716884213)
                  ·
                    refine ⟨805808271984672160957895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8595288234503169716884213 805808271984672160957895)
                    ·
                      rfl

theorem cell23_4707918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_4707918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707918 prefixEnd_4707918 := by exact prefixLift 4707918
  have htrace : WordTrace (prefixWord ++ tailWord_4707918) baseStart_4707918 baseEnd_4707918 := by
    simpa [prefixWord, tailWord_4707918, baseEnd_4707918] using wordTrace_append hprefix tailTrace_4707918
  have hstable : (prefixWord ++ tailWord_4707918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707918).length < 2 ^ (prefixWord ++ tailWord_4707918).sum := by decide
  have hdescent : baseEnd_4707918 < baseStart_4707918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707933 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4707933 : Nat := 118140960795 + 4707933 * 2 ^ 59
def prefixEnd_4707933 : Nat := 4983230072969 + 3 ^ 40 * 4707933 * 2
def baseEnd_4707933 : Nat := 2417432518163833924186117

theorem tailTrace_4707933 : CollatzResearch.WordTrace tailWord_4707933 prefixEnd_4707933 2417432518163833924186117 := by
  unfold tailWord_4707933
  simp only [CollatzResearch.WordTrace]
  refine ⟨171712423252970266787744453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114474948835313511191829635 171712423252970266787744453)
  ·
    refine ⟨32196079359931925022702085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171712423252970266787744453 32196079359931925022702085)
    ·
      refine ⟨6036764879987235941756641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32196079359931925022702085 6036764879987235941756641)
      ·
        refine ⟨4527573659990426956317481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6036764879987235941756641 4527573659990426956317481)
        ·
          refine ⟨3395680244992820217238111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4527573659990426956317481 3395680244992820217238111)
          ·
            refine ⟨5093520367489230325857167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395680244992820217238111 5093520367489230325857167)
            ·
              refine ⟨7640280551233845488785751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093520367489230325857167 7640280551233845488785751)
              ·
                refine ⟨11460420826850768233178627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7640280551233845488785751 11460420826850768233178627)
                ·
                  refine ⟨17190631240276152349767941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11460420826850768233178627 17190631240276152349767941)
                  ·
                    refine ⟨3223243357551778565581489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17190631240276152349767941 3223243357551778565581489)
                    ·
                      refine ⟨2417432518163833924186117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3223243357551778565581489 2417432518163833924186117)
                      ·
                        rfl

theorem cell23_4707933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4707933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707933 prefixEnd_4707933 := by exact prefixLift 4707933
  have htrace : WordTrace (prefixWord ++ tailWord_4707933) baseStart_4707933 baseEnd_4707933 := by
    simpa [prefixWord, tailWord_4707933, baseEnd_4707933] using wordTrace_append hprefix tailTrace_4707933
  have hstable : (prefixWord ++ tailWord_4707933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707933).length < 2 ^ (prefixWord ++ tailWord_4707933).sum := by decide
  have hdescent : baseEnd_4707933 < baseStart_4707933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707972 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_4707972 : Nat := 118140960795 + 4707972 * 2 ^ 59
def prefixEnd_4707972 : Nat := 4983230072969 + 3 ^ 40 * 4707972 * 2
def baseEnd_4707972 : Nat := 2417452543909359271598437

theorem tailTrace_4707972 : CollatzResearch.WordTrace tailWord_4707972 prefixEnd_4707972 2417452543909359271598437 := by
  unfold tailWord_4707972
  simp only [CollatzResearch.WordTrace]
  refine ⟨85856922849914488224207085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114475897133219317632276113 85856922849914488224207085)
  ·
    refine ⟨32196346068717933084077657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85856922849914488224207085 32196346068717933084077657)
    ·
      refine ⟨24147259551538449813058243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32196346068717933084077657 24147259551538449813058243)
      ·
        refine ⟨36220889327307674719587365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24147259551538449813058243 36220889327307674719587365)
        ·
          refine ⟨6791416748870189009922631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36220889327307674719587365 6791416748870189009922631)
          ·
            refine ⟨10187125123305283514883947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6791416748870189009922631 10187125123305283514883947)
            ·
              refine ⟨15280687684957925272325921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10187125123305283514883947 15280687684957925272325921)
              ·
                refine ⟨11460515763718443954244441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15280687684957925272325921 11460515763718443954244441)
                ·
                  refine ⟨8595386822788832965683331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11460515763718443954244441 8595386822788832965683331)
                  ·
                    refine ⟨12893080234183249448524997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8595386822788832965683331 12893080234183249448524997)
                    ·
                      refine ⟨2417452543909359271598437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12893080234183249448524997 2417452543909359271598437)
                      ·
                        rfl

theorem cell23_4707972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_4707972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707972 prefixEnd_4707972 := by exact prefixLift 4707972
  have htrace : WordTrace (prefixWord ++ tailWord_4707972) baseStart_4707972 baseEnd_4707972 := by
    simpa [prefixWord, tailWord_4707972, baseEnd_4707972] using wordTrace_append hprefix tailTrace_4707972
  have hstable : (prefixWord ++ tailWord_4707972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707972).length < 2 ^ (prefixWord ++ tailWord_4707972).sum := by decide
  have hdescent : baseEnd_4707972 < baseStart_4707972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707975 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_4707975 : Nat := 118140960795 + 4707975 * 2 ^ 59
def prefixEnd_4707975 : Nat := 4983230072969 + 3 ^ 40 * 4707975 * 2
def baseEnd_4707975 : Nat := 2417454084351322759860923

theorem tailTrace_4707975 : CollatzResearch.WordTrace tailWord_4707975 prefixEnd_4707975 2417454084351322759860923 := by
  unfold tailWord_4707975
  simp only [CollatzResearch.WordTrace]
  refine ⟨171713955118818107960773379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114475970079212071973848919 171713955118818107960773379)
  ·
    refine ⟨257570932678227161941160069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171713955118818107960773379 257570932678227161941160069)
    ·
      refine ⟨48294549877167592863967513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257570932678227161941160069 48294549877167592863967513)
      ·
        refine ⟨36220912407875694647975635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48294549877167592863967513 36220912407875694647975635)
        ·
          refine ⟨54331368611813541971963453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36220912407875694647975635 54331368611813541971963453)
          ·
            refine ⟨20374263229430078239486295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54331368611813541971963453 20374263229430078239486295)
            ·
              refine ⟨30561394844145117359229443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20374263229430078239486295 30561394844145117359229443)
              ·
                refine ⟨45842092266217676038844165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30561394844145117359229443 45842092266217676038844165)
                ·
                  refine ⟨8595392299915814257283281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45842092266217676038844165 8595392299915814257283281)
                  ·
                    refine ⟨6446544224936860692962461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8595392299915814257283281 6446544224936860692962461)
                    ·
                      refine ⟨2417454084351322759860923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6446544224936860692962461 2417454084351322759860923)
                      ·
                        rfl

theorem cell23_4707975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_4707975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707975 prefixEnd_4707975 := by exact prefixLift 4707975
  have htrace : WordTrace (prefixWord ++ tailWord_4707975) baseStart_4707975 baseEnd_4707975 := by
    simpa [prefixWord, tailWord_4707975, baseEnd_4707975] using wordTrace_append hprefix tailTrace_4707975
  have hstable : (prefixWord ++ tailWord_4707975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707975).length < 2 ^ (prefixWord ++ tailWord_4707975).sum := by decide
  have hdescent : baseEnd_4707975 < baseStart_4707975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4707982 : List Nat := [4, 1, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_4707982 : Nat := 118140960795 + 4707982 * 2 ^ 59
def prefixEnd_4707982 : Nat := 4983230072969 + 3 ^ 40 * 4707982 * 2
def baseEnd_4707982 : Nat := 805819226238634744157797

theorem tailTrace_4707982 : CollatzResearch.WordTrace tailWord_4707982 prefixEnd_4707982 805819226238634744157797 := by
  unfold tailWord_4707982
  simp only [CollatzResearch.WordTrace]
  refine ⟨21464276303724093519534775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114476140286528498770852133 21464276303724093519534775)
  ·
    refine ⟨32196414455586140279302163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21464276303724093519534775 32196414455586140279302163)
    ·
      refine ⟨48294621683379210418953245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32196414455586140279302163 48294621683379210418953245)
      ·
        refine ⟨18110483131267203907107467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48294621683379210418953245 18110483131267203907107467)
        ·
          refine ⟨27165724696900805860661201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18110483131267203907107467 27165724696900805860661201)
          ·
            refine ⟨20374293522675604395495901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27165724696900805860661201 20374293522675604395495901)
            ·
              refine ⟨7640360071003351648310963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20374293522675604395495901 7640360071003351648310963)
              ·
                refine ⟨11460540106505027472466445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7640360071003351648310963 11460540106505027472466445)
                ·
                  refine ⟨4297702539939385302174917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11460540106505027472466445 4297702539939385302174917)
                  ·
                    refine ⟨805819226238634744157797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4297702539939385302174917 805819226238634744157797)
                    ·
                      rfl

theorem cell23_4707982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_4707982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4707982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4707982 prefixEnd_4707982 := by exact prefixLift 4707982
  have htrace : WordTrace (prefixWord ++ tailWord_4707982) baseStart_4707982 baseEnd_4707982 := by
    simpa [prefixWord, tailWord_4707982, baseEnd_4707982] using wordTrace_append hprefix tailTrace_4707982
  have hstable : (prefixWord ++ tailWord_4707982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4707982).length < 2 ^ (prefixWord ++ tailWord_4707982).sum := by decide
  have hdescent : baseEnd_4707982 < baseStart_4707982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4707982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708025 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 1, 5]
def baseStart_4708025 : Nat := 118140960795 + 4708025 * 2 ^ 59
def prefixEnd_4708025 : Nat := 4983230072969 + 3 ^ 40 * 4708025 * 2
def baseEnd_4708025 : Nat := 805826586128015854745231

theorem tailTrace_4708025 : CollatzResearch.WordTrace tailWord_4708025 prefixEnd_4708025 805826586128015854745231 := by
  unfold tailWord_4708025
  simp only [CollatzResearch.WordTrace]
  refine ⟨171715778768636966500093529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114477185845757977666729019 171715778768636966500093529)
  ·
    refine ⟨128786834076477724875070147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171715778768636966500093529 128786834076477724875070147)
    ·
      refine ⟨193180251114716587312605221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128786834076477724875070147 193180251114716587312605221)
      ·
        refine ⟨36221297084009360121113479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193180251114716587312605221 36221297084009360121113479)
        ·
          refine ⟨54331945626014040181670219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36221297084009360121113479 54331945626014040181670219)
          ·
            refine ⟨81497918439021060272505329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54331945626014040181670219 81497918439021060272505329)
            ·
              refine ⟨61123438829265795204378997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81497918439021060272505329 61123438829265795204378997)
              ·
                refine ⟨5730322390243668300410531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61123438829265795204378997 5730322390243668300410531)
                ·
                  refine ⟨8595483585365502450615797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5730322390243668300410531 8595483585365502450615797)
                  ·
                    refine ⟨805826586128015854745231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8595483585365502450615797 805826586128015854745231)
                    ·
                      rfl

theorem cell23_4708025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 5].length) (baseStart_4708025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708025 prefixEnd_4708025 := by exact prefixLift 4708025
  have htrace : WordTrace (prefixWord ++ tailWord_4708025) baseStart_4708025 baseEnd_4708025 := by
    simpa [prefixWord, tailWord_4708025, baseEnd_4708025] using wordTrace_append hprefix tailTrace_4708025
  have hstable : (prefixWord ++ tailWord_4708025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708025).length < 2 ^ (prefixWord ++ tailWord_4708025).sum := by decide
  have hdescent : baseEnd_4708025 < baseStart_4708025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708032 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 2, 3, 2]
def baseStart_4708032 : Nat := 118140960795 + 4708032 * 2 ^ 59
def prefixEnd_4708032 : Nat := 4983230072969 + 3 ^ 40 * 4708032 * 2
def baseEnd_4708032 : Nat := 2417483352748629036848161

theorem tailTrace_4708032 : CollatzResearch.WordTrace tailWord_4708032 prefixEnd_4708032 2417483352748629036848161 := by
  unfold tailWord_4708032
  simp only [CollatzResearch.WordTrace]
  refine ⟨85858017039805803347799175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114477356053074404463732233 85858017039805803347799175)
  ·
    refine ⟨128787025559708705021698763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85858017039805803347799175 128787025559708705021698763)
    ·
      refine ⟨193180538339563057532548145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128787025559708705021698763 193180538339563057532548145)
      ·
        refine ⟨144885403754672293149411109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193180538339563057532548145 144885403754672293149411109)
        ·
          refine ⟨27166013204001054965514583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144885403754672293149411109 27166013204001054965514583)
          ·
            refine ⟨40749019806001582448271875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27166013204001054965514583 40749019806001582448271875)
            ·
              refine ⟨61123529709002373672407813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40749019806001582448271875 61123529709002373672407813)
              ·
                refine ⟨11460661820437945063576465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61123529709002373672407813 11460661820437945063576465)
                ·
                  refine ⟨8595496365328458797682349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11460661820437945063576465 8595496365328458797682349)
                  ·
                    refine ⟨3223311136998172049130881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8595496365328458797682349 3223311136998172049130881)
                    ·
                      refine ⟨2417483352748629036848161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3223311136998172049130881 2417483352748629036848161)
                      ·
                        rfl

theorem cell23_4708032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 2, 3, 2].length) (baseStart_4708032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708032 prefixEnd_4708032 := by exact prefixLift 4708032
  have htrace : WordTrace (prefixWord ++ tailWord_4708032) baseStart_4708032 baseEnd_4708032 := by
    simpa [prefixWord, tailWord_4708032, baseEnd_4708032] using wordTrace_append hprefix tailTrace_4708032
  have hstable : (prefixWord ++ tailWord_4708032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708032).length < 2 ^ (prefixWord ++ tailWord_4708032).sum := by decide
  have hdescent : baseEnd_4708032 < baseStart_4708032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708039 : List Nat := [1, 1, 4, 1, 1, 1, 5, 4, 1, 1, 3]
def baseStart_4708039 : Nat := 118140960795 + 4708039 * 2 ^ 59
def prefixEnd_4708039 : Nat := 4983230072969 + 3 ^ 40 * 4708039 * 2
def baseEnd_4708039 : Nat := 2417486947113210509460629

theorem tailTrace_4708039 : CollatzResearch.WordTrace tailWord_4708039 prefixEnd_4708039 2417486947113210509460629 := by
  unfold tailWord_4708039
  simp only [CollatzResearch.WordTrace]
  refine ⟨171716289390586246891103171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114477526260390831260735447 171716289390586246891103171)
  ·
    refine ⟨257574434085879370336654757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171716289390586246891103171 257574434085879370336654757)
    ·
      refine ⟨48295206391102381938122767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257574434085879370336654757 48295206391102381938122767)
      ·
        refine ⟨72442809586653572907184151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48295206391102381938122767 72442809586653572907184151)
        ·
          refine ⟨108664214379980359360776227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72442809586653572907184151 108664214379980359360776227)
          ·
            refine ⟨162996321569970539041164341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108664214379980359360776227 162996321569970539041164341)
            ·
              refine ⟨15280905147184738035109157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 162996321569970539041164341 15280905147184738035109157)
              ·
                refine ⟨2865169715097138381582967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15280905147184738035109157 2865169715097138381582967)
                ·
                  refine ⟨4297754572645707572374451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2865169715097138381582967 4297754572645707572374451)
                  ·
                    refine ⟨6446631858968561358561677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4297754572645707572374451 6446631858968561358561677)
                    ·
                      refine ⟨2417486947113210509460629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6446631858968561358561677 2417486947113210509460629)
                      ·
                        rfl

theorem cell23_4708039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_4708039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708039 prefixEnd_4708039 := by exact prefixLift 4708039
  have htrace : WordTrace (prefixWord ++ tailWord_4708039) baseStart_4708039 baseEnd_4708039 := by
    simpa [prefixWord, tailWord_4708039, baseEnd_4708039] using wordTrace_append hprefix tailTrace_4708039
  have hstable : (prefixWord ++ tailWord_4708039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708039).length < 2 ^ (prefixWord ++ tailWord_4708039).sum := by decide
  have hdescent : baseEnd_4708039 < baseStart_4708039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708055 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 1, 6]
def baseStart_4708055 : Nat := 118140960795 + 4708055 * 2 ^ 59
def prefixEnd_4708055 : Nat := 4983230072969 + 3 ^ 40 * 4708055 * 2
def baseEnd_4708055 : Nat := 805831720934560815620185

theorem tailTrace_4708055 : CollatzResearch.WordTrace tailWord_4708055 prefixEnd_4708055 805831720934560815620185 := by
  unfold tailWord_4708055
  simp only [CollatzResearch.WordTrace]
  refine ⟨171716872958528281623685619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114477915305685521082457079 171716872958528281623685619)
  ·
    refine ⟨257575309437792422435528429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171716872958528281623685619 257575309437792422435528429)
    ·
      refine ⟨96590741039172158413323161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257575309437792422435528429 96590741039172158413323161)
      ·
        refine ⟨72443055779379118809992371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96590741039172158413323161 72443055779379118809992371)
        ·
          refine ⟨108664583669068678214988557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72443055779379118809992371 108664583669068678214988557)
          ·
            refine ⟨40749218875900754330620709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108664583669068678214988557 40749218875900754330620709)
            ·
              refine ⟨7640478539231391436991383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40749218875900754330620709 7640478539231391436991383)
              ·
                refine ⟨11460717808847087155487075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7640478539231391436991383 11460717808847087155487075)
                ·
                  refine ⟨17191076713270630733230613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11460717808847087155487075 17191076713270630733230613)
                  ·
                    refine ⟨805831720934560815620185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17191076713270630733230613 805831720934560815620185)
                    ·
                      rfl

theorem cell23_4708055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_4708055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708055 prefixEnd_4708055 := by exact prefixLift 4708055
  have htrace : WordTrace (prefixWord ++ tailWord_4708055) baseStart_4708055 baseEnd_4708055 := by
    simpa [prefixWord, tailWord_4708055, baseEnd_4708055] using wordTrace_append hprefix tailTrace_4708055
  have hstable : (prefixWord ++ tailWord_4708055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708055).length < 2 ^ (prefixWord ++ tailWord_4708055).sum := by decide
  have hdescent : baseEnd_4708055 < baseStart_4708055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708075 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 4]
def baseStart_4708075 : Nat := 118140960795 + 4708075 * 2 ^ 59
def prefixEnd_4708075 : Nat := 4983230072969 + 3 ^ 40 * 4708075 * 2
def baseEnd_4708075 : Nat := 2417505432416772368610463

theorem tailTrace_4708075 : CollatzResearch.WordTrace tailWord_4708075 prefixEnd_4708075 2417505432416772368610463 := by
  unfold tailWord_4708075
  simp only [CollatzResearch.WordTrace]
  refine ⟨171717602418455825039413679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114478401612303883359609119 171717602418455825039413679)
  ·
    refine ⟨257576403627683737559120519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171717602418455825039413679 257576403627683737559120519)
    ·
      refine ⟨386364605441525606338680779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257576403627683737559120519 386364605441525606338680779)
      ·
        refine ⟨579546908162288409508021169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386364605441525606338680779 579546908162288409508021169)
        ·
          refine ⟨434660181121716307131015877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 579546908162288409508021169 434660181121716307131015877)
          ·
            refine ⟨81498783960321807587065477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 434660181121716307131015877 81498783960321807587065477)
            ·
              refine ⟨15281021992560338922574777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81498783960321807587065477 15281021992560338922574777)
              ·
                refine ⟨11460766494420254191931083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15281021992560338922574777 11460766494420254191931083)
                ·
                  refine ⟨17191149741630381287896625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11460766494420254191931083 17191149741630381287896625)
                  ·
                    refine ⟨12893362306222785965922469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17191149741630381287896625 12893362306222785965922469)
                    ·
                      refine ⟨2417505432416772368610463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12893362306222785965922469 2417505432416772368610463)
                      ·
                        rfl

theorem cell23_4708075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 1, 2, 4].length) (baseStart_4708075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708075 prefixEnd_4708075 := by exact prefixLift 4708075
  have htrace : WordTrace (prefixWord ++ tailWord_4708075) baseStart_4708075 baseEnd_4708075 := by
    simpa [prefixWord, tailWord_4708075, baseEnd_4708075] using wordTrace_append hprefix tailTrace_4708075
  have hstable : (prefixWord ++ tailWord_4708075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708075).length < 2 ^ (prefixWord ++ tailWord_4708075).sum := by decide
  have hdescent : baseEnd_4708075 < baseStart_4708075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708095 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 3]
def baseStart_4708095 : Nat := 118140960795 + 4708095 * 2 ^ 59
def prefixEnd_4708095 : Nat := 4983230072969 + 3 ^ 40 * 4708095 * 2
def baseEnd_4708095 : Nat := 2417515702029862290360371

theorem tailTrace_4708095 : CollatzResearch.WordTrace tailWord_4708095 prefixEnd_4708095 2417515702029862290360371 := by
  unfold tailWord_4708095
  simp only [CollatzResearch.WordTrace]
  refine ⟨171718331878383368455141739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114478887918922245636761159 171718331878383368455141739)
  ·
    refine ⟨257577497817575052682712609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171718331878383368455141739 257577497817575052682712609)
    ·
      refine ⟨193183123363181289512034457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257577497817575052682712609 193183123363181289512034457)
      ·
        refine ⟨144887342522385967134025843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193183123363181289512034457 144887342522385967134025843)
        ·
          refine ⟨217331013783578950701038765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144887342522385967134025843 217331013783578950701038765)
          ·
            refine ⟨81499130168842106512889537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217331013783578950701038765 81499130168842106512889537)
            ·
              refine ⟨61124347626631579884667153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81499130168842106512889537 61124347626631579884667153)
              ·
                refine ⟨45843260719973684913500365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61124347626631579884667153 45843260719973684913500365)
                ·
                  refine ⟨17191222769990131842562637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45843260719973684913500365 17191222769990131842562637)
                  ·
                    refine ⟨6446708538746299440960989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17191222769990131842562637 6446708538746299440960989)
                    ·
                      refine ⟨2417515702029862290360371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6446708538746299440960989 2417515702029862290360371)
                      ·
                        rfl

theorem cell23_4708095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_4708095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708095 prefixEnd_4708095 := by exact prefixLift 4708095
  have htrace : WordTrace (prefixWord ++ tailWord_4708095) baseStart_4708095 baseEnd_4708095 := by
    simpa [prefixWord, tailWord_4708095, baseEnd_4708095] using wordTrace_append hprefix tailTrace_4708095
  have hstable : (prefixWord ++ tailWord_4708095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708095).length < 2 ^ (prefixWord ++ tailWord_4708095).sum := by decide
  have hdescent : baseEnd_4708095 < baseStart_4708095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708165 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 4]
def baseStart_4708165 : Nat := 118140960795 + 4708165 * 2 ^ 59
def prefixEnd_4708165 : Nat := 4983230072969 + 3 ^ 40 * 4708165 * 2
def baseEnd_4708165 : Nat := 2417551645675677016485049

theorem tailTrace_4708165 : CollatzResearch.WordTrace tailWord_4708165 prefixEnd_4708165 2417551645675677016485049 := by
  unfold tailWord_4708165
  simp only [CollatzResearch.WordTrace]
  refine ⟨171720884988129770410189949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114480589992086513606793299 171720884988129770410189949)
  ·
    refine ⟨64395331870548663903821231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171720884988129770410189949 64395331870548663903821231)
    ·
      refine ⟨96592997805822995855731847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64395331870548663903821231 96592997805822995855731847)
      ·
        refine ⟨144889496708734493783597771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96592997805822995855731847 144889496708734493783597771)
        ·
          refine ⟨217334245063101740675396657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144889496708734493783597771 217334245063101740675396657)
          ·
            refine ⟨163000683797326305506547493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217334245063101740675396657 163000683797326305506547493)
            ·
              refine ⟨30562628211998682282477655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163000683797326305506547493 30562628211998682282477655)
              ·
                refine ⟨45843942317998023423716483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30562628211998682282477655 45843942317998023423716483)
                ·
                  refine ⟨68765913476997035135574725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45843942317998023423716483 68765913476997035135574725)
                  ·
                    refine ⟨12893608776936944087920261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68765913476997035135574725 12893608776936944087920261)
                    ·
                      refine ⟨2417551645675677016485049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12893608776936944087920261 2417551645675677016485049)
                      ·
                        rfl

theorem cell23_4708165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_4708165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708165 prefixEnd_4708165 := by exact prefixLift 4708165
  have htrace : WordTrace (prefixWord ++ tailWord_4708165) baseStart_4708165 baseEnd_4708165 := by
    simpa [prefixWord, tailWord_4708165, baseEnd_4708165] using wordTrace_append hprefix tailTrace_4708165
  have hstable : (prefixWord ++ tailWord_4708165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708165).length < 2 ^ (prefixWord ++ tailWord_4708165).sum := by decide
  have hdescent : baseEnd_4708165 < baseStart_4708165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708173 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_4708173 : Nat := 118140960795 + 4708173 * 2 ^ 59
def prefixEnd_4708173 : Nat := 4983230072969 + 3 ^ 40 * 4708173 * 2
def baseEnd_4708173 : Nat := 2417555753520912985185013

theorem tailTrace_4708173 : CollatzResearch.WordTrace tailWord_4708173 prefixEnd_4708173 2417555753520912985185013 := by
  unfold tailWord_4708173
  simp only [CollatzResearch.WordTrace]
  refine ⟨171721176772100787776481173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114480784514733858517654115 171721176772100787776481173)
  ·
    refine ⟨8049430161192224427022555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 171721176772100787776481173 8049430161192224427022555)
    ·
      refine ⟨12074145241788336640533833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8049430161192224427022555 12074145241788336640533833)
      ·
        refine ⟨9055608931341252480400375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12074145241788336640533833 9055608931341252480400375)
        ·
          refine ⟨13583413397011878720600563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9055608931341252480400375 13583413397011878720600563)
          ·
            refine ⟨20375120095517818080900845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13583413397011878720600563 20375120095517818080900845)
            ·
              refine ⟨7640670035819181780337817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20375120095517818080900845 7640670035819181780337817)
              ·
                refine ⟨5730502526864386335253363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7640670035819181780337817 5730502526864386335253363)
                ·
                  refine ⟨8595753790296579502880045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5730502526864386335253363 8595753790296579502880045)
                  ·
                    refine ⟨3223407671361217313580017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8595753790296579502880045 3223407671361217313580017)
                    ·
                      refine ⟨2417555753520912985185013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3223407671361217313580017 2417555753520912985185013)
                      ·
                        rfl

theorem cell23_4708173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_4708173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708173 prefixEnd_4708173 := by exact prefixLift 4708173
  have htrace : WordTrace (prefixWord ++ tailWord_4708173) baseStart_4708173 baseEnd_4708173 := by
    simpa [prefixWord, tailWord_4708173, baseEnd_4708173] using wordTrace_append hprefix tailTrace_4708173
  have hstable : (prefixWord ++ tailWord_4708173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708173).length < 2 ^ (prefixWord ++ tailWord_4708173).sum := by decide
  have hdescent : baseEnd_4708173 < baseStart_4708173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708254 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4708254 : Nat := 118140960795 + 4708254 * 2 ^ 59
def prefixEnd_4708254 : Nat := 4983230072969 + 3 ^ 40 * 4708254 * 2
def baseEnd_4708254 : Nat := 2417597345453927168272141

theorem tailTrace_4708254 : CollatzResearch.WordTrace tailWord_4708254 prefixEnd_4708254 2417597345453927168272141 := by
  unfold tailWord_4708254
  simp only [CollatzResearch.WordTrace]
  refine ⟨21465516385600917326272477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114482754056538225740119877 21465516385600917326272477)
  ·
    refine ⟨8049568644600343997352179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21465516385600917326272477 8049568644600343997352179)
    ·
      refine ⟨12074352966900515996028269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8049568644600343997352179 12074352966900515996028269)
      ·
        refine ⟨4527882362587693498510601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12074352966900515996028269 4527882362587693498510601)
        ·
          refine ⟨3395911771940770123882951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4527882362587693498510601 3395911771940770123882951)
          ·
            refine ⟨5093867657911155185824427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3395911771940770123882951 5093867657911155185824427)
            ·
              refine ⟨7640801486866732778736641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5093867657911155185824427 7640801486866732778736641)
              ·
                refine ⟨5730601115150049584052481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7640801486866732778736641 5730601115150049584052481)
                ·
                  refine ⟨4297950836362537188039361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5730601115150049584052481 4297950836362537188039361)
                  ·
                    refine ⟨3223463127271902891029521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4297950836362537188039361 3223463127271902891029521)
                    ·
                      refine ⟨2417597345453927168272141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3223463127271902891029521 2417597345453927168272141)
                      ·
                        rfl

theorem cell23_4708254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4708254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708254 prefixEnd_4708254 := by exact prefixLift 4708254
  have htrace : WordTrace (prefixWord ++ tailWord_4708254) baseStart_4708254 baseEnd_4708254 := by
    simpa [prefixWord, tailWord_4708254, baseEnd_4708254] using wordTrace_append hprefix tailTrace_4708254
  have hstable : (prefixWord ++ tailWord_4708254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708254).length < 2 ^ (prefixWord ++ tailWord_4708254).sum := by decide
  have hdescent : baseEnd_4708254 < baseStart_4708254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708349 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 2, 6, 2]
def baseStart_4708349 : Nat := 118140960795 + 4708349 * 2 ^ 59
def prefixEnd_4708349 : Nat := 4983230072969 + 3 ^ 40 * 4708349 * 2
def baseEnd_4708349 : Nat := 2417646126116104296584203

theorem tailTrace_4708349 : CollatzResearch.WordTrace tailWord_4708349 prefixEnd_4708349 2417646126116104296584203 := by
  unfold tailWord_4708349
  simp only [CollatzResearch.WordTrace]
  refine ⟨171727596019463169834888101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114485064012975446556592067 171727596019463169834888101)
  ·
    refine ⟨32198924253649344344041519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171727596019463169834888101 32198924253649344344041519)
    ·
      refine ⟨48298386380474016516062279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32198924253649344344041519 48298386380474016516062279)
      ·
        refine ⟨72447579570711024774093419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48298386380474016516062279 72447579570711024774093419)
        ·
          refine ⟨108671369356066537161140129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72447579570711024774093419 108671369356066537161140129)
          ·
            refine ⟨81503527017049902870855097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108671369356066537161140129 81503527017049902870855097)
            ·
              refine ⟨61127645262787427153141323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81503527017049902870855097 61127645262787427153141323)
              ·
                refine ⟨91691467894181140729711985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61127645262787427153141323 91691467894181140729711985)
                ·
                  refine ⟨68768600920635855547283989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91691467894181140729711985 68768600920635855547283989)
                  ·
                    refine ⟨3223528168154805728778937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68768600920635855547283989 3223528168154805728778937)
                    ·
                      refine ⟨2417646126116104296584203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3223528168154805728778937 2417646126116104296584203)
                      ·
                        rfl

theorem cell23_4708349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 6, 2].length) (baseStart_4708349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708349 prefixEnd_4708349 := by exact prefixLift 4708349
  have htrace : WordTrace (prefixWord ++ tailWord_4708349) baseStart_4708349 baseEnd_4708349 := by
    simpa [prefixWord, tailWord_4708349, baseEnd_4708349] using wordTrace_append hprefix tailTrace_4708349
  have hstable : (prefixWord ++ tailWord_4708349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708349).length < 2 ^ (prefixWord ++ tailWord_4708349).sum := by decide
  have hdescent : baseEnd_4708349 < baseStart_4708349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708359 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 1, 6]
def baseStart_4708359 : Nat := 118140960795 + 4708359 * 2 ^ 59
def prefixEnd_4708359 : Nat := 4983230072969 + 3 ^ 40 * 4708359 * 2
def baseEnd_4708359 : Nat := 805883753640883085819719

theorem tailTrace_4708359 : CollatzResearch.WordTrace tailWord_4708359 prefixEnd_4708359 805883753640883085819719 := by
  unfold tailWord_4708359
  simp only [CollatzResearch.WordTrace]
  refine ⟨171727960749426941542752131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114485307166284627695168087 171727960749426941542752131)
  ·
    refine ⟨257591941124140412314128197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171727960749426941542752131 257591941124140412314128197)
    ·
      refine ⟨48298488960776327308899037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257591941124140412314128197 48298488960776327308899037)
      ·
        refine ⟨18111933360291122740837139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48298488960776327308899037 18111933360291122740837139)
        ·
          refine ⟨27167900040436684111255709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18111933360291122740837139 27167900040436684111255709)
          ·
            refine ⟨10187962515163756541720891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27167900040436684111255709 10187962515163756541720891)
            ·
              refine ⟨15281943772745634812581337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10187962515163756541720891 15281943772745634812581337)
              ·
                refine ⟨11461457829559226109436003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15281943772745634812581337 11461457829559226109436003)
                ·
                  refine ⟨17192186744338839164154005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11461457829559226109436003 17192186744338839164154005)
                  ·
                    refine ⟨805883753640883085819719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17192186744338839164154005 805883753640883085819719)
                    ·
                      rfl

theorem cell23_4708359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_4708359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708359 prefixEnd_4708359 := by exact prefixLift 4708359
  have htrace : WordTrace (prefixWord ++ tailWord_4708359) baseStart_4708359 baseEnd_4708359 := by
    simpa [prefixWord, tailWord_4708359, baseEnd_4708359] using wordTrace_append hprefix tailTrace_4708359
  have hstable : (prefixWord ++ tailWord_4708359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708359).length < 2 ^ (prefixWord ++ tailWord_4708359).sum := by decide
  have hdescent : baseEnd_4708359 < baseStart_4708359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708376 : List Nat := [2, 1, 2, 3, 2, 1, 4, 2, 2, 4]
def baseStart_4708376 : Nat := 118140960795 + 4708376 * 2 ^ 59
def prefixEnd_4708376 : Nat := 4983230072969 + 3 ^ 40 * 4708376 * 2
def baseEnd_4708376 : Nat := 805886663364591896982193

theorem tailTrace_4708376 : CollatzResearch.WordTrace tailWord_4708376 prefixEnd_4708376 805886663364591896982193 := by
  unfold tailWord_4708376
  simp only [CollatzResearch.WordTrace]
  refine ⟨85864290395182676723060491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114485720526910235630747321 85864290395182676723060491)
  ·
    refine ⟨128796435592774015084590737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85864290395182676723060491 128796435592774015084590737)
    ·
      refine ⟨96597326694580511313443053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128796435592774015084590737 96597326694580511313443053)
      ·
        refine ⟨36223997510467691742541145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96597326694580511313443053 36223997510467691742541145)
        ·
          refine ⟨27167998132850768806905859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36223997510467691742541145 27167998132850768806905859)
          ·
            refine ⟨40751997199276153210358789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27167998132850768806905859 40751997199276153210358789)
            ·
              refine ⟨7640999474864278726942273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40751997199276153210358789 7640999474864278726942273)
              ·
                refine ⟨5730749606148209045206705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7640999474864278726942273 5730749606148209045206705)
                ·
                  refine ⟨4298062204611156783905029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5730749606148209045206705 4298062204611156783905029)
                  ·
                    refine ⟨805886663364591896982193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4298062204611156783905029 805886663364591896982193)
                    ·
                      rfl

theorem cell23_4708376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_4708376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708376 prefixEnd_4708376 := by exact prefixLift 4708376
  have htrace : WordTrace (prefixWord ++ tailWord_4708376) baseStart_4708376 baseEnd_4708376 := by
    simpa [prefixWord, tailWord_4708376, baseEnd_4708376] using wordTrace_append hprefix tailTrace_4708376
  have hstable : (prefixWord ++ tailWord_4708376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708376).length < 2 ^ (prefixWord ++ tailWord_4708376).sum := by decide
  have hdescent : baseEnd_4708376 < baseStart_4708376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708389 : List Nat := [1, 3, 1, 2, 2, 5, 1, 8]
def baseStart_4708389 : Nat := 118140960795 + 4708389 * 2 ^ 59
def prefixEnd_4708389 : Nat := 4983230072969 + 3 ^ 40 * 4708389 * 2
def baseEnd_4708389 : Nat := 89543209827492005188297

theorem tailTrace_4708389 : CollatzResearch.WordTrace tailWord_4708389 prefixEnd_4708389 89543209827492005188297 := by
  unfold tailWord_4708389
  simp only [CollatzResearch.WordTrace]
  refine ⟨171729054939318256666344221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114486036626212171110896147 171729054939318256666344221)
  ·
    refine ⟨64398395602244346249879083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171729054939318256666344221 64398395602244346249879083)
    ·
      refine ⟨96597593403366519374818625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64398395602244346249879083 96597593403366519374818625)
      ·
        refine ⟨72448195052524889531113969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96597593403366519374818625 72448195052524889531113969)
        ·
          refine ⟨54336146289393667148335477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72448195052524889531113969 54336146289393667148335477)
          ·
            refine ⟨5094013714630656295156451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54336146289393667148335477 5094013714630656295156451)
            ·
              refine ⟨7641020571945984442734677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5094013714630656295156451 7641020571945984442734677)
              ·
                refine ⟨89543209827492005188297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7641020571945984442734677 89543209827492005188297)
                ·
                  rfl

theorem cell23_4708389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 8].length) (baseStart_4708389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708389 prefixEnd_4708389 := by exact prefixLift 4708389
  have htrace : WordTrace (prefixWord ++ tailWord_4708389) baseStart_4708389 baseEnd_4708389 := by
    simpa [prefixWord, tailWord_4708389, baseEnd_4708389] using wordTrace_append hprefix tailTrace_4708389
  have hstable : (prefixWord ++ tailWord_4708389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708389).length < 2 ^ (prefixWord ++ tailWord_4708389).sum := by decide
  have hdescent : baseEnd_4708389 < baseStart_4708389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708406 : List Nat := [5, 1, 2, 1, 1, 1, 5, 7]
def baseStart_4708406 : Nat := 118140960795 + 4708406 * 2 ^ 59
def prefixEnd_4708406 : Nat := 4983230072969 + 3 ^ 40 * 4708406 * 2
def baseEnd_4708406 : Nat := 89543533130126317539683

theorem tailTrace_4708406 : CollatzResearch.WordTrace tailWord_4708406 prefixEnd_4708406 89543533130126317539683 := by
  unfold tailWord_4708406
  simp only [CollatzResearch.WordTrace]
  refine ⟨10733104686266041785607067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114486449986837779046475381 10733104686266041785607067)
  ·
    refine ⟨16099657029399062678410601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10733104686266041785607067 16099657029399062678410601)
    ·
      refine ⟨12074742772049297008807951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16099657029399062678410601 12074742772049297008807951)
      ·
        refine ⟨18112114158073945513211927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12074742772049297008807951 18112114158073945513211927)
        ·
          refine ⟨27168171237110918269817891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18112114158073945513211927 27168171237110918269817891)
          ·
            refine ⟨40752256855666377404726837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27168171237110918269817891 40752256855666377404726837)
            ·
              refine ⟨3820524080218722881693141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40752256855666377404726837 3820524080218722881693141)
              ·
                refine ⟨89543533130126317539683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3820524080218722881693141 89543533130126317539683)
                ·
                  rfl

theorem cell23_4708406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_4708406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708406 prefixEnd_4708406 := by exact prefixLift 4708406
  have htrace : WordTrace (prefixWord ++ tailWord_4708406) baseStart_4708406 baseEnd_4708406 := by
    simpa [prefixWord, tailWord_4708406, baseEnd_4708406] using wordTrace_append hprefix tailTrace_4708406
  have hstable : (prefixWord ++ tailWord_4708406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708406).length < 2 ^ (prefixWord ++ tailWord_4708406).sum := by decide
  have hdescent : baseEnd_4708406 < baseStart_4708406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708417 : List Nat := [1, 2, 5, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_4708417 : Nat := 118140960795 + 4708417 * 2 ^ 59
def prefixEnd_4708417 : Nat := 4983230072969 + 3 ^ 40 * 4708417 * 2
def baseEnd_4708417 : Nat := 2417681042800610030533891

theorem tailTrace_4708417 : CollatzResearch.WordTrace tailWord_4708417 prefixEnd_4708417 2417681042800610030533891 := by
  unfold tailWord_4708417
  simp only [CollatzResearch.WordTrace]
  refine ⟨171730076183216817448363505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114486717455477878298909003 171730076183216817448363505)
  ·
    refine ⟨128797557137412613086272629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171730076183216817448363505 128797557137412613086272629)
    ·
      refine ⟨12074770981632432476838059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128797557137412613086272629 12074770981632432476838059)
      ·
        refine ⟨18112156472448648715257089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12074770981632432476838059 18112156472448648715257089)
        ·
          refine ⟨13584117354336486536442817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18112156472448648715257089 13584117354336486536442817)
          ·
            refine ⟨10188088015752364902332113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13584117354336486536442817 10188088015752364902332113)
            ·
              refine ⟨7641066011814273676749085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10188088015752364902332113 7641066011814273676749085)
              ·
                refine ⟨2865399754430352628780907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7641066011814273676749085 2865399754430352628780907)
                ·
                  refine ⟨4298099631645528943171361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2865399754430352628780907 4298099631645528943171361)
                  ·
                    refine ⟨3223574723734146707378521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4298099631645528943171361 3223574723734146707378521)
                    ·
                      refine ⟨2417681042800610030533891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3223574723734146707378521 2417681042800610030533891)
                      ·
                        rfl

theorem cell23_4708417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_4708417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708417 prefixEnd_4708417 := by exact prefixLift 4708417
  have htrace : WordTrace (prefixWord ++ tailWord_4708417) baseStart_4708417 baseEnd_4708417 := by
    simpa [prefixWord, tailWord_4708417, baseEnd_4708417] using wordTrace_append hprefix tailTrace_4708417
  have hstable : (prefixWord ++ tailWord_4708417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708417).length < 2 ^ (prefixWord ++ tailWord_4708417).sum := by decide
  have hdescent : baseEnd_4708417 < baseStart_4708417 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708450 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4708450 : Nat := 118140960795 + 4708450 * 2 ^ 59
def prefixEnd_4708450 : Nat := 4983230072969 + 3 ^ 40 * 4708450 * 2
def baseEnd_4708450 : Nat := 2417697987662208401421239

theorem tailTrace_4708450 : CollatzResearch.WordTrace tailWord_4708450 prefixEnd_4708450 2417697987662208401421239 := by
  unfold tailWord_4708450
  simp only [CollatzResearch.WordTrace]
  refine ⟨42932819948024316021078701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114487519861398176056209869 42932819948024316021078701)
  ·
    refine ⟨16099807480509118507904513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42932819948024316021078701 16099807480509118507904513)
    ·
      refine ⟨12074855610381838880928385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16099807480509118507904513 12074855610381838880928385)
      ·
        refine ⟨9056141707786379160696289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12074855610381838880928385 9056141707786379160696289)
        ·
          refine ⟨6792106280839784370522217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9056141707786379160696289 6792106280839784370522217)
          ·
            refine ⟨5094079710629838277891663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6792106280839784370522217 5094079710629838277891663)
            ·
              refine ⟨7641119565944757416837495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5094079710629838277891663 7641119565944757416837495)
              ·
                refine ⟨11461679348917136125256243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7641119565944757416837495 11461679348917136125256243)
                ·
                  refine ⟨17192519023375704187884365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11461679348917136125256243 17192519023375704187884365)
                  ·
                    refine ⟨6447194633765889070456637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17192519023375704187884365 6447194633765889070456637)
                    ·
                      refine ⟨2417697987662208401421239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6447194633765889070456637 2417697987662208401421239)
                      ·
                        rfl

theorem cell23_4708450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4708450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708450 prefixEnd_4708450 := by exact prefixLift 4708450
  have htrace : WordTrace (prefixWord ++ tailWord_4708450) baseStart_4708450 baseEnd_4708450 := by
    simpa [prefixWord, tailWord_4708450, baseEnd_4708450] using wordTrace_append hprefix tailTrace_4708450
  have hstable : (prefixWord ++ tailWord_4708450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708450).length < 2 ^ (prefixWord ++ tailWord_4708450).sum := by decide
  have hdescent : baseEnd_4708450 < baseStart_4708450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708473 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 4, 2, 2]
def baseStart_4708473 : Nat := 118140960795 + 4708473 * 2 ^ 59
def prefixEnd_4708473 : Nat := 4983230072969 + 3 ^ 40 * 4708473 * 2
def baseEnd_4708473 : Nat := 2417709797717261811433633

theorem tailTrace_4708473 : CollatzResearch.WordTrace tailWord_4708473 prefixEnd_4708473 2417709797717261811433633 := by
  unfold tailWord_4708473
  simp only [CollatzResearch.WordTrace]
  refine ⟨171732118671013939012402073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114488079114009292674934715 171732118671013939012402073)
  ·
    refine ⟨128799089003260454259301555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171732118671013939012402073 128799089003260454259301555)
    ·
      refine ⟨193198633504890681388952333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128799089003260454259301555 193198633504890681388952333)
      ·
        refine ⟨72449487564334005520857125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193198633504890681388952333 72449487564334005520857125)
        ·
          refine ⟨13584278918312626035160711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72449487564334005520857125 13584278918312626035160711)
          ·
            refine ⟨20376418377468939052741067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13584278918312626035160711 20376418377468939052741067)
            ·
              refine ⟨30564627566203408579111601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20376418377468939052741067 30564627566203408579111601)
              ·
                refine ⟨22923470674652556434333701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30564627566203408579111601 22923470674652556434333701)
                ·
                  refine ⟨4298150751497354331437569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22923470674652556434333701 4298150751497354331437569)
                  ·
                    refine ⟨3223613063623015748578177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4298150751497354331437569 3223613063623015748578177)
                    ·
                      refine ⟨2417709797717261811433633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3223613063623015748578177 2417709797717261811433633)
                      ·
                        rfl

theorem cell23_4708473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_4708473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708473 prefixEnd_4708473 := by exact prefixLift 4708473
  have htrace : WordTrace (prefixWord ++ tailWord_4708473) baseStart_4708473 baseEnd_4708473 := by
    simpa [prefixWord, tailWord_4708473, baseEnd_4708473] using wordTrace_append hprefix tailTrace_4708473
  have hstable : (prefixWord ++ tailWord_4708473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708473).length < 2 ^ (prefixWord ++ tailWord_4708473).sum := by decide
  have hdescent : baseEnd_4708473 < baseStart_4708473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708573 : List Nat := [1, 4, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_4708573 : Nat := 118140960795 + 4708573 * 2 ^ 59
def prefixEnd_4708573 : Nat := 4983230072969 + 3 ^ 40 * 4708573 * 2
def baseEnd_4708573 : Nat := 805920381927570473394391

theorem tailTrace_4708573 : CollatzResearch.WordTrace tailWord_4708573 prefixEnd_4708573 805920381927570473394391 := by
  unfold tailWord_4708573
  simp only [CollatzResearch.WordTrace]
  refine ⟨171735765970651656091042373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114490510647101104060694915 171735765970651656091042373)
  ·
    refine ⟨32200456119497185517070445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171735765970651656091042373 32200456119497185517070445)
    ·
      refine ⟨12075171044811444568901417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32200456119497185517070445 12075171044811444568901417)
      ·
        refine ⟨9056378283608583426676063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12075171044811444568901417 9056378283608583426676063)
        ·
          refine ⟨13584567425412875140014095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9056378283608583426676063 13584567425412875140014095)
          ·
            refine ⟨20376851138119312710021143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13584567425412875140014095 20376851138119312710021143)
            ·
              refine ⟨30565276707178969065031715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20376851138119312710021143 30565276707178969065031715)
              ·
                refine ⟨45847915060768453597547573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30565276707178969065031715 45847915060768453597547573)
                ·
                  refine ⟨4298242036947042524770085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45847915060768453597547573 4298242036947042524770085)
                  ·
                    refine ⟨805920381927570473394391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4298242036947042524770085 805920381927570473394391)
                    ·
                      rfl

theorem cell23_4708573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_4708573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708573 prefixEnd_4708573 := by exact prefixLift 4708573
  have htrace : WordTrace (prefixWord ++ tailWord_4708573) baseStart_4708573 baseEnd_4708573 := by
    simpa [prefixWord, tailWord_4708573, baseEnd_4708573] using wordTrace_append hprefix tailTrace_4708573
  have hstable : (prefixWord ++ tailWord_4708573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708573).length < 2 ^ (prefixWord ++ tailWord_4708573).sum := by decide
  have hdescent : baseEnd_4708573 < baseStart_4708573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708583 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4708583 : Nat := 118140960795 + 4708583 * 2 ^ 59
def prefixEnd_4708583 : Nat := 4983230072969 + 3 ^ 40 * 4708583 * 2
def baseEnd_4708583 : Nat := 2417766280589256381058127

theorem tailTrace_4708583 : CollatzResearch.WordTrace tailWord_4708583 prefixEnd_4708583 2417766280589256381058127 := by
  unfold tailWord_4708583
  simp only [CollatzResearch.WordTrace]
  refine ⟨171736130700615427798906403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114490753800410285199270935 171736130700615427798906403)
  ·
    refine ⟨257604196050923141698359605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171736130700615427798906403 257604196050923141698359605)
    ·
      refine ⟨24150393379774044534221213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 257604196050923141698359605 24150393379774044534221213)
      ·
        refine ⟨9056397517415266700332955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24150393379774044534221213 9056397517415266700332955)
        ·
          refine ⟨13584596276122900050499433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9056397517415266700332955 13584596276122900050499433)
          ·
            refine ⟨10188447207092175037874575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13584596276122900050499433 10188447207092175037874575)
            ·
              refine ⟨15282670810638262556811863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10188447207092175037874575 15282670810638262556811863)
              ·
                refine ⟨22924006215957393835217795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15282670810638262556811863 22924006215957393835217795)
                ·
                  refine ⟨34386009323936090752826693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22924006215957393835217795 34386009323936090752826693)
                  ·
                    refine ⟨6447376748238017016155005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34386009323936090752826693 6447376748238017016155005)
                    ·
                      refine ⟨2417766280589256381058127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6447376748238017016155005 2417766280589256381058127)
                      ·
                        rfl

theorem cell23_4708583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4708583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708583 prefixEnd_4708583 := by exact prefixLift 4708583
  have htrace : WordTrace (prefixWord ++ tailWord_4708583) baseStart_4708583 baseEnd_4708583 := by
    simpa [prefixWord, tailWord_4708583, baseEnd_4708583] using wordTrace_append hprefix tailTrace_4708583
  have hstable : (prefixWord ++ tailWord_4708583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708583).length < 2 ^ (prefixWord ++ tailWord_4708583).sum := by decide
  have hdescent : baseEnd_4708583 < baseStart_4708583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708606 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_4708606 : Nat := 118140960795 + 4708606 * 2 ^ 59
def prefixEnd_4708606 : Nat := 4983230072969 + 3 ^ 40 * 4708606 * 2
def baseEnd_4708606 : Nat := 2417778090644309791070521

theorem tailTrace_4708606 : CollatzResearch.WordTrace tailWord_4708606 prefixEnd_4708606 2417778090644309791070521 := by
  unfold tailWord_4708606
  simp only [CollatzResearch.WordTrace]
  refine ⟨21467121197441512840874209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114491313053021401817995781 21467121197441512840874209)
  ·
    refine ⟨16100340898081134630655657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21467121197441512840874209 16100340898081134630655657)
    ·
      refine ⟨12075255673560850972991743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16100340898081134630655657 12075255673560850972991743)
      ·
        refine ⟨18112883510341276459487615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12075255673560850972991743 18112883510341276459487615)
        ·
          refine ⟨27169325265511914689231423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18112883510341276459487615 27169325265511914689231423)
          ·
            refine ⟨40753987898267872033847135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27169325265511914689231423 40753987898267872033847135)
            ·
              refine ⟨61130981847401808050770703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40753987898267872033847135 61130981847401808050770703)
              ·
                refine ⟨91696472771102712076156055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61130981847401808050770703 91696472771102712076156055)
                ·
                  refine ⟨137544709156654068114234083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91696472771102712076156055 137544709156654068114234083)
                  ·
                    refine ⟨206317063734981102171351125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 137544709156654068114234083 206317063734981102171351125)
                    ·
                      refine ⟨2417778090644309791070521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 206317063734981102171351125 2417778090644309791070521)
                      ·
                        rfl

theorem cell23_4708606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_4708606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708606 prefixEnd_4708606 := by exact prefixLift 4708606
  have htrace : WordTrace (prefixWord ++ tailWord_4708606) baseStart_4708606 baseEnd_4708606 := by
    simpa [prefixWord, tailWord_4708606, baseEnd_4708606] using wordTrace_append hprefix tailTrace_4708606
  have hstable : (prefixWord ++ tailWord_4708606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708606).length < 2 ^ (prefixWord ++ tailWord_4708606).sum := by decide
  have hdescent : baseEnd_4708606 < baseStart_4708606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708666 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_4708666 : Nat := 118140960795 + 4708666 * 2 ^ 59
def prefixEnd_4708666 : Nat := 4983230072969 + 3 ^ 40 * 4708666 * 2
def baseEnd_4708666 : Nat := 2417808899483579556320245

theorem tailTrace_4708666 : CollatzResearch.WordTrace tailWord_4708666 prefixEnd_4708666 2417808899483579556320245 := by
  unfold tailWord_4708666
  simp only [CollatzResearch.WordTrace]
  refine ⟨42934789489828683243544463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114492771972876488649451901 42934789489828683243544463)
  ·
    refine ⟨64402184234743024865316695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42934789489828683243544463 64402184234743024865316695)
    ·
      refine ⟨96603276352114537297975043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64402184234743024865316695 96603276352114537297975043)
      ·
        refine ⟨144904914528171805946962565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96603276352114537297975043 144904914528171805946962565)
        ·
          refine ⟨27169671474032213615055481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144904914528171805946962565 27169671474032213615055481)
          ·
            refine ⟨20377253605524160211291611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27169671474032213615055481 20377253605524160211291611)
            ·
              refine ⟨30565880408286240316937417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20377253605524160211291611 30565880408286240316937417)
              ·
                refine ⟨22924410306214680237703063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30565880408286240316937417 22924410306214680237703063)
                ·
                  refine ⟨34386615459322020356554595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22924410306214680237703063 34386615459322020356554595)
                  ·
                    refine ⟨51579923188983030534831893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34386615459322020356554595 51579923188983030534831893)
                    ·
                      refine ⟨2417808899483579556320245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51579923188983030534831893 2417808899483579556320245)
                      ·
                        rfl

theorem cell23_4708666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_4708666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708666 prefixEnd_4708666 := by exact prefixLift 4708666
  have htrace : WordTrace (prefixWord ++ tailWord_4708666) baseStart_4708666 baseEnd_4708666 := by
    simpa [prefixWord, tailWord_4708666, baseEnd_4708666] using wordTrace_append hprefix tailTrace_4708666
  have hstable : (prefixWord ++ tailWord_4708666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708666).length < 2 ^ (prefixWord ++ tailWord_4708666).sum := by decide
  have hdescent : baseEnd_4708666 < baseStart_4708666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708680 : List Nat := [2, 1, 3, 1, 1, 2, 6, 1, 2, 4]
def baseStart_4708680 : Nat := 118140960795 + 4708680 * 2 ^ 59
def prefixEnd_4708680 : Nat := 4983230072969 + 3 ^ 40 * 4708680 * 2
def baseEnd_4708680 : Nat := 805938696070914167181727

theorem tailTrace_4708680 : CollatzResearch.WordTrace tailWord_4708680 prefixEnd_4708680 805938696070914167181727 := by
  unfold tailWord_4708680
  simp only [CollatzResearch.WordTrace]
  refine ⟨85869834290632006682593747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114493112387509342243458329 85869834290632006682593747)
  ·
    refine ⟨128804751435948010023890621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85869834290632006682593747 128804751435948010023890621)
    ·
      refine ⟨48301781788480503758958983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128804751435948010023890621 48301781788480503758958983)
      ·
        refine ⟨72452672682720755638438475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48301781788480503758958983 72452672682720755638438475)
        ·
          refine ⟨108679009024081133457657713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72452672682720755638438475 108679009024081133457657713)
          ·
            refine ⟨81509256768060850093243285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108679009024081133457657713 81509256768060850093243285)
            ·
              refine ⟨3820746411002852348120779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 81509256768060850093243285 3820746411002852348120779)
              ·
                refine ⟨5731119616504278522181169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3820746411002852348120779 5731119616504278522181169)
                ·
                  refine ⟨4298339712378208891635877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5731119616504278522181169 4298339712378208891635877)
                  ·
                    refine ⟨805938696070914167181727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4298339712378208891635877 805938696070914167181727)
                    ·
                      rfl

theorem cell23_4708680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_4708680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708680 prefixEnd_4708680 := by exact prefixLift 4708680
  have htrace : WordTrace (prefixWord ++ tailWord_4708680) baseStart_4708680 baseEnd_4708680 := by
    simpa [prefixWord, tailWord_4708680, baseEnd_4708680] using wordTrace_append hprefix tailTrace_4708680
  have hstable : (prefixWord ++ tailWord_4708680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708680).length < 2 ^ (prefixWord ++ tailWord_4708680).sum := by decide
  have hdescent : baseEnd_4708680 < baseStart_4708680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708690 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_4708690 : Nat := 118140960795 + 4708690 * 2 ^ 59
def prefixEnd_4708690 : Nat := 4983230072969 + 3 ^ 40 * 4708690 * 2
def baseEnd_4708690 : Nat := 2417821223019287462420135

theorem tailTrace_4708690 : CollatzResearch.WordTrace tailWord_4708690 prefixEnd_4708690 2417821223019287462420135 := by
  unfold tailWord_4708690
  simp only [CollatzResearch.WordTrace]
  refine ⟨42935008327806946268262881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114493355540818523382034349 42935008327806946268262881)
  ·
    refine ⟨32201256245855209701197161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42935008327806946268262881 32201256245855209701197161)
    ·
      refine ⟨24150942184391407275897871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32201256245855209701197161 24150942184391407275897871)
      ·
        refine ⟨36226413276587110913846807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24150942184391407275897871 36226413276587110913846807)
        ·
          refine ⟨54339619914880666370770211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36226413276587110913846807 54339619914880666370770211)
          ·
            refine ⟨81509429872320999556155317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54339619914880666370770211 81509429872320999556155317)
            ·
              refine ⟨7641509050530093708389561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81509429872320999556155317 7641509050530093708389561)
              ·
                refine ⟨5731131787897570281292171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7641509050530093708389561 5731131787897570281292171)
                ·
                  refine ⟨8596697681846355421938257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5731131787897570281292171 8596697681846355421938257)
                  ·
                    refine ⟨6447523261384766566453693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8596697681846355421938257 6447523261384766566453693)
                    ·
                      refine ⟨2417821223019287462420135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6447523261384766566453693 2417821223019287462420135)
                      ·
                        rfl

theorem cell23_4708690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_4708690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708690 prefixEnd_4708690 := by exact prefixLift 4708690
  have htrace : WordTrace (prefixWord ++ tailWord_4708690) baseStart_4708690 baseEnd_4708690 := by
    simpa [prefixWord, tailWord_4708690, baseEnd_4708690] using wordTrace_append hprefix tailTrace_4708690
  have hstable : (prefixWord ++ tailWord_4708690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708690).length < 2 ^ (prefixWord ++ tailWord_4708690).sum := by decide
  have hdescent : baseEnd_4708690 < baseStart_4708690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708703 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 6, 1, 3]
def baseStart_4708703 : Nat := 118140960795 + 4708703 * 2 ^ 59
def prefixEnd_4708703 : Nat := 4983230072969 + 3 ^ 40 * 4708703 * 2
def baseEnd_4708703 : Nat := 2417827898267795911557575

theorem tailTrace_4708703 : CollatzResearch.WordTrace tailWord_4708703 prefixEnd_4708703 2417827898267795911557575 := by
  unfold tailWord_4708703
  simp only [CollatzResearch.WordTrace]
  refine ⟨171740507460180688293274763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114493671640120458862183175 171740507460180688293274763)
  ·
    refine ⟨257610761190271032439912145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171740507460180688293274763 257610761190271032439912145)
    ·
      refine ⟨193208070892703274329934109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257610761190271032439912145 193208070892703274329934109)
      ·
        refine ⟨72453026584763727873725291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193208070892703274329934109 72453026584763727873725291)
        ·
          refine ⟨108679539877145591810587937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72453026584763727873725291 108679539877145591810587937)
          ·
            refine ⟨81509654907859193857940953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108679539877145591810587937 81509654907859193857940953)
            ·
              refine ⟨61132241180894395393455715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81509654907859193857940953 61132241180894395393455715)
              ·
                refine ⟨91698361771341593090183573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61132241180894395393455715 91698361771341593090183573)
                ·
                  refine ⟨4298360708031637176102355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91698361771341593090183573 4298360708031637176102355)
                  ·
                    refine ⟨6447541062047455764153533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4298360708031637176102355 6447541062047455764153533)
                    ·
                      refine ⟨2417827898267795911557575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6447541062047455764153533 2417827898267795911557575)
                      ·
                        rfl

theorem cell23_4708703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_4708703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708703 prefixEnd_4708703 := by exact prefixLift 4708703
  have htrace : WordTrace (prefixWord ++ tailWord_4708703) baseStart_4708703 baseEnd_4708703 := by
    simpa [prefixWord, tailWord_4708703, baseEnd_4708703] using wordTrace_append hprefix tailTrace_4708703
  have hstable : (prefixWord ++ tailWord_4708703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708703).length < 2 ^ (prefixWord ++ tailWord_4708703).sum := by decide
  have hdescent : baseEnd_4708703 < baseStart_4708703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708720 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 2, 1, 3]
def baseStart_4708720 : Nat := 118140960795 + 4708720 * 2 ^ 59
def prefixEnd_4708720 : Nat := 4983230072969 + 3 ^ 40 * 4708720 * 2
def baseEnd_4708720 : Nat := 2417836627438922345044997

theorem tailTrace_4708720 : CollatzResearch.WordTrace tailWord_4708720 prefixEnd_4708720 2417836627438922345044997 := by
  unfold tailWord_4708720
  simp only [CollatzResearch.WordTrace]
  refine ⟨85870563750559550098321807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114494085000746066797762409 85870563750559550098321807)
  ·
    refine ⟨128805845625839325147482711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85870563750559550098321807 128805845625839325147482711)
    ·
      refine ⟨193208768438758987721224067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128805845625839325147482711 193208768438758987721224067)
      ·
        refine ⟨289813152658138481581836101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193208768438758987721224067 289813152658138481581836101)
        ·
          refine ⟨54339966123400965296594269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 289813152658138481581836101 54339966123400965296594269)
          ·
            refine ⟨20377487296275361986222851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54339966123400965296594269 20377487296275361986222851)
            ·
              refine ⟨30566230944413042979334277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20377487296275361986222851 30566230944413042979334277)
              ·
                refine ⟨5731168302077445558625177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30566230944413042979334277 5731168302077445558625177)
                ·
                  refine ⟨4298376226558084168968883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5731168302077445558625177 4298376226558084168968883)
                  ·
                    refine ⟨6447564339837126253453325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4298376226558084168968883 6447564339837126253453325)
                    ·
                      refine ⟨2417836627438922345044997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6447564339837126253453325 2417836627438922345044997)
                      ·
                        rfl

theorem cell23_4708720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 2, 1, 3].length) (baseStart_4708720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708720 prefixEnd_4708720 := by exact prefixLift 4708720
  have htrace : WordTrace (prefixWord ++ tailWord_4708720) baseStart_4708720 baseEnd_4708720 := by
    simpa [prefixWord, tailWord_4708720, baseEnd_4708720] using wordTrace_append hprefix tailTrace_4708720
  have hstable : (prefixWord ++ tailWord_4708720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708720).length < 2 ^ (prefixWord ++ tailWord_4708720).sum := by decide
  have hdescent : baseEnd_4708720 < baseStart_4708720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708737 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_4708737 : Nat := 118140960795 + 4708737 * 2 ^ 59
def prefixEnd_4708737 : Nat := 4983230072969 + 3 ^ 40 * 4708737 * 2
def baseEnd_4708737 : Nat := 2417845356610048778532419

theorem tailTrace_4708737 : CollatzResearch.WordTrace tailWord_4708737 prefixEnd_4708737 2417845356610048778532419 := by
  unfold tailWord_4708737
  simp only [CollatzResearch.WordTrace]
  refine ⟨171741747542057512100012465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114494498361371674733341643 171741747542057512100012465)
  ·
    refine ⟨128806310656543134075009349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171741747542057512100012465 128806310656543134075009349)
    ·
      refine ⟨24151183248101837639064253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128806310656543134075009349 24151183248101837639064253)
      ·
        refine ⟨9056693718038189114649095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24151183248101837639064253 9056693718038189114649095)
        ·
          refine ⟨13585040577057283671973643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9056693718038189114649095 13585040577057283671973643)
          ·
            refine ⟨20377560865585925507960465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13585040577057283671973643 20377560865585925507960465)
            ·
              refine ⟨15283170649189444130970349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20377560865585925507960465 15283170649189444130970349)
              ·
                refine ⟨5731188993446041549113881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15283170649189444130970349 5731188993446041549113881)
                ·
                  refine ⟨4298391745084531161835411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5731188993446041549113881 4298391745084531161835411)
                  ·
                    refine ⟨6447587617626796742753117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4298391745084531161835411 6447587617626796742753117)
                    ·
                      refine ⟨2417845356610048778532419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6447587617626796742753117 2417845356610048778532419)
                      ·
                        rfl

theorem cell23_4708737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_4708737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708737 prefixEnd_4708737 := by exact prefixLift 4708737
  have htrace : WordTrace (prefixWord ++ tailWord_4708737) baseStart_4708737 baseEnd_4708737 := by
    simpa [prefixWord, tailWord_4708737, baseEnd_4708737] using wordTrace_append hprefix tailTrace_4708737
  have hstable : (prefixWord ++ tailWord_4708737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708737).length < 2 ^ (prefixWord ++ tailWord_4708737).sum := by decide
  have hdescent : baseEnd_4708737 < baseStart_4708737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708788 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_4708788 : Nat := 118140960795 + 4708788 * 2 ^ 59
def prefixEnd_4708788 : Nat := 4983230072969 + 3 ^ 40 * 4708788 * 2
def baseEnd_4708788 : Nat := 2417871544123428078994685

theorem tailTrace_4708788 : CollatzResearch.WordTrace tailWord_4708788 prefixEnd_4708788 2417871544123428078994685 := by
  unfold tailWord_4708788
  simp only [CollatzResearch.WordTrace]
  refine ⟨85871803832436373905059509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114495738443248498540079345 85871803832436373905059509)
  ·
    refine ⟨8050481609290910053599329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85871803832436373905059509 8050481609290910053599329)
    ·
      refine ⟨6037861206968182540199497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8050481609290910053599329 6037861206968182540199497)
      ·
        refine ⟨4528395905226136905149623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6037861206968182540199497 4528395905226136905149623)
        ·
          refine ⟨6792593857839205357724435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528395905226136905149623 6792593857839205357724435)
          ·
            refine ⟨10188890786758808036586653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6792593857839205357724435 10188890786758808036586653)
            ·
              refine ⟨3820834045034553013719995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10188890786758808036586653 3820834045034553013719995)
              ·
                refine ⟨5731251067551829520579993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3820834045034553013719995 5731251067551829520579993)
                ·
                  refine ⟨4298438300663872140434995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5731251067551829520579993 4298438300663872140434995)
                  ·
                    refine ⟨6447657450995808210652493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4298438300663872140434995 6447657450995808210652493)
                    ·
                      refine ⟨2417871544123428078994685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6447657450995808210652493 2417871544123428078994685)
                      ·
                        rfl

theorem cell23_4708788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_4708788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708788 prefixEnd_4708788 := by exact prefixLift 4708788
  have htrace : WordTrace (prefixWord ++ tailWord_4708788) baseStart_4708788 baseEnd_4708788 := by
    simpa [prefixWord, tailWord_4708788, baseEnd_4708788] using wordTrace_append hprefix tailTrace_4708788
  have hstable : (prefixWord ++ tailWord_4708788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708788).length < 2 ^ (prefixWord ++ tailWord_4708788).sum := by decide
  have hdescent : baseEnd_4708788 < baseStart_4708788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708834 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 7]
def baseStart_4708834 : Nat := 118140960795 + 4708834 * 2 ^ 59
def prefixEnd_4708834 : Nat := 4983230072969 + 3 ^ 40 * 4708834 * 2
def baseEnd_4708834 : Nat := 268655018248170544335497

theorem tailTrace_4708834 : CollatzResearch.WordTrace tailWord_4708834 prefixEnd_4708834 268655018248170544335497 := by
  unfold tailWord_4708834
  simp only [CollatzResearch.WordTrace]
  refine ⟨42936321355676524416573389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114496856948470731777529037 42936321355676524416573389)
  ·
    refine ⟨16101120508378696656215021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42936321355676524416573389 16101120508378696656215021)
    ·
      refine ⟨6037920190642011246080633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16101120508378696656215021 6037920190642011246080633)
      ·
        refine ⟨4528440142981508434560475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6037920190642011246080633 4528440142981508434560475)
        ·
          refine ⟨6792660214472262651840713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528440142981508434560475 6792660214472262651840713)
          ·
            refine ⟨5094495160854196988880535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6792660214472262651840713 5094495160854196988880535)
            ·
              refine ⟨7641742741281295483320803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5094495160854196988880535 7641742741281295483320803)
              ·
                refine ⟨11462614111921943224981205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7641742741281295483320803 11462614111921943224981205)
                ·
                  refine ⟨268655018248170544335497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11462614111921943224981205 268655018248170544335497)
                  ·
                    rfl

theorem cell23_4708834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_4708834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708834 prefixEnd_4708834 := by exact prefixLift 4708834
  have htrace : WordTrace (prefixWord ++ tailWord_4708834) baseStart_4708834 baseEnd_4708834 := by
    simpa [prefixWord, tailWord_4708834, baseEnd_4708834] using wordTrace_append hprefix tailTrace_4708834
  have hstable : (prefixWord ++ tailWord_4708834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708834).length < 2 ^ (prefixWord ++ tailWord_4708834).sum := by decide
  have hdescent : baseEnd_4708834 < baseStart_4708834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708917 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 3, 1, 3]
def baseStart_4708917 : Nat := 118140960795 + 4708917 * 2 ^ 59
def prefixEnd_4708917 : Nat := 4983230072969 + 3 ^ 40 * 4708917 * 2
def baseEnd_4708917 : Nat := 2417937783127858074281591

theorem tailTrace_4708917 : CollatzResearch.WordTrace tailWord_4708917 prefixEnd_4708917 2417937783127858074281591 := by
  unfold tailWord_4708917
  simp only [CollatzResearch.WordTrace]
  refine ⟨171748312681405402841565005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114498875120936935227710003 171748312681405402841565005)
  ·
    refine ⟨64405617255527026065586877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171748312681405402841565005 64405617255527026065586877)
    ·
      refine ⟨24152106470822634774595079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64405617255527026065586877 24152106470822634774595079)
      ·
        refine ⟨36228159706233952161892619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24152106470822634774595079 36228159706233952161892619)
        ·
          refine ⟨54342239559350928242838929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36228159706233952161892619 54342239559350928242838929)
          ·
            refine ⟨40756679669513196182129197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54342239559350928242838929 40756679669513196182129197)
            ·
              refine ⟨15283754876067448568298449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40756679669513196182129197 15283754876067448568298449)
              ·
                refine ⟨11462816157050586426223837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15283754876067448568298449 11462816157050586426223837)
                ·
                  refine ⟨4298556058893969909833939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11462816157050586426223837 4298556058893969909833939)
                  ·
                    refine ⟨6447834088340954864750909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4298556058893969909833939 6447834088340954864750909)
                    ·
                      refine ⟨2417937783127858074281591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6447834088340954864750909 2417937783127858074281591)
                      ·
                        rfl

theorem cell23_4708917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_4708917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708917 prefixEnd_4708917 := by exact prefixLift 4708917
  have htrace : WordTrace (prefixWord ++ tailWord_4708917) baseStart_4708917 baseEnd_4708917 := by
    simpa [prefixWord, tailWord_4708917, baseEnd_4708917] using wordTrace_append hprefix tailTrace_4708917
  have hstable : (prefixWord ++ tailWord_4708917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708917).length < 2 ^ (prefixWord ++ tailWord_4708917).sum := by decide
  have hdescent : baseEnd_4708917 < baseStart_4708917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708920 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 1, 5]
def baseStart_4708920 : Nat := 118140960795 + 4708920 * 2 ^ 59
def prefixEnd_4708920 : Nat := 4983230072969 + 3 ^ 40 * 4708920 * 2
def baseEnd_4708920 : Nat := 805979774523273854181359

theorem tailTrace_4708920 : CollatzResearch.WordTrace tailWord_4708920 prefixEnd_4708920 805979774523273854181359 := by
  unfold tailWord_4708920
  simp only [CollatzResearch.WordTrace]
  refine ⟨85874211050197267176962107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114498948066929689569282809 85874211050197267176962107)
  ·
    refine ⟨128811316575295900765443161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85874211050197267176962107 128811316575295900765443161)
    ·
      refine ⟨96608487431471925574082371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128811316575295900765443161 96608487431471925574082371)
      ·
        refine ⟨144912731147207888361123557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96608487431471925574082371 144912731147207888361123557)
        ·
          refine ⟨27171137090101479067710667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 144912731147207888361123557 27171137090101479067710667)
          ·
            refine ⟨40756705635152218601566001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27171137090101479067710667 40756705635152218601566001)
            ·
              refine ⟨30567529226364163951174501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40756705635152218601566001 30567529226364163951174501)
              ·
                refine ⟨5731411729943280740845219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30567529226364163951174501 5731411729943280740845219)
                ·
                  refine ⟨8597117594914921111267829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5731411729943280740845219 8597117594914921111267829)
                  ·
                    refine ⟨805979774523273854181359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8597117594914921111267829 805979774523273854181359)
                    ·
                      rfl

theorem cell23_4708920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_4708920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708920 prefixEnd_4708920 := by exact prefixLift 4708920
  have htrace : WordTrace (prefixWord ++ tailWord_4708920) baseStart_4708920 baseEnd_4708920 := by
    simpa [prefixWord, tailWord_4708920, baseEnd_4708920] using wordTrace_append hprefix tailTrace_4708920
  have hstable : (prefixWord ++ tailWord_4708920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708920).length < 2 ^ (prefixWord ++ tailWord_4708920).sum := by decide
  have hdescent : baseEnd_4708920 < baseStart_4708920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708953 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 4]
def baseStart_4708953 : Nat := 118140960795 + 4708953 * 2 ^ 59
def prefixEnd_4708953 : Nat := 4983230072969 + 3 ^ 40 * 4708953 * 2
def baseEnd_4708953 : Nat := 2417956268431419933431425

theorem tailTrace_4708953 : CollatzResearch.WordTrace tailWord_4708953 prefixEnd_4708953 2417956268431419933431425 := by
  unfold tailWord_4708953
  simp only [CollatzResearch.WordTrace]
  refine ⟨171749625709274980989875513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114499750472849987326583675 171749625709274980989875513)
  ·
    refine ⟨128812219281956235742406635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171749625709274980989875513 128812219281956235742406635)
    ·
      refine ⟨193218328922934353613609953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128812219281956235742406635 193218328922934353613609953)
      ·
        refine ⟨144913746692200765210207465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193218328922934353613609953 144913746692200765210207465)
        ·
          refine ⟨108685310019150573907655599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144913746692200765210207465 108685310019150573907655599)
          ·
            refine ⟨163027965028725860861483399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108685310019150573907655599 163027965028725860861483399)
            ·
              refine ⟨244541947543088791292225099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163027965028725860861483399 244541947543088791292225099)
              ·
                refine ⟨366812921314633186938337649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244541947543088791292225099 366812921314633186938337649)
                ·
                  refine ⟨275109690985974890203753237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 366812921314633186938337649 275109690985974890203753237)
                  ·
                    refine ⟨12895766764967572978300933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 275109690985974890203753237 12895766764967572978300933)
                    ·
                      refine ⟨2417956268431419933431425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12895766764967572978300933 2417956268431419933431425)
                      ·
                        rfl

theorem cell23_4708953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_4708953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708953 prefixEnd_4708953 := by exact prefixLift 4708953
  have htrace : WordTrace (prefixWord ++ tailWord_4708953) baseStart_4708953 baseEnd_4708953 := by
    simpa [prefixWord, tailWord_4708953, baseEnd_4708953] using wordTrace_append hprefix tailTrace_4708953
  have hstable : (prefixWord ++ tailWord_4708953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708953).length < 2 ^ (prefixWord ++ tailWord_4708953).sum := by decide
  have hdescent : baseEnd_4708953 < baseStart_4708953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708958 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 6]
def baseStart_4708958 : Nat := 118140960795 + 4708958 * 2 ^ 59
def prefixEnd_4708958 : Nat := 4983230072969 + 3 ^ 40 * 4708958 * 2
def baseEnd_4708958 : Nat := 268662092870521379318767

theorem tailTrace_4708958 : CollatzResearch.WordTrace tailWord_4708958 prefixEnd_4708958 268662092870521379318767 := by
  unfold tailWord_4708958
  simp only [CollatzResearch.WordTrace]
  refine ⟨21468726009282108355475941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114499872049504577895871685 21468726009282108355475941)
  ·
    refine ⟨4025386126740395316651739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21468726009282108355475941 4025386126740395316651739)
    ·
      refine ⟨6038079190110592974977609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4025386126740395316651739 6038079190110592974977609)
      ·
        refine ⟨4528559392582944731233207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6038079190110592974977609 4528559392582944731233207)
        ·
          refine ⟨6792839088874417096849811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528559392582944731233207 6792839088874417096849811)
          ·
            refine ⟨10189258633311625645274717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6792839088874417096849811 10189258633311625645274717)
            ·
              refine ⟨3820971987491859616978019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10189258633311625645274717 3820971987491859616978019)
              ·
                refine ⟨5731457981237789425467029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3820971987491859616978019 5731457981237789425467029)
                ·
                  refine ⟨268662092870521379318767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5731457981237789425467029 268662092870521379318767)
                  ·
                    rfl

theorem cell23_4708958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_4708958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708958 prefixEnd_4708958 := by exact prefixLift 4708958
  have htrace : WordTrace (prefixWord ++ tailWord_4708958) baseStart_4708958 baseEnd_4708958 := by
    simpa [prefixWord, tailWord_4708958, baseEnd_4708958] using wordTrace_append hprefix tailTrace_4708958
  have hstable : (prefixWord ++ tailWord_4708958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708958).length < 2 ^ (prefixWord ++ tailWord_4708958).sum := by decide
  have hdescent : baseEnd_4708958 < baseStart_4708958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708960 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 3]
def baseStart_4708960 : Nat := 118140960795 + 4708960 * 2 ^ 59
def prefixEnd_4708960 : Nat := 4983230072969 + 3 ^ 40 * 4708960 * 2
def baseEnd_4708960 : Nat := 2417959862796001406043893

theorem tailTrace_4708960 : CollatzResearch.WordTrace tailWord_4708960 prefixEnd_4708960 2417959862796001406043893 := by
  unfold tailWord_4708960
  simp only [CollatzResearch.WordTrace]
  refine ⟨85874940510124810592690167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114499920680166414123586889 85874940510124810592690167)
  ·
    refine ⟨128812410765187215889035251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85874940510124810592690167 128812410765187215889035251)
    ·
      refine ⟨193218616147780823833552877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128812410765187215889035251 193218616147780823833552877)
      ·
        refine ⟨72456981055417808937582329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193218616147780823833552877 72456981055417808937582329)
        ·
          refine ⟨54342735791563356703186747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72456981055417808937582329 54342735791563356703186747)
          ·
            refine ⟨81514103687345035054780121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54342735791563356703186747 81514103687345035054780121)
            ·
              refine ⟨61135577765508776291085091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81514103687345035054780121 61135577765508776291085091)
              ·
                refine ⟨91703366648263164436627637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61135577765508776291085091 91703366648263164436627637)
                ·
                  refine ⟨8597190623274671665933841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91703366648263164436627637 8597190623274671665933841)
                  ·
                    refine ⟨6447892967456003749450381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8597190623274671665933841 6447892967456003749450381)
                    ·
                      refine ⟨2417959862796001406043893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6447892967456003749450381 2417959862796001406043893)
                      ·
                        rfl

theorem cell23_4708960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_4708960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708960 prefixEnd_4708960 := by exact prefixLift 4708960
  have htrace : WordTrace (prefixWord ++ tailWord_4708960) baseStart_4708960 baseEnd_4708960 := by
    simpa [prefixWord, tailWord_4708960, baseEnd_4708960] using wordTrace_append hprefix tailTrace_4708960
  have hstable : (prefixWord ++ tailWord_4708960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708960).length < 2 ^ (prefixWord ++ tailWord_4708960).sum := by decide
  have hdescent : baseEnd_4708960 < baseStart_4708960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708963 : List Nat := [1, 1, 1, 5, 1, 2, 2, 10]
def baseStart_4708963 : Nat := 118140960795 + 4708963 * 2 ^ 59
def prefixEnd_4708963 : Nat := 4983230072969 + 3 ^ 40 * 4708963 * 2
def baseEnd_4708963 : Nat := 89554126045850551640977

theorem tailTrace_4708963 : CollatzResearch.WordTrace tailWord_4708963 prefixEnd_4708963 89554126045850551640977 := by
  unfold tailWord_4708963
  simp only [CollatzResearch.WordTrace]
  refine ⟨171749990439238752697739543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114499993626159168465159695 171749990439238752697739543)
  ·
    refine ⟨257624985658858129046609315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171749990439238752697739543 257624985658858129046609315)
    ·
      refine ⟨386437478488287193569913973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257624985658858129046609315 386437478488287193569913973)
      ·
        refine ⟨36228513608276924397179435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 386437478488287193569913973 36228513608276924397179435)
        ·
          refine ⟨54342770412415386595769153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36228513608276924397179435 54342770412415386595769153)
          ·
            refine ⟨40757077809311539946826865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54342770412415386595769153 40757077809311539946826865)
            ·
              refine ⟨30567808356983654960120149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40757077809311539946826865 30567808356983654960120149)
              ·
                refine ⟨89554126045850551640977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30567808356983654960120149 89554126045850551640977)
                ·
                  rfl

theorem cell23_4708963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 10].length) (baseStart_4708963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708963 prefixEnd_4708963 := by exact prefixLift 4708963
  have htrace : WordTrace (prefixWord ++ tailWord_4708963) baseStart_4708963 baseEnd_4708963 := by
    simpa [prefixWord, tailWord_4708963, baseEnd_4708963] using wordTrace_append hprefix tailTrace_4708963
  have hstable : (prefixWord ++ tailWord_4708963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708963).length < 2 ^ (prefixWord ++ tailWord_4708963).sum := by decide
  have hdescent : baseEnd_4708963 < baseStart_4708963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708970 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_4708970 : Nat := 118140960795 + 4708970 * 2 ^ 59
def prefixEnd_4708970 : Nat := 4983230072969 + 3 ^ 40 * 4708970 * 2
def baseEnd_4708970 : Nat := 2417964997602546366918847

theorem tailTrace_4708970 : CollatzResearch.WordTrace tailWord_4708970 prefixEnd_4708970 2417964997602546366918847 := by
  unfold tailWord_4708970
  simp only [CollatzResearch.WordTrace]
  refine ⟨42937561437553348223311091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114500163833475595262162909 42937561437553348223311091)
  ·
    refine ⟨64406342156330022334966637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42937561437553348223311091 64406342156330022334966637)
    ·
      refine ⟨24152378308623758375612489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64406342156330022334966637 24152378308623758375612489)
      ·
        refine ⟨18114283731467818781709367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24152378308623758375612489 18114283731467818781709367)
        ·
          refine ⟨27171425597201728172564051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18114283731467818781709367 27171425597201728172564051)
          ·
            refine ⟨40757138395802592258846077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27171425597201728172564051 40757138395802592258846077)
            ·
              refine ⟨15283926898425972097067279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40757138395802592258846077 15283926898425972097067279)
              ·
                refine ⟨22925890347638958145600919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15283926898425972097067279 22925890347638958145600919)
                ·
                  refine ⟨34388835521458437218401379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22925890347638958145600919 34388835521458437218401379)
                  ·
                    refine ⟨51583253282187655827602069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34388835521458437218401379 51583253282187655827602069)
                    ·
                      refine ⟨2417964997602546366918847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51583253282187655827602069 2417964997602546366918847)
                      ·
                        rfl

theorem cell23_4708970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_4708970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708970 prefixEnd_4708970 := by exact prefixLift 4708970
  have htrace : WordTrace (prefixWord ++ tailWord_4708970) baseStart_4708970 baseEnd_4708970 := by
    simpa [prefixWord, tailWord_4708970, baseEnd_4708970] using wordTrace_append hprefix tailTrace_4708970
  have hstable : (prefixWord ++ tailWord_4708970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708970).length < 2 ^ (prefixWord ++ tailWord_4708970).sum := by decide
  have hdescent : baseEnd_4708970 < baseStart_4708970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4708974 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_4708974 : Nat := 118140960795 + 4708974 * 2 ^ 59
def prefixEnd_4708974 : Nat := 4983230072969 + 3 ^ 40 * 4708974 * 2
def baseEnd_4708974 : Nat := 2417967051525164351268829

theorem tailTrace_4708974 : CollatzResearch.WordTrace tailWord_4708974 prefixEnd_4708974 2417967051525164351268829 := by
  unfold tailWord_4708974
  simp only [CollatzResearch.WordTrace]
  refine ⟨21468798955274862697048747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114500261094799267717593317 21468798955274862697048747)
  ·
    refine ⟨32203198432912294045573121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21468798955274862697048747 32203198432912294045573121)
    ·
      refine ⟨24152398824684220534179841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32203198432912294045573121 24152398824684220534179841)
      ·
        refine ⟨18114299118513165400634881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24152398824684220534179841 18114299118513165400634881)
        ·
          refine ⟨13585724338884874050476161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18114299118513165400634881 13585724338884874050476161)
          ·
            refine ⟨10189293254163655537857121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13585724338884874050476161 10189293254163655537857121)
            ·
              refine ⟨7641969940622741653392841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10189293254163655537857121 7641969940622741653392841)
              ·
                refine ⟨5731477455467056240044631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7641969940622741653392841 5731477455467056240044631)
                ·
                  refine ⟨8597216183200584360066947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5731477455467056240044631 8597216183200584360066947)
                  ·
                    refine ⟨12895824274800876540100421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8597216183200584360066947 12895824274800876540100421)
                    ·
                      refine ⟨2417967051525164351268829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12895824274800876540100421 2417967051525164351268829)
                      ·
                        rfl

theorem cell23_4708974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_4708974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4708974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4708974 prefixEnd_4708974 := by exact prefixLift 4708974
  have htrace : WordTrace (prefixWord ++ tailWord_4708974) baseStart_4708974 baseEnd_4708974 := by
    simpa [prefixWord, tailWord_4708974, baseEnd_4708974] using wordTrace_append hprefix tailTrace_4708974
  have hstable : (prefixWord ++ tailWord_4708974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4708974).length < 2 ^ (prefixWord ++ tailWord_4708974).sum := by decide
  have hdescent : baseEnd_4708974 < baseStart_4708974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4708974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709017 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 3, 3, 2]
def baseStart_4709017 : Nat := 118140960795 + 4709017 * 2 ^ 59
def prefixEnd_4709017 : Nat := 4983230072969 + 3 ^ 40 * 4709017 * 2
def baseEnd_4709017 : Nat := 2417989131193307683031131

theorem tailTrace_4709017 : CollatzResearch.WordTrace tailWord_4709017 prefixEnd_4709017 2417989131193307683031131 := by
  unfold tailWord_4709017
  simp only [CollatzResearch.WordTrace]
  refine ⟨171751959981043119920205305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114501306654028746613470203 171751959981043119920205305)
  ·
    refine ⟨128813969985782339940153979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171751959981043119920205305 128813969985782339940153979)
    ·
      refine ⟨193220954978673509910230969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128813969985782339940153979 193220954978673509910230969)
      ·
        refine ⟨144915716234005132432673227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193220954978673509910230969 144915716234005132432673227)
        ·
          refine ⟨217373574351007698649009841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144915716234005132432673227 217373574351007698649009841)
          ·
            refine ⟨163030180763255773986757381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217373574351007698649009841 163030180763255773986757381)
            ·
              refine ⟨30568158893110457622517009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163030180763255773986757381 30568158893110457622517009)
              ·
                refine ⟨22926119169832843216887757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30568158893110457622517009 22926119169832843216887757)
                ·
                  refine ⟨8597294688687316206332909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22926119169832843216887757 8597294688687316206332909)
                  ·
                    refine ⟨3223985508257743577374841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8597294688687316206332909 3223985508257743577374841)
                    ·
                      refine ⟨2417989131193307683031131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3223985508257743577374841 2417989131193307683031131)
                      ·
                        rfl

theorem cell23_4709017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 3, 2].length) (baseStart_4709017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709017 prefixEnd_4709017 := by exact prefixLift 4709017
  have htrace : WordTrace (prefixWord ++ tailWord_4709017) baseStart_4709017 baseEnd_4709017 := by
    simpa [prefixWord, tailWord_4709017, baseEnd_4709017] using wordTrace_append hprefix tailTrace_4709017
  have hstable : (prefixWord ++ tailWord_4709017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709017).length < 2 ^ (prefixWord ++ tailWord_4709017).sum := by decide
  have hdescent : baseEnd_4709017 < baseStart_4709017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709018 : List Nat := [3, 1, 1, 6, 1, 2, 2, 1, 2, 4]
def baseStart_4709018 : Nat := 118140960795 + 4709018 * 2 ^ 59
def prefixEnd_4709018 : Nat := 4983230072969 + 3 ^ 40 * 4709018 * 2
def baseEnd_4709018 : Nat := 805996548224654059706209

theorem tailTrace_4709018 : CollatzResearch.WordTrace tailWord_4709018 prefixEnd_4709018 805996548224654059706209 := by
  unfold tailWord_4709018
  simp only [CollatzResearch.WordTrace]
  refine ⟨42937999113509874272747927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114501330969359664727327805 42937999113509874272747927)
  ·
    refine ⟨64406998670264811409121891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42937999113509874272747927 64406998670264811409121891)
    ·
      refine ⟨96610498005397217113682837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64406998670264811409121891 96610498005397217113682837)
      ·
        refine ⟨4528617094002994552203883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96610498005397217113682837 4528617094002994552203883)
        ·
          refine ⟨6792925641004491828305825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4528617094002994552203883 6792925641004491828305825)
          ·
            refine ⟨5094694230753368871229369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6792925641004491828305825 5094694230753368871229369)
            ·
              refine ⟨3821020673065026653422027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5094694230753368871229369 3821020673065026653422027)
              ·
                refine ⟨5731531009597539980133041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3821020673065026653422027 5731531009597539980133041)
                ·
                  refine ⟨4298648257198154985099781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5731531009597539980133041 4298648257198154985099781)
                  ·
                    refine ⟨805996548224654059706209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4298648257198154985099781 805996548224654059706209)
                    ·
                      rfl

theorem cell23_4709018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_4709018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709018 prefixEnd_4709018 := by exact prefixLift 4709018
  have htrace : WordTrace (prefixWord ++ tailWord_4709018) baseStart_4709018 baseEnd_4709018 := by
    simpa [prefixWord, tailWord_4709018, baseEnd_4709018] using wordTrace_append hprefix tailTrace_4709018
  have hstable : (prefixWord ++ tailWord_4709018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709018).length < 2 ^ (prefixWord ++ tailWord_4709018).sum := by decide
  have hdescent : baseEnd_4709018 < baseStart_4709018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709050 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_4709050 : Nat := 118140960795 + 4709050 * 2 ^ 59
def prefixEnd_4709050 : Nat := 4983230072969 + 3 ^ 40 * 4709050 * 2
def baseEnd_4709050 : Nat := 2418006076054906053918479

theorem tailTrace_4709050 : CollatzResearch.WordTrace tailWord_4709050 prefixEnd_4709050 2418006076054906053918479 := by
  unfold tailWord_4709050
  simp only [CollatzResearch.WordTrace]
  refine ⟨42938290897480891639039151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114502109059949044370771069 42938290897480891639039151)
  ·
    refine ⟨64407436346221337458558727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42938290897480891639039151 64407436346221337458558727)
    ·
      refine ⟨96611154519332006187838091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64407436346221337458558727 96611154519332006187838091)
      ·
        refine ⟨144916731778998009281757137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96611154519332006187838091 144916731778998009281757137)
        ·
          refine ⟨108687548834248506961317853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144916731778998009281757137 108687548834248506961317853)
          ·
            refine ⟨40757830812843190110494195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108687548834248506961317853 40757830812843190110494195)
            ·
              refine ⟨61136746219264785165741293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40757830812843190110494195 61136746219264785165741293)
              ·
                refine ⟨22926279832224294437152985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61136746219264785165741293 22926279832224294437152985)
                ·
                  refine ⟨17194709874168220827864739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22926279832224294437152985 17194709874168220827864739)
                  ·
                    refine ⟨25792064811252331241797109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17194709874168220827864739 25792064811252331241797109)
                    ·
                      refine ⟨2418006076054906053918479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25792064811252331241797109 2418006076054906053918479)
                      ·
                        rfl

theorem cell23_4709050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_4709050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709050 prefixEnd_4709050 := by exact prefixLift 4709050
  have htrace : WordTrace (prefixWord ++ tailWord_4709050) baseStart_4709050 baseEnd_4709050 := by
    simpa [prefixWord, tailWord_4709050, baseEnd_4709050] using wordTrace_append hprefix tailTrace_4709050
  have hstable : (prefixWord ++ tailWord_4709050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709050).length < 2 ^ (prefixWord ++ tailWord_4709050).sum := by decide
  have hdescent : baseEnd_4709050 < baseStart_4709050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709120 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 4]
def baseStart_4709120 : Nat := 118140960795 + 4709120 * 2 ^ 59
def prefixEnd_4709120 : Nat := 4983230072969 + 3 ^ 40 * 4709120 * 2
def baseEnd_4709120 : Nat := 2418042019700720780043157

theorem tailTrace_4709120 : CollatzResearch.WordTrace tailWord_4709120 prefixEnd_4709120 2418042019700720780043157 := by
  unfold tailWord_4709120
  simp only [CollatzResearch.WordTrace]
  refine ⟨85877858349834984255602407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114503811133113312340803209 85877858349834984255602407)
  ·
    refine ⟨128816787524752476383403611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85877858349834984255602407 128816787524752476383403611)
    ·
      refine ⟨193225181287128714575105417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128816787524752476383403611 193225181287128714575105417)
      ·
        refine ⟨144918885965346535931329063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193225181287128714575105417 144918885965346535931329063)
        ·
          refine ⟨217378328948019803896993595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144918885965346535931329063 217378328948019803896993595)
          ·
            refine ⟨326067493422029705845490393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217378328948019803896993595 326067493422029705845490393)
            ·
              refine ⟨244550620066522279384117795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326067493422029705845490393 244550620066522279384117795)
              ·
                refine ⟨366825930099783419076176693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244550620066522279384117795 366825930099783419076176693)
                ·
                  refine ⟨34389930946854695538391565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 366825930099783419076176693 34389930946854695538391565)
                  ·
                    refine ⟨12896224105070510826896837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34389930946854695538391565 12896224105070510826896837)
                    ·
                      refine ⟨2418042019700720780043157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12896224105070510826896837 2418042019700720780043157)
                      ·
                        rfl

theorem cell23_4709120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_4709120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709120 prefixEnd_4709120 := by exact prefixLift 4709120
  have htrace : WordTrace (prefixWord ++ tailWord_4709120) baseStart_4709120 baseEnd_4709120 := by
    simpa [prefixWord, tailWord_4709120, baseEnd_4709120] using wordTrace_append hprefix tailTrace_4709120
  have hstable : (prefixWord ++ tailWord_4709120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709120).length < 2 ^ (prefixWord ++ tailWord_4709120).sum := by decide
  have hdescent : baseEnd_4709120 < baseStart_4709120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709157 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 1, 4, 3]
def baseStart_4709157 : Nat := 118140960795 + 4709157 * 2 ^ 59
def prefixEnd_4709157 : Nat := 4983230072969 + 3 ^ 40 * 4709157 * 2
def baseEnd_4709157 : Nat := 2418061018484937135280487

theorem tailTrace_4709157 : CollatzResearch.WordTrace tailWord_4709157 prefixEnd_4709157 2418061018484937135280487 := by
  unfold tailWord_4709157
  simp only [CollatzResearch.WordTrace]
  refine ⟨171757066200535923830301725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114504710800357282553534483 171757066200535923830301725)
  ·
    refine ⟨64408899825200971436363147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171757066200535923830301725 64408899825200971436363147)
    ·
      refine ⟨96613349737801457154544721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64408899825200971436363147 96613349737801457154544721)
      ·
        refine ⟨72460012303351092865908541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96613349737801457154544721 72460012303351092865908541)
        ·
          refine ⟨27172504613756659824715703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72460012303351092865908541 27172504613756659824715703)
          ·
            refine ⟨40758756920634989737073555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27172504613756659824715703 40758756920634989737073555)
            ·
              refine ⟨61138135380952484605610333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40758756920634989737073555 61138135380952484605610333)
              ·
                refine ⟨22926800767857181727103875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61138135380952484605610333 22926800767857181727103875)
                ·
                  refine ⟨34390201151785772590655813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22926800767857181727103875 34390201151785772590655813)
                  ·
                    refine ⟨6448162715959832360747965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34390201151785772590655813 6448162715959832360747965)
                    ·
                      refine ⟨2418061018484937135280487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6448162715959832360747965 2418061018484937135280487)
                      ·
                        rfl

theorem cell23_4709157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_4709157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709157 prefixEnd_4709157 := by exact prefixLift 4709157
  have htrace : WordTrace (prefixWord ++ tailWord_4709157) baseStart_4709157 baseEnd_4709157 := by
    simpa [prefixWord, tailWord_4709157, baseEnd_4709157] using wordTrace_append hprefix tailTrace_4709157
  have hstable : (prefixWord ++ tailWord_4709157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709157).length < 2 ^ (prefixWord ++ tailWord_4709157).sum := by decide
  have hdescent : baseEnd_4709157 < baseStart_4709157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709247 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 5]
def baseStart_4709247 : Nat := 118140960795 + 4709247 * 2 ^ 59
def prefixEnd_4709247 : Nat := 4983230072969 + 3 ^ 40 * 4709247 * 2
def baseEnd_4709247 : Nat := 2418107231743841783155073

theorem tailTrace_4709247 : CollatzResearch.WordTrace tailWord_4709247 prefixEnd_4709247 2418107231743841783155073 := by
  unfold tailWord_4709247
  simp only [CollatzResearch.WordTrace]
  refine ⟨171760348770209869201077995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114506899180139912800718663 171760348770209869201077995)
  ·
    refine ⟨257640523155314803801616993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171760348770209869201077995 257640523155314803801616993)
    ·
      refine ⟨193230392366486102851212745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257640523155314803801616993 193230392366486102851212745)
      ·
        refine ⟨144922794274864577138409559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193230392366486102851212745 144922794274864577138409559)
        ·
          refine ⟨217384191412296865707614339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144922794274864577138409559 217384191412296865707614339)
          ·
            refine ⟨326076287118445298561421509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217384191412296865707614339 326076287118445298561421509)
            ·
              refine ⟨61139303834708493480266533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 326076287118445298561421509 61139303834708493480266533)
              ·
                refine ⟨11463619469007842527549975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61139303834708493480266533 11463619469007842527549975)
                ·
                  refine ⟨17195429203511763791324963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11463619469007842527549975 17195429203511763791324963)
                  ·
                    refine ⟨25793143805267645686987445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17195429203511763791324963 25793143805267645686987445)
                    ·
                      refine ⟨2418107231743841783155073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25793143805267645686987445 2418107231743841783155073)
                      ·
                        rfl

theorem cell23_4709247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_4709247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709247 prefixEnd_4709247 := by exact prefixLift 4709247
  have htrace : WordTrace (prefixWord ++ tailWord_4709247) baseStart_4709247 baseEnd_4709247 := by
    simpa [prefixWord, tailWord_4709247, baseEnd_4709247] using wordTrace_append hprefix tailTrace_4709247
  have hstable : (prefixWord ++ tailWord_4709247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709247).length < 2 ^ (prefixWord ++ tailWord_4709247).sum := by decide
  have hdescent : baseEnd_4709247 < baseStart_4709247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709317 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_4709317 : Nat := 118140960795 + 4709317 * 2 ^ 59
def prefixEnd_4709317 : Nat := 4983230072969 + 3 ^ 40 * 4709317 * 2
def baseEnd_4709317 : Nat := 2418143175389656509279751

theorem tailTrace_4709317 : CollatzResearch.WordTrace tailWord_4709317 prefixEnd_4709317 2418143175389656509279751 := by
  unfold tailWord_4709317
  simp only [CollatzResearch.WordTrace]
  refine ⟨171762901879956271156126205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114508601253304180770750803 171762901879956271156126205)
  ·
    refine ⟨64411088204983601683547327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171762901879956271156126205 64411088204983601683547327)
    ·
      refine ⟨96616632307475402525320991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64411088204983601683547327 96616632307475402525320991)
      ·
        refine ⟨144924948461213103787981487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96616632307475402525320991 144924948461213103787981487)
        ·
          refine ⟨217387422691819655681972231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144924948461213103787981487 217387422691819655681972231)
          ·
            refine ⟨326081134037729483522958347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217387422691819655681972231 326081134037729483522958347)
            ·
              refine ⟨489121701056594225284437521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326081134037729483522958347 489121701056594225284437521)
              ·
                refine ⟨366841275792445668963328141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489121701056594225284437521 366841275792445668963328141)
                ·
                  refine ⟨137565478422167125861248053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 366841275792445668963328141 137565478422167125861248053)
                  ·
                    refine ⟨12896763602078168049492005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 137565478422167125861248053 12896763602078168049492005)
                    ·
                      refine ⟨2418143175389656509279751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12896763602078168049492005 2418143175389656509279751)
                      ·
                        rfl

theorem cell23_4709317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_4709317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709317 prefixEnd_4709317 := by exact prefixLift 4709317
  have htrace : WordTrace (prefixWord ++ tailWord_4709317) baseStart_4709317 baseEnd_4709317 := by
    simpa [prefixWord, tailWord_4709317, baseEnd_4709317] using wordTrace_append hprefix tailTrace_4709317
  have hstable : (prefixWord ++ tailWord_4709317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709317).length < 2 ^ (prefixWord ++ tailWord_4709317).sum := by decide
  have hdescent : baseEnd_4709317 < baseStart_4709317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709338 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2]
def baseStart_4709338 : Nat := 118140960795 + 4709338 * 2 ^ 59
def prefixEnd_4709338 : Nat := 4983230072969 + 3 ^ 40 * 4709338 * 2
def baseEnd_4709338 : Nat := 2418153958483400927117155

theorem tailTrace_4709338 : CollatzResearch.WordTrace tailWord_4709338 prefixEnd_4709338 2418153958483400927117155 := by
  unfold tailWord_4709338
  simp only [CollatzResearch.WordTrace]
  refine ⟨42940916953220047935660167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114509111875253461161760445 42940916953220047935660167)
  ·
    refine ⟨64411375429830071903490251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42940916953220047935660167 64411375429830071903490251)
    ·
      refine ⟨96617063144745107855235377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64411375429830071903490251 96617063144745107855235377)
      ·
        refine ⟨72462797358558830891426533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96617063144745107855235377 72462797358558830891426533)
        ·
          refine ⟨13586774504729780792142475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72462797358558830891426533 13586774504729780792142475)
          ·
            refine ⟨20380161757094671188213713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13586774504729780792142475 20380161757094671188213713)
            ·
              refine ⟨15285121317821003391160285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20380161757094671188213713 15285121317821003391160285)
              ·
                refine ⟨5731920494182876271685107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15285121317821003391160285 5731920494182876271685107)
                ·
                  refine ⟨8597880741274314407527661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5731920494182876271685107 8597880741274314407527661)
                  ·
                    refine ⟨3224205277977867902822873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8597880741274314407527661 3224205277977867902822873)
                    ·
                      refine ⟨2418153958483400927117155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3224205277977867902822873 2418153958483400927117155)
                      ·
                        rfl

theorem cell23_4709338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_4709338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709338 prefixEnd_4709338 := by exact prefixLift 4709338
  have htrace : WordTrace (prefixWord ++ tailWord_4709338) baseStart_4709338 baseEnd_4709338 := by
    simpa [prefixWord, tailWord_4709338, baseEnd_4709338] using wordTrace_append hprefix tailTrace_4709338
  have hstable : (prefixWord ++ tailWord_4709338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709338).length < 2 ^ (prefixWord ++ tailWord_4709338).sum := by decide
  have hdescent : baseEnd_4709338 < baseStart_4709338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709411 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 2, 5, 2]
def baseStart_4709411 : Nat := 118140960795 + 4709411 * 2 ^ 59
def prefixEnd_4709411 : Nat := 4983230072969 + 3 ^ 40 * 4709411 * 2
def baseEnd_4709411 : Nat := 2418191442571179141504319

theorem tailTrace_4709411 : CollatzResearch.WordTrace tailWord_4709411 prefixEnd_4709411 2418191442571179141504319 := by
  unfold tailWord_4709411
  simp only [CollatzResearch.WordTrace]
  refine ⟨171766330341615725210048087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114510886894410483473365391 171766330341615725210048087)
  ·
    refine ⟨257649495512423587815072131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171766330341615725210048087 257649495512423587815072131)
    ·
      refine ⟨386474243268635381722608197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257649495512423587815072131 386474243268635381722608197)
      ·
        refine ⟨72463920612869134072989037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 386474243268635381722608197 72463920612869134072989037)
        ·
          refine ⟨27173970229825925277370889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72463920612869134072989037 27173970229825925277370889)
          ·
            refine ⟨20380477672369443958028167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27173970229825925277370889 20380477672369443958028167)
            ·
              refine ⟨30570716508554165937042251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20380477672369443958028167 30570716508554165937042251)
              ·
                refine ⟨45856074762831248905563377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30570716508554165937042251 45856074762831248905563377)
                ·
                  refine ⟨34392056072123436679172533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45856074762831248905563377 34392056072123436679172533)
                  ·
                    refine ⟨3224255256761572188672425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34392056072123436679172533 3224255256761572188672425)
                    ·
                      refine ⟨2418191442571179141504319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3224255256761572188672425 2418191442571179141504319)
                      ·
                        rfl

theorem cell23_4709411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_4709411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709411 prefixEnd_4709411 := by exact prefixLift 4709411
  have htrace : WordTrace (prefixWord ++ tailWord_4709411) baseStart_4709411 baseEnd_4709411 := by
    simpa [prefixWord, tailWord_4709411, baseEnd_4709411] using wordTrace_append hprefix tailTrace_4709411
  have hstable : (prefixWord ++ tailWord_4709411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709411).length < 2 ^ (prefixWord ++ tailWord_4709411).sum := by decide
  have hdescent : baseEnd_4709411 < baseStart_4709411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709418 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_4709418 : Nat := 118140960795 + 4709418 * 2 ^ 59
def prefixEnd_4709418 : Nat := 4983230072969 + 3 ^ 40 * 4709418 * 2
def baseEnd_4709418 : Nat := 2418195036935760614116787

theorem tailTrace_4709418 : CollatzResearch.WordTrace tailWord_4709418 prefixEnd_4709418 2418195036935760614116787 := by
  unfold tailWord_4709418
  simp only [CollatzResearch.WordTrace]
  refine ⟨42941646413147591351388227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114511057101726910270368605 42941646413147591351388227)
  ·
    refine ⟨64412469619721387027082341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42941646413147591351388227 64412469619721387027082341)
    ·
      refine ⟨12077338053697760067577939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64412469619721387027082341 12077338053697760067577939)
      ·
        refine ⟨18116007080546640101366909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12077338053697760067577939 18116007080546640101366909)
        ·
          refine ⟨6793502655204990038012591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18116007080546640101366909 6793502655204990038012591)
          ·
            refine ⟨10190253982807485057018887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6793502655204990038012591 10190253982807485057018887)
            ·
              refine ⟨15285380974211227585528331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10190253982807485057018887 15285380974211227585528331)
              ·
                refine ⟨22928071461316841378292497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15285380974211227585528331 22928071461316841378292497)
                ·
                  refine ⟨17196053595987631033719373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22928071461316841378292497 17196053595987631033719373)
                  ·
                    refine ⟨6448520098495361637644765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17196053595987631033719373 6448520098495361637644765)
                    ·
                      refine ⟨2418195036935760614116787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6448520098495361637644765 2418195036935760614116787)
                      ·
                        rfl

theorem cell23_4709418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_4709418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709418 prefixEnd_4709418 := by exact prefixLift 4709418
  have htrace : WordTrace (prefixWord ++ tailWord_4709418) baseStart_4709418 baseEnd_4709418 := by
    simpa [prefixWord, tailWord_4709418, baseEnd_4709418] using wordTrace_append hprefix tailTrace_4709418
  have hstable : (prefixWord ++ tailWord_4709418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709418).length < 2 ^ (prefixWord ++ tailWord_4709418).sum := by decide
  have hdescent : baseEnd_4709418 < baseStart_4709418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709424 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 4]
def baseStart_4709424 : Nat := 118140960795 + 4709424 * 2 ^ 59
def prefixEnd_4709424 : Nat := 4983230072969 + 3 ^ 40 * 4709424 * 2
def baseEnd_4709424 : Nat := 2418198117819687590641759

theorem tailTrace_4709424 : CollatzResearch.WordTrace tailWord_4709424 prefixEnd_4709424 2418198117819687590641759 := by
  unfold tailWord_4709424
  simp only [CollatzResearch.WordTrace]
  refine ⟨85883402245284314215135663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114511202993712418953514217 85883402245284314215135663)
  ·
    refine ⟨128825103367926471322703495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85883402245284314215135663 128825103367926471322703495)
    ·
      refine ⟨193237655051889706984055243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128825103367926471322703495 193237655051889706984055243)
      ·
        refine ⟨289856482577834560476082865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193237655051889706984055243 289856482577834560476082865)
        ·
          refine ⟨217392361933375920357062149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289856482577834560476082865 217392361933375920357062149)
          ·
            refine ⟨40761067862507985066949153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217392361933375920357062149 40761067862507985066949153)
            ·
              refine ⟨30570800896880988800211865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40761067862507985066949153 30570800896880988800211865)
              ·
                refine ⟨22928100672660741600158899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30570800896880988800211865 22928100672660741600158899)
                ·
                  refine ⟨34392151008991112400238349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22928100672660741600158899 34392151008991112400238349)
                  ·
                    refine ⟨12897056628371667150089381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34392151008991112400238349 12897056628371667150089381)
                    ·
                      refine ⟨2418198117819687590641759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12897056628371667150089381 2418198117819687590641759)
                      ·
                        rfl

theorem cell23_4709424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_4709424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709424 prefixEnd_4709424 := by exact prefixLift 4709424
  have htrace : WordTrace (prefixWord ++ tailWord_4709424) baseStart_4709424 baseEnd_4709424 := by
    simpa [prefixWord, tailWord_4709424, baseEnd_4709424] using wordTrace_append hprefix tailTrace_4709424
  have hstable : (prefixWord ++ tailWord_4709424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709424).length < 2 ^ (prefixWord ++ tailWord_4709424).sum := by decide
  have hdescent : baseEnd_4709424 < baseStart_4709424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709438 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_4709438 : Nat := 118140960795 + 4709438 * 2 ^ 59
def prefixEnd_4709438 : Nat := 4983230072969 + 3 ^ 40 * 4709438 * 2
def baseEnd_4709438 : Nat := 806068435516283511955565

theorem tailTrace_4709438 : CollatzResearch.WordTrace tailWord_4709438 prefixEnd_4709438 806068435516283511955565 := by
  unfold tailWord_4709438
  simp only [CollatzResearch.WordTrace]
  refine ⟨21470914389064738602660121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114511543408345272547520645 21470914389064738602660121)
  ·
    refine ⟨16103185791798553951995091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21470914389064738602660121 16103185791798553951995091)
    ·
      refine ⟨24154778687697830927992637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16103185791798553951995091 24154778687697830927992637)
      ·
        refine ⟨9058042007886686597997239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24154778687697830927992637 9058042007886686597997239)
        ·
          refine ⟨13587063011830029896995859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9058042007886686597997239 13587063011830029896995859)
          ·
            refine ⟨20380594517745044845493789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13587063011830029896995859 20380594517745044845493789)
            ·
              refine ⟨7642722944154391817060171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20380594517745044845493789 7642722944154391817060171)
              ·
                refine ⟨11464084416231587725590257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7642722944154391817060171 11464084416231587725590257)
                ·
                  refine ⟨8598063312173690794192693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11464084416231587725590257 8598063312173690794192693)
                  ·
                    refine ⟨806068435516283511955565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8598063312173690794192693 806068435516283511955565)
                    ·
                      rfl

theorem cell23_4709438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_4709438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709438 prefixEnd_4709438 := by exact prefixLift 4709438
  have htrace : WordTrace (prefixWord ++ tailWord_4709438) baseStart_4709438 baseEnd_4709438 := by
    simpa [prefixWord, tailWord_4709438, baseEnd_4709438] using wordTrace_append hprefix tailTrace_4709438
  have hstable : (prefixWord ++ tailWord_4709438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709438).length < 2 ^ (prefixWord ++ tailWord_4709438).sum := by decide
  have hdescent : baseEnd_4709438 < baseStart_4709438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709454 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6]
def baseStart_4709454 : Nat := 118140960795 + 4709454 * 2 ^ 59
def prefixEnd_4709454 : Nat := 4983230072969 + 3 ^ 40 * 4709454 * 2
def baseEnd_4709454 : Nat := 2418213522239322473266621

theorem tailTrace_4709454 : CollatzResearch.WordTrace tailWord_4709454 prefixEnd_4709454 2418213522239322473266621 := by
  unfold tailWord_4709454
  simp only [CollatzResearch.WordTrace]
  refine ⟨21470987335057492944232927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114511932453639962369242277 21470987335057492944232927)
  ·
    refine ⟨32206481002586239416349391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21470987335057492944232927 32206481002586239416349391)
    ·
      refine ⟨48309721503879359124524087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32206481002586239416349391 48309721503879359124524087)
      ·
        refine ⟨72464582255819038686786131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48309721503879359124524087 72464582255819038686786131)
        ·
          refine ⟨108696873383728558030179197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72464582255819038686786131 108696873383728558030179197)
          ·
            refine ⟨40761327518898209261317199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108696873383728558030179197 40761327518898209261317199)
            ·
              refine ⟨61141991278347313891975799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40761327518898209261317199 61141991278347313891975799)
              ·
                refine ⟨91712986917520970837963699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61141991278347313891975799 91712986917520970837963699)
                ·
                  refine ⟨137569480376281456256945549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91712986917520970837963699 137569480376281456256945549)
                  ·
                    refine ⟨51588555141105546096354581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 137569480376281456256945549 51588555141105546096354581)
                    ·
                      refine ⟨2418213522239322473266621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51588555141105546096354581 2418213522239322473266621)
                      ·
                        rfl

theorem cell23_4709454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_4709454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709454 prefixEnd_4709454 := by exact prefixLift 4709454
  have htrace : WordTrace (prefixWord ++ tailWord_4709454) baseStart_4709454 baseEnd_4709454 := by
    simpa [prefixWord, tailWord_4709454, baseEnd_4709454] using wordTrace_append hprefix tailTrace_4709454
  have hstable : (prefixWord ++ tailWord_4709454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709454).length < 2 ^ (prefixWord ++ tailWord_4709454).sum := by decide
  have hdescent : baseEnd_4709454 < baseStart_4709454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709458 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_4709458 : Nat := 118140960795 + 4709458 * 2 ^ 59
def prefixEnd_4709458 : Nat := 4983230072969 + 3 ^ 40 * 4709458 * 2
def baseEnd_4709458 : Nat := 2418215576161940457616603

theorem tailTrace_4709458 : CollatzResearch.WordTrace tailWord_4709458 prefixEnd_4709458 2418215576161940457616603 := by
  unfold tailWord_4709458
  simp only [CollatzResearch.WordTrace]
  refine ⟨42942011143111363059252257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114512029714963634824672685 42942011143111363059252257)
  ·
    refine ⟨32206508357333522294439193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42942011143111363059252257 32206508357333522294439193)
    ·
      refine ⟨24154881268000141720829395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32206508357333522294439193 24154881268000141720829395)
      ·
        refine ⟨36232321902000212581244093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24154881268000141720829395 36232321902000212581244093)
        ·
          refine ⟨13587120713250079717966535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36232321902000212581244093 13587120713250079717966535)
          ·
            refine ⟨20380681069875119576949803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13587120713250079717966535 20380681069875119576949803)
            ·
              refine ⟨30571021604812679365424705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20380681069875119576949803 30571021604812679365424705)
              ·
                refine ⟨22928266203609509524068529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30571021604812679365424705 22928266203609509524068529)
                ·
                  refine ⟨17196199652707132143051397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22928266203609509524068529 17196199652707132143051397)
                  ·
                    refine ⟨3224287434882587276822137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17196199652707132143051397 3224287434882587276822137)
                    ·
                      refine ⟨2418215576161940457616603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3224287434882587276822137 2418215576161940457616603)
                      ·
                        rfl

theorem cell23_4709458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_4709458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709458 prefixEnd_4709458 := by exact prefixLift 4709458
  have htrace : WordTrace (prefixWord ++ tailWord_4709458) baseStart_4709458 baseEnd_4709458 := by
    simpa [prefixWord, tailWord_4709458, baseEnd_4709458] using wordTrace_append hprefix tailTrace_4709458
  have hstable : (prefixWord ++ tailWord_4709458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709458).length < 2 ^ (prefixWord ++ tailWord_4709458).sum := by decide
  have hdescent : baseEnd_4709458 < baseStart_4709458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709461 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 4, 2, 3]
def baseStart_4709461 : Nat := 118140960795 + 4709461 * 2 ^ 59
def prefixEnd_4709461 : Nat := 4983230072969 + 3 ^ 40 * 4709461 * 2
def baseEnd_4709461 : Nat := 2418217116603903945879089

theorem tailTrace_4709461 : CollatzResearch.WordTrace tailWord_4709461 prefixEnd_4709461 2418217116603903945879089 := by
  unfold tailWord_4709461
  simp only [CollatzResearch.WordTrace]
  refine ⟨171768153991434583749368237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114512102660956389166245491 171768153991434583749368237)
  ·
    refine ⟨64413057746787968906013089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171768153991434583749368237 64413057746787968906013089)
    ·
      refine ⟨48309793310090976679509817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64413057746787968906013089 48309793310090976679509817)
      ·
        refine ⟨36232344982568232509632363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48309793310090976679509817 36232344982568232509632363)
        ·
          refine ⟨54348517473852348764448545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36232344982568232509632363 54348517473852348764448545)
          ·
            refine ⟨40761388105389261573336409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54348517473852348764448545 40761388105389261573336409)
            ·
              refine ⟨30571041079041946180002307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40761388105389261573336409 30571041079041946180002307)
              ·
                refine ⟨45856561618562919270003461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30571041079041946180002307 45856561618562919270003461)
                ·
                  refine ⟨8598105303480547363125649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45856561618562919270003461 8598105303480547363125649)
                  ·
                    refine ⟨6448578977610410522344237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8598105303480547363125649 6448578977610410522344237)
                    ·
                      refine ⟨2418217116603903945879089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6448578977610410522344237 2418217116603903945879089)
                      ·
                        rfl

theorem cell23_4709461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_4709461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709461 prefixEnd_4709461 := by exact prefixLift 4709461
  have htrace : WordTrace (prefixWord ++ tailWord_4709461) baseStart_4709461 baseEnd_4709461 := by
    simpa [prefixWord, tailWord_4709461, baseEnd_4709461] using wordTrace_append hprefix tailTrace_4709461
  have hstable : (prefixWord ++ tailWord_4709461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709461).length < 2 ^ (prefixWord ++ tailWord_4709461).sum := by decide
  have hdescent : baseEnd_4709461 < baseStart_4709461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709464 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 8]
def baseStart_4709464 : Nat := 118140960795 + 4709464 * 2 ^ 59
def prefixEnd_4709464 : Nat := 4983230072969 + 3 ^ 40 * 4709464 * 2
def baseEnd_4709464 : Nat := 268690961893985270460175

theorem tailTrace_4709464 : CollatzResearch.WordTrace tailWord_4709464 prefixEnd_4709464 268690961893985270460175 := by
  unfold tailWord_4709464
  simp only [CollatzResearch.WordTrace]
  refine ⟨85884131705211857630863723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114512175606949143507818297 85884131705211857630863723)
  ·
    refine ⟨128826197557817786446295585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85884131705211857630863723 128826197557817786446295585)
    ·
      refine ⟨96619648168363339834721689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128826197557817786446295585 96619648168363339834721689)
      ·
        refine ⟨72464736126272504876041267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96619648168363339834721689 72464736126272504876041267)
        ·
          refine ⟨108697104189408757314061901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72464736126272504876041267 108697104189408757314061901)
          ·
            refine ⟨40761414071028283992773213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108697104189408757314061901 40761414071028283992773213)
            ·
              refine ⟨15285530276635606497289955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40761414071028283992773213 15285530276635606497289955)
              ·
                refine ⟨22928295414953409745934933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15285530276635606497289955 22928295414953409745934933)
                ·
                  refine ⟨268690961893985270460175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22928295414953409745934933 268690961893985270460175)
                  ·
                    rfl

theorem cell23_4709464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 8].length) (baseStart_4709464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709464 prefixEnd_4709464 := by exact prefixLift 4709464
  have htrace : WordTrace (prefixWord ++ tailWord_4709464) baseStart_4709464 baseEnd_4709464 := by
    simpa [prefixWord, tailWord_4709464, baseEnd_4709464] using wordTrace_append hprefix tailTrace_4709464
  have hstable : (prefixWord ++ tailWord_4709464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709464).length < 2 ^ (prefixWord ++ tailWord_4709464).sum := by decide
  have hdescent : baseEnd_4709464 < baseStart_4709464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709468 : List Nat := [2, 2, 4, 1, 1, 1, 4, 1, 3, 4]
def baseStart_4709468 : Nat := 118140960795 + 4709468 * 2 ^ 59
def prefixEnd_4709468 : Nat := 4983230072969 + 3 ^ 40 * 4709468 * 2
def baseEnd_4709468 : Nat := 806073570322828472830519

theorem tailTrace_4709468 : CollatzResearch.WordTrace tailWord_4709468 prefixEnd_4709468 806073570322828472830519 := by
  unfold tailWord_4709468
  simp only [CollatzResearch.WordTrace]
  refine ⟨85884204651204611972436529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114512272868272815963248705 85884204651204611972436529)
  ·
    refine ⟨64413153488403458979327397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85884204651204611972436529 64413153488403458979327397)
    ·
      refine ⟨12077466279075648558623887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64413153488403458979327397 12077466279075648558623887)
      ·
        refine ⟨18116199418613472837935831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12077466279075648558623887 18116199418613472837935831)
        ·
          refine ⟨27174299127920209256903747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18116199418613472837935831 27174299127920209256903747)
          ·
            refine ⟨40761448691880313885355621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27174299127920209256903747 40761448691880313885355621)
            ·
              refine ⟨7642771629727558853504179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40761448691880313885355621 7642771629727558853504179)
              ·
                refine ⟨11464157444591338280256269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7642771629727558853504179 11464157444591338280256269)
                ·
                  refine ⟨4299059041721751855096101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11464157444591338280256269 4299059041721751855096101)
                  ·
                    refine ⟨806073570322828472830519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4299059041721751855096101 806073570322828472830519)
                    ·
                      rfl

theorem cell23_4709468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_4709468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709468 prefixEnd_4709468 := by exact prefixLift 4709468
  have htrace : WordTrace (prefixWord ++ tailWord_4709468) baseStart_4709468 baseEnd_4709468 := by
    simpa [prefixWord, tailWord_4709468, baseEnd_4709468] using wordTrace_append hprefix tailTrace_4709468
  have hstable : (prefixWord ++ tailWord_4709468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709468).length < 2 ^ (prefixWord ++ tailWord_4709468).sum := by decide
  have hdescent : baseEnd_4709468 < baseStart_4709468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709484 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_4709484 : Nat := 118140960795 + 4709484 * 2 ^ 59
def prefixEnd_4709484 : Nat := 4983230072969 + 3 ^ 40 * 4709484 * 2
def baseEnd_4709484 : Nat := 2418228926658957355891483

theorem tailTrace_4709484 : CollatzResearch.WordTrace tailWord_4709484 prefixEnd_4709484 2418228926658957355891483 := by
  unfold tailWord_4709484
  simp only [CollatzResearch.WordTrace]
  refine ⟨85884496435175629338727753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114512661913567505784970337 85884496435175629338727753)
  ·
    refine ⟨64413372326381722004045815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85884496435175629338727753 64413372326381722004045815)
    ·
      refine ⟨96620058489572583006068723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64413372326381722004045815 96620058489572583006068723)
      ·
        refine ⟨144930087734358874509103085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96620058489572583006068723 144930087734358874509103085)
        ·
          refine ⟨54348782900384577940913657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144930087734358874509103085 54348782900384577940913657)
          ·
            refine ⟨40761587175288433455685243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54348782900384577940913657 40761587175288433455685243)
            ·
              refine ⟨61142380762932650183527865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40761587175288433455685243 61142380762932650183527865)
              ·
                refine ⟨45856785572199487637645899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61142380762932650183527865 45856785572199487637645899)
                ·
                  refine ⟨68785178358299231456468849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45856785572199487637645899 68785178358299231456468849)
                  ·
                    refine ⟨51588883768724423592351637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68785178358299231456468849 51588883768724423592351637)
                    ·
                      refine ⟨2418228926658957355891483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51588883768724423592351637 2418228926658957355891483)
                      ·
                        rfl

theorem cell23_4709484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_4709484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709484 prefixEnd_4709484 := by exact prefixLift 4709484
  have htrace : WordTrace (prefixWord ++ tailWord_4709484) baseStart_4709484 baseEnd_4709484 := by
    simpa [prefixWord, tailWord_4709484, baseEnd_4709484] using wordTrace_append hprefix tailTrace_4709484
  have hstable : (prefixWord ++ tailWord_4709484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709484).length < 2 ^ (prefixWord ++ tailWord_4709484).sum := by decide
  have hdescent : baseEnd_4709484 < baseStart_4709484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709531 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 4, 6, 2]
def baseStart_4709531 : Nat := 118140960795 + 4709531 * 2 ^ 59
def prefixEnd_4709531 : Nat := 4983230072969 + 3 ^ 40 * 4709531 * 2
def baseEnd_4709531 : Nat := 2418253060249718672003767

theorem tailTrace_4709531 : CollatzResearch.WordTrace tailWord_4709531 prefixEnd_4709531 2418253060249718672003767 := by
  unfold tailWord_4709531
  simp only [CollatzResearch.WordTrace]
  refine ⟨171770707101180985704416447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114513804734120657136277631 171770707101180985704416447)
  ·
    refine ⟨257656060651771478556624671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171770707101180985704416447 257656060651771478556624671)
    ·
      refine ⟨386484090977657217834937007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257656060651771478556624671 386484090977657217834937007)
      ·
        refine ⟨579726136466485826752405511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386484090977657217834937007 579726136466485826752405511)
        ·
          refine ⟨869589204699728740128608267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579726136466485826752405511 869589204699728740128608267)
          ·
            refine ⟨1304383807049593110192912401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 869589204699728740128608267 1304383807049593110192912401)
            ·
              refine ⟨978287855287194832644684301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1304383807049593110192912401 978287855287194832644684301)
              ·
                refine ⟨366857945732698062241756613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 978287855287194832644684301 366857945732698062241756613)
                ·
                  refine ⟨68785864824880886670329365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 366857945732698062241756613 68785864824880886670329365)
                  ·
                    refine ⟨3224337413666291562671689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68785864824880886670329365 3224337413666291562671689)
                    ·
                      refine ⟨2418253060249718672003767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3224337413666291562671689 2418253060249718672003767)
                      ·
                        rfl

theorem cell23_4709531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 6, 2].length) (baseStart_4709531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709531 prefixEnd_4709531 := by exact prefixLift 4709531
  have htrace : WordTrace (prefixWord ++ tailWord_4709531) baseStart_4709531 baseEnd_4709531 := by
    simpa [prefixWord, tailWord_4709531, baseEnd_4709531] using wordTrace_append hprefix tailTrace_4709531
  have hstable : (prefixWord ++ tailWord_4709531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709531).length < 2 ^ (prefixWord ++ tailWord_4709531).sum := by decide
  have hdescent : baseEnd_4709531 < baseStart_4709531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709561 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 4]
def baseStart_4709561 : Nat := 118140960795 + 4709561 * 2 ^ 59
def prefixEnd_4709561 : Nat := 4983230072969 + 3 ^ 40 * 4709561 * 2
def baseEnd_4709561 : Nat := 2418268464669353554628629

theorem tailTrace_4709561 : CollatzResearch.WordTrace tailWord_4709561 prefixEnd_4709561 2418268464669353554628629 := by
  unfold tailWord_4709561
  simp only [CollatzResearch.WordTrace]
  refine ⟨171771801291072300828008537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114514534194048200552005691 171771801291072300828008537)
  ·
    refine ⟨128828850968304225621006403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171771801291072300828008537 128828850968304225621006403)
    ·
      refine ⟨193243276452456338431509605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128828850968304225621006403 193243276452456338431509605)
      ·
        refine ⟨36233114334835563455908051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193243276452456338431509605 36233114334835563455908051)
        ·
          refine ⟨54349671502253345183862077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36233114334835563455908051 54349671502253345183862077)
          ·
            refine ⟨20381126813345004443948279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54349671502253345183862077 20381126813345004443948279)
            ·
              refine ⟨30571690220017506665922419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20381126813345004443948279 30571690220017506665922419)
              ·
                refine ⟨45857535330026259998883629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30571690220017506665922419 45857535330026259998883629)
                ·
                  refine ⟨17196575748759847499581361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45857535330026259998883629 17196575748759847499581361)
                  ·
                    refine ⟨12897431811569885624686021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17196575748759847499581361 12897431811569885624686021)
                    ·
                      refine ⟨2418268464669353554628629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12897431811569885624686021 2418268464669353554628629)
                      ·
                        rfl

theorem cell23_4709561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_4709561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709561 prefixEnd_4709561 := by exact prefixLift 4709561
  have htrace : WordTrace (prefixWord ++ tailWord_4709561) baseStart_4709561 baseEnd_4709561 := by
    simpa [prefixWord, tailWord_4709561, baseEnd_4709561] using wordTrace_append hprefix tailTrace_4709561
  have hstable : (prefixWord ++ tailWord_4709561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709561).length < 2 ^ (prefixWord ++ tailWord_4709561).sum := by decide
  have hdescent : baseEnd_4709561 < baseStart_4709561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709625 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 1, 3, 2]
def baseStart_4709625 : Nat := 118140960795 + 4709625 * 2 ^ 59
def prefixEnd_4709625 : Nat := 4983230072969 + 3 ^ 40 * 4709625 * 2
def baseEnd_4709625 : Nat := 2418301327431241304228335

theorem tailTrace_4709625 : CollatzResearch.WordTrace tailWord_4709625 prefixEnd_4709625 2418301327431241304228335 := by
  unfold tailWord_4709625
  simp only [CollatzResearch.WordTrace]
  refine ⟨171774135562840439758338329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114516090375226959838892219 171774135562840439758338329)
  ·
    refine ⟨128830601672130329818753747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171774135562840439758338329 128830601672130329818753747)
    ·
      refine ⟨193245902508195494728130621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128830601672130329818753747 193245902508195494728130621)
      ·
        refine ⟨72467213440573310523048983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193245902508195494728130621 72467213440573310523048983)
        ·
          refine ⟨108700820160859965784573475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72467213440573310523048983 108700820160859965784573475)
          ·
            refine ⟨163051230241289948676860213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108700820160859965784573475 163051230241289948676860213)
            ·
              refine ⟨15286052835120932688455645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163051230241289948676860213 15286052835120932688455645)
              ·
                refine ⟨5732269813170349758170867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15286052835120932688455645 5732269813170349758170867)
                ·
                  refine ⟨8598404719755524637256301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5732269813170349758170867 8598404719755524637256301)
                  ·
                    refine ⟨3224401769908321738971113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8598404719755524637256301 3224401769908321738971113)
                    ·
                      refine ⟨2418301327431241304228335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3224401769908321738971113 2418301327431241304228335)
                      ·
                        rfl

theorem cell23_4709625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_4709625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709625 prefixEnd_4709625 := by exact prefixLift 4709625
  have htrace : WordTrace (prefixWord ++ tailWord_4709625) baseStart_4709625 baseEnd_4709625 := by
    simpa [prefixWord, tailWord_4709625, baseEnd_4709625] using wordTrace_append hprefix tailTrace_4709625
  have hstable : (prefixWord ++ tailWord_4709625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709625).length < 2 ^ (prefixWord ++ tailWord_4709625).sum := by decide
  have hdescent : baseEnd_4709625 < baseStart_4709625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709631 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 2, 6]
def baseStart_4709631 : Nat := 118140960795 + 4709631 * 2 ^ 59
def prefixEnd_4709631 : Nat := 4983230072969 + 3 ^ 40 * 4709631 * 2
def baseEnd_4709631 : Nat := 806101469438389426917769

theorem tailTrace_4709631 : CollatzResearch.WordTrace tailWord_4709631 prefixEnd_4709631 806101469438389426917769 := by
  unfold tailWord_4709631
  simp only [CollatzResearch.WordTrace]
  refine ⟨171774354400818702783056747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114516236267212468522037831 171774354400818702783056747)
  ·
    refine ⟨257661531601228054174585121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171774354400818702783056747 257661531601228054174585121)
    ·
      refine ⟨193246148700921040630938841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257661531601228054174585121 193246148700921040630938841)
      ·
        refine ⟨144934611525690780473204131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193246148700921040630938841 144934611525690780473204131)
        ·
          refine ⟨217401917288536170709806197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144934611525690780473204131 217401917288536170709806197)
          ·
            refine ⟨20381429745800266004044331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 217401917288536170709806197 20381429745800266004044331)
            ·
              refine ⟨30572144618700399006066497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20381429745800266004044331 30572144618700399006066497)
              ·
                refine ⟨22929108464025299254549873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30572144618700399006066497 22929108464025299254549873)
                ·
                  refine ⟨17196831348018974440912405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22929108464025299254549873 17196831348018974440912405)
                  ·
                    refine ⟨806101469438389426917769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17196831348018974440912405 806101469438389426917769)
                    ·
                      rfl

theorem cell23_4709631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_4709631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709631 prefixEnd_4709631 := by exact prefixLift 4709631
  have htrace : WordTrace (prefixWord ++ tailWord_4709631) baseStart_4709631 baseEnd_4709631 := by
    simpa [prefixWord, tailWord_4709631, baseEnd_4709631] using wordTrace_append hprefix tailTrace_4709631
  have hstable : (prefixWord ++ tailWord_4709631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709631).length < 2 ^ (prefixWord ++ tailWord_4709631).sum := by decide
  have hdescent : baseEnd_4709631 < baseStart_4709631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709672 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_4709672 : Nat := 118140960795 + 4709672 * 2 ^ 59
def prefixEnd_4709672 : Nat := 4983230072969 + 3 ^ 40 * 4709672 * 2
def baseEnd_4709672 : Nat := 2418325461022002620340619

theorem tailTrace_4709672 : CollatzResearch.WordTrace tailWord_4709672 prefixEnd_4709672 2418325461022002620340619 := by
  unfold tailWord_4709672
  simp only [CollatzResearch.WordTrace]
  refine ⟨85887924896835083392649635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114517233195780111190199513 85887924896835083392649635)
  ·
    refine ⟨128831887345252625088974453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85887924896835083392649635 128831887345252625088974453)
    ·
      refine ⟨12077989438617433602091355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 128831887345252625088974453 12077989438617433602091355)
      ·
        refine ⟨18116984157926150403137033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12077989438617433602091355 18116984157926150403137033)
        ·
          refine ⟨13587738118444612802352775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18116984157926150403137033 13587738118444612802352775)
          ·
            refine ⟨20381607177666919203529163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13587738118444612802352775 20381607177666919203529163)
            ·
              refine ⟨30572410766500378805293745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20381607177666919203529163 30572410766500378805293745)
              ·
                refine ⟨22929308074875284103970309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30572410766500378805293745 22929308074875284103970309)
                ·
                  refine ⟨4299245264039115769494433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22929308074875284103970309 4299245264039115769494433)
                  ·
                    refine ⟨3224433948029336827120825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4299245264039115769494433 3224433948029336827120825)
                    ·
                      refine ⟨2418325461022002620340619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3224433948029336827120825 2418325461022002620340619)
                      ·
                        rfl

theorem cell23_4709672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_4709672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709672 prefixEnd_4709672 := by exact prefixLift 4709672
  have htrace : WordTrace (prefixWord ++ tailWord_4709672) baseStart_4709672 baseEnd_4709672 := by
    simpa [prefixWord, tailWord_4709672, baseEnd_4709672] using wordTrace_append hprefix tailTrace_4709672
  have hstable : (prefixWord ++ tailWord_4709672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709672).length < 2 ^ (prefixWord ++ tailWord_4709672).sum := by decide
  have hdescent : baseEnd_4709672 < baseStart_4709672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709721 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 2, 8]
def baseStart_4709721 : Nat := 118140960795 + 4709721 * 2 ^ 59
def prefixEnd_4709721 : Nat := 4983230072969 + 3 ^ 40 * 4709721 * 2
def baseEnd_4709721 : Nat := 806116873858024309542631

theorem tailTrace_4709721 : CollatzResearch.WordTrace tailWord_4709721 prefixEnd_4709721 806116873858024309542631 := by
  unfold tailWord_4709721
  simp only [CollatzResearch.WordTrace]
  refine ⟨171777636970492648153833017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114518424646995098769222011 171777636970492648153833017)
  ·
    refine ⟨128833227727869486115374763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171777636970492648153833017 128833227727869486115374763)
    ·
      refine ⟨193249841591804229173062145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128833227727869486115374763 193249841591804229173062145)
      ·
        refine ⟨144937381193853171879796609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193249841591804229173062145 144937381193853171879796609)
        ·
          refine ⟨108703035895389878909847457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144937381193853171879796609 108703035895389878909847457)
          ·
            refine ⟨81527276921542409182385593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108703035895389878909847457 81527276921542409182385593)
            ·
              refine ⟨61145457691156806886789195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81527276921542409182385593 61145457691156806886789195)
              ·
                refine ⟨91718186536735210330183793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61145457691156806886789195 91718186536735210330183793)
                ·
                  refine ⟨68788639902551407747637845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91718186536735210330183793 68788639902551407747637845)
                  ·
                    refine ⟨806116873858024309542631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 68788639902551407747637845 806116873858024309542631)
                    ·
                      rfl

theorem cell23_4709721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_4709721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709721 prefixEnd_4709721 := by exact prefixLift 4709721
  have htrace : WordTrace (prefixWord ++ tailWord_4709721) baseStart_4709721 baseEnd_4709721 := by
    simpa [prefixWord, tailWord_4709721, baseEnd_4709721] using wordTrace_append hprefix tailTrace_4709721
  have hstable : (prefixWord ++ tailWord_4709721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709721).length < 2 ^ (prefixWord ++ tailWord_4709721).sum := by decide
  have hdescent : baseEnd_4709721 < baseStart_4709721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709789 : List Nat := [1, 4, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_4709789 : Nat := 118140960795 + 4709789 * 2 ^ 59
def prefixEnd_4709789 : Nat := 4983230072969 + 3 ^ 40 * 4709789 * 2
def baseEnd_4709789 : Nat := 806128512752859554192527

theorem tailTrace_4709789 : CollatzResearch.WordTrace tailWord_4709789 prefixEnd_4709789 806128512752859554192527 := by
  unfold tailWord_4709789
  simp only [CollatzResearch.WordTrace]
  refine ⟨171780117134246295767308421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114520078089497530511538947 171780117134246295767308421)
  ·
    refine ⟨32208771962671180456370329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171780117134246295767308421 32208771962671180456370329)
    ·
      refine ⟨24156578972003385342277747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32208771962671180456370329 24156578972003385342277747)
      ·
        refine ⟨36234868458005078013416621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24156578972003385342277747 36234868458005078013416621)
        ·
          refine ⟨13588075671751904255031233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36234868458005078013416621 13588075671751904255031233)
          ·
            refine ⟨10191056753813928191273425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13588075671751904255031233 10191056753813928191273425)
            ·
              refine ⟨7643292565360446143455069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10191056753813928191273425 7643292565360446143455069)
              ·
                refine ⟨2866234712010167303795651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7643292565360446143455069 2866234712010167303795651)
                ·
                  refine ⟨4299352068015250955693477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866234712010167303795651 4299352068015250955693477)
                  ·
                    refine ⟨806128512752859554192527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4299352068015250955693477 806128512752859554192527)
                    ·
                      rfl

theorem cell23_4709789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_4709789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709789 prefixEnd_4709789 := by exact prefixLift 4709789
  have htrace : WordTrace (prefixWord ++ tailWord_4709789) baseStart_4709789 baseEnd_4709789 := by
    simpa [prefixWord, tailWord_4709789, baseEnd_4709789] using wordTrace_append hprefix tailTrace_4709789
  have hstable : (prefixWord ++ tailWord_4709789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709789).length < 2 ^ (prefixWord ++ tailWord_4709789).sum := by decide
  have hdescent : baseEnd_4709789 < baseStart_4709789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709795 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 5, 1, 3]
def baseStart_4709795 : Nat := 118140960795 + 4709795 * 2 ^ 59
def prefixEnd_4709795 : Nat := 4983230072969 + 3 ^ 40 * 4709795 * 2
def baseEnd_4709795 : Nat := 2418388619142505639102553

theorem tailTrace_4709795 : CollatzResearch.WordTrace tailWord_4709795 prefixEnd_4709795 2418388619142505639102553 := by
  unfold tailWord_4709795
  simp only [CollatzResearch.WordTrace]
  refine ⟨171780335972224558792026839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114520223981483039194684559 171780335972224558792026839)
  ·
    refine ⟨257670503958336838188040259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171780335972224558792026839 257670503958336838188040259)
    ·
      refine ⟨386505755937505257282060389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257670503958336838188040259 386505755937505257282060389)
      ·
        refine ⟨72469829238282235740386323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 386505755937505257282060389 72469829238282235740386323)
        ·
          refine ⟨108704743857423353610579485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72469829238282235740386323 108704743857423353610579485)
          ·
            refine ⟨40764278946533757603967307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108704743857423353610579485 40764278946533757603967307)
            ·
              refine ⟨61146418419800636405950961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40764278946533757603967307 61146418419800636405950961)
              ·
                refine ⟨45859813814850477304463221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61146418419800636405950961 45859813814850477304463221)
                ·
                  refine ⟨4299357545142232247293427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45859813814850477304463221 4299357545142232247293427)
                  ·
                    refine ⟨6449036317713348370940141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4299357545142232247293427 6449036317713348370940141)
                    ·
                      refine ⟨2418388619142505639102553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6449036317713348370940141 2418388619142505639102553)
                      ·
                        rfl

theorem cell23_4709795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_4709795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709795 prefixEnd_4709795 := by exact prefixLift 4709795
  have htrace : WordTrace (prefixWord ++ tailWord_4709795) baseStart_4709795 baseEnd_4709795 := by
    simpa [prefixWord, tailWord_4709795, baseEnd_4709795] using wordTrace_append hprefix tailTrace_4709795
  have hstable : (prefixWord ++ tailWord_4709795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709795).length < 2 ^ (prefixWord ++ tailWord_4709795).sum := by decide
  have hdescent : baseEnd_4709795 < baseStart_4709795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709805 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_4709805 : Nat := 118140960795 + 4709805 * 2 ^ 59
def prefixEnd_4709805 : Nat := 4983230072969 + 3 ^ 40 * 4709805 * 2
def baseEnd_4709805 : Nat := 2418393753949050599977507

theorem tailTrace_4709805 : CollatzResearch.WordTrace tailWord_4709805 prefixEnd_4709805 2418393753949050599977507 := by
  unfold tailWord_4709805
  simp only [CollatzResearch.WordTrace]
  refine ⟨171780700702188330499890869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114520467134792220333260579 171780700702188330499890869)
  ·
    refine ⟨16104440690830155984364769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171780700702188330499890869 16104440690830155984364769)
    ·
      refine ⟨12078330518122616988273577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16104440690830155984364769 12078330518122616988273577)
      ·
        refine ⟨9058747888591962741205183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12078330518122616988273577 9058747888591962741205183)
        ·
          refine ⟨13588121832887944111807775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9058747888591962741205183 13588121832887944111807775)
          ·
            refine ⟨20382182749331916167711663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13588121832887944111807775 20382182749331916167711663)
            ·
              refine ⟨30573274123997874251567495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20382182749331916167711663 30573274123997874251567495)
              ·
                refine ⟨45859911185996811377351243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30573274123997874251567495 45859911185996811377351243)
                ·
                  refine ⟨68789866778995217066026865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45859911185996811377351243 68789866778995217066026865)
                  ·
                    refine ⟨51592400084246412799520149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68789866778995217066026865 51592400084246412799520149)
                    ·
                      refine ⟨2418393753949050599977507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51592400084246412799520149 2418393753949050599977507)
                      ·
                        rfl

theorem cell23_4709805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_4709805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709805 prefixEnd_4709805 := by exact prefixLift 4709805
  have htrace : WordTrace (prefixWord ++ tailWord_4709805) baseStart_4709805 baseEnd_4709805 := by
    simpa [prefixWord, tailWord_4709805, baseEnd_4709805] using wordTrace_append hprefix tailTrace_4709805
  have hstable : (prefixWord ++ tailWord_4709805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709805).length < 2 ^ (prefixWord ++ tailWord_4709805).sum := by decide
  have hdescent : baseEnd_4709805 < baseStart_4709805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709835 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 4]
def baseStart_4709835 : Nat := 118140960795 + 4709835 * 2 ^ 59
def prefixEnd_4709835 : Nat := 4983230072969 + 3 ^ 40 * 4709835 * 2
def baseEnd_4709835 : Nat := 2418409158368685482602369

theorem tailTrace_4709835 : CollatzResearch.WordTrace tailWord_4709835 prefixEnd_4709835 2418409158368685482602369 := by
  unfold tailWord_4709835
  simp only [CollatzResearch.WordTrace]
  refine ⟨171781794892079645623482959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114521196594719763748988639 171781794892079645623482959)
  ·
    refine ⟨257672692338119468435224439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171781794892079645623482959 257672692338119468435224439)
    ·
      refine ⟨386509038507179202652836659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257672692338119468435224439 386509038507179202652836659)
      ·
        refine ⟨579763557760768803979254989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386509038507179202652836659 579763557760768803979254989)
        ·
          refine ⟨217411334160288301492220621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 579763557760768803979254989 217411334160288301492220621)
          ·
            refine ⟨81529250310108113059582733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217411334160288301492220621 81529250310108113059582733)
            ·
              refine ⟨30573468866290542397343525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81529250310108113059582733 30573468866290542397343525)
              ·
                refine ⟨5732525412429476699501911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30573468866290542397343525 5732525412429476699501911)
                ·
                  refine ⟨8598788118644215049252867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5732525412429476699501911 8598788118644215049252867)
                  ·
                    refine ⟨12898182177966322573879301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8598788118644215049252867 12898182177966322573879301)
                    ·
                      refine ⟨2418409158368685482602369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12898182177966322573879301 2418409158368685482602369)
                      ·
                        rfl

theorem cell23_4709835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 1, 4].length) (baseStart_4709835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709835 prefixEnd_4709835 := by exact prefixLift 4709835
  have htrace : WordTrace (prefixWord ++ tailWord_4709835) baseStart_4709835 baseEnd_4709835 := by
    simpa [prefixWord, tailWord_4709835, baseEnd_4709835] using wordTrace_append hprefix tailTrace_4709835
  have hstable : (prefixWord ++ tailWord_4709835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709835).length < 2 ^ (prefixWord ++ tailWord_4709835).sum := by decide
  have hdescent : baseEnd_4709835 < baseStart_4709835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709845 : List Nat := [1, 3, 2, 3, 1, 1, 1, 1, 6, 4]
def baseStart_4709845 : Nat := 118140960795 + 4709845 * 2 ^ 59
def prefixEnd_4709845 : Nat := 4983230072969 + 3 ^ 40 * 4709845 * 2
def baseEnd_4709845 : Nat := 806138097725076814492441

theorem tailTrace_4709845 : CollatzResearch.WordTrace tailWord_4709845 prefixEnd_4709845 806138097725076814492441 := by
  unfold tailWord_4709845
  simp only [CollatzResearch.WordTrace]
  refine ⟨171782159622043417331346989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114521439748028944887564659 171782159622043417331346989)
  ·
    refine ⟨64418309858266281499255121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171782159622043417331346989 64418309858266281499255121)
    ·
      refine ⟨48313732393699711124441341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64418309858266281499255121 48313732393699711124441341)
      ·
        refine ⟨18117649647637391671665503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48313732393699711124441341 18117649647637391671665503)
        ·
          refine ⟨27176474471456087507498255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18117649647637391671665503 27176474471456087507498255)
          ·
            refine ⟨40764711707184131261247383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27176474471456087507498255 40764711707184131261247383)
            ·
              refine ⟨61147067560776196891871075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40764711707184131261247383 61147067560776196891871075)
              ·
                refine ⟨91720601341164295337806613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61147067560776196891871075 91720601341164295337806613)
                ·
                  refine ⟨4299403187867076343959685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91720601341164295337806613 4299403187867076343959685)
                  ·
                    refine ⟨806138097725076814492441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4299403187867076343959685 806138097725076814492441)
                    ·
                      rfl

theorem cell23_4709845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_4709845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709845 prefixEnd_4709845 := by exact prefixLift 4709845
  have htrace : WordTrace (prefixWord ++ tailWord_4709845) baseStart_4709845 baseEnd_4709845 := by
    simpa [prefixWord, tailWord_4709845, baseEnd_4709845] using wordTrace_append hprefix tailTrace_4709845
  have hstable : (prefixWord ++ tailWord_4709845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709845).length < 2 ^ (prefixWord ++ tailWord_4709845).sum := by decide
  have hdescent : baseEnd_4709845 < baseStart_4709845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709855 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 5]
def baseStart_4709855 : Nat := 118140960795 + 4709855 * 2 ^ 59
def prefixEnd_4709855 : Nat := 4983230072969 + 3 ^ 40 * 4709855 * 2
def baseEnd_4709855 : Nat := 2418419427981775404352277

theorem tailTrace_4709855 : CollatzResearch.WordTrace tailWord_4709855 prefixEnd_4709855 2418419427981775404352277 := by
  unfold tailWord_4709855
  simp only [CollatzResearch.WordTrace]
  refine ⟨171782524352007189039211019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114521682901338126026140679 171782524352007189039211019)
  ·
    refine ⟨257673786528010783558816529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171782524352007189039211019 257673786528010783558816529)
    ·
      refine ⟨193255339896008087669112397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257673786528010783558816529 193255339896008087669112397)
      ·
        refine ⟨72470752461003032875917149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193255339896008087669112397 72470752461003032875917149)
        ·
          refine ⟨27176532172876137328468931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72470752461003032875917149 27176532172876137328468931)
          ·
            refine ⟨40764798259314205992703397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27176532172876137328468931 40764798259314205992703397)
            ·
              refine ⟨7643399673621413623631887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40764798259314205992703397 7643399673621413623631887)
              ·
                refine ⟨11465099510432120435447831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7643399673621413623631887 11465099510432120435447831)
                ·
                  refine ⟨17197649265648180653171747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11465099510432120435447831 17197649265648180653171747)
                  ·
                    refine ⟨25796473898472270979757621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17197649265648180653171747 25796473898472270979757621)
                    ·
                      refine ⟨2418419427981775404352277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25796473898472270979757621 2418419427981775404352277)
                      ·
                        rfl

theorem cell23_4709855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_4709855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709855 prefixEnd_4709855 := by exact prefixLift 4709855
  have htrace : WordTrace (prefixWord ++ tailWord_4709855) baseStart_4709855 baseEnd_4709855 := by
    simpa [prefixWord, tailWord_4709855, baseEnd_4709855] using wordTrace_append hprefix tailTrace_4709855
  have hstable : (prefixWord ++ tailWord_4709855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709855).length < 2 ^ (prefixWord ++ tailWord_4709855).sum := by decide
  have hdescent : baseEnd_4709855 < baseStart_4709855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4709920 : List Nat := [2, 1, 1, 6, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4709920 : Nat := 118140960795 + 4709920 * 2 ^ 59
def prefixEnd_4709920 : Nat := 4983230072969 + 3 ^ 40 * 4709920 * 2
def baseEnd_4709920 : Nat := 2418452804224317650039479

theorem tailTrace_4709920 : CollatzResearch.WordTrace tailWord_4709920 prefixEnd_4709920 2418452804224317650039479 := by
  unfold tailWord_4709920
  simp only [CollatzResearch.WordTrace]
  refine ⟨85892447548385852570163607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114523263397847803426884809 85892447548385852570163607)
  ·
    refine ⟨128838671322578778855245411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85892447548385852570163607 128838671322578778855245411)
    ·
      refine ⟨193258006983868168282868117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128838671322578778855245411 193258006983868168282868117)
      ·
        refine ⟨9058969077368820388259443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 193258006983868168282868117 9058969077368820388259443)
        ·
          refine ⟨13588453616053230582389165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9058969077368820388259443 13588453616053230582389165)
          ·
            refine ⟨5095670106019961468395937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13588453616053230582389165 5095670106019961468395937)
            ·
              refine ⟨3821752579514971101296953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5095670106019961468395937 3821752579514971101296953)
              ·
                refine ⟨2866314434636228325972715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3821752579514971101296953 2866314434636228325972715)
                ·
                  refine ⟨4299471651954342488959073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866314434636228325972715 4299471651954342488959073)
                  ·
                    refine ⟨3224603738965756866719305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4299471651954342488959073 3224603738965756866719305)
                    ·
                      refine ⟨2418452804224317650039479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3224603738965756866719305 2418452804224317650039479)
                      ·
                        rfl

theorem cell23_4709920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4709920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4709920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4709920 prefixEnd_4709920 := by exact prefixLift 4709920
  have htrace : WordTrace (prefixWord ++ tailWord_4709920) baseStart_4709920 baseEnd_4709920 := by
    simpa [prefixWord, tailWord_4709920, baseEnd_4709920] using wordTrace_append hprefix tailTrace_4709920
  have hstable : (prefixWord ++ tailWord_4709920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4709920).length < 2 ^ (prefixWord ++ tailWord_4709920).sum := by decide
  have hdescent : baseEnd_4709920 < baseStart_4709920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4709920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710032 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 4, 4, 2]
def baseStart_4710032 : Nat := 118140960795 + 4710032 * 2 ^ 59
def prefixEnd_4710032 : Nat := 4983230072969 + 3 ^ 40 * 4710032 * 2
def baseEnd_4710032 : Nat := 2418510314057621211838963

theorem tailTrace_4710032 : CollatzResearch.WordTrace tailWord_4710032 prefixEnd_4710032 2418510314057621211838963 := by
  unfold tailWord_4710032
  simp only [CollatzResearch.WordTrace]
  refine ⟨85894490036182974134202175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114525986714910632178936233 85894490036182974134202175)
  ·
    refine ⟨128841735054274461201303263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85894490036182974134202175 128841735054274461201303263)
    ·
      refine ⟨193262602581411691801954895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128841735054274461201303263 193262602581411691801954895)
      ·
        refine ⟨289893903872117537702932343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193262602581411691801954895 289893903872117537702932343)
        ·
          refine ⟨434840855808176306554398515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289893903872117537702932343 434840855808176306554398515)
          ·
            refine ⟨652261283712264459831597773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 434840855808176306554398515 652261283712264459831597773)
            ·
              refine ⟨244597981392099172436849165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 652261283712264459831597773 244597981392099172436849165)
              ·
                refine ⟨91724243022037189663818437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244597981392099172436849165 91724243022037189663818437)
                ·
                  refine ⟨17198295566631973061965957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91724243022037189663818437 17198295566631973061965957)
                  ·
                    refine ⟨3224680418743494949118617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17198295566631973061965957 3224680418743494949118617)
                    ·
                      refine ⟨2418510314057621211838963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3224680418743494949118617 2418510314057621211838963)
                      ·
                        rfl

theorem cell23_4710032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 4, 2].length) (baseStart_4710032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710032 prefixEnd_4710032 := by exact prefixLift 4710032
  have htrace : WordTrace (prefixWord ++ tailWord_4710032) baseStart_4710032 baseEnd_4710032 := by
    simpa [prefixWord, tailWord_4710032, baseEnd_4710032] using wordTrace_append hprefix tailTrace_4710032
  have hstable : (prefixWord ++ tailWord_4710032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710032).length < 2 ^ (prefixWord ++ tailWord_4710032).sum := by decide
  have hdescent : baseEnd_4710032 < baseStart_4710032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710095 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_4710095 : Nat := 118140960795 + 4710095 * 2 ^ 59
def prefixEnd_4710095 : Nat := 4983230072969 + 3 ^ 40 * 4710095 * 2
def baseEnd_4710095 : Nat := 2418542663338854465351173

theorem tailTrace_4710095 : CollatzResearch.WordTrace tailWord_4710095 prefixEnd_4710095 2418542663338854465351173 := by
  unfold tailWord_4710095
  simp only [CollatzResearch.WordTrace]
  refine ⟨171791277871137710027947739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114527518580758473351965159 171791277871137710027947739)
  ·
    refine ⟨257686916806706565041921609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171791277871137710027947739 257686916806706565041921609)
    ·
      refine ⟨193265187605029923781441207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257686916806706565041921609 193265187605029923781441207)
      ·
        refine ⟨289897781407544885672161811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193265187605029923781441207 289897781407544885672161811)
        ·
          refine ⟨434846672111317328508242717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289897781407544885672161811 434846672111317328508242717)
          ·
            refine ⟨163067502041743998190591019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 434846672111317328508242717 163067502041743998190591019)
            ·
              refine ⟨244601253062615997285886529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163067502041743998190591019 244601253062615997285886529)
              ·
                refine ⟨183450939796961997964414897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244601253062615997285886529 183450939796961997964414897)
                ·
                  refine ⟨137588204847721498473311173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183450939796961997964414897 137588204847721498473311173)
                  ·
                    refine ⟨25797788408947780963745845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 137588204847721498473311173 25797788408947780963745845)
                    ·
                      refine ⟨2418542663338854465351173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25797788408947780963745845 2418542663338854465351173)
                      ·
                        rfl

theorem cell23_4710095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_4710095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710095 prefixEnd_4710095 := by exact prefixLift 4710095
  have htrace : WordTrace (prefixWord ++ tailWord_4710095) baseStart_4710095 baseEnd_4710095 := by
    simpa [prefixWord, tailWord_4710095, baseEnd_4710095] using wordTrace_append hprefix tailTrace_4710095
  have hstable : (prefixWord ++ tailWord_4710095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710095).length < 2 ^ (prefixWord ++ tailWord_4710095).sum := by decide
  have hdescent : baseEnd_4710095 < baseStart_4710095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710152 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_4710152 : Nat := 118140960795 + 4710152 * 2 ^ 59
def prefixEnd_4710152 : Nat := 4983230072969 + 3 ^ 40 * 4710152 * 2
def baseEnd_4710152 : Nat := 2418571931736160742338411

theorem tailTrace_4710152 : CollatzResearch.WordTrace tailWord_4710152 prefixEnd_4710152 2418571931736160742338411 := by
  unfold tailWord_4710152
  simp only [CollatzResearch.WordTrace]
  refine ⟨85896678415965604381386355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114528904554620805841848473 85896678415965604381386355)
  ·
    refine ⟨128845017623948406572079533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85896678415965604381386355 128845017623948406572079533)
    ·
      refine ⟨48316881608980652464529825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128845017623948406572079533 48316881608980652464529825)
      ·
        refine ⟨36237661206735489348397369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48316881608980652464529825 36237661206735489348397369)
        ·
          refine ⟨27178245905051617011298027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36237661206735489348397369 27178245905051617011298027)
          ·
            refine ⟨40767368857577425516947041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27178245905051617011298027 40767368857577425516947041)
            ·
              refine ⟨30575526643183069137710281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40767368857577425516947041 30575526643183069137710281)
              ·
                refine ⟨22931644982387301853282711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30575526643183069137710281 22931644982387301853282711)
                ·
                  refine ⟨34397467473580952779924067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22931644982387301853282711 34397467473580952779924067)
                  ·
                    refine ⟨51596201210371429169886101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34397467473580952779924067 51596201210371429169886101)
                    ·
                      refine ⟨2418571931736160742338411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51596201210371429169886101 2418571931736160742338411)
                      ·
                        rfl

theorem cell23_4710152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_4710152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710152 prefixEnd_4710152 := by exact prefixLift 4710152
  have htrace : WordTrace (prefixWord ++ tailWord_4710152) baseStart_4710152 baseEnd_4710152 := by
    simpa [prefixWord, tailWord_4710152, baseEnd_4710152] using wordTrace_append hprefix tailTrace_4710152
  have hstable : (prefixWord ++ tailWord_4710152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710152).length < 2 ^ (prefixWord ++ tailWord_4710152).sum := by decide
  have hdescent : baseEnd_4710152 < baseStart_4710152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710156 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 3, 2, 2]
def baseStart_4710156 : Nat := 118140960795 + 4710156 * 2 ^ 59
def prefixEnd_4710156 : Nat := 4983230072969 + 3 ^ 40 * 4710156 * 2
def baseEnd_4710156 : Nat := 2418573985658778726688393

theorem tailTrace_4710156 : CollatzResearch.WordTrace tailWord_4710156 prefixEnd_4710156 2418573985658778726688393 := by
  unfold tailWord_4710156
  simp only [CollatzResearch.WordTrace]
  refine ⟨85896751361958358722959161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114529001815944478297278881 85896751361958358722959161)
  ·
    refine ⟨64422563521468769042219371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85896751361958358722959161 64422563521468769042219371)
    ·
      refine ⟨96633845282203153563329057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64422563521468769042219371 96633845282203153563329057)
      ·
        refine ⟨72475383961652365172496793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96633845282203153563329057 72475383961652365172496793)
        ·
          refine ⟨54356537971239273879372595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72475383961652365172496793 54356537971239273879372595)
          ·
            refine ⟨81534806956858910819058893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54356537971239273879372595 81534806956858910819058893)
            ·
              refine ⟨30575552608822091557147085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81534806956858910819058893 30575552608822091557147085)
              ·
                refine ⟨11465832228308284333930157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30575552608822091557147085 11465832228308284333930157)
                ·
                  refine ⟨4299687085615606625223809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11465832228308284333930157 4299687085615606625223809)
                  ·
                    refine ⟨3224765314211704968917857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4299687085615606625223809 3224765314211704968917857)
                    ·
                      refine ⟨2418573985658778726688393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3224765314211704968917857 2418573985658778726688393)
                      ·
                        rfl

theorem cell23_4710156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_4710156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710156 prefixEnd_4710156 := by exact prefixLift 4710156
  have htrace : WordTrace (prefixWord ++ tailWord_4710156) baseStart_4710156 baseEnd_4710156 := by
    simpa [prefixWord, tailWord_4710156, baseEnd_4710156] using wordTrace_append hprefix tailTrace_4710156
  have hstable : (prefixWord ++ tailWord_4710156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710156).length < 2 ^ (prefixWord ++ tailWord_4710156).sum := by decide
  have hdescent : baseEnd_4710156 < baseStart_4710156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710157 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 6]
def baseStart_4710157 : Nat := 118140960795 + 4710157 * 2 ^ 59
def prefixEnd_4710157 : Nat := 4983230072969 + 3 ^ 40 * 4710157 * 2
def baseEnd_4710157 : Nat := 268730499904381469197321

theorem tailTrace_4710157 : CollatzResearch.WordTrace tailWord_4710157 prefixEnd_4710157 268730499904381469197321 := by
  unfold tailWord_4710157
  simp only [CollatzResearch.WordTrace]
  refine ⟨171793539196913094616704725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114529026131275396411136483 171793539196913094616704725)
  ·
    refine ⟨4026411074927650655079017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 171793539196913094616704725 4026411074927650655079017)
    ·
      refine ⟨3019808306195737991309263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4026411074927650655079017 3019808306195737991309263)
      ·
        refine ⟨4529712459293606986963895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3019808306195737991309263 4529712459293606986963895)
        ·
          refine ⟨6794568688940410480445843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4529712459293606986963895 6794568688940410480445843)
          ·
            refine ⟨10191853033410615720668765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6794568688940410480445843 10191853033410615720668765)
            ·
              refine ⟨3821944887528980895250787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10191853033410615720668765 3821944887528980895250787)
              ·
                refine ⟨5732917331293471342876181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3821944887528980895250787 5732917331293471342876181)
                ·
                  refine ⟨268730499904381469197321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5732917331293471342876181 268730499904381469197321)
                  ·
                    rfl

theorem cell23_4710157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_4710157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710157 prefixEnd_4710157 := by exact prefixLift 4710157
  have htrace : WordTrace (prefixWord ++ tailWord_4710157) baseStart_4710157 baseEnd_4710157 := by
    simpa [prefixWord, tailWord_4710157, baseEnd_4710157] using wordTrace_append hprefix tailTrace_4710157
  have hstable : (prefixWord ++ tailWord_4710157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710157).length < 2 ^ (prefixWord ++ tailWord_4710157).sum := by decide
  have hdescent : baseEnd_4710157 < baseStart_4710157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710176 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 3]
def baseStart_4710176 : Nat := 118140960795 + 4710176 * 2 ^ 59
def prefixEnd_4710176 : Nat := 4983230072969 + 3 ^ 40 * 4710176 * 2
def baseEnd_4710176 : Nat := 2418584255271868648438301

theorem tailTrace_4710176 : CollatzResearch.WordTrace tailWord_4710176 prefixEnd_4710176 2418584255271868648438301 := by
  unfold tailWord_4710176
  simp only [CollatzResearch.WordTrace]
  refine ⟨85897116091922130430823191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114529488122562840574430921 85897116091922130430823191)
  ·
    refine ⟨128845674137883195646234787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85897116091922130430823191 128845674137883195646234787)
    ·
      refine ⟨193268511206824793469352181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128845674137883195646234787 193268511206824793469352181)
      ·
        refine ⟨18118922925639824387751767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193268511206824793469352181 18118922925639824387751767)
        ·
          refine ⟨27178384388459736581627651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18118922925639824387751767 27178384388459736581627651)
          ·
            refine ⟨40767576582689604872441477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27178384388459736581627651 40767576582689604872441477)
            ·
              refine ⟨7643920609254300913582777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40767576582689604872441477 7643920609254300913582777)
              ·
                refine ⟨5732940456940725685187083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7643920609254300913582777 5732940456940725685187083)
                ·
                  refine ⟨8599410685411088527780625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5732940456940725685187083 8599410685411088527780625)
                  ·
                    refine ⟨6449558014058316395835469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8599410685411088527780625 6449558014058316395835469)
                    ·
                      refine ⟨2418584255271868648438301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6449558014058316395835469 2418584255271868648438301)
                      ·
                        rfl

theorem cell23_4710176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_4710176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710176 prefixEnd_4710176 := by exact prefixLift 4710176
  have htrace : WordTrace (prefixWord ++ tailWord_4710176) baseStart_4710176 baseEnd_4710176 := by
    simpa [prefixWord, tailWord_4710176, baseEnd_4710176] using wordTrace_append hprefix tailTrace_4710176
  have hstable : (prefixWord ++ tailWord_4710176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710176).length < 2 ^ (prefixWord ++ tailWord_4710176).sum := by decide
  have hdescent : baseEnd_4710176 < baseStart_4710176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710207 : List Nat := [1, 1, 2, 2, 6, 1, 3, 2, 1, 2, 2]
def baseStart_4710207 : Nat := 118140960795 + 4710207 * 2 ^ 59
def prefixEnd_4710207 : Nat := 4983230072969 + 3 ^ 40 * 4710207 * 2
def baseEnd_4710207 : Nat := 2418600173172158027150659

theorem tailTrace_4710207 : CollatzResearch.WordTrace tailWord_4710207 prefixEnd_4710207 2418600173172158027150659 := by
  unfold tailWord_4710207
  simp only [CollatzResearch.WordTrace]
  refine ⟨171795362846731953156024875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114530241897821302104016583 171795362846731953156024875)
  ·
    refine ⟨257693044270097929734037313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171795362846731953156024875 257693044270097929734037313)
    ·
      refine ⟨193269783202573447300527985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257693044270097929734037313 193269783202573447300527985)
      ·
        refine ⟨144952337401930085475395989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193269783202573447300527985 144952337401930085475395989)
        ·
          refine ⟨6794640815715472756659187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 144952337401930085475395989 6794640815715472756659187)
          ·
            refine ⟨10191961223573209134988781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6794640815715472756659187 10191961223573209134988781)
            ·
              refine ⟨3821985458839953425620793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10191961223573209134988781 3821985458839953425620793)
              ·
                refine ⟨2866489094129965069215595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3821985458839953425620793 2866489094129965069215595)
                ·
                  refine ⟨4299733641194947603823393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866489094129965069215595 4299733641194947603823393)
                  ·
                    refine ⟨3224800230896210702867545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4299733641194947603823393 3224800230896210702867545)
                    ·
                      refine ⟨2418600173172158027150659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3224800230896210702867545 2418600173172158027150659)
                      ·
                        rfl

theorem cell23_4710207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 1, 2, 2].length) (baseStart_4710207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710207 prefixEnd_4710207 := by exact prefixLift 4710207
  have htrace : WordTrace (prefixWord ++ tailWord_4710207) baseStart_4710207 baseEnd_4710207 := by
    simpa [prefixWord, tailWord_4710207, baseEnd_4710207] using wordTrace_append hprefix tailTrace_4710207
  have hstable : (prefixWord ++ tailWord_4710207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710207).length < 2 ^ (prefixWord ++ tailWord_4710207).sum := by decide
  have hdescent : baseEnd_4710207 < baseStart_4710207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710303 : List Nat := [1, 1, 2, 5, 3, 1, 2, 3, 5]
def baseStart_4710303 : Nat := 118140960795 + 4710303 * 2 ^ 59
def prefixEnd_4710303 : Nat := 4983230072969 + 3 ^ 40 * 4710303 * 2
def baseEnd_4710303 : Nat := 268738829701665516838913

theorem tailTrace_4710303 : CollatzResearch.WordTrace tailWord_4710303 prefixEnd_4710303 268738829701665516838913 := by
  unfold tailWord_4710303
  simp only [CollatzResearch.WordTrace]
  refine ⟨171798864254384161551519563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114532576169589441034346375 171798864254384161551519563)
  ·
    refine ⟨257698296381576242327279345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171798864254384161551519563 257698296381576242327279345)
    ·
      refine ⟨193273722286182181745459509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257698296381576242327279345 193273722286182181745459509)
      ·
        refine ⟨18119411464329579538636829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193273722286182181745459509 18119411464329579538636829)
        ·
          refine ⟨6794779299123592326988811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18119411464329579538636829 6794779299123592326988811)
          ·
            refine ⟨10192168948685388490483217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6794779299123592326988811 10192168948685388490483217)
            ·
              refine ⟨7644126711514041367862413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10192168948685388490483217 7644126711514041367862413)
              ·
                refine ⟨2866547516817765512948405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7644126711514041367862413 2866547516817765512948405)
                ·
                  refine ⟨268738829701665516838913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2866547516817765512948405 268738829701665516838913)
                  ·
                    rfl

theorem cell23_4710303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 5].length) (baseStart_4710303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710303 prefixEnd_4710303 := by exact prefixLift 4710303
  have htrace : WordTrace (prefixWord ++ tailWord_4710303) baseStart_4710303 baseEnd_4710303 := by
    simpa [prefixWord, tailWord_4710303, baseEnd_4710303] using wordTrace_append hprefix tailTrace_4710303
  have hstable : (prefixWord ++ tailWord_4710303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710303).length < 2 ^ (prefixWord ++ tailWord_4710303).sum := by decide
  have hdescent : baseEnd_4710303 < baseStart_4710303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710319 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 4]
def baseStart_4710319 : Nat := 118140960795 + 4710319 * 2 ^ 59
def prefixEnd_4710319 : Nat := 4983230072969 + 3 ^ 40 * 4710319 * 2
def baseEnd_4710319 : Nat := 2418657683005461588950143

theorem tailTrace_4710319 : CollatzResearch.WordTrace tailWord_4710319 prefixEnd_4710319 2418657683005461588950143 := by
  unfold tailWord_4710319
  simp only [CollatzResearch.WordTrace]
  refine ⟨171799447822326196284102011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114532965214884130856068007 171799447822326196284102011)
  ·
    refine ⟨257699171733489294426153017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171799447822326196284102011 257699171733489294426153017)
    ·
      refine ⟨193274378800116970819614763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257699171733489294426153017 193274378800116970819614763)
      ·
        refine ⟨289911568200175456229422145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193274378800116970819614763 289911568200175456229422145)
        ·
          refine ⟨217433676150131592172066609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289911568200175456229422145 217433676150131592172066609)
          ·
            refine ⟨163075257112598694129049957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217433676150131592172066609 163075257112598694129049957)
            ·
              refine ⟨30576610708612255149196867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163075257112598694129049957 30576610708612255149196867)
              ·
                refine ⟨45864916062918382723795301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30576610708612255149196867 45864916062918382723795301)
                ·
                  refine ⟨8599671761797196760711619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45864916062918382723795301 8599671761797196760711619)
                  ·
                    refine ⟨12899507642695795141067429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8599671761797196760711619 12899507642695795141067429)
                    ·
                      refine ⟨2418657683005461588950143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12899507642695795141067429 2418657683005461588950143)
                      ·
                        rfl

theorem cell23_4710319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_4710319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710319 prefixEnd_4710319 := by exact prefixLift 4710319
  have htrace : WordTrace (prefixWord ++ tailWord_4710319) baseStart_4710319 baseEnd_4710319 := by
    simpa [prefixWord, tailWord_4710319, baseEnd_4710319] using wordTrace_append hprefix tailTrace_4710319
  have hstable : (prefixWord ++ tailWord_4710319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710319).length < 2 ^ (prefixWord ++ tailWord_4710319).sum := by decide
  have hdescent : baseEnd_4710319 < baseStart_4710319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710336 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 2, 4, 2]
def baseStart_4710336 : Nat := 118140960795 + 4710336 * 2 ^ 59
def prefixEnd_4710336 : Nat := 4983230072969 + 3 ^ 40 * 4710336 * 2
def baseEnd_4710336 : Nat := 2418666412176588022437565

theorem tailTrace_4710336 : CollatzResearch.WordTrace tailWord_4710336 prefixEnd_4710336 2418666412176588022437565 := by
  unfold tailWord_4710336
  simp only [CollatzResearch.WordTrace]
  refine ⟨85900033931632304093735431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114533378575509738791647241 85900033931632304093735431)
  ·
    refine ⟨128850050897448456140603147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85900033931632304093735431 128850050897448456140603147)
    ·
      refine ⟨193275076346172684210904721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128850050897448456140603147 193275076346172684210904721)
      ·
        refine ⟨144956307259629513158178541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193275076346172684210904721 144956307259629513158178541)
        ·
          refine ⟨54358615222361067434316953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 144956307259629513158178541 54358615222361067434316953)
          ·
            refine ⟨40768961416770800575737715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54358615222361067434316953 40768961416770800575737715)
            ·
              refine ⟨61153442125156200863606573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40768961416770800575737715 61153442125156200863606573)
              ·
                refine ⟨22932540796933575323852465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61153442125156200863606573 22932540796933575323852465)
                ·
                  refine ⟨17199405597700181492889349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22932540796933575323852465 17199405597700181492889349)
                  ·
                    refine ⟨3224888549568784029916753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17199405597700181492889349 3224888549568784029916753)
                    ·
                      refine ⟨2418666412176588022437565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3224888549568784029916753 2418666412176588022437565)
                      ·
                        rfl

theorem cell23_4710336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 4, 2].length) (baseStart_4710336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710336 prefixEnd_4710336 := by exact prefixLift 4710336
  have htrace : WordTrace (prefixWord ++ tailWord_4710336) baseStart_4710336 baseEnd_4710336 := by
    simpa [prefixWord, tailWord_4710336, baseEnd_4710336] using wordTrace_append hprefix tailTrace_4710336
  have hstable : (prefixWord ++ tailWord_4710336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710336).length < 2 ^ (prefixWord ++ tailWord_4710336).sum := by decide
  have hdescent : baseEnd_4710336 < baseStart_4710336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710346 : List Nat := [3, 1, 2, 1, 2, 1, 4, 2, 3, 4]
def baseStart_4710346 : Nat := 118140960795 + 4710346 * 2 ^ 59
def prefixEnd_4710346 : Nat := 4983230072969 + 3 ^ 40 * 4710346 * 2
def baseEnd_4710346 : Nat := 806223848994377661104173

theorem tailTrace_4710346 : CollatzResearch.WordTrace tailWord_4710346 prefixEnd_4710346 806223848994377661104173 := by
  unfold tailWord_4710346
  simp only [CollatzResearch.WordTrace]
  refine ⟨42950108148307094973833723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114533621728818919930223261 42950108148307094973833723)
  ·
    refine ⟨64425162222460642460750585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42950108148307094973833723 64425162222460642460750585)
    ·
      refine ⟨48318871666845481845562939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64425162222460642460750585 48318871666845481845562939)
      ·
        refine ⟨72478307500268222768344409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48318871666845481845562939 72478307500268222768344409)
        ·
          refine ⟨54358730625201167076258307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72478307500268222768344409 54358730625201167076258307)
          ·
            refine ⟨81538095937801750614387461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54358730625201167076258307 81538095937801750614387461)
            ·
              refine ⟨15288392988337828240197649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81538095937801750614387461 15288392988337828240197649)
              ·
                refine ⟨11466294741253371180148237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15288392988337828240197649 11466294741253371180148237)
                ·
                  refine ⟨4299860527970014192555589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11466294741253371180148237 4299860527970014192555589)
                  ·
                    refine ⟨806223848994377661104173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4299860527970014192555589 806223848994377661104173)
                    ·
                      rfl

theorem cell23_4710346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_4710346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710346 prefixEnd_4710346 := by exact prefixLift 4710346
  have htrace : WordTrace (prefixWord ++ tailWord_4710346) baseStart_4710346 baseEnd_4710346 := by
    simpa [prefixWord, tailWord_4710346, baseEnd_4710346] using wordTrace_append hprefix tailTrace_4710346
  have hstable : (prefixWord ++ tailWord_4710346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710346).length < 2 ^ (prefixWord ++ tailWord_4710346).sum := by decide
  have hdescent : baseEnd_4710346 < baseStart_4710346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710356 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_4710356 : Nat := 118140960795 + 4710356 * 2 ^ 59
def prefixEnd_4710356 : Nat := 4983230072969 + 3 ^ 40 * 4710356 * 2
def baseEnd_4710356 : Nat := 2418676681789677944187473

theorem tailTrace_4710356 : CollatzResearch.WordTrace tailWord_4710356 prefixEnd_4710356 2418676681789677944187473 := by
  unfold tailWord_4710356
  simp only [CollatzResearch.WordTrace]
  refine ⟨85900398661596075801599461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114533864882128101068799281 85900398661596075801599461)
  ·
    refine ⟨16106324749049264212799899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85900398661596075801599461 16106324749049264212799899)
    ·
      refine ⟨24159487123573896319199849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16106324749049264212799899 24159487123573896319199849)
      ·
        refine ⟨18119615342680422239399887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24159487123573896319199849 18119615342680422239399887)
        ·
          refine ⟨27179423014020633359099831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18119615342680422239399887 27179423014020633359099831)
          ·
            refine ⟨40769134521030950038649747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27179423014020633359099831 40769134521030950038649747)
            ·
              refine ⟨61153701781546425057974621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40769134521030950038649747 61153701781546425057974621)
              ·
                refine ⟨22932638168079909396740483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61153701781546425057974621 22932638168079909396740483)
                ·
                  refine ⟨34398957252119864095110725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22932638168079909396740483 34398957252119864095110725)
                  ·
                    refine ⟨6449804484772474517833261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34398957252119864095110725 6449804484772474517833261)
                    ·
                      refine ⟨2418676681789677944187473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6449804484772474517833261 2418676681789677944187473)
                      ·
                        rfl

theorem cell23_4710356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_4710356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710356 prefixEnd_4710356 := by exact prefixLift 4710356
  have htrace : WordTrace (prefixWord ++ tailWord_4710356) baseStart_4710356 baseEnd_4710356 := by
    simpa [prefixWord, tailWord_4710356, baseEnd_4710356] using wordTrace_append hprefix tailTrace_4710356
  have hstable : (prefixWord ++ tailWord_4710356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710356).length < 2 ^ (prefixWord ++ tailWord_4710356).sum := by decide
  have hdescent : baseEnd_4710356 < baseStart_4710356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710370 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_4710370 : Nat := 118140960795 + 4710370 * 2 ^ 59
def prefixEnd_4710370 : Nat := 4983230072969 + 3 ^ 40 * 4710370 * 2
def baseEnd_4710370 : Nat := 2418683870518840889412409

theorem tailTrace_4710370 : CollatzResearch.WordTrace tailWord_4710370 prefixEnd_4710370 2418683870518840889412409 := by
  unfold tailWord_4710370
  simp only [CollatzResearch.WordTrace]
  refine ⟨42950326986285357998552141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114534205296760954662805709 42950326986285357998552141)
  ·
    refine ⟨16106372619857009249457053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42950326986285357998552141 16106372619857009249457053)
    ·
      refine ⟨6039889732446378468546395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16106372619857009249457053 6039889732446378468546395)
      ·
        refine ⟨9059834598669567702819593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6039889732446378468546395 9059834598669567702819593)
        ·
          refine ⟨6794875949002175777114695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9059834598669567702819593 6794875949002175777114695)
          ·
            refine ⟨10192313923503263665672043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6794875949002175777114695 10192313923503263665672043)
            ·
              refine ⟨15288470885254895498508065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10192313923503263665672043 15288470885254895498508065)
              ·
                refine ⟨11466353163941171623881049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15288470885254895498508065 11466353163941171623881049)
                ·
                  refine ⟨8599764872955878717910787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11466353163941171623881049 8599764872955878717910787)
                  ·
                    refine ⟨12899647309433818076866181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8599764872955878717910787 12899647309433818076866181)
                    ·
                      refine ⟨2418683870518840889412409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12899647309433818076866181 2418683870518840889412409)
                      ·
                        rfl

theorem cell23_4710370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_4710370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710370 prefixEnd_4710370 := by exact prefixLift 4710370
  have htrace : WordTrace (prefixWord ++ tailWord_4710370) baseStart_4710370 baseEnd_4710370 := by
    simpa [prefixWord, tailWord_4710370, baseEnd_4710370] using wordTrace_append hprefix tailTrace_4710370
  have hstable : (prefixWord ++ tailWord_4710370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710370).length < 2 ^ (prefixWord ++ tailWord_4710370).sum := by decide
  have hdescent : baseEnd_4710370 < baseStart_4710370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710393 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 6]
def baseStart_4710393 : Nat := 118140960795 + 4710393 * 2 ^ 59
def prefixEnd_4710393 : Nat := 4983230072969 + 3 ^ 40 * 4710393 * 2
def baseEnd_4710393 : Nat := 268743964508210477713867

theorem tailTrace_4710393 : CollatzResearch.WordTrace tailWord_4710393 prefixEnd_4710393 268743964508210477713867 := by
  unfold tailWord_4710393
  simp only [CollatzResearch.WordTrace]
  refine ⟨171802146824058106922295833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114534764549372071281530555 171802146824058106922295833)
  ·
    refine ⟨128851610118043580191721875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171802146824058106922295833 128851610118043580191721875)
    ·
      refine ⟨193277415177065370287582813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128851610118043580191721875 193277415177065370287582813)
      ·
        refine ⟨72479030691399513857843555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193277415177065370287582813 72479030691399513857843555)
        ·
          refine ⟨108718546037099270786765333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72479030691399513857843555 108718546037099270786765333)
          ·
            refine ⟨5096181845489028318129625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 108718546037099270786765333 5096181845489028318129625)
            ·
              refine ⟨3822136384116771238597219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5096181845489028318129625 3822136384116771238597219)
              ·
                refine ⟨5733204576175156857895829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3822136384116771238597219 5733204576175156857895829)
                ·
                  refine ⟨268743964508210477713867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5733204576175156857895829 268743964508210477713867)
                  ·
                    rfl

theorem cell23_4710393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 6].length) (baseStart_4710393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710393 prefixEnd_4710393 := by exact prefixLift 4710393
  have htrace : WordTrace (prefixWord ++ tailWord_4710393) baseStart_4710393 baseEnd_4710393 := by
    simpa [prefixWord, tailWord_4710393, baseEnd_4710393] using wordTrace_append hprefix tailTrace_4710393
  have hstable : (prefixWord ++ tailWord_4710393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710393).length < 2 ^ (prefixWord ++ tailWord_4710393).sum := by decide
  have hdescent : baseEnd_4710393 < baseStart_4710393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710419 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 3, 6]
def baseStart_4710419 : Nat := 118140960795 + 4710419 * 2 ^ 59
def prefixEnd_4710419 : Nat := 4983230072969 + 3 ^ 40 * 4710419 * 2
def baseEnd_4710419 : Nat := 806236343690303732566561

theorem tailTrace_4710419 : CollatzResearch.WordTrace tailWord_4710419 prefixEnd_4710419 806236343690303732566561 := by
  unfold tailWord_4710419
  simp only [CollatzResearch.WordTrace]
  refine ⟨171803095121963913362742311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114535396747975942241828207 171803095121963913362742311)
  ·
    refine ⟨257704642682945870044113467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171803095121963913362742311 257704642682945870044113467)
    ·
      refine ⟨386556964024418805066170201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257704642682945870044113467 386556964024418805066170201)
      ·
        refine ⟨289917723018314103799627651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386556964024418805066170201 289917723018314103799627651)
        ·
          refine ⟨434876584527471155699441477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289917723018314103799627651 434876584527471155699441477)
          ·
            refine ⟨81539359598900841693645277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 434876584527471155699441477 81539359598900841693645277)
            ·
              refine ⟨30577259849587815635116979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81539359598900841693645277 30577259849587815635116979)
              ·
                refine ⟨45865889774381723452675469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30577259849587815635116979 45865889774381723452675469)
                ·
                  refine ⟨17199708665393146294753301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45865889774381723452675469 17199708665393146294753301)
                  ·
                    refine ⟨806236343690303732566561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17199708665393146294753301 806236343690303732566561)
                    ·
                      rfl

theorem cell23_4710419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 6].length) (baseStart_4710419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710419 prefixEnd_4710419 := by exact prefixLift 4710419
  have htrace : WordTrace (prefixWord ++ tailWord_4710419) baseStart_4710419 baseEnd_4710419 := by
    simpa [prefixWord, tailWord_4710419, baseEnd_4710419] using wordTrace_append hprefix tailTrace_4710419
  have hstable : (prefixWord ++ tailWord_4710419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710419).length < 2 ^ (prefixWord ++ tailWord_4710419).sum := by decide
  have hdescent : baseEnd_4710419 < baseStart_4710419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710437 : List Nat := [1, 3, 1, 2, 2, 3, 4, 2, 1, 1, 3]
def baseStart_4710437 : Nat := 118140960795 + 4710437 * 2 ^ 59
def prefixEnd_4710437 : Nat := 4983230072969 + 3 ^ 40 * 4710437 * 2
def baseEnd_4710437 : Nat := 2418718273722692127274601

theorem tailTrace_4710437 : CollatzResearch.WordTrace tailWord_4710437 prefixEnd_4710437 2418718273722692127274601 := by
  unfold tailWord_4710437
  simp only [CollatzResearch.WordTrace]
  refine ⟨171803751635898702436897565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114535834423932468291265043 171803751635898702436897565)
  ·
    refine ⟨64426406863462013413836587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171803751635898702436897565 64426406863462013413836587)
    ·
      refine ⟨96639610295193020120754881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64426406863462013413836587 96639610295193020120754881)
      ·
        refine ⟨72479707721394765090566161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96639610295193020120754881 72479707721394765090566161)
        ·
          refine ⟨54359780791046073817924621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72479707721394765090566161 54359780791046073817924621)
          ·
            refine ⟨20384917796642277681721733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54359780791046073817924621 20384917796642277681721733)
            ·
              refine ⟨3822172086870427065322825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20384917796642277681721733 3822172086870427065322825)
              ·
                refine ⟨2866629065152820298992119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3822172086870427065322825 2866629065152820298992119)
                ·
                  refine ⟨4299943597729230448488179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866629065152820298992119 4299943597729230448488179)
                  ·
                    refine ⟨6449915396593845672732269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4299943597729230448488179 6449915396593845672732269)
                    ·
                      refine ⟨2418718273722692127274601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6449915396593845672732269 2418718273722692127274601)
                      ·
                        rfl

theorem cell23_4710437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_4710437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710437 prefixEnd_4710437 := by exact prefixLift 4710437
  have htrace : WordTrace (prefixWord ++ tailWord_4710437) baseStart_4710437 baseEnd_4710437 := by
    simpa [prefixWord, tailWord_4710437, baseEnd_4710437] using wordTrace_append hprefix tailTrace_4710437
  have hstable : (prefixWord ++ tailWord_4710437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710437).length < 2 ^ (prefixWord ++ tailWord_4710437).sum := by decide
  have hdescent : baseEnd_4710437 < baseStart_4710437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710453 : List Nat := [1, 3, 3, 1, 1, 1, 4, 3, 2, 4]
def baseStart_4710453 : Nat := 118140960795 + 4710453 * 2 ^ 59
def prefixEnd_4710453 : Nat := 4983230072969 + 3 ^ 40 * 4710453 * 2
def baseEnd_4710453 : Nat := 806242163137721354891509

theorem tailTrace_4710453 : CollatzResearch.WordTrace tailWord_4710453 prefixEnd_4710453 806242163137721354891509 := by
  unfold tailWord_4710453
  simp only [CollatzResearch.WordTrace]
  refine ⟨171804335203840737169480013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114536223469227158112986675 171804335203840737169480013)
  ·
    refine ⟨64426625701440276438555005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171804335203840737169480013 64426625701440276438555005)
    ·
      refine ⟨24159984638040103664458127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64426625701440276438555005 24159984638040103664458127)
      ·
        refine ⟨36239976957060155496687191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24159984638040103664458127 36239976957060155496687191)
        ·
          refine ⟨54359965435590233245030787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36239976957060155496687191 54359965435590233245030787)
          ·
            refine ⟨81539948153385349867546181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54359965435590233245030787 81539948153385349867546181)
            ·
              refine ⟨15288740278759753100164909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81539948153385349867546181 15288740278759753100164909)
              ·
                refine ⟨5733277604534907412561841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15288740278759753100164909 5733277604534907412561841)
                ·
                  refine ⟨4299958203401180559421381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5733277604534907412561841 4299958203401180559421381)
                  ·
                    refine ⟨806242163137721354891509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4299958203401180559421381 806242163137721354891509)
                    ·
                      rfl

theorem cell23_4710453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_4710453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710453 prefixEnd_4710453 := by exact prefixLift 4710453
  have htrace : WordTrace (prefixWord ++ tailWord_4710453) baseStart_4710453 baseEnd_4710453 := by
    simpa [prefixWord, tailWord_4710453, baseEnd_4710453] using wordTrace_append hprefix tailTrace_4710453
  have hstable : (prefixWord ++ tailWord_4710453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710453).length < 2 ^ (prefixWord ++ tailWord_4710453).sum := by decide
  have hdescent : baseEnd_4710453 < baseStart_4710453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710460 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 3, 2, 2]
def baseStart_4710460 : Nat := 118140960795 + 4710460 * 2 ^ 59
def prefixEnd_4710460 : Nat := 4983230072969 + 3 ^ 40 * 4710460 * 2
def baseEnd_4710460 : Nat := 2418730083777745537286995

theorem tailTrace_4710460 : CollatzResearch.WordTrace tailWord_4710460 prefixEnd_4710460 2418730083777745537286995 := by
  unfold tailWord_4710460
  simp only [CollatzResearch.WordTrace]
  refine ⟨85902295257407688682492417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114536393676543584909989889 85902295257407688682492417)
  ·
    refine ⟨64426721443055766511869313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85902295257407688682492417 64426721443055766511869313)
    ·
      refine ⟨48320041082291824883901985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64426721443055766511869313 48320041082291824883901985)
      ·
        refine ⟨36240030811718868662926489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48320041082291824883901985 36240030811718868662926489)
        ·
          refine ⟨27180023108789151497194867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36240030811718868662926489 27180023108789151497194867)
          ·
            refine ⟨40770034663183727245792301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27180023108789151497194867 40770034663183727245792301)
            ·
              refine ⟨15288762998693897717172113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40770034663183727245792301 15288762998693897717172113)
              ·
                refine ⟨11466572249020423287879085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15288762998693897717172113 11466572249020423287879085)
                ·
                  refine ⟨4299964593382658732954657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11466572249020423287879085 4299964593382658732954657)
                  ·
                    refine ⟨3224973445036994049715993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4299964593382658732954657 3224973445036994049715993)
                    ·
                      refine ⟨2418730083777745537286995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3224973445036994049715993 2418730083777745537286995)
                      ·
                        rfl

theorem cell23_4710460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_4710460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710460 prefixEnd_4710460 := by exact prefixLift 4710460
  have htrace : WordTrace (prefixWord ++ tailWord_4710460) baseStart_4710460 baseEnd_4710460 := by
    simpa [prefixWord, tailWord_4710460, baseEnd_4710460] using wordTrace_append hprefix tailTrace_4710460
  have hstable : (prefixWord ++ tailWord_4710460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710460).length < 2 ^ (prefixWord ++ tailWord_4710460).sum := by decide
  have hdescent : baseEnd_4710460 < baseStart_4710460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710470 : List Nat := [6, 1, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_4710470 : Nat := 118140960795 + 4710470 * 2 ^ 59
def prefixEnd_4710470 : Nat := 4983230072969 + 3 ^ 40 * 4710470 * 2
def baseEnd_4710470 : Nat := 806245072861430166053983

theorem tailTrace_4710470 : CollatzResearch.WordTrace tailWord_4710470 prefixEnd_4710470 806245072861430166053983 := by
  unfold tailWord_4710470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5368904851399348408526527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 114536636829852766048565909 5368904851399348408526527)
  ·
    refine ⟨8053357277099022612789791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5368904851399348408526527 8053357277099022612789791)
    ·
      refine ⟨12080035915648533919184687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8053357277099022612789791 12080035915648533919184687)
      ·
        refine ⟨18120053873472800878777031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12080035915648533919184687 18120053873472800878777031)
        ·
          refine ⟨27180080810209201318165547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18120053873472800878777031 27180080810209201318165547)
          ·
            refine ⟨40770121215313801977248321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27180080810209201318165547 40770121215313801977248321)
            ·
              refine ⟨30577590911485351482936241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40770121215313801977248321 30577590911485351482936241)
              ·
                refine ⟨22933193183614013612202181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30577590911485351482936241 22933193183614013612202181)
                ·
                  refine ⟨4299973721927627552287909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22933193183614013612202181 4299973721927627552287909)
                  ·
                    refine ⟨806245072861430166053983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4299973721927627552287909 806245072861430166053983)
                    ·
                      rfl

theorem cell23_4710470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_4710470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710470 prefixEnd_4710470 := by exact prefixLift 4710470
  have htrace : WordTrace (prefixWord ++ tailWord_4710470) baseStart_4710470 baseEnd_4710470 := by
    simpa [prefixWord, tailWord_4710470, baseEnd_4710470] using wordTrace_append hprefix tailTrace_4710470
  have hstable : (prefixWord ++ tailWord_4710470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710470).length < 2 ^ (prefixWord ++ tailWord_4710470).sum := by decide
  have hdescent : baseEnd_4710470 < baseStart_4710470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710479 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 4, 7]
def baseStart_4710479 : Nat := 118140960795 + 4710479 * 2 ^ 59
def prefixEnd_4710479 : Nat := 4983230072969 + 3 ^ 40 * 4710479 * 2
def baseEnd_4710479 : Nat := 806246613303393654316469

theorem tailTrace_4710479 : CollatzResearch.WordTrace tailWord_4710479 prefixEnd_4710479 806246613303393654316469 := by
  unfold tailWord_4710479
  simp only [CollatzResearch.WordTrace]
  refine ⟨171805283501746543609926491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114536855667831029073284327 171805283501746543609926491)
  ·
    refine ⟨257707925252619815414889737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171805283501746543609926491 257707925252619815414889737)
    ·
      refine ⟨193280943939464861561167303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257707925252619815414889737 193280943939464861561167303)
      ·
        refine ⟨289921415909197292341750955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193280943939464861561167303 289921415909197292341750955)
        ·
          refine ⟨434882123863795938512626433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289921415909197292341750955 434882123863795938512626433)
          ·
            refine ⟨326161592897846953884469825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434882123863795938512626433 326161592897846953884469825)
            ·
              refine ⟨244621194673385215413352369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326161592897846953884469825 244621194673385215413352369)
              ·
                refine ⟨183465896005038911560014277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244621194673385215413352369 183465896005038911560014277)
                ·
                  refine ⟨34399855500944795917502677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183465896005038911560014277 34399855500944795917502677)
                  ·
                    refine ⟨806246613303393654316469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34399855500944795917502677 806246613303393654316469)
                    ·
                      rfl

theorem cell23_4710479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_4710479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710479 prefixEnd_4710479 := by exact prefixLift 4710479
  have htrace : WordTrace (prefixWord ++ tailWord_4710479) baseStart_4710479 baseEnd_4710479 := by
    simpa [prefixWord, tailWord_4710479, baseEnd_4710479] using wordTrace_append hprefix tailTrace_4710479
  have hstable : (prefixWord ++ tailWord_4710479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710479).length < 2 ^ (prefixWord ++ tailWord_4710479).sum := by decide
  have hdescent : baseEnd_4710479 < baseStart_4710479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710586 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_4710586 : Nat := 118140960795 + 4710586 * 2 ^ 59
def prefixEnd_4710586 : Nat := 4983230072969 + 3 ^ 40 * 4710586 * 2
def baseEnd_4710586 : Nat := 806264927446737348103805

theorem tailTrace_4710586 : CollatzResearch.WordTrace tailWord_4710586 prefixEnd_4710586 806264927446737348103805 := by
  unfold tailWord_4710586
  simp only [CollatzResearch.WordTrace]
  refine ⟨42952296528089725221017903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114539457408239267256047741 42952296528089725221017903)
  ·
    refine ⟨64428444792134587831526855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42952296528089725221017903 64428444792134587831526855)
    ·
      refine ⟨96642667188201881747290283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64428444792134587831526855 96642667188201881747290283)
      ·
        refine ⟨144964000782302822620935425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96642667188201881747290283 144964000782302822620935425)
        ·
          refine ⟨108723000586727116965701569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144964000782302822620935425 108723000586727116965701569)
          ·
            refine ⟨81542250440045337724276177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108723000586727116965701569 81542250440045337724276177)
            ·
              refine ⟨61156687830034003293207133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81542250440045337724276177 61156687830034003293207133)
              ·
                refine ⟨22933757936262751234952675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61156687830034003293207133 22933757936262751234952675)
                ·
                  refine ⟨34400636904394126852429013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22933757936262751234952675 34400636904394126852429013)
                  ·
                    refine ⟨806264927446737348103805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34400636904394126852429013 806264927446737348103805)
                    ·
                      rfl

theorem cell23_4710586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_4710586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710586 prefixEnd_4710586 := by exact prefixLift 4710586
  have htrace : WordTrace (prefixWord ++ tailWord_4710586) baseStart_4710586 baseEnd_4710586 := by
    simpa [prefixWord, tailWord_4710586, baseEnd_4710586] using wordTrace_append hprefix tailTrace_4710586
  have hstable : (prefixWord ++ tailWord_4710586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710586).length < 2 ^ (prefixWord ++ tailWord_4710586).sum := by decide
  have hdescent : baseEnd_4710586 < baseStart_4710586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710610 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_4710610 : Nat := 118140960795 + 4710610 * 2 ^ 59
def prefixEnd_4710610 : Nat := 4983230072969 + 3 ^ 40 * 4710610 * 2
def baseEnd_4710610 : Nat := 2418807105875919950411305

theorem tailTrace_4710610 : CollatzResearch.WordTrace tailWord_4710610 prefixEnd_4710610 2418807105875919950411305 := by
  unfold tailWord_4710610
  simp only [CollatzResearch.WordTrace]
  refine ⟨42952515366067988245736321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114540040976181301988630189 42952515366067988245736321)
  ·
    refine ⟨32214386524550991184302241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42952515366067988245736321 32214386524550991184302241)
    ·
      refine ⟨24160789893413243388226681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32214386524550991184302241 24160789893413243388226681)
      ·
        refine ⟨18120592420059932541170011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24160789893413243388226681 18120592420059932541170011)
        ·
          refine ⟨27180888630089898811755017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18120592420059932541170011 27180888630089898811755017)
          ·
            refine ⟨20385666472567424108816263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27180888630089898811755017 20385666472567424108816263)
            ·
              refine ⟨30578499708851136163224395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20385666472567424108816263 30578499708851136163224395)
              ·
                refine ⟨45867749563276704244836593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30578499708851136163224395 45867749563276704244836593)
                ·
                  refine ⟨34400812172457528183627445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45867749563276704244836593 34400812172457528183627445)
                  ·
                    refine ⟨3225076141167893267215073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34400812172457528183627445 3225076141167893267215073)
                    ·
                      refine ⟨2418807105875919950411305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225076141167893267215073 2418807105875919950411305)
                      ·
                        rfl

theorem cell23_4710610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_4710610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710610 prefixEnd_4710610 := by exact prefixLift 4710610
  have htrace : WordTrace (prefixWord ++ tailWord_4710610) baseStart_4710610 baseEnd_4710610 := by
    simpa [prefixWord, tailWord_4710610, baseEnd_4710610] using wordTrace_append hprefix tailTrace_4710610
  have hstable : (prefixWord ++ tailWord_4710610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710610).length < 2 ^ (prefixWord ++ tailWord_4710610).sum := by decide
  have hdescent : baseEnd_4710610 < baseStart_4710610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710633 : List Nat := [1, 2, 1, 1, 1, 2, 2, 6, 3, 4]
def baseStart_4710633 : Nat := 118140960795 + 4710633 * 2 ^ 59
def prefixEnd_4710633 : Nat := 4983230072969 + 3 ^ 40 * 4710633 * 2
def baseEnd_4710633 : Nat := 806272971976991120141233

theorem tailTrace_4710633 : CollatzResearch.WordTrace tailWord_4710633 prefixEnd_4710633 806272971976991120141233 := by
  unfold tailWord_4710633
  simp only [CollatzResearch.WordTrace]
  refine ⟨171810900343188627911032553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114540600228792418607355035 171810900343188627911032553)
  ·
    refine ⟨128858175257391470933274415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171810900343188627911032553 128858175257391470933274415)
    ·
      refine ⟨193287262886087206399911623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128858175257391470933274415 193287262886087206399911623)
      ·
        refine ⟨289930894329130809599867435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193287262886087206399911623 289930894329130809599867435)
        ·
          refine ⟨434896341493696214399801153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289930894329130809599867435 434896341493696214399801153)
          ·
            refine ⟨326172256120272160799850865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434896341493696214399801153 326172256120272160799850865)
            ·
              refine ⟨244629192090204120599888149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326172256120272160799850865 244629192090204120599888149)
              ·
                refine ⟨11466993379228318153119757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 244629192090204120599888149 11466993379228318153119757)
                ·
                  refine ⟨4300122517210619307419909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11466993379228318153119757 4300122517210619307419909)
                  ·
                    refine ⟨806272971976991120141233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4300122517210619307419909 806272971976991120141233)
                    ·
                      rfl

theorem cell23_4710633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 4].length) (baseStart_4710633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710633 prefixEnd_4710633 := by exact prefixLift 4710633
  have htrace : WordTrace (prefixWord ++ tailWord_4710633) baseStart_4710633 baseEnd_4710633 := by
    simpa [prefixWord, tailWord_4710633, baseEnd_4710633] using wordTrace_append hprefix tailTrace_4710633
  have hstable : (prefixWord ++ tailWord_4710633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710633).length < 2 ^ (prefixWord ++ tailWord_4710633).sum := by decide
  have hdescent : baseEnd_4710633 < baseStart_4710633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710637 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_4710637 : Nat := 118140960795 + 4710637 * 2 ^ 59
def prefixEnd_4710637 : Nat := 4983230072969 + 3 ^ 40 * 4710637 * 2
def baseEnd_4710637 : Nat := 806273656617863781591227

theorem tailTrace_4710637 : CollatzResearch.WordTrace tailWord_4710637 prefixEnd_4710637 806273656617863781591227 := by
  unfold tailWord_4710637
  simp only [CollatzResearch.WordTrace]
  refine ⟨171811046235174136594178165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114540697490116091062785443 171811046235174136594178165)
  ·
    refine ⟨16107285584547575305704203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171811046235174136594178165 16107285584547575305704203)
    ·
      refine ⟨24160928376821362958556305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16107285584547575305704203 24160928376821362958556305)
      ·
        refine ⟨18120696282616022218917229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24160928376821362958556305 18120696282616022218917229)
        ·
          refine ⟨6795261105981008332093961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18120696282616022218917229 6795261105981008332093961)
          ·
            refine ⟨5096445829485756249070471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6795261105981008332093961 5096445829485756249070471)
            ·
              refine ⟨7644668744228634373605707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5096445829485756249070471 7644668744228634373605707)
              ·
                refine ⟨11467003116342951560408561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7644668744228634373605707 11467003116342951560408561)
                ·
                  refine ⟨8600252337257213670306421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11467003116342951560408561 8600252337257213670306421)
                  ·
                    refine ⟨806273656617863781591227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8600252337257213670306421 806273656617863781591227)
                    ·
                      rfl

theorem cell23_4710637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_4710637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710637 prefixEnd_4710637 := by exact prefixLift 4710637
  have htrace : WordTrace (prefixWord ++ tailWord_4710637) baseStart_4710637 baseEnd_4710637 := by
    simpa [prefixWord, tailWord_4710637, baseEnd_4710637] using wordTrace_append hprefix tailTrace_4710637
  have hstable : (prefixWord ++ tailWord_4710637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710637).length < 2 ^ (prefixWord ++ tailWord_4710637).sum := by decide
  have hdescent : baseEnd_4710637 < baseStart_4710637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710643 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 3]
def baseStart_4710643 : Nat := 118140960795 + 4710643 * 2 ^ 59
def prefixEnd_4710643 : Nat := 4983230072969 + 3 ^ 40 * 4710643 * 2
def baseEnd_4710643 : Nat := 2418824050737518321298653

theorem tailTrace_4710643 : CollatzResearch.WordTrace tailWord_4710643 prefixEnd_4710643 2418824050737518321298653 := by
  unfold tailWord_4710643
  simp only [CollatzResearch.WordTrace]
  refine ⟨171811265073152399618896583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114540843382101599745931055 171811265073152399618896583)
  ·
    refine ⟨257716897609728599428344875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171811265073152399618896583 257716897609728599428344875)
    ·
      refine ⟨386575346414592899142517313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257716897609728599428344875 386575346414592899142517313)
      ·
        refine ⟨289931509810944674356887985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386575346414592899142517313 289931509810944674356887985)
        ·
          refine ⟨217448632358208505767665989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289931509810944674356887985 217448632358208505767665989)
          ·
            refine ⟨40771618567164094831437373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 217448632358208505767665989 40771618567164094831437373)
            ·
              refine ⟨15289356962686535561789015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40771618567164094831437373 15289356962686535561789015)
              ·
                refine ⟨22934035444029803342683523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15289356962686535561789015 22934035444029803342683523)
                ·
                  refine ⟨34401053166044705014025285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22934035444029803342683523 34401053166044705014025285)
                  ·
                    refine ⟨6450197468633382190129741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34401053166044705014025285 6450197468633382190129741)
                    ·
                      refine ⟨2418824050737518321298653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6450197468633382190129741 2418824050737518321298653)
                      ·
                        rfl

theorem cell23_4710643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 3].length) (baseStart_4710643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710643 prefixEnd_4710643 := by exact prefixLift 4710643
  have htrace : WordTrace (prefixWord ++ tailWord_4710643) baseStart_4710643 baseEnd_4710643 := by
    simpa [prefixWord, tailWord_4710643, baseEnd_4710643] using wordTrace_append hprefix tailTrace_4710643
  have hstable : (prefixWord ++ tailWord_4710643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710643).length < 2 ^ (prefixWord ++ tailWord_4710643).sum := by decide
  have hdescent : baseEnd_4710643 < baseStart_4710643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710680 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 6]
def baseStart_4710680 : Nat := 118140960795 + 4710680 * 2 ^ 59
def prefixEnd_4710680 : Nat := 4983230072969 + 3 ^ 40 * 4710680 * 2
def baseEnd_4710680 : Nat := 268760338835748297392887

theorem tailTrace_4710680 : CollatzResearch.WordTrace tailWord_4710680 prefixEnd_4710680 268760338835748297392887 := by
  unfold tailWord_4710680
  simp only [CollatzResearch.WordTrace]
  refine ⟨85906307287009177468996747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114541743049345569958662329 85906307287009177468996747)
  ·
    refine ⟨128859460930513766203495121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85906307287009177468996747 128859460930513766203495121)
    ·
      refine ⟨96644595697885324652621341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128859460930513766203495121 96644595697885324652621341)
      ·
        refine ⟨36241723386706996744733003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96644595697885324652621341 36241723386706996744733003)
        ·
          refine ⟨54362585080060495117099505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36241723386706996744733003 54362585080060495117099505)
          ·
            refine ⟨40771938810045371337824629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54362585080060495117099505 40771938810045371337824629)
            ·
              refine ⟨3822369263441753562921059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40771938810045371337824629 3822369263441753562921059)
              ·
                refine ⟨5733553895162630344381589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3822369263441753562921059 5733553895162630344381589)
                ·
                  refine ⟨268760338835748297392887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5733553895162630344381589 268760338835748297392887)
                  ·
                    rfl

theorem cell23_4710680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 6].length) (baseStart_4710680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710680 prefixEnd_4710680 := by exact prefixLift 4710680
  have htrace : WordTrace (prefixWord ++ tailWord_4710680) baseStart_4710680 baseEnd_4710680 := by
    simpa [prefixWord, tailWord_4710680, baseEnd_4710680] using wordTrace_append hprefix tailTrace_4710680
  have hstable : (prefixWord ++ tailWord_4710680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710680).length < 2 ^ (prefixWord ++ tailWord_4710680).sum := by decide
  have hdescent : baseEnd_4710680 < baseStart_4710680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710700 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 1, 5, 2]
def baseStart_4710700 : Nat := 118140960795 + 4710700 * 2 ^ 59
def prefixEnd_4710700 : Nat := 4983230072969 + 3 ^ 40 * 4710700 * 2
def baseEnd_4710700 : Nat := 2418853319134824598285891

theorem tailTrace_4710700 : CollatzResearch.WordTrace tailWord_4710700 prefixEnd_4710700 2418853319134824598285891 := by
  unfold tailWord_4710700
  simp only [CollatzResearch.WordTrace]
  refine ⟨85906672016972949176860777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114542229355963932235814369 85906672016972949176860777)
  ·
    refine ⟨64430004012729711882645583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85906672016972949176860777 64430004012729711882645583)
    ·
      refine ⟨96645006019094567823968375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64430004012729711882645583 96645006019094567823968375)
      ·
        refine ⟨144967509028641851735952563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96645006019094567823968375 144967509028641851735952563)
        ·
          refine ⟨217451263542962777603928845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144967509028641851735952563 217451263542962777603928845)
          ·
            refine ⟨81544223828611041601473317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217451263542962777603928845 81544223828611041601473317)
            ·
              refine ⟨15289541967864570300276247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81544223828611041601473317 15289541967864570300276247)
              ·
                refine ⟨22934312951796855450414371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15289541967864570300276247 22934312951796855450414371)
                ·
                  refine ⟨34401469427695283175621557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22934312951796855450414371 34401469427695283175621557)
                  ·
                    refine ⟨3225137758846432797714521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34401469427695283175621557 3225137758846432797714521)
                    ·
                      refine ⟨2418853319134824598285891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225137758846432797714521 2418853319134824598285891)
                      ·
                        rfl

theorem cell23_4710700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 5, 2].length) (baseStart_4710700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710700 prefixEnd_4710700 := by exact prefixLift 4710700
  have htrace : WordTrace (prefixWord ++ tailWord_4710700) baseStart_4710700 baseEnd_4710700 := by
    simpa [prefixWord, tailWord_4710700, baseEnd_4710700] using wordTrace_append hprefix tailTrace_4710700
  have hstable : (prefixWord ++ tailWord_4710700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710700).length < 2 ^ (prefixWord ++ tailWord_4710700).sum := by decide
  have hdescent : baseEnd_4710700 < baseStart_4710700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710743 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_4710743 : Nat := 118140960795 + 4710743 * 2 ^ 59
def prefixEnd_4710743 : Nat := 4983230072969 + 3 ^ 40 * 4710743 * 2
def baseEnd_4710743 : Nat := 2418875398802967930048193

theorem tailTrace_4710743 : CollatzResearch.WordTrace tailWord_4710743 prefixEnd_4710743 2418875398802967930048193 := by
  unfold tailWord_4710743
  simp only [CollatzResearch.WordTrace]
  refine ⟨171814912372790116697536883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114543274915193411131691255 171814912372790116697536883)
  ·
    refine ⟨257722368559185175046305325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171814912372790116697536883 257722368559185175046305325)
    ·
      refine ⟨96645888209694440642364497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257722368559185175046305325 96645888209694440642364497)
      ·
        refine ⟨72484416157270830481773373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96645888209694440642364497 72484416157270830481773373)
        ·
          refine ⟨27181656058976561430665015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72484416157270830481773373 27181656058976561430665015)
          ·
            refine ⟨40772484088464842145997523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27181656058976561430665015 40772484088464842145997523)
            ·
              refine ⟨61158726132697263218996285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40772484088464842145997523 61158726132697263218996285)
              ·
                refine ⟨22934522299761473707123607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61158726132697263218996285 22934522299761473707123607)
                ·
                  refine ⟨34401783449642210560685411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22934522299761473707123607 34401783449642210560685411)
                  ·
                    refine ⟨51602675174463315841028117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34401783449642210560685411 51602675174463315841028117)
                    ·
                      refine ⟨2418875398802967930048193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51602675174463315841028117 2418875398802967930048193)
                      ·
                        rfl

theorem cell23_4710743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_4710743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710743 prefixEnd_4710743 := by exact prefixLift 4710743
  have htrace : WordTrace (prefixWord ++ tailWord_4710743) baseStart_4710743 baseEnd_4710743 := by
    simpa [prefixWord, tailWord_4710743, baseEnd_4710743] using wordTrace_append hprefix tailTrace_4710743
  have hstable : (prefixWord ++ tailWord_4710743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710743).length < 2 ^ (prefixWord ++ tailWord_4710743).sum := by decide
  have hdescent : baseEnd_4710743 < baseStart_4710743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710760 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_4710760 : Nat := 118140960795 + 4710760 * 2 ^ 59
def prefixEnd_4710760 : Nat := 4983230072969 + 3 ^ 40 * 4710760 * 2
def baseEnd_4710760 : Nat := 2418884127974094363535615

theorem tailTrace_4710760 : CollatzResearch.WordTrace tailWord_4710760 prefixEnd_4710760 2418884127974094363535615 := by
  unfold tailWord_4710760
  simp only [CollatzResearch.WordTrace]
  refine ⟨85907766206864264300452867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114543688275819019067270489 85907766206864264300452867)
  ·
    refine ⟨128861649310296396450679301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85907766206864264300452867 128861649310296396450679301)
    ·
      refine ⟨24161559245680574334502369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128861649310296396450679301 24161559245680574334502369)
      ·
        refine ⟨18121169434260430750876777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24161559245680574334502369 18121169434260430750876777)
        ·
          refine ⟨13590877075695323063157583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18121169434260430750876777 13590877075695323063157583)
          ·
            refine ⟨20386315613542984594736375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13590877075695323063157583 20386315613542984594736375)
            ·
              refine ⟨30579473420314476892104563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20386315613542984594736375 30579473420314476892104563)
              ·
                refine ⟨45869210130471715338156845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30579473420314476892104563 45869210130471715338156845)
                ·
                  refine ⟨17200953798926893251808817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45869210130471715338156845 17200953798926893251808817)
                  ·
                    refine ⟨12900715349195169938856613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17200953798926893251808817 12900715349195169938856613)
                    ·
                      refine ⟨2418884127974094363535615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12900715349195169938856613 2418884127974094363535615)
                      ·
                        rfl

theorem cell23_4710760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_4710760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710760 prefixEnd_4710760 := by exact prefixLift 4710760
  have htrace : WordTrace (prefixWord ++ tailWord_4710760) baseStart_4710760 baseEnd_4710760 := by
    simpa [prefixWord, tailWord_4710760, baseEnd_4710760] using wordTrace_append hprefix tailTrace_4710760
  have hstable : (prefixWord ++ tailWord_4710760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710760).length < 2 ^ (prefixWord ++ tailWord_4710760).sum := by decide
  have hdescent : baseEnd_4710760 < baseStart_4710760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710764 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 4]
def baseStart_4710764 : Nat := 118140960795 + 4710764 * 2 ^ 59
def prefixEnd_4710764 : Nat := 4983230072969 + 3 ^ 40 * 4710764 * 2
def baseEnd_4710764 : Nat := 2418886181896712347885597

theorem tailTrace_4710764 : CollatzResearch.WordTrace tailWord_4710764 prefixEnd_4710764 2418886181896712347885597 := by
  unfold tailWord_4710764
  simp only [CollatzResearch.WordTrace]
  refine ⟨85907839152857018642025673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114543785537142691522700897 85907839152857018642025673)
  ·
    refine ⟨64430879364642763981519255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85907839152857018642025673 64430879364642763981519255)
    ·
      refine ⟨96646319046964145972278883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64430879364642763981519255 96646319046964145972278883)
      ·
        refine ⟨144969478570446218958418325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96646319046964145972278883 144969478570446218958418325)
        ·
          refine ⟨6795444307989666513675859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 144969478570446218958418325 6795444307989666513675859)
          ·
            refine ⟨10193166461984499770513789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6795444307989666513675859 10193166461984499770513789)
            ·
              refine ⟨3822437423244187413942671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10193166461984499770513789 3822437423244187413942671)
              ·
                refine ⟨5733656134866281120914007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3822437423244187413942671 5733656134866281120914007)
                ·
                  refine ⟨8600484202299421681371011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5733656134866281120914007 8600484202299421681371011)
                  ·
                    refine ⟨12900726303449132522056517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8600484202299421681371011 12900726303449132522056517)
                    ·
                      refine ⟨2418886181896712347885597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12900726303449132522056517 2418886181896712347885597)
                      ·
                        rfl

theorem cell23_4710764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 4].length) (baseStart_4710764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710764 prefixEnd_4710764 := by exact prefixLift 4710764
  have htrace : WordTrace (prefixWord ++ tailWord_4710764) baseStart_4710764 baseEnd_4710764 := by
    simpa [prefixWord, tailWord_4710764, baseEnd_4710764] using wordTrace_append hprefix tailTrace_4710764
  have hstable : (prefixWord ++ tailWord_4710764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710764).length < 2 ^ (prefixWord ++ tailWord_4710764).sum := by decide
  have hdescent : baseEnd_4710764 < baseStart_4710764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710781 : List Nat := [1, 4, 1, 1, 2, 4, 1, 4, 1, 2, 2]
def baseStart_4710781 : Nat := 118140960795 + 4710781 * 2 ^ 59
def prefixEnd_4710781 : Nat := 4983230072969 + 3 ^ 40 * 4710781 * 2
def baseEnd_4710781 : Nat := 2418894911067838781373019

theorem tailTrace_4710781 : CollatzResearch.WordTrace tailWord_4710781 prefixEnd_4710781 2418894911067838781373019 := by
  unfold tailWord_4710781
  simp only [CollatzResearch.WordTrace]
  refine ⟨171816298346652449187420197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114544198897768299458280131 171816298346652449187420197)
  ·
    refine ⟨32215555939997334222641287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171816298346652449187420197 32215555939997334222641287)
    ·
      refine ⟨48323333909996001333961931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32215555939997334222641287 48323333909996001333961931)
      ·
        refine ⟨72485000864994002000942897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48323333909996001333961931 72485000864994002000942897)
        ·
          refine ⟨54363750648745501500707173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72485000864994002000942897 54363750648745501500707173)
          ·
            refine ⟨10193203246639781531382595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54363750648745501500707173 10193203246639781531382595)
            ·
              refine ⟨15289804869959672297073893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10193203246639781531382595 15289804869959672297073893)
              ·
                refine ⟨2866838413117438555701355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15289804869959672297073893 2866838413117438555701355)
                ·
                  refine ⟨4300257619676157833552033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866838413117438555701355 4300257619676157833552033)
                  ·
                    refine ⟨3225193214757118375164025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4300257619676157833552033 3225193214757118375164025)
                    ·
                      refine ⟨2418894911067838781373019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225193214757118375164025 2418894911067838781373019)
                      ·
                        rfl

theorem cell23_4710781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 4, 1, 2, 2].length) (baseStart_4710781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710781 prefixEnd_4710781 := by exact prefixLift 4710781
  have htrace : WordTrace (prefixWord ++ tailWord_4710781) baseStart_4710781 baseEnd_4710781 := by
    simpa [prefixWord, tailWord_4710781, baseEnd_4710781] using wordTrace_append hprefix tailTrace_4710781
  have hstable : (prefixWord ++ tailWord_4710781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710781).length < 2 ^ (prefixWord ++ tailWord_4710781).sum := by decide
  have hdescent : baseEnd_4710781 < baseStart_4710781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710787 : List Nat := [1, 1, 1, 3, 7, 1, 1, 8]
def baseStart_4710787 : Nat := 118140960795 + 4710787 * 2 ^ 59
def prefixEnd_4710787 : Nat := 4983230072969 + 3 ^ 40 * 4710787 * 2
def baseEnd_4710787 : Nat := 89588814516732065107333

theorem tailTrace_4710787 : CollatzResearch.WordTrace tailWord_4710787 prefixEnd_4710787 89588814516732065107333 := by
  unfold tailWord_4710787
  simp only [CollatzResearch.WordTrace]
  refine ⟨171816517184630712212138615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114544344789753808141425743 171816517184630712212138615)
  ·
    refine ⟨257724775776946068318207923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171816517184630712212138615 257724775776946068318207923)
    ·
      refine ⟨386587163665419102477311885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257724775776946068318207923 386587163665419102477311885)
      ·
        refine ⟨144970186374532163428991957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 386587163665419102477311885 144970186374532163428991957)
        ·
          refine ⟨3397738743153097580366999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 144970186374532163428991957 3397738743153097580366999)
          ·
            refine ⟨5096608114729646370550499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3397738743153097580366999 5096608114729646370550499)
            ·
              refine ⟨7644912172094469555825749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5096608114729646370550499 7644912172094469555825749)
              ·
                refine ⟨89588814516732065107333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7644912172094469555825749 89588814516732065107333)
                ·
                  rfl

theorem cell23_4710787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 8].length) (baseStart_4710787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710787 prefixEnd_4710787 := by exact prefixLift 4710787
  have htrace : WordTrace (prefixWord ++ tailWord_4710787) baseStart_4710787 baseEnd_4710787 := by
    simpa [prefixWord, tailWord_4710787, baseEnd_4710787] using wordTrace_append hprefix tailTrace_4710787
  have hstable : (prefixWord ++ tailWord_4710787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710787).length < 2 ^ (prefixWord ++ tailWord_4710787).sum := by decide
  have hdescent : baseEnd_4710787 < baseStart_4710787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710794 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_4710794 : Nat := 118140960795 + 4710794 * 2 ^ 59
def prefixEnd_4710794 : Nat := 4983230072969 + 3 ^ 40 * 4710794 * 2
def baseEnd_4710794 : Nat := 2418901586316347230510459

theorem tailTrace_4710794 : CollatzResearch.WordTrace tailWord_4710794 prefixEnd_4710794 2418901586316347230510459 := by
  unfold tailWord_4710794
  simp only [CollatzResearch.WordTrace]
  refine ⟨42954193123901338101910859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114544514997070234938428957 42954193123901338101910859)
  ·
    refine ⟨64431289685852007152866289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42954193123901338101910859 64431289685852007152866289)
    ·
      refine ⟨48323467264389005364649717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64431289685852007152866289 48323467264389005364649717)
      ·
        refine ⟨4530325056036469252935911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48323467264389005364649717 4530325056036469252935911)
        ·
          refine ⟨6795487584054703879403867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4530325056036469252935911 6795487584054703879403867)
          ·
            refine ⟨10193231376082055819105801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6795487584054703879403867 10193231376082055819105801)
            ·
              refine ⟨7644923532061541864329351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10193231376082055819105801 7644923532061541864329351)
              ·
                refine ⟨11467385298092312796494027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7644923532061541864329351 11467385298092312796494027)
                ·
                  refine ⟨17201077947138469194741041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11467385298092312796494027 17201077947138469194741041)
                  ·
                    refine ⟨12900808460353851896055781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17201077947138469194741041 12900808460353851896055781)
                    ·
                      refine ⟨2418901586316347230510459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12900808460353851896055781 2418901586316347230510459)
                      ·
                        rfl

theorem cell23_4710794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_4710794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710794 prefixEnd_4710794 := by exact prefixLift 4710794
  have htrace : WordTrace (prefixWord ++ tailWord_4710794) baseStart_4710794 baseEnd_4710794 := by
    simpa [prefixWord, tailWord_4710794, baseEnd_4710794] using wordTrace_append hprefix tailTrace_4710794
  have hstable : (prefixWord ++ tailWord_4710794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710794).length < 2 ^ (prefixWord ++ tailWord_4710794).sum := by decide
  have hdescent : baseEnd_4710794 < baseStart_4710794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710807 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 3, 3, 2]
def baseStart_4710807 : Nat := 118140960795 + 4710807 * 2 ^ 59
def prefixEnd_4710807 : Nat := 4983230072969 + 3 ^ 40 * 4710807 * 2
def baseEnd_4710807 : Nat := 2418908261564855679647899

theorem tailTrace_4710807 : CollatzResearch.WordTrace tailWord_4710807 prefixEnd_4710807 2418908261564855679647899 := by
  unfold tailWord_4710807
  simp only [CollatzResearch.WordTrace]
  refine ⟨171817246644558255627866675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114544831096372170418577783 171817246644558255627866675)
  ·
    refine ⟨257725869966837383441800013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171817246644558255627866675 257725869966837383441800013)
    ·
      refine ⟨96647201237564018790675005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257725869966837383441800013 96647201237564018790675005)
      ·
        refine ⟨36242700464086507046503127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96647201237564018790675005 36242700464086507046503127)
        ·
          refine ⟨54364050696129760569754691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36242700464086507046503127 54364050696129760569754691)
          ·
            refine ⟨81546076044194640854632037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54364050696129760569754691 81546076044194640854632037)
            ·
              refine ⟨15289889258286495160243507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81546076044194640854632037 15289889258286495160243507)
              ·
                refine ⟨22934833887429742740365261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15289889258286495160243507 22934833887429742740365261)
                ·
                  refine ⟨8600562707786153527636973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22934833887429742740365261 8600562707786153527636973)
                  ·
                    refine ⟨3225211015419807572863865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8600562707786153527636973 3225211015419807572863865)
                    ·
                      refine ⟨2418908261564855679647899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225211015419807572863865 2418908261564855679647899)
                      ·
                        rfl

theorem cell23_4710807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_4710807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710807 prefixEnd_4710807 := by exact prefixLift 4710807
  have htrace : WordTrace (prefixWord ++ tailWord_4710807) baseStart_4710807 baseEnd_4710807 := by
    simpa [prefixWord, tailWord_4710807, baseEnd_4710807] using wordTrace_append hprefix tailTrace_4710807
  have hstable : (prefixWord ++ tailWord_4710807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710807).length < 2 ^ (prefixWord ++ tailWord_4710807).sum := by decide
  have hdescent : baseEnd_4710807 < baseStart_4710807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710814 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_4710814 : Nat := 118140960795 + 4710814 * 2 ^ 59
def prefixEnd_4710814 : Nat := 4983230072969 + 3 ^ 40 * 4710814 * 2
def baseEnd_4710814 : Nat := 2418911855929437152260367

theorem tailTrace_4710814 : CollatzResearch.WordTrace tailWord_4710814 prefixEnd_4710814 2418911855929437152260367 := by
  unfold tailWord_4710814
  simp only [CollatzResearch.WordTrace]
  refine ⟨21477187744441611977921437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114545001303688597215580997 21477187744441611977921437)
  ·
    refine ⟨8053945404165604491720539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21477187744441611977921437 8053945404165604491720539)
    ·
      refine ⟨12080918106248406737580809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8053945404165604491720539 12080918106248406737580809)
      ·
        refine ⟨9060688579686305053185607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12080918106248406737580809 9060688579686305053185607)
        ·
          refine ⟨13591032869529457579778411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9060688579686305053185607 13591032869529457579778411)
          ·
            refine ⟨20386549304294186369667617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13591032869529457579778411 20386549304294186369667617)
            ·
              refine ⟨15289911978220639777250713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20386549304294186369667617 15289911978220639777250713)
              ·
                refine ⟨11467433983665479832938035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15289911978220639777250713 11467433983665479832938035)
                ·
                  refine ⟨17201150975498219749407053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11467433983665479832938035 17201150975498219749407053)
                  ·
                    refine ⟨6450431615811832406027645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17201150975498219749407053 6450431615811832406027645)
                    ·
                      refine ⟨2418911855929437152260367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6450431615811832406027645 2418911855929437152260367)
                      ·
                        rfl

theorem cell23_4710814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_4710814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710814 prefixEnd_4710814 := by exact prefixLift 4710814
  have htrace : WordTrace (prefixWord ++ tailWord_4710814) baseStart_4710814 baseEnd_4710814 := by
    simpa [prefixWord, tailWord_4710814, baseEnd_4710814] using wordTrace_append hprefix tailTrace_4710814
  have hstable : (prefixWord ++ tailWord_4710814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710814).length < 2 ^ (prefixWord ++ tailWord_4710814).sum := by decide
  have hdescent : baseEnd_4710814 < baseStart_4710814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710853 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_4710853 : Nat := 118140960795 + 4710853 * 2 ^ 59
def prefixEnd_4710853 : Nat := 4983230072969 + 3 ^ 40 * 4710853 * 2
def baseEnd_4710853 : Nat := 2418931881674962499672687

theorem tailTrace_4710853 : CollatzResearch.WordTrace tailWord_4710853 prefixEnd_4710853 2418931881674962499672687 := by
  unfold tailWord_4710853
  simp only [CollatzResearch.WordTrace]
  refine ⟨171818924402391605484041213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114545949601594403656027475 171818924402391605484041213)
  ·
    refine ⟨64432096650896852056515455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171818924402391605484041213 64432096650896852056515455)
    ·
      refine ⟨96648144976345278084773183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64432096650896852056515455 96648144976345278084773183)
      ·
        refine ⟨144972217464517917127159775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96648144976345278084773183 144972217464517917127159775)
        ·
          refine ⟨217458326196776875690739663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144972217464517917127159775 217458326196776875690739663)
          ·
            refine ⟨326187489295165313536109495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217458326196776875690739663 326187489295165313536109495)
            ·
              refine ⟨489281233942747970304164243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326187489295165313536109495 489281233942747970304164243)
              ·
                refine ⟨733921850914121955456246365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 489281233942747970304164243 733921850914121955456246365)
                ·
                  refine ⟨275220694092795733296092387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733921850914121955456246365 275220694092795733296092387)
                  ·
                    refine ⟨412831041139193599944138581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 275220694092795733296092387 412831041139193599944138581)
                    ·
                      refine ⟨2418931881674962499672687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 412831041139193599944138581 2418931881674962499672687)
                      ·
                        rfl

theorem cell23_4710853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_4710853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710853 prefixEnd_4710853 := by exact prefixLift 4710853
  have htrace : WordTrace (prefixWord ++ tailWord_4710853) baseStart_4710853 baseEnd_4710853 := by
    simpa [prefixWord, tailWord_4710853, baseEnd_4710853] using wordTrace_append hprefix tailTrace_4710853
  have hstable : (prefixWord ++ tailWord_4710853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710853).length < 2 ^ (prefixWord ++ tailWord_4710853).sum := by decide
  have hdescent : baseEnd_4710853 < baseStart_4710853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710897 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 2, 5, 2]
def baseStart_4710897 : Nat := 118140960795 + 4710897 * 2 ^ 59
def prefixEnd_4710897 : Nat := 4983230072969 + 3 ^ 40 * 4710897 * 2
def baseEnd_4710897 : Nat := 2418954474823760327522485

theorem tailTrace_4710897 : CollatzResearch.WordTrace tailWord_4710897 prefixEnd_4710897 2418954474823760327522485 := by
  unfold tailWord_4710897
  simp only [CollatzResearch.WordTrace]
  refine ⟨171820529214232200998642945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114547019476154800665761963 171820529214232200998642945)
  ·
    refine ⟨128865396910674150748982209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171820529214232200998642945 128865396910674150748982209)
    ·
      refine ⟨96649047683005613061736657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128865396910674150748982209 96649047683005613061736657)
      ·
        refine ⟨72486785762254209796302493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96649047683005613061736657 72486785762254209796302493)
        ·
          refine ⟨27182544660845328673613435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72486785762254209796302493 27182544660845328673613435)
          ·
            refine ⟨40773816991267993010420153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27182544660845328673613435 40773816991267993010420153)
            ·
              refine ⟨30580362743450994757815115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40773816991267993010420153 30580362743450994757815115)
              ·
                refine ⟨45870544115176492136722673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30580362743450994757815115 45870544115176492136722673)
                ·
                  refine ⟨34402908086382369102542005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45870544115176492136722673 34402908086382369102542005)
                  ·
                    refine ⟨3225272633098347103363313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34402908086382369102542005 3225272633098347103363313)
                    ·
                      refine ⟨2418954474823760327522485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225272633098347103363313 2418954474823760327522485)
                      ·
                        rfl

theorem cell23_4710897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_4710897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710897 prefixEnd_4710897 := by exact prefixLift 4710897
  have htrace : WordTrace (prefixWord ++ tailWord_4710897) baseStart_4710897 baseEnd_4710897 := by
    simpa [prefixWord, tailWord_4710897, baseEnd_4710897] using wordTrace_append hprefix tailTrace_4710897
  have hstable : (prefixWord ++ tailWord_4710897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710897).length < 2 ^ (prefixWord ++ tailWord_4710897).sum := by decide
  have hdescent : baseEnd_4710897 < baseStart_4710897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4710994 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_4710994 : Nat := 118140960795 + 4710994 * 2 ^ 59
def prefixEnd_4710994 : Nat := 4983230072969 + 3 ^ 40 * 4710994 * 2
def baseEnd_4710994 : Nat := 2419004282447246448009539

theorem tailTrace_4710994 : CollatzResearch.WordTrace tailWord_4710994 prefixEnd_4710994 2419004282447246448009539 := by
  unfold tailWord_4710994
  simp only [CollatzResearch.WordTrace]
  refine ⟨42956016773720196641231009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114549378063253857709949357 42956016773720196641231009)
  ·
    refine ⟨32217012580290147480923257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42956016773720196641231009 32217012580290147480923257)
    ·
      refine ⟨24162759435217610610692443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32217012580290147480923257 24162759435217610610692443)
      ·
        refine ⟨36244139152826415916038665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24162759435217610610692443 36244139152826415916038665)
        ·
          refine ⟨27183104364619811937028999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36244139152826415916038665 27183104364619811937028999)
          ·
            refine ⟨40774656546929717905543499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27183104364619811937028999 40774656546929717905543499)
            ·
              refine ⟨61161984820394576858315249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40774656546929717905543499 61161984820394576858315249)
              ·
                refine ⟨45871488615295932643736437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61161984820394576858315249 45871488615295932643736437)
                ·
                  refine ⟨4300452057683993685350291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45871488615295932643736437 4300452057683993685350291)
                  ·
                    refine ⟨6450678086525990528025437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4300452057683993685350291 6450678086525990528025437)
                    ·
                      refine ⟨2419004282447246448009539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6450678086525990528025437 2419004282447246448009539)
                      ·
                        rfl

theorem cell23_4710994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_4710994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4710994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4710994 prefixEnd_4710994 := by exact prefixLift 4710994
  have htrace : WordTrace (prefixWord ++ tailWord_4710994) baseStart_4710994 baseEnd_4710994 := by
    simpa [prefixWord, tailWord_4710994, baseEnd_4710994] using wordTrace_append hprefix tailTrace_4710994
  have hstable : (prefixWord ++ tailWord_4710994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4710994).length < 2 ^ (prefixWord ++ tailWord_4710994).sum := by decide
  have hdescent : baseEnd_4710994 < baseStart_4710994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4710994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711011 : List Nat := [1, 1, 1, 5, 1, 2, 1, 6, 1, 1, 3]
def baseStart_4711011 : Nat := 118140960795 + 4711011 * 2 ^ 59
def prefixEnd_4711011 : Nat := 4983230072969 + 3 ^ 40 * 4711011 * 2
def baseEnd_4711011 : Nat := 2419013011618372881496961

theorem tailTrace_4711011 : CollatzResearch.WordTrace tailWord_4711011 prefixEnd_4711011 2419013011618372881496961 := by
  unfold tailWord_4711011
  simp only [CollatzResearch.WordTrace]
  refine ⟨171824687135819198468292887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114549791423879465645528591 171824687135819198468292887)
  ·
    refine ⟨257737030703728797702439331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171824687135819198468292887 257737030703728797702439331)
    ·
      refine ⟨386605546055593196553658997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257737030703728797702439331 386605546055593196553658997)
      ·
        refine ⟨36244269942711862176905531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 386605546055593196553658997 36244269942711862176905531)
        ·
          refine ⟨54366404914067793265358297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36244269942711862176905531 54366404914067793265358297)
          ·
            refine ⟨40774803685550844949018723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54366404914067793265358297 40774803685550844949018723)
            ·
              refine ⟨61162205528326267423528085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40774803685550844949018723 61162205528326267423528085)
              ·
                refine ⟨2866978384140293785477879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61162205528326267423528085 2866978384140293785477879)
                ·
                  refine ⟨4300467576210440678216819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2866978384140293785477879 4300467576210440678216819)
                  ·
                    refine ⟨6450701364315661017325229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4300467576210440678216819 6450701364315661017325229)
                    ·
                      refine ⟨2419013011618372881496961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6450701364315661017325229 2419013011618372881496961)
                      ·
                        rfl

theorem cell23_4711011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_4711011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711011 prefixEnd_4711011 := by exact prefixLift 4711011
  have htrace : WordTrace (prefixWord ++ tailWord_4711011) baseStart_4711011 baseEnd_4711011 := by
    simpa [prefixWord, tailWord_4711011, baseEnd_4711011] using wordTrace_append hprefix tailTrace_4711011
  have hstable : (prefixWord ++ tailWord_4711011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711011).length < 2 ^ (prefixWord ++ tailWord_4711011).sum := by decide
  have hdescent : baseEnd_4711011 < baseStart_4711011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711044 : List Nat := [2, 3, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_4711044 : Nat := 118140960795 + 4711044 * 2 ^ 59
def prefixEnd_4711044 : Nat := 4983230072969 + 3 ^ 40 * 4711044 * 2
def baseEnd_4711044 : Nat := 806343318826657084128103

theorem tailTrace_4711044 : CollatzResearch.WordTrace tailWord_4711044 prefixEnd_4711044 806343318826657084128103 := by
  unfold tailWord_4711044
  simp only [CollatzResearch.WordTrace]
  refine ⟨85912945372349822552122093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114550593829799763402829457 85912945372349822552122093)
  ·
    refine ⟨32217354514631183457045785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85912945372349822552122093 32217354514631183457045785)
    ·
      refine ⟨24163015885973387592784339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32217354514631183457045785 24163015885973387592784339)
      ·
        refine ⟨36244523828960081389176509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24163015885973387592784339 36244523828960081389176509)
        ·
          refine ⟨13591696435860030520941191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36244523828960081389176509 13591696435860030520941191)
          ·
            refine ⟨20387544653790045781411787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13591696435860030520941191 20387544653790045781411787)
            ·
              refine ⟨30581316980685068672117681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20387544653790045781411787 30581316980685068672117681)
              ·
                refine ⟨22935987735513801504088261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30581316980685068672117681 22935987735513801504088261)
                ·
                  refine ⟨4300497700408837782016549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22935987735513801504088261 4300497700408837782016549)
                  ·
                    refine ⟨806343318826657084128103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4300497700408837782016549 806343318826657084128103)
                    ·
                      rfl

theorem cell23_4711044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_4711044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711044 prefixEnd_4711044 := by exact prefixLift 4711044
  have htrace : WordTrace (prefixWord ++ tailWord_4711044) baseStart_4711044 baseEnd_4711044 := by
    simpa [prefixWord, tailWord_4711044, baseEnd_4711044] using wordTrace_append hprefix tailTrace_4711044
  have hstable : (prefixWord ++ tailWord_4711044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711044).length < 2 ^ (prefixWord ++ tailWord_4711044).sum := by decide
  have hdescent : baseEnd_4711044 < baseStart_4711044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711047 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_4711047 : Nat := 118140960795 + 4711047 * 2 ^ 59
def prefixEnd_4711047 : Nat := 4983230072969 + 3 ^ 40 * 4711047 * 2
def baseEnd_4711047 : Nat := 2419031496921934740646795

theorem tailTrace_4711047 : CollatzResearch.WordTrace tailWord_4711047 prefixEnd_4711047 2419031496921934740646795 := by
  unfold tailWord_4711047
  simp only [CollatzResearch.WordTrace]
  refine ⟨171826000163688776616603395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114550666775792517744402263 171826000163688776616603395)
  ·
    refine ⟨257739000245533164924905093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171826000163688776616603395 257739000245533164924905093)
    ·
      refine ⟨48326062546037468423419705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257739000245533164924905093 48326062546037468423419705)
      ·
        refine ⟨36244546909528101317564779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48326062546037468423419705 36244546909528101317564779)
        ·
          refine ⟨54366820364292151976347169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36244546909528101317564779 54366820364292151976347169)
          ·
            refine ⟨40775115273219113982260377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54366820364292151976347169 40775115273219113982260377)
            ·
              refine ⟨30581336454914335486695283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40775115273219113982260377 30581336454914335486695283)
              ·
                refine ⟨45872004682371503230042925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30581336454914335486695283 45872004682371503230042925)
                ·
                  refine ⟨17202001755889313711266097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45872004682371503230042925 17202001755889313711266097)
                  ·
                    refine ⟨12901501316916985283449573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17202001755889313711266097 12901501316916985283449573)
                    ·
                      refine ⟨2419031496921934740646795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12901501316916985283449573 2419031496921934740646795)
                      ·
                        rfl

theorem cell23_4711047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_4711047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711047 prefixEnd_4711047 := by exact prefixLift 4711047
  have htrace : WordTrace (prefixWord ++ tailWord_4711047) baseStart_4711047 baseEnd_4711047 := by
    simpa [prefixWord, tailWord_4711047, baseEnd_4711047] using wordTrace_append hprefix tailTrace_4711047
  have hstable : (prefixWord ++ tailWord_4711047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711047).length < 2 ^ (prefixWord ++ tailWord_4711047).sum := by decide
  have hdescent : baseEnd_4711047 < baseStart_4711047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711054 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_4711054 : Nat := 118140960795 + 4711054 * 2 ^ 59
def prefixEnd_4711054 : Nat := 4983230072969 + 3 ^ 40 * 4711054 * 2
def baseEnd_4711054 : Nat := 2419035091286516213259263

theorem tailTrace_4711054 : CollatzResearch.WordTrace tailWord_4711054 prefixEnd_4711054 2419035091286516213259263 := by
  unfold tailWord_4711054
  simp only [CollatzResearch.WordTrace]
  refine ⟨21478281934332927101513527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114550836983108944541405477 21478281934332927101513527)
  ·
    refine ⟨32217422901499390652270291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21478281934332927101513527 32217422901499390652270291)
    ·
      refine ⟨48326134352249085978405437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32217422901499390652270291 48326134352249085978405437)
      ·
        refine ⟨18122300382093407241902039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48326134352249085978405437 18122300382093407241902039)
        ·
          refine ⟨27183450573140110862853059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18122300382093407241902039 27183450573140110862853059)
          ·
            refine ⟨40775175859710166294279589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27183450573140110862853059 40775175859710166294279589)
            ·
              refine ⟨7645345473695656180177423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40775175859710166294279589 7645345473695656180177423)
              ·
                refine ⟨11468018210543484270266135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7645345473695656180177423 11468018210543484270266135)
                ·
                  refine ⟨17202027315815226405399203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11468018210543484270266135 17202027315815226405399203)
                  ·
                    refine ⟨25803040973722839608098805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17202027315815226405399203 25803040973722839608098805)
                    ·
                      refine ⟨2419035091286516213259263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25803040973722839608098805 2419035091286516213259263)
                      ·
                        rfl

theorem cell23_4711054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_4711054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711054 prefixEnd_4711054 := by exact prefixLift 4711054
  have htrace : WordTrace (prefixWord ++ tailWord_4711054) baseStart_4711054 baseEnd_4711054 := by
    simpa [prefixWord, tailWord_4711054, baseEnd_4711054] using wordTrace_append hprefix tailTrace_4711054
  have hstable : (prefixWord ++ tailWord_4711054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711054).length < 2 ^ (prefixWord ++ tailWord_4711054).sum := by decide
  have hdescent : baseEnd_4711054 < baseStart_4711054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711068 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_4711068 : Nat := 118140960795 + 4711068 * 2 ^ 59
def prefixEnd_4711068 : Nat := 4983230072969 + 3 ^ 40 * 4711068 * 2
def baseEnd_4711068 : Nat := 2419042280015679158484199

theorem tailTrace_4711068 : CollatzResearch.WordTrace tailWord_4711068 prefixEnd_4711068 2419042280015679158484199 := by
  unfold tailWord_4711068
  simp only [CollatzResearch.WordTrace]
  refine ⟨85913383048306348601558929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114551177397741798135411905 85913383048306348601558929)
  ·
    refine ⟨64435037286229761451169197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85913383048306348601558929 64435037286229761451169197)
    ·
      refine ⟨24163138982336160544188449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64435037286229761451169197 24163138982336160544188449)
      ·
        refine ⟨18122354236752120408141337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24163138982336160544188449 18122354236752120408141337)
        ·
          refine ⟨13591765677564090306106003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18122354236752120408141337 13591765677564090306106003)
          ·
            refine ⟨20387648516346135459159005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13591765677564090306106003 20387648516346135459159005)
            ·
              refine ⟨7645368193629800797184627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20387648516346135459159005 7645368193629800797184627)
              ·
                refine ⟨11468052290444701195776941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7645368193629800797184627 11468052290444701195776941)
                ·
                  refine ⟨4300519608916762948416353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11468052290444701195776941 4300519608916762948416353)
                  ·
                    refine ⟨3225389706687572211312265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4300519608916762948416353 3225389706687572211312265)
                    ·
                      refine ⟨2419042280015679158484199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225389706687572211312265 2419042280015679158484199)
                      ·
                        rfl

theorem cell23_4711068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_4711068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711068 prefixEnd_4711068 := by exact prefixLift 4711068
  have htrace : WordTrace (prefixWord ++ tailWord_4711068) baseStart_4711068 baseEnd_4711068 := by
    simpa [prefixWord, tailWord_4711068, baseEnd_4711068] using wordTrace_append hprefix tailTrace_4711068
  have hstable : (prefixWord ++ tailWord_4711068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711068).length < 2 ^ (prefixWord ++ tailWord_4711068).sum := by decide
  have hdescent : baseEnd_4711068 < baseStart_4711068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711105 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4711105 : Nat := 118140960795 + 4711105 * 2 ^ 59
def prefixEnd_4711105 : Nat := 4983230072969 + 3 ^ 40 * 4711105 * 2
def baseEnd_4711105 : Nat := 2419061278799895513721529

theorem tailTrace_4711105 : CollatzResearch.WordTrace tailWord_4711105 prefixEnd_4711105 2419061278799895513721529 := by
  unfold tailWord_4711105
  simp only [CollatzResearch.WordTrace]
  refine ⟨171828115597478652522214769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114552077064985768348143179 171828115597478652522214769)
  ·
    refine ⟨128871086698108989391661077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171828115597478652522214769 128871086698108989391661077)
    ·
      refine ⟨6040832188973858877734113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 128871086698108989391661077 6040832188973858877734113)
      ·
        refine ⟨4530624141730394158300585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6040832188973858877734113 4530624141730394158300585)
        ·
          refine ⟨3397968106297795618725439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4530624141730394158300585 3397968106297795618725439)
          ·
            refine ⟨5096952159446693428088159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3397968106297795618725439 5096952159446693428088159)
            ·
              refine ⟨7645428239170040142132239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5096952159446693428088159 7645428239170040142132239)
              ·
                refine ⟨11468142358755060213198359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7645428239170040142132239 11468142358755060213198359)
                ·
                  refine ⟨17202213538132590319797539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11468142358755060213198359 17202213538132590319797539)
                  ·
                    refine ⟨25803320307198885479696309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17202213538132590319797539 25803320307198885479696309)
                    ·
                      refine ⟨2419061278799895513721529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25803320307198885479696309 2419061278799895513721529)
                      ·
                        rfl

theorem cell23_4711105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4711105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711105 prefixEnd_4711105 := by exact prefixLift 4711105
  have htrace : WordTrace (prefixWord ++ tailWord_4711105) baseStart_4711105 baseEnd_4711105 := by
    simpa [prefixWord, tailWord_4711105, baseEnd_4711105] using wordTrace_append hprefix tailTrace_4711105
  have hstable : (prefixWord ++ tailWord_4711105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711105).length < 2 ^ (prefixWord ++ tailWord_4711105).sum := by decide
  have hdescent : baseEnd_4711105 < baseStart_4711105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711118 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_4711118 : Nat := 118140960795 + 4711118 * 2 ^ 59
def prefixEnd_4711118 : Nat := 4983230072969 + 3 ^ 40 * 4711118 * 2
def baseEnd_4711118 : Nat := 2419067954048403962858969

theorem tailTrace_4711118 : CollatzResearch.WordTrace tailWord_4711118 prefixEnd_4711118 2419067954048403962858969 := by
  unfold tailWord_4711118
  simp only [CollatzResearch.WordTrace]
  refine ⟨21478573718303944467804751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114552393164287703828292005 21478573718303944467804751)
  ·
    refine ⟨32217860577455916701707127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21478573718303944467804751 32217860577455916701707127)
    ·
      refine ⟨48326790866183875052560691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32217860577455916701707127 48326790866183875052560691)
      ·
        refine ⟨72490186299275812578841037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48326790866183875052560691 72490186299275812578841037)
        ·
          refine ⟨27183819862228429717065389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72490186299275812578841037 27183819862228429717065389)
          ·
            refine ⟨10193932448335661143899521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27183819862228429717065389 10193932448335661143899521)
            ·
              refine ⟨7645449336251745857924641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10193932448335661143899521 7645449336251745857924641)
              ·
                refine ⟨5734087002188809393443481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7645449336251745857924641 5734087002188809393443481)
                ·
                  refine ⟨4300565251641607045082611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5734087002188809393443481 4300565251641607045082611)
                  ·
                    refine ⟨6450847877462410567623917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4300565251641607045082611 6450847877462410567623917)
                    ·
                      refine ⟨2419067954048403962858969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6450847877462410567623917 2419067954048403962858969)
                      ·
                        rfl

theorem cell23_4711118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_4711118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711118 prefixEnd_4711118 := by exact prefixLift 4711118
  have htrace : WordTrace (prefixWord ++ tailWord_4711118) baseStart_4711118 baseEnd_4711118 := by
    simpa [prefixWord, tailWord_4711118, baseEnd_4711118] using wordTrace_append hprefix tailTrace_4711118
  have hstable : (prefixWord ++ tailWord_4711118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711118).length < 2 ^ (prefixWord ++ tailWord_4711118).sum := by decide
  have hdescent : baseEnd_4711118 < baseStart_4711118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711141 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 1, 4, 2]
def baseStart_4711141 : Nat := 118140960795 + 4711141 * 2 ^ 59
def prefixEnd_4711141 : Nat := 4983230072969 + 3 ^ 40 * 4711141 * 2
def baseEnd_4711141 : Nat := 2419079764103457372871363

theorem tailTrace_4711141 : CollatzResearch.WordTrace tailWord_4711141 prefixEnd_4711141 2419079764103457372871363 := by
  unfold tailWord_4711141
  simp only [CollatzResearch.WordTrace]
  refine ⟨171829428625348230670525277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114552952416898820447016851 171829428625348230670525277)
  ·
    refine ⟨64436035734505586501446979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171829428625348230670525277 64436035734505586501446979)
    ·
      refine ⟨96654053601758379752170469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64436035734505586501446979 96654053601758379752170469)
      ·
        refine ⟨18122635050329696203531963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96654053601758379752170469 18122635050329696203531963)
        ·
          refine ⟨27183952575494544305297945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18122635050329696203531963 27183952575494544305297945)
          ·
            refine ⟨20387964431620908228973459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27183952575494544305297945 20387964431620908228973459)
            ·
              refine ⟨30581946647431362343460189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20387964431620908228973459 30581946647431362343460189)
              ·
                refine ⟨11468229992786760878797571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30581946647431362343460189 11468229992786760878797571)
                ·
                  refine ⟨17202344989180141318196357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11468229992786760878797571 17202344989180141318196357)
                  ·
                    refine ⟨3225439685471276497161817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17202344989180141318196357 3225439685471276497161817)
                    ·
                      refine ⟨2419079764103457372871363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225439685471276497161817 2419079764103457372871363)
                      ·
                        rfl

theorem cell23_4711141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_4711141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711141 prefixEnd_4711141 := by exact prefixLift 4711141
  have htrace : WordTrace (prefixWord ++ tailWord_4711141) baseStart_4711141 baseEnd_4711141 := by
    simpa [prefixWord, tailWord_4711141, baseEnd_4711141] using wordTrace_append hprefix tailTrace_4711141
  have hstable : (prefixWord ++ tailWord_4711141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711141).length < 2 ^ (prefixWord ++ tailWord_4711141).sum := by decide
  have hdescent : baseEnd_4711141 < baseStart_4711141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711158 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_4711158 : Nat := 118140960795 + 4711158 * 2 ^ 59
def prefixEnd_4711158 : Nat := 4983230072969 + 3 ^ 40 * 4711158 * 2
def baseEnd_4711158 : Nat := 2419088493274583806358785

theorem tailTrace_4711158 : CollatzResearch.WordTrace tailWord_4711158 prefixEnd_4711158 2419088493274583806358785 := by
  unfold tailWord_4711158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10739378041642915160868383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114553365777524428382596085 10739378041642915160868383)
  ·
    refine ⟨16109067062464372741302575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10739378041642915160868383 16109067062464372741302575)
    ·
      refine ⟨24163600593696559111953863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16109067062464372741302575 24163600593696559111953863)
      ·
        refine ⟨36245400890544838667930795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24163600593696559111953863 36245400890544838667930795)
        ·
          refine ⟨54368101335817258001896193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36245400890544838667930795 54368101335817258001896193)
          ·
            refine ⟨40776076001862943501422145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54368101335817258001896193 40776076001862943501422145)
            ·
              refine ⟨30582057001397207626066609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40776076001862943501422145 30582057001397207626066609)
              ·
                refine ⟨22936542751047905719549957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30582057001397207626066609 22936542751047905719549957)
                ·
                  refine ⟨4300601765821482322415617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22936542751047905719549957 4300601765821482322415617)
                  ·
                    refine ⟨3225451324366111741811713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4300601765821482322415617 3225451324366111741811713)
                    ·
                      refine ⟨2419088493274583806358785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225451324366111741811713 2419088493274583806358785)
                      ·
                        rfl

theorem cell23_4711158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_4711158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711158 prefixEnd_4711158 := by exact prefixLift 4711158
  have htrace : WordTrace (prefixWord ++ tailWord_4711158) baseStart_4711158 baseEnd_4711158 := by
    simpa [prefixWord, tailWord_4711158, baseEnd_4711158] using wordTrace_append hprefix tailTrace_4711158
  have hstable : (prefixWord ++ tailWord_4711158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711158).length < 2 ^ (prefixWord ++ tailWord_4711158).sum := by decide
  have hdescent : baseEnd_4711158 < baseStart_4711158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711175 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 2, 2, 2]
def baseStart_4711175 : Nat := 118140960795 + 4711175 * 2 ^ 59
def prefixEnd_4711175 : Nat := 4983230072969 + 3 ^ 40 * 4711175 * 2
def baseEnd_4711175 : Nat := 2419097222445710239846207

theorem tailTrace_4711175 : CollatzResearch.WordTrace tailWord_4711175 prefixEnd_4711175 2419097222445710239846207 := by
  unfold tailWord_4711175
  simp only [CollatzResearch.WordTrace]
  refine ⟨171830668707225054477262979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114553779138150036318175319 171830668707225054477262979)
  ·
    refine ⟨257746003060837581715894469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171830668707225054477262979 257746003060837581715894469)
    ·
      refine ⟨48327375573907046571730213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257746003060837581715894469 48327375573907046571730213)
      ·
        refine ⟨9061382920107571232199415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48327375573907046571730213 9061382920107571232199415)
        ·
          refine ⟨13592074380161356848299123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9061382920107571232199415 13592074380161356848299123)
          ·
            refine ⟨20388111570242035272448685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13592074380161356848299123 20388111570242035272448685)
            ·
              refine ⟨7645541838840763227168257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20388111570242035272448685 7645541838840763227168257)
              ·
                refine ⟨5734156379130572420376193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7645541838840763227168257 5734156379130572420376193)
                ·
                  refine ⟨4300617284347929315282145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5734156379130572420376193 4300617284347929315282145)
                  ·
                    refine ⟨3225462963260946986461609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4300617284347929315282145 3225462963260946986461609)
                    ·
                      refine ⟨2419097222445710239846207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225462963260946986461609 2419097222445710239846207)
                      ·
                        rfl

theorem cell23_4711175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_4711175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711175 prefixEnd_4711175 := by exact prefixLift 4711175
  have htrace : WordTrace (prefixWord ++ tailWord_4711175) baseStart_4711175 baseEnd_4711175 := by
    simpa [prefixWord, tailWord_4711175, baseEnd_4711175] using wordTrace_append hprefix tailTrace_4711175
  have hstable : (prefixWord ++ tailWord_4711175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711175).length < 2 ^ (prefixWord ++ tailWord_4711175).sum := by decide
  have hdescent : baseEnd_4711175 < baseStart_4711175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711187 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 7]
def baseStart_4711187 : Nat := 118140960795 + 4711187 * 2 ^ 59
def prefixEnd_4711187 : Nat := 4983230072969 + 3 ^ 40 * 4711187 * 2
def baseEnd_4711187 : Nat := 2419103384213564192896151

theorem tailTrace_4711187 : CollatzResearch.WordTrace tailWord_4711187 prefixEnd_4711187 2419103384213564192896151 := by
  unfold tailWord_4711187
  simp only [CollatzResearch.WordTrace]
  refine ⟨171831106383181580526699815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114554070922121053684466543 171831106383181580526699815)
  ·
    refine ⟨257746659574772370790049723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171831106383181580526699815 257746659574772370790049723)
    ·
      refine ⟨386619989362158556185074585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257746659574772370790049723 386619989362158556185074585)
      ·
        refine ⟨289964992021618917138805939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386619989362158556185074585 289964992021618917138805939)
        ·
          refine ⟨434947488032428375708208909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289964992021618917138805939 434947488032428375708208909)
          ·
            refine ⟨163105308012160640890578341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 434947488032428375708208909 163105308012160640890578341)
            ·
              refine ⟨30582245252280120166983439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163105308012160640890578341 30582245252280120166983439)
              ·
                refine ⟨45873367878420180250475159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30582245252280120166983439 45873367878420180250475159)
                ·
                  refine ⟨68810051817630270375712739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45873367878420180250475159 68810051817630270375712739)
                  ·
                    refine ⟨103215077726445405563569109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68810051817630270375712739 103215077726445405563569109)
                    ·
                      refine ⟨2419103384213564192896151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103215077726445405563569109 2419103384213564192896151)
                      ·
                        rfl

theorem cell23_4711187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_4711187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711187 prefixEnd_4711187 := by exact prefixLift 4711187
  have htrace : WordTrace (prefixWord ++ tailWord_4711187) baseStart_4711187 baseEnd_4711187 := by
    simpa [prefixWord, tailWord_4711187, baseEnd_4711187] using wordTrace_append hprefix tailTrace_4711187
  have hstable : (prefixWord ++ tailWord_4711187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711187).length < 2 ^ (prefixWord ++ tailWord_4711187).sum := by decide
  have hdescent : baseEnd_4711187 < baseStart_4711187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711231 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 4]
def baseStart_4711231 : Nat := 118140960795 + 4711231 * 2 ^ 59
def prefixEnd_4711231 : Nat := 4983230072969 + 3 ^ 40 * 4711231 * 2
def baseEnd_4711231 : Nat := 2419125977362362020745949

theorem tailTrace_4711231 : CollatzResearch.WordTrace tailWord_4711231 prefixEnd_4711231 2419125977362362020745949 := by
  unfold tailWord_4711231
  simp only [CollatzResearch.WordTrace]
  refine ⟨171832711195022176041301547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114555140796681450694201031 171832711195022176041301547)
  ·
    refine ⟨257749066792533264061952321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171832711195022176041301547 257749066792533264061952321)
    ·
      refine ⟨193311800094399948046464241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257749066792533264061952321 193311800094399948046464241)
      ·
        refine ⟨144983850070799961034848181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193311800094399948046464241 144983850070799961034848181)
        ·
          refine ⟨13592235944137496347017017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 144983850070799961034848181 13592235944137496347017017)
          ·
            refine ⟨10194176958103122260262763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13592235944137496347017017 10194176958103122260262763)
            ·
              refine ⟨15291265437154683390394145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10194176958103122260262763 15291265437154683390394145)
              ·
                refine ⟨11468449077866012542795609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15291265437154683390394145 11468449077866012542795609)
                ·
                  refine ⟨8601336808399509407096707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11468449077866012542795609 8601336808399509407096707)
                  ·
                    refine ⟨12902005212599264110645061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8601336808399509407096707 12902005212599264110645061)
                    ·
                      refine ⟨2419125977362362020745949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12902005212599264110645061 2419125977362362020745949)
                      ·
                        rfl

theorem cell23_4711231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_4711231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711231 prefixEnd_4711231 := by exact prefixLift 4711231
  have htrace : WordTrace (prefixWord ++ tailWord_4711231) baseStart_4711231 baseEnd_4711231 := by
    simpa [prefixWord, tailWord_4711231, baseEnd_4711231] using wordTrace_append hprefix tailTrace_4711231
  have hstable : (prefixWord ++ tailWord_4711231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711231).length < 2 ^ (prefixWord ++ tailWord_4711231).sum := by decide
  have hdescent : baseEnd_4711231 < baseStart_4711231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711241 : List Nat := [1, 2, 1, 1, 2, 5, 3, 1, 3, 4]
def baseStart_4711241 : Nat := 118140960795 + 4711241 * 2 ^ 59
def prefixEnd_4711241 : Nat := 4983230072969 + 3 ^ 40 * 4711241 * 2
def baseEnd_4711241 : Nat := 806377037389635660540301

theorem tailTrace_4711241 : CollatzResearch.WordTrace tailWord_4711241 prefixEnd_4711241 806377037389635660540301 := by
  unfold tailWord_4711241
  simp only [CollatzResearch.WordTrace]
  refine ⟨171833075924985947749165577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114555383949990631832777051 171833075924985947749165577)
  ·
    refine ⟨128874806943739460811874183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171833075924985947749165577 128874806943739460811874183)
    ·
      refine ⟨193312210415609191217811275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128874806943739460811874183 193312210415609191217811275)
      ·
        refine ⟨289968315623413786826716913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193312210415609191217811275 289968315623413786826716913)
        ·
          refine ⟨217476236717560340120037685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289968315623413786826716913 217476236717560340120037685)
          ·
            refine ⟨20388397192271281886253533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 217476236717560340120037685 20388397192271281886253533)
            ·
              refine ⟨7645648947101730707345075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20388397192271281886253533 7645648947101730707345075)
              ·
                refine ⟨11468473420652596061017613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7645648947101730707345075 11468473420652596061017613)
                ·
                  refine ⟨4300677532744723522881605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11468473420652596061017613 4300677532744723522881605)
                  ·
                    refine ⟨806377037389635660540301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4300677532744723522881605 806377037389635660540301)
                    ·
                      rfl

theorem cell23_4711241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 4].length) (baseStart_4711241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711241 prefixEnd_4711241 := by exact prefixLift 4711241
  have htrace : WordTrace (prefixWord ++ tailWord_4711241) baseStart_4711241 baseEnd_4711241 := by
    simpa [prefixWord, tailWord_4711241, baseEnd_4711241] using wordTrace_append hprefix tailTrace_4711241
  have hstable : (prefixWord ++ tailWord_4711241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711241).length < 2 ^ (prefixWord ++ tailWord_4711241).sum := by decide
  have hdescent : baseEnd_4711241 < baseStart_4711241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711268 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_4711268 : Nat := 118140960795 + 4711268 * 2 ^ 59
def prefixEnd_4711268 : Nat := 4983230072969 + 3 ^ 40 * 4711268 * 2
def baseEnd_4711268 : Nat := 2419144976146578375983279

theorem tailTrace_4711268 : CollatzResearch.WordTrace tailWord_4711268 prefixEnd_4711268 2419144976146578375983279 := by
  unfold tailWord_4711268
  simp only [CollatzResearch.WordTrace]
  refine ⟨85917030347944065680199229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114556040463925420906932305 85917030347944065680199229)
  ·
    refine ⟨32218886380479024630074711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85917030347944065680199229 32218886380479024630074711)
    ·
      refine ⟨48328329570718536945112067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32218886380479024630074711 48328329570718536945112067)
      ·
        refine ⟨72492494356077805417668101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48328329570718536945112067 72492494356077805417668101)
        ·
          refine ⟨13592342691764588515812769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72492494356077805417668101 13592342691764588515812769)
          ·
            refine ⟨10194257018823441386859577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13592342691764588515812769 10194257018823441386859577)
            ·
              refine ⟨7645692764117581040144683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10194257018823441386859577 7645692764117581040144683)
              ·
                refine ⟨11468539146176371560217025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7645692764117581040144683 11468539146176371560217025)
                ·
                  refine ⟨8601404359632278670162769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11468539146176371560217025 8601404359632278670162769)
                  ·
                    refine ⟨6451053269724209002622077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8601404359632278670162769 6451053269724209002622077)
                    ·
                      refine ⟨2419144976146578375983279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6451053269724209002622077 2419144976146578375983279)
                      ·
                        rfl

theorem cell23_4711268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_4711268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711268 prefixEnd_4711268 := by exact prefixLift 4711268
  have htrace : WordTrace (prefixWord ++ tailWord_4711268) baseStart_4711268 baseEnd_4711268 := by
    simpa [prefixWord, tailWord_4711268, baseEnd_4711268] using wordTrace_append hprefix tailTrace_4711268
  have hstable : (prefixWord ++ tailWord_4711268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711268).length < 2 ^ (prefixWord ++ tailWord_4711268).sum := by decide
  have hdescent : baseEnd_4711268 < baseStart_4711268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711321 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 4]
def baseStart_4711321 : Nat := 118140960795 + 4711321 * 2 ^ 59
def prefixEnd_4711321 : Nat := 4983230072969 + 3 ^ 40 * 4711321 * 2
def baseEnd_4711321 : Nat := 2419172190621266668620535

theorem tailTrace_4711321 : CollatzResearch.WordTrace tailWord_4711321 prefixEnd_4711321 2419172190621266668620535 := by
  unfold tailWord_4711321
  simp only [CollatzResearch.WordTrace]
  refine ⟨171835993764696121412077817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114557329176464080941385211 171835993764696121412077817)
  ·
    refine ⟨128876995323522091059058363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171835993764696121412077817 128876995323522091059058363)
    ·
      refine ⟨193315492985283136588587545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128876995323522091059058363 193315492985283136588587545)
      ·
        refine ⟨144986619738962352441440659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193315492985283136588587545 144986619738962352441440659)
        ·
          refine ⟨217479929608443528662160989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144986619738962352441440659 217479929608443528662160989)
          ·
            refine ⟨81554973603166323248310371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217479929608443528662160989 81554973603166323248310371)
            ·
              refine ⟨122332460404749484872465557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81554973603166323248310371 122332460404749484872465557)
              ·
                refine ⟨5734334081472632103396823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122332460404749484872465557 5734334081472632103396823)
                ·
                  refine ⟨8601501122208948155095235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5734334081472632103396823 8601501122208948155095235)
                  ·
                    refine ⟨12902251683313422232642853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8601501122208948155095235 12902251683313422232642853)
                    ·
                      refine ⟨2419172190621266668620535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12902251683313422232642853 2419172190621266668620535)
                      ·
                        rfl

theorem cell23_4711321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_4711321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711321 prefixEnd_4711321 := by exact prefixLift 4711321
  have htrace : WordTrace (prefixWord ++ tailWord_4711321) baseStart_4711321 baseEnd_4711321 := by
    simpa [prefixWord, tailWord_4711321, baseEnd_4711321] using wordTrace_append hprefix tailTrace_4711321
  have hstable : (prefixWord ++ tailWord_4711321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711321).length < 2 ^ (prefixWord ++ tailWord_4711321).sum := by decide
  have hdescent : baseEnd_4711321 < baseStart_4711321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711378 : List Nat := [3, 2, 2, 3, 1, 1, 4, 7]
def baseStart_4711378 : Nat := 118140960795 + 4711378 * 2 ^ 59
def prefixEnd_4711378 : Nat := 4983230072969 + 3 ^ 40 * 4711378 * 2
def baseEnd_4711378 : Nat := 89600054037724923911399

theorem tailTrace_4711378 : CollatzResearch.WordTrace tailWord_4711378 prefixEnd_4711378 89600054037724923911399 := by
  unfold tailWord_4711378
  simp only [CollatzResearch.WordTrace]
  refine ⟨42959518181372405036725697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114558715150326413431268525 42959518181372405036725697)
  ·
    refine ⟨32219638636029303777544273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42959518181372405036725697 32219638636029303777544273)
    ·
      refine ⟨24164728977021977833158205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32219638636029303777544273 24164728977021977833158205)
      ·
        refine ⟨9061773366383241687434327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24164728977021977833158205 9061773366383241687434327)
        ·
          refine ⟨13592660049574862531151491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9061773366383241687434327 13592660049574862531151491)
          ·
            refine ⟨20388990074362293796727237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13592660049574862531151491 20388990074362293796727237)
            ·
              refine ⟨3822935638942930086886357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20388990074362293796727237 3822935638942930086886357)
              ·
                refine ⟨89600054037724923911399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3822935638942930086886357 89600054037724923911399)
                ·
                  rfl

theorem cell23_4711378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 7].length) (baseStart_4711378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711378 prefixEnd_4711378 := by exact prefixLift 4711378
  have htrace : WordTrace (prefixWord ++ tailWord_4711378) baseStart_4711378 baseEnd_4711378 := by
    simpa [prefixWord, tailWord_4711378, baseEnd_4711378] using wordTrace_append hprefix tailTrace_4711378
  have hstable : (prefixWord ++ tailWord_4711378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711378).length < 2 ^ (prefixWord ++ tailWord_4711378).sum := by decide
  have hdescent : baseEnd_4711378 < baseStart_4711378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711389 : List Nat := [1, 4, 3, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_4711389 : Nat := 118140960795 + 4711389 * 2 ^ 59
def prefixEnd_4711389 : Nat := 4983230072969 + 3 ^ 40 * 4711389 * 2
def baseEnd_4711389 : Nat := 2419207107305772402570223

theorem tailTrace_4711389 : CollatzResearch.WordTrace tailWord_4711389 prefixEnd_4711389 2419207107305772402570223 := by
  unfold tailWord_4711389
  simp only [CollatzResearch.WordTrace]
  refine ⟨171838473928449769025553221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114558982618966512683702147 171838473928449769025553221)
  ·
    refine ⟨32219713861584331692291229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171838473928449769025553221 32219713861584331692291229)
    ·
      refine ⟨12082392698094124384609211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32219713861584331692291229 12082392698094124384609211)
      ·
        refine ⟨18123589047141186576913817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12082392698094124384609211 18123589047141186576913817)
        ·
          refine ⟨13592691785355889932685363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18123589047141186576913817 13592691785355889932685363)
          ·
            refine ⟨20389037678033834899028045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13592691785355889932685363 20389037678033834899028045)
            ·
              refine ⟨7645889129262688087135517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20389037678033834899028045 7645889129262688087135517)
              ·
                refine ⟨2867208423473508032675819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7645889129262688087135517 2867208423473508032675819)
                ·
                  refine ⟨4300812635210262049013729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867208423473508032675819 4300812635210262049013729)
                  ·
                    refine ⟨3225609476407696536760297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4300812635210262049013729 3225609476407696536760297)
                    ·
                      refine ⟨2419207107305772402570223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225609476407696536760297 2419207107305772402570223)
                      ·
                        rfl

theorem cell23_4711389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_4711389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711389 prefixEnd_4711389 := by exact prefixLift 4711389
  have htrace : WordTrace (prefixWord ++ tailWord_4711389) baseStart_4711389 baseEnd_4711389 := by
    simpa [prefixWord, tailWord_4711389, baseEnd_4711389] using wordTrace_append hprefix tailTrace_4711389
  have hstable : (prefixWord ++ tailWord_4711389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711389).length < 2 ^ (prefixWord ++ tailWord_4711389).sum := by decide
  have hdescent : baseEnd_4711389 < baseStart_4711389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711406 : List Nat := [4, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_4711406 : Nat := 118140960795 + 4711406 * 2 ^ 59
def prefixEnd_4711406 : Nat := 4983230072969 + 3 ^ 40 * 4711406 * 2
def baseEnd_4711406 : Nat := 2419215836476898836057645

theorem tailTrace_4711406 : CollatzResearch.WordTrace tailWord_4711406 prefixEnd_4711406 2419215836476898836057645 := by
  unfold tailWord_4711406
  simp only [CollatzResearch.WordTrace]
  refine ⟨21479886746173522616115259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114559395979592120619281381 21479886746173522616115259)
  ·
    refine ⟨32219830119260283924172889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21479886746173522616115259 32219830119260283924172889)
    ·
      refine ⟨24164872589445212943129667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32219830119260283924172889 24164872589445212943129667)
      ·
        refine ⟨36247308884167819414694501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24164872589445212943129667 36247308884167819414694501)
        ·
          refine ⟨6796370415781466140255219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36247308884167819414694501 6796370415781466140255219)
          ·
            refine ⟨10194555623672199210382829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6796370415781466140255219 10194555623672199210382829)
            ·
              refine ⟨3822958358877074703893561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10194555623672199210382829 3822958358877074703893561)
              ·
                refine ⟨2867218769157806027920171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3822958358877074703893561 2867218769157806027920171)
                ·
                  refine ⟨4300828153736709041880257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867218769157806027920171 4300828153736709041880257)
                  ·
                    refine ⟨3225621115302531781410193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4300828153736709041880257 3225621115302531781410193)
                    ·
                      refine ⟨2419215836476898836057645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225621115302531781410193 2419215836476898836057645)
                      ·
                        rfl

theorem cell23_4711406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_4711406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711406 prefixEnd_4711406 := by exact prefixLift 4711406
  have htrace : WordTrace (prefixWord ++ tailWord_4711406) baseStart_4711406 baseEnd_4711406 := by
    simpa [prefixWord, tailWord_4711406, baseEnd_4711406] using wordTrace_append hprefix tailTrace_4711406
  have hstable : (prefixWord ++ tailWord_4711406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711406).length < 2 ^ (prefixWord ++ tailWord_4711406).sum := by decide
  have hdescent : baseEnd_4711406 < baseStart_4711406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711426 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4711426 : Nat := 118140960795 + 4711426 * 2 ^ 59
def prefixEnd_4711426 : Nat := 4983230072969 + 3 ^ 40 * 4711426 * 2
def baseEnd_4711426 : Nat := 2419226106089988757807553

theorem tailTrace_4711426 : CollatzResearch.WordTrace tailWord_4711426 prefixEnd_4711426 2419226106089988757807553 := by
  unfold tailWord_4711426
  simp only [CollatzResearch.WordTrace]
  refine ⟨42959955857328931086162533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114559882286210482896433421 42959955857328931086162533)
  ·
    refine ⟨8054991723249174578655475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42959955857328931086162533 8054991723249174578655475)
    ·
      refine ⟨12082487584873761867983213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8054991723249174578655475 12082487584873761867983213)
      ·
        refine ⟨4530932844327660700493705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12082487584873761867983213 4530932844327660700493705)
        ·
          refine ⟨3398199633245745525370279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4530932844327660700493705 3398199633245745525370279)
          ·
            refine ⟨5097299449868618288055419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3398199633245745525370279 5097299449868618288055419)
            ·
              refine ⟨7645949174802927432083129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5097299449868618288055419 7645949174802927432083129)
              ·
                refine ⟨5734461881102195574062347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7645949174802927432083129 5734461881102195574062347)
                ·
                  refine ⟨8601692821653293361093521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5734461881102195574062347 8601692821653293361093521)
                  ·
                    refine ⟨6451269616239970020820141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8601692821653293361093521 6451269616239970020820141)
                    ·
                      refine ⟨2419226106089988757807553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6451269616239970020820141 2419226106089988757807553)
                      ·
                        rfl

theorem cell23_4711426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4711426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711426 prefixEnd_4711426 := by exact prefixLift 4711426
  have htrace : WordTrace (prefixWord ++ tailWord_4711426) baseStart_4711426 baseEnd_4711426 := by
    simpa [prefixWord, tailWord_4711426, baseEnd_4711426] using wordTrace_append hprefix tailTrace_4711426
  have hstable : (prefixWord ++ tailWord_4711426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711426).length < 2 ^ (prefixWord ++ tailWord_4711426).sum := by decide
  have hdescent : baseEnd_4711426 < baseStart_4711426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711431 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4711431 : Nat := 118140960795 + 4711431 * 2 ^ 59
def prefixEnd_4711431 : Nat := 4983230072969 + 3 ^ 40 * 4711431 * 2
def baseEnd_4711431 : Nat := 2419228673493261238245029

theorem tailTrace_4711431 : CollatzResearch.WordTrace tailWord_4711431 prefixEnd_4711431 2419228673493261238245029 := by
  unfold tailWord_4711431
  simp only [CollatzResearch.WordTrace]
  refine ⟨171840005794297610198582147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114560003862865073465721431 171840005794297610198582147)
  ·
    refine ⟨257760008691446415297873221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171840005794297610198582147 257760008691446415297873221)
    ·
      refine ⟨48330001629646202868351229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257760008691446415297873221 48330001629646202868351229)
      ·
        refine ⟨18123750611117326075631711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48330001629646202868351229 18123750611117326075631711)
        ·
          refine ⟨27185625916675989113447567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18123750611117326075631711 27185625916675989113447567)
          ·
            refine ⟨40778438875013983670171351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27185625916675989113447567 40778438875013983670171351)
            ·
              refine ⟨61167658312520975505257027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40778438875013983670171351 61167658312520975505257027)
              ·
                refine ⟨91751487468781463257885541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61167658312520975505257027 91751487468781463257885541)
                ·
                  refine ⟨17203403900396524360853539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91751487468781463257885541 17203403900396524360853539)
                  ·
                    refine ⟨25805105850594786541280309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17203403900396524360853539 25805105850594786541280309)
                    ·
                      refine ⟨2419228673493261238245029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25805105850594786541280309 2419228673493261238245029)
                      ·
                        rfl

theorem cell23_4711431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4711431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711431 prefixEnd_4711431 := by exact prefixLift 4711431
  have htrace : WordTrace (prefixWord ++ tailWord_4711431) baseStart_4711431 baseEnd_4711431 := by
    simpa [prefixWord, tailWord_4711431, baseEnd_4711431] using wordTrace_append hprefix tailTrace_4711431
  have hstable : (prefixWord ++ tailWord_4711431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711431).length < 2 ^ (prefixWord ++ tailWord_4711431).sum := by decide
  have hdescent : baseEnd_4711431 < baseStart_4711431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711432 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 1, 3, 2]
def baseStart_4711432 : Nat := 118140960795 + 4711432 * 2 ^ 59
def prefixEnd_4711432 : Nat := 4983230072969 + 3 ^ 40 * 4711432 * 2
def baseEnd_4711432 : Nat := 2419229186973915734332525

theorem tailTrace_4711432 : CollatzResearch.WordTrace tailWord_4711432 prefixEnd_4711432 2419229186973915734332525 := by
  unfold tailWord_4711432
  simp only [CollatzResearch.WordTrace]
  refine ⟨85920021133646993684684275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114560028178195991579579033 85920021133646993684684275)
  ·
    refine ⟨128880031700470490527026413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85920021133646993684684275 128880031700470490527026413)
    ·
      refine ⟨48330011887676433947634905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128880031700470490527026413 48330011887676433947634905)
      ·
        refine ⟨36247508915757325460726179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48330011887676433947634905 36247508915757325460726179)
        ·
          refine ⟨54371263373635988191089269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36247508915757325460726179 54371263373635988191089269)
          ·
            refine ⟨5097305941278373892914619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54371263373635988191089269 5097305941278373892914619)
            ·
              refine ⟨7645958911917560839371929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5097305941278373892914619 7645958911917560839371929)
              ·
                refine ⟨5734469183938170629528947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7645958911917560839371929 5734469183938170629528947)
                ·
                  refine ⟨8601703775907255944293421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5734469183938170629528947 8601703775907255944293421)
                  ·
                    refine ⟨3225638915965220979110033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8601703775907255944293421 3225638915965220979110033)
                    ·
                      refine ⟨2419229186973915734332525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225638915965220979110033 2419229186973915734332525)
                      ·
                        rfl

theorem cell23_4711432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_4711432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711432 prefixEnd_4711432 := by exact prefixLift 4711432
  have htrace : WordTrace (prefixWord ++ tailWord_4711432) baseStart_4711432 baseEnd_4711432 := by
    simpa [prefixWord, tailWord_4711432, baseEnd_4711432] using wordTrace_append hprefix tailTrace_4711432
  have hstable : (prefixWord ++ tailWord_4711432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711432).length < 2 ^ (prefixWord ++ tailWord_4711432).sum := by decide
  have hdescent : baseEnd_4711432 < baseStart_4711432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711445 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 1, 4, 2]
def baseStart_4711445 : Nat := 118140960795 + 4711445 * 2 ^ 59
def prefixEnd_4711445 : Nat := 4983230072969 + 3 ^ 40 * 4711445 * 2
def baseEnd_4711445 : Nat := 2419235862222424183469965

theorem tailTrace_4711445 : CollatzResearch.WordTrace tailWord_4711445 prefixEnd_4711445 2419235862222424183469965 := by
  unfold tailWord_4711445
  simp only [CollatzResearch.WordTrace]
  refine ⟨171840516416246890589591789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114560344277497927059727859 171840516416246890589591789)
  ·
    refine ⟨64440193656092583971096921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171840516416246890589591789 64440193656092583971096921)
    ·
      refine ⟨48330145242069437978322691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64440193656092583971096921 48330145242069437978322691)
      ·
        refine ⟨72495217863104156967484037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48330145242069437978322691 72495217863104156967484037)
        ·
          refine ⟨13592853349332029431403257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72495217863104156967484037 13592853349332029431403257)
          ·
            refine ⟨10194640011999022073552443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13592853349332029431403257 10194640011999022073552443)
            ·
              refine ⟨15291960017998533110328665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10194640011999022073552443 15291960017998533110328665)
              ·
                refine ⟨11468970013498899832746499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15291960017998533110328665 11468970013498899832746499)
                ·
                  refine ⟨17203455020248349749119749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11468970013498899832746499 17203455020248349749119749)
                  ·
                    refine ⟨3225647816296565577959953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17203455020248349749119749 3225647816296565577959953)
                    ·
                      refine ⟨2419235862222424183469965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225647816296565577959953 2419235862222424183469965)
                      ·
                        rfl

theorem cell23_4711445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_4711445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711445 prefixEnd_4711445 := by exact prefixLift 4711445
  have htrace : WordTrace (prefixWord ++ tailWord_4711445) baseStart_4711445 baseEnd_4711445 := by
    simpa [prefixWord, tailWord_4711445, baseEnd_4711445] using wordTrace_append hprefix tailTrace_4711445
  have hstable : (prefixWord ++ tailWord_4711445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711445).length < 2 ^ (prefixWord ++ tailWord_4711445).sum := by decide
  have hdescent : baseEnd_4711445 < baseStart_4711445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711468 : List Nat := [2, 2, 1, 1, 1, 2, 5, 4, 5]
def baseStart_4711468 : Nat := 118140960795 + 4711468 * 2 ^ 59
def prefixEnd_4711468 : Nat := 4983230072969 + 3 ^ 40 * 4711468 * 2
def baseEnd_4711468 : Nat := 268805296919719732609151

theorem tailTrace_4711468 : CollatzResearch.WordTrace tailWord_4711468 prefixEnd_4711468 268805296919719732609151 := by
  unfold tailWord_4711468
  simp only [CollatzResearch.WordTrace]
  refine ⟨85920677647581782758839529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114560903530109043678452705 85920677647581782758839529)
  ·
    refine ⟨64440508235686337069129647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85920677647581782758839529 64440508235686337069129647)
    ·
      refine ⟨96660762353529505603694471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64440508235686337069129647 96660762353529505603694471)
      ·
        refine ⟨144991143530294258405541707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96660762353529505603694471 144991143530294258405541707)
        ·
          refine ⟨217486715295441387608312561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144991143530294258405541707 217486715295441387608312561)
          ·
            refine ⟨163115036471581040706234421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217486715295441387608312561 163115036471581040706234421)
            ·
              refine ⟨15292034669210722566209477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163115036471581040706234421 15292034669210722566209477)
              ·
                refine ⟨2867256500477010481164277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15292034669210722566209477 2867256500477010481164277)
                ·
                  refine ⟨268805296919719732609151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2867256500477010481164277 268805296919719732609151)
                  ·
                    rfl

theorem cell23_4711468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_4711468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711468 prefixEnd_4711468 := by exact prefixLift 4711468
  have htrace : WordTrace (prefixWord ++ tailWord_4711468) baseStart_4711468 baseEnd_4711468 := by
    simpa [prefixWord, tailWord_4711468, baseEnd_4711468] using wordTrace_append hprefix tailTrace_4711468
  have hstable : (prefixWord ++ tailWord_4711468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711468).length < 2 ^ (prefixWord ++ tailWord_4711468).sum := by decide
  have hdescent : baseEnd_4711468 < baseStart_4711468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711488 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 2, 5, 2]
def baseStart_4711488 : Nat := 118140960795 + 4711488 * 2 ^ 59
def prefixEnd_4711488 : Nat := 4983230072969 + 3 ^ 40 * 4711488 * 2
def baseEnd_4711488 : Nat := 2419257941890567515232267

theorem tailTrace_4711488 : CollatzResearch.WordTrace tailWord_4711488 prefixEnd_4711488 2419257941890567515232267 := by
  unfold tailWord_4711488
  simp only [CollatzResearch.WordTrace]
  refine ⟨85921042377545554466703559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114561389836727405955604745 85921042377545554466703559)
  ·
    refine ⟨128881563566318331700055339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85921042377545554466703559 128881563566318331700055339)
    ·
      refine ⟨193322345349477497550083009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128881563566318331700055339 193322345349477497550083009)
      ·
        refine ⟨144991759012108123162562257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193322345349477497550083009 144991759012108123162562257)
        ·
          refine ⟨108743819259081092371921693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144991759012108123162562257 108743819259081092371921693)
          ·
            refine ⟨40778932222155409639470635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108743819259081092371921693 40778932222155409639470635)
            ·
              refine ⟨61168398333233114459205953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40778932222155409639470635 61168398333233114459205953)
              ·
                refine ⟨45876298749924835844404465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61168398333233114459205953 45876298749924835844404465)
                ·
                  refine ⟨34407224062443626883303349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45876298749924835844404465 34407224062443626883303349)
                  ·
                    refine ⟨3225677255854090020309689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34407224062443626883303349 3225677255854090020309689)
                    ·
                      refine ⟨2419257941890567515232267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225677255854090020309689 2419257941890567515232267)
                      ·
                        rfl

theorem cell23_4711488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 5, 2].length) (baseStart_4711488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711488 prefixEnd_4711488 := by exact prefixLift 4711488
  have htrace : WordTrace (prefixWord ++ tailWord_4711488) baseStart_4711488 baseEnd_4711488 := by
    simpa [prefixWord, tailWord_4711488, baseEnd_4711488] using wordTrace_append hprefix tailTrace_4711488
  have hstable : (prefixWord ++ tailWord_4711488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711488).length < 2 ^ (prefixWord ++ tailWord_4711488).sum := by decide
  have hdescent : baseEnd_4711488 < baseStart_4711488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711498 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 2, 5]
def baseStart_4711498 : Nat := 118140960795 + 4711498 * 2 ^ 59
def prefixEnd_4711498 : Nat := 4983230072969 + 3 ^ 40 * 4711498 * 2
def baseEnd_4711498 : Nat := 806421025565704158702407

theorem tailTrace_4711498 : CollatzResearch.WordTrace tailWord_4711498 prefixEnd_4711498 806421025565704158702407 := by
  unfold tailWord_4711498
  simp only [CollatzResearch.WordTrace]
  refine ⟨42960612371263720160317787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114561632990036587094180765 42960612371263720160317787)
  ·
    refine ⟨64440918556895580240476681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42960612371263720160317787 64440918556895580240476681)
    ·
      refine ⟨48330688917671685180357511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64440918556895580240476681 48330688917671685180357511)
      ·
        refine ⟨72496033376507527770536267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48330688917671685180357511 72496033376507527770536267)
        ·
          refine ⟨108744050064761291655804401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72496033376507527770536267 108744050064761291655804401)
          ·
            refine ⟨81558037548570968741853301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108744050064761291655804401 81558037548570968741853301)
            ·
              refine ⟨7646066020178528319548747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81558037548570968741853301 7646066020178528319548747)
              ·
                refine ⟨11469099030267792479323121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7646066020178528319548747 11469099030267792479323121)
                ·
                  refine ⟨8601824272700844359492341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11469099030267792479323121 8601824272700844359492341)
                  ·
                    refine ⟨806421025565704158702407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8601824272700844359492341 806421025565704158702407)
                    ·
                      rfl

theorem cell23_4711498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_4711498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711498 prefixEnd_4711498 := by exact prefixLift 4711498
  have htrace : WordTrace (prefixWord ++ tailWord_4711498) baseStart_4711498 baseEnd_4711498 := by
    simpa [prefixWord, tailWord_4711498, baseEnd_4711498] using wordTrace_append hprefix tailTrace_4711498
  have hstable : (prefixWord ++ tailWord_4711498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711498).length < 2 ^ (prefixWord ++ tailWord_4711498).sum := by decide
  have hdescent : baseEnd_4711498 < baseStart_4711498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711521 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_4711521 : Nat := 118140960795 + 4711521 * 2 ^ 59
def prefixEnd_4711521 : Nat := 4983230072969 + 3 ^ 40 * 4711521 * 2
def baseEnd_4711521 : Nat := 2419274886752165886119615

theorem tailTrace_4711521 : CollatzResearch.WordTrace tailWord_4711521 prefixEnd_4711521 2419274886752165886119615 := by
  unfold tailWord_4711521
  simp only [CollatzResearch.WordTrace]
  refine ⟨171843288363971555569358417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114562192242647703712905611 171843288363971555569358417)
  ·
    refine ⟨128882466272978666677018813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171843288363971555569358417 128882466272978666677018813)
    ·
      refine ⟨48330924852367000003882055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 128882466272978666677018813 48330924852367000003882055)
      ·
        refine ⟨72496387278550500005823083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48330924852367000003882055 72496387278550500005823083)
        ·
          refine ⟨108744580917825750008734625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72496387278550500005823083 108744580917825750008734625)
          ·
            refine ⟨81558435688369312506550969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108744580917825750008734625 81558435688369312506550969)
            ·
              refine ⟨61168826766276984379913227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81558435688369312506550969 61168826766276984379913227)
              ·
                refine ⟨91753240149415476569869841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61168826766276984379913227 91753240149415476569869841)
                ·
                  refine ⟨68814930112061607427402381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91753240149415476569869841 68814930112061607427402381)
                  ·
                    refine ⟨25805598792023102785275893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68814930112061607427402381 25805598792023102785275893)
                    ·
                      refine ⟨2419274886752165886119615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25805598792023102785275893 2419274886752165886119615)
                      ·
                        rfl

theorem cell23_4711521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_4711521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711521 prefixEnd_4711521 := by exact prefixLift 4711521
  have htrace : WordTrace (prefixWord ++ tailWord_4711521) baseStart_4711521 baseEnd_4711521 := by
    simpa [prefixWord, tailWord_4711521, baseEnd_4711521] using wordTrace_append hprefix tailTrace_4711521
  have hstable : (prefixWord ++ tailWord_4711521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711521).length < 2 ^ (prefixWord ++ tailWord_4711521).sum := by decide
  have hdescent : baseEnd_4711521 < baseStart_4711521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711538 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_4711538 : Nat := 118140960795 + 4711538 * 2 ^ 59
def prefixEnd_4711538 : Nat := 4983230072969 + 3 ^ 40 * 4711538 * 2
def baseEnd_4711538 : Nat := 2419283615923292319607037

theorem tailTrace_4711538 : CollatzResearch.WordTrace tailWord_4711538 prefixEnd_4711538 2419283615923292319607037 := by
  unfold tailWord_4711538
  simp only [CollatzResearch.WordTrace]
  refine ⟨42960977101227491868181817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114562605603273311648484845 42960977101227491868181817)
  ·
    refine ⟨32220732825920618901136363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42960977101227491868181817 32220732825920618901136363)
    ·
      refine ⟨48331099238880928351704545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32220732825920618901136363 48331099238880928351704545)
      ·
        refine ⟨36248324429160696263778409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48331099238880928351704545 36248324429160696263778409)
        ·
          refine ⟨27186243321870522197833807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36248324429160696263778409 27186243321870522197833807)
          ·
            refine ⟨40779364982805783296750711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27186243321870522197833807 40779364982805783296750711)
            ·
              refine ⟨61169047474208674945126067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40779364982805783296750711 61169047474208674945126067)
              ·
                refine ⟨91753571211313012417689101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61169047474208674945126067 91753571211313012417689101)
                ·
                  refine ⟨34407589204242379656633413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91753571211313012417689101 34407589204242379656633413)
                  ·
                    refine ⟨6451422975795446185618765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34407589204242379656633413 6451422975795446185618765)
                    ·
                      refine ⟨2419283615923292319607037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6451422975795446185618765 2419283615923292319607037)
                      ·
                        rfl

theorem cell23_4711538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_4711538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711538 prefixEnd_4711538 := by exact prefixLift 4711538
  have htrace : WordTrace (prefixWord ++ tailWord_4711538) baseStart_4711538 baseEnd_4711538 := by
    simpa [prefixWord, tailWord_4711538, baseEnd_4711538] using wordTrace_append hprefix tailTrace_4711538
  have hstable : (prefixWord ++ tailWord_4711538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711538).length < 2 ^ (prefixWord ++ tailWord_4711538).sum := by decide
  have hdescent : baseEnd_4711538 < baseStart_4711538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711606 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4711606 : Nat := 118140960795 + 4711606 * 2 ^ 59
def prefixEnd_4711606 : Nat := 4983230072969 + 3 ^ 40 * 4711606 * 2
def baseEnd_4711606 : Nat := 2419318532607798053556725

theorem tailTrace_4711606 : CollatzResearch.WordTrace tailWord_4711606 prefixEnd_4711606 2419318532607798053556725 := by
  unfold tailWord_4711606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10740399285541475942887667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114564259045775743390801781 10740399285541475942887667)
  ·
    refine ⟨16110598928312213914331501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10740399285541475942887667 16110598928312213914331501)
    ·
      refine ⟨6041474598117080217874313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16110598928312213914331501 6041474598117080217874313)
      ·
        refine ⟨4531105948587810163405735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6041474598117080217874313 4531105948587810163405735)
        ·
          refine ⟨6796658922881715245108603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4531105948587810163405735 6796658922881715245108603)
          ·
            refine ⟨10194988384322572867662905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6796658922881715245108603 10194988384322572867662905)
            ·
              refine ⟨7646241288241929650747179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10194988384322572867662905 7646241288241929650747179)
              ·
                refine ⟨11469361932362894476120769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7646241288241929650747179 11469361932362894476120769)
                ·
                  refine ⟨8602021449272170857090577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11469361932362894476120769 8602021449272170857090577)
                  ·
                    refine ⟨6451516086954128142817933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8602021449272170857090577 6451516086954128142817933)
                    ·
                      refine ⟨2419318532607798053556725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6451516086954128142817933 2419318532607798053556725)
                      ·
                        rfl

theorem cell23_4711606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4711606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711606 prefixEnd_4711606 := by exact prefixLift 4711606
  have htrace : WordTrace (prefixWord ++ tailWord_4711606) baseStart_4711606 baseEnd_4711606 := by
    simpa [prefixWord, tailWord_4711606, baseEnd_4711606] using wordTrace_append hprefix tailTrace_4711606
  have hstable : (prefixWord ++ tailWord_4711606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711606).length < 2 ^ (prefixWord ++ tailWord_4711606).sum := by decide
  have hdescent : baseEnd_4711606 < baseStart_4711606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711612 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 2, 3, 2]
def baseStart_4711612 : Nat := 118140960795 + 4711612 * 2 ^ 59
def prefixEnd_4711612 : Nat := 4983230072969 + 3 ^ 40 * 4711612 * 2
def baseEnd_4711612 : Nat := 2419321613491725030081697

theorem tailTrace_4711612 : CollatzResearch.WordTrace tailWord_4711612 prefixEnd_4711612 2419321613491725030081697 := by
  unfold tailWord_4711612
  simp only [CollatzResearch.WordTrace]
  refine ⟨85923303703320939055460545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114564404937761252073947393 85923303703320939055460545)
  ·
    refine ⟨64442477777490704291595409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85923303703320939055460545 64442477777490704291595409)
    ·
      refine ⟨48331858333118028218696557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64442477777490704291595409 48331858333118028218696557)
      ·
        refine ⟨18124446874919260582011209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48331858333118028218696557 18124446874919260582011209)
        ·
          refine ⟨13593335156189445436508407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18124446874919260582011209 13593335156189445436508407)
          ·
            refine ⟨20390002734284168154762611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13593335156189445436508407 20390002734284168154762611)
            ·
              refine ⟨30585004101426252232143917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20390002734284168154762611 30585004101426252232143917)
              ·
                refine ⟨11469376538034844587053969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30585004101426252232143917 11469376538034844587053969)
                ·
                  refine ⟨8602032403526133440290477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11469376538034844587053969 8602032403526133440290477)
                  ·
                    refine ⟨3225762151322300040108929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8602032403526133440290477 3225762151322300040108929)
                    ·
                      refine ⟨2419321613491725030081697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225762151322300040108929 2419321613491725030081697)
                      ·
                        rfl

theorem cell23_4711612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_4711612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711612 prefixEnd_4711612 := by exact prefixLift 4711612
  have htrace : WordTrace (prefixWord ++ tailWord_4711612) baseStart_4711612 baseEnd_4711612 := by
    simpa [prefixWord, tailWord_4711612, baseEnd_4711612] using wordTrace_append hprefix tailTrace_4711612
  have hstable : (prefixWord ++ tailWord_4711612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711612).length < 2 ^ (prefixWord ++ tailWord_4711612).sum := by decide
  have hdescent : baseEnd_4711612 < baseStart_4711612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711642 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2]
def baseStart_4711642 : Nat := 118140960795 + 4711642 * 2 ^ 59
def prefixEnd_4711642 : Nat := 4983230072969 + 3 ^ 40 * 4711642 * 2
def baseEnd_4711642 : Nat := 2419337017911359912706559

theorem tailTrace_4711642 : CollatzResearch.WordTrace tailWord_4711642 prefixEnd_4711642 2419337017911359912706559 := by
  unfold tailWord_4711642
  simp only [CollatzResearch.WordTrace]
  refine ⟨42961925399133298308628295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114565134397688795489675453 42961925399133298308628295)
  ·
    refine ⟨64442888098699947462942443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42961925399133298308628295 64442888098699947462942443)
    ·
      refine ⟨96664332148049921194413665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64442888098699947462942443 96664332148049921194413665)
      ·
        refine ⟨72498249111037440895810249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96664332148049921194413665 72498249111037440895810249)
        ·
          refine ⟨54373686833278080671857687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72498249111037440895810249 54373686833278080671857687)
          ·
            refine ⟨81560530249917121007786531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54373686833278080671857687 81560530249917121007786531)
            ·
              refine ⟨122340795374875681511679797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81560530249917121007786531 122340795374875681511679797)
              ·
                refine ⟨11469449566394595141719981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122340795374875681511679797 11469449566394595141719981)
                ·
                  refine ⟨4301043587397973178144993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11469449566394595141719981 4301043587397973178144993)
                  ·
                    refine ⟨3225782690548479883608745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4301043587397973178144993 3225782690548479883608745)
                    ·
                      refine ⟨2419337017911359912706559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3225782690548479883608745 2419337017911359912706559)
                      ·
                        rfl

theorem cell23_4711642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_4711642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711642 prefixEnd_4711642 := by exact prefixLift 4711642
  have htrace : WordTrace (prefixWord ++ tailWord_4711642) baseStart_4711642 baseEnd_4711642 := by
    simpa [prefixWord, tailWord_4711642, baseEnd_4711642] using wordTrace_append hprefix tailTrace_4711642
  have hstable : (prefixWord ++ tailWord_4711642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711642).length < 2 ^ (prefixWord ++ tailWord_4711642).sum := by decide
  have hdescent : baseEnd_4711642 < baseStart_4711642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711648 : List Nat := [2, 1, 1, 3, 1, 4, 3, 8]
def baseStart_4711648 : Nat := 118140960795 + 4711648 * 2 ^ 59
def prefixEnd_4711648 : Nat := 4983230072969 + 3 ^ 40 * 4711648 * 2
def baseEnd_4711648 : Nat := 89605188844269884786353

theorem tailTrace_4711648 : CollatzResearch.WordTrace tailWord_4711648 prefixEnd_4711648 89605188844269884786353 := by
  unfold tailWord_4711648
  simp only [CollatzResearch.WordTrace]
  refine ⟨85923960217255728129615799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114565280289674304172821065 85923960217255728129615799)
  ·
    refine ⟨128885940325883592194423699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85923960217255728129615799 128885940325883592194423699)
    ·
      refine ⟨193328910488825388291635549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128885940325883592194423699 193328910488825388291635549)
      ·
        refine ⟨72498341433309520609363331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193328910488825388291635549 72498341433309520609363331)
        ·
          refine ⟨108747512149964280914044997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72498341433309520609363331 108747512149964280914044997)
          ·
            refine ⟨20390158528118302671383437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108747512149964280914044997 20390158528118302671383437)
            ·
              refine ⟨7646309448044363501768789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20390158528118302671383437 7646309448044363501768789)
              ·
                refine ⟨89605188844269884786353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7646309448044363501768789 89605188844269884786353)
                ·
                  rfl

theorem cell23_4711648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 8].length) (baseStart_4711648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711648 prefixEnd_4711648 := by exact prefixLift 4711648
  have htrace : WordTrace (prefixWord ++ tailWord_4711648) baseStart_4711648 baseEnd_4711648 := by
    simpa [prefixWord, tailWord_4711648, baseEnd_4711648] using wordTrace_append hprefix tailTrace_4711648
  have hstable : (prefixWord ++ tailWord_4711648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711648).length < 2 ^ (prefixWord ++ tailWord_4711648).sum := by decide
  have hdescent : baseEnd_4711648 < baseStart_4711648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711676 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 1, 1, 4]
def baseStart_4711676 : Nat := 118140960795 + 4711676 * 2 ^ 59
def prefixEnd_4711676 : Nat := 4983230072969 + 3 ^ 40 * 4711676 * 2
def baseEnd_4711676 : Nat := 2419354476253612779681403

theorem tailTrace_4711676 : CollatzResearch.WordTrace tailWord_4711676 prefixEnd_4711676 2419354476253612779681403 := by
  unfold tailWord_4711676
  simp only [CollatzResearch.WordTrace]
  refine ⟨85924470839205008520625441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114565961118940011360833921 85924470839205008520625441)
  ·
    refine ⟨64443353129403756390469081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85924470839205008520625441 64443353129403756390469081)
    ·
      refine ⟨48332514847052817292851811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64443353129403756390469081 48332514847052817292851811)
      ·
        refine ⟨72498772270579225939277717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48332514847052817292851811 72498772270579225939277717)
        ·
          refine ⟨3398379950183401215903643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 72498772270579225939277717 3398379950183401215903643)
          ·
            refine ⟨5097569925275101823855465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3398379950183401215903643 5097569925275101823855465)
            ·
              refine ⟨3823177443956326367891599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5097569925275101823855465 3823177443956326367891599)
              ·
                refine ⟨5734766165934489551837399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3823177443956326367891599 5734766165934489551837399)
                ·
                  refine ⟨8602149248901734327756099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5734766165934489551837399 8602149248901734327756099)
                  ·
                    refine ⟨12903223873352601491634149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8602149248901734327756099 12903223873352601491634149)
                    ·
                      refine ⟨2419354476253612779681403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12903223873352601491634149 2419354476253612779681403)
                      ·
                        rfl

theorem cell23_4711676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_4711676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711676 prefixEnd_4711676 := by exact prefixLift 4711676
  have htrace : WordTrace (prefixWord ++ tailWord_4711676) baseStart_4711676 baseEnd_4711676 := by
    simpa [prefixWord, tailWord_4711676, baseEnd_4711676] using wordTrace_append hprefix tailTrace_4711676
  have hstable : (prefixWord ++ tailWord_4711676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711676).length < 2 ^ (prefixWord ++ tailWord_4711676).sum := by decide
  have hdescent : baseEnd_4711676 < baseStart_4711676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711679 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 1, 2, 3]
def baseStart_4711679 : Nat := 118140960795 + 4711679 * 2 ^ 59
def prefixEnd_4711679 : Nat := 4983230072969 + 3 ^ 40 * 4711679 * 2
def baseEnd_4711679 : Nat := 2419356016695576267943889

theorem tailTrace_4711679 : CollatzResearch.WordTrace tailWord_4711679 prefixEnd_4711679 2419356016695576267943889 := by
  unfold tailWord_4711679
  simp only [CollatzResearch.WordTrace]
  refine ⟨171849051097399148553610091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114566034064932765702406727 171849051097399148553610091)
  ·
    refine ⟨257773576646098722830415137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171849051097399148553610091 257773576646098722830415137)
    ·
      refine ⟨193330182484574042122811353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257773576646098722830415137 193330182484574042122811353)
      ·
        refine ⟨144997636863430531592108515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193330182484574042122811353 144997636863430531592108515)
        ·
          refine ⟨217496455295145797388162773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144997636863430531592108515 217496455295145797388162773)
          ·
            refine ⟨5097573170979979626285065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 217496455295145797388162773 5097573170979979626285065)
            ·
              refine ⟨3823179878234984719713799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5097573170979979626285065 3823179878234984719713799)
              ·
                refine ⟨5734769817352477079570699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3823179878234984719713799 5734769817352477079570699)
                ·
                  refine ⟨8602154726028715619356049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5734769817352477079570699 8602154726028715619356049)
                  ·
                    refine ⟨6451616044521536714517037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8602154726028715619356049 6451616044521536714517037)
                    ·
                      refine ⟨2419356016695576267943889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6451616044521536714517037 2419356016695576267943889)
                      ·
                        rfl

theorem cell23_4711679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 1, 2, 3].length) (baseStart_4711679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711679 prefixEnd_4711679 := by exact prefixLift 4711679
  have htrace : WordTrace (prefixWord ++ tailWord_4711679) baseStart_4711679 baseEnd_4711679 := by
    simpa [prefixWord, tailWord_4711679, baseEnd_4711679] using wordTrace_append hprefix tailTrace_4711679
  have hstable : (prefixWord ++ tailWord_4711679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711679).length < 2 ^ (prefixWord ++ tailWord_4711679).sum := by decide
  have hdescent : baseEnd_4711679 < baseStart_4711679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711692 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 4, 1, 3]
def baseStart_4711692 : Nat := 118140960795 + 4711692 * 2 ^ 59
def prefixEnd_4711692 : Nat := 4983230072969 + 3 ^ 40 * 4711692 * 2
def baseEnd_4711692 : Nat := 2419362691944084717081329

theorem tailTrace_4711692 : CollatzResearch.WordTrace tailWord_4711692 prefixEnd_4711692 2419362691944084717081329 := by
  unfold tailWord_4711692
  simp only [CollatzResearch.WordTrace]
  refine ⟨85924762623176025886916665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114566350164234701182555553 85924762623176025886916665)
  ·
    refine ⟨64443571967382019415187499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85924762623176025886916665 64443571967382019415187499)
    ·
      refine ⟨96665357951073029122781249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64443571967382019415187499 96665357951073029122781249)
      ·
        refine ⟨72499018463304771842085937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96665357951073029122781249 72499018463304771842085937)
        ·
          refine ⟨54374263847478578881564453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72499018463304771842085937 54374263847478578881564453)
          ·
            refine ⟨10195174471402233540293335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54374263847478578881564453 10195174471402233540293335)
            ·
              refine ⟨15292761707103350310440003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10195174471402233540293335 15292761707103350310440003)
              ·
                refine ⟨22939142560655025465660005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15292761707103350310440003 22939142560655025465660005)
                ·
                  refine ⟨4301089230122817274811251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22939142560655025465660005 4301089230122817274811251)
                  ·
                    refine ⟨6451633845184225912216877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4301089230122817274811251 6451633845184225912216877)
                    ·
                      refine ⟨2419362691944084717081329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6451633845184225912216877 2419362691944084717081329)
                      ·
                        rfl

theorem cell23_4711692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_4711692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711692 prefixEnd_4711692 := by exact prefixLift 4711692
  have htrace : WordTrace (prefixWord ++ tailWord_4711692) baseStart_4711692 baseEnd_4711692 := by
    simpa [prefixWord, tailWord_4711692, baseEnd_4711692] using wordTrace_append hprefix tailTrace_4711692
  have hstable : (prefixWord ++ tailWord_4711692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711692).length < 2 ^ (prefixWord ++ tailWord_4711692).sum := by decide
  have hdescent : baseEnd_4711692 < baseStart_4711692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711709 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_4711709 : Nat := 118140960795 + 4711709 * 2 ^ 59
def prefixEnd_4711709 : Nat := 4983230072969 + 3 ^ 40 * 4711709 * 2
def baseEnd_4711709 : Nat := 2419371421115211150568751

theorem tailTrace_4711709 : CollatzResearch.WordTrace tailWord_4711709 prefixEnd_4711709 2419371421115211150568751 := by
  unfold tailWord_4711709
  simp only [CollatzResearch.WordTrace]
  refine ⟨171850145287290463677202181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114566763524860309118134787 171850145287290463677202181)
  ·
    refine ⟨32221902241366961939475409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171850145287290463677202181 32221902241366961939475409)
    ·
      refine ⟨24166426681025221454606557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32221902241366961939475409 24166426681025221454606557)
      ·
        refine ⟨9062410005384458045477459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24166426681025221454606557 9062410005384458045477459)
        ·
          refine ⟨13593615008076687068216189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9062410005384458045477459 13593615008076687068216189)
          ·
            refine ⟨5097605628028757650581071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13593615008076687068216189 5097605628028757650581071)
            ·
              refine ⟨7646408442043136475871607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5097605628028757650581071 7646408442043136475871607)
              ·
                refine ⟨11469612663064704713807411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7646408442043136475871607 11469612663064704713807411)
                ·
                  refine ⟨17204418994597057070711117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11469612663064704713807411 17204418994597057070711117)
                  ·
                    refine ⟨6451657122973896401516669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17204418994597057070711117 6451657122973896401516669)
                    ·
                      refine ⟨2419371421115211150568751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6451657122973896401516669 2419371421115211150568751)
                      ·
                        rfl

theorem cell23_4711709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_4711709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711709 prefixEnd_4711709 := by exact prefixLift 4711709
  have htrace : WordTrace (prefixWord ++ tailWord_4711709) baseStart_4711709 baseEnd_4711709 := by
    simpa [prefixWord, tailWord_4711709, baseEnd_4711709] using wordTrace_append hprefix tailTrace_4711709
  have hstable : (prefixWord ++ tailWord_4711709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711709).length < 2 ^ (prefixWord ++ tailWord_4711709).sum := by decide
  have hdescent : baseEnd_4711709 < baseStart_4711709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711825 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 3]
def baseStart_4711825 : Nat := 118140960795 + 4711825 * 2 ^ 59
def prefixEnd_4711825 : Nat := 4983230072969 + 3 ^ 40 * 4711825 * 2
def baseEnd_4711825 : Nat := 2419430984871132696718217

theorem tailTrace_4711825 : CollatzResearch.WordTrace tailWord_4711825 prefixEnd_4711825 2419430984871132696718217 := by
  unfold tailWord_4711825
  simp only [CollatzResearch.WordTrace]
  refine ⟨171854376154870215488424929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114569584103246810325616619 171854376154870215488424929)
  ·
    refine ⟨128890782116152661616318697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171854376154870215488424929 128890782116152661616318697)
    ·
      refine ⟨96668086587114496212239023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128890782116152661616318697 96668086587114496212239023)
      ·
        refine ⟨145002129880671744318358535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96668086587114496212239023 145002129880671744318358535)
        ·
          refine ⟨217503194821007616477537803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145002129880671744318358535 217503194821007616477537803)
          ·
            refine ⟨326254792231511424716306705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217503194821007616477537803 326254792231511424716306705)
            ·
              refine ⟨244691094173633568537230029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326254792231511424716306705 244691094173633568537230029)
              ·
                refine ⟨91759160315112588201461261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244691094173633568537230029 91759160315112588201461261)
                ·
                  refine ⟨34409685118167220575547973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91759160315112588201461261 34409685118167220575547973)
                  ·
                    refine ⟨6451815959656353857915245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34409685118167220575547973 6451815959656353857915245)
                    ·
                      refine ⟨2419430984871132696718217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6451815959656353857915245 2419430984871132696718217)
                      ·
                        rfl

theorem cell23_4711825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_4711825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711825 prefixEnd_4711825 := by exact prefixLift 4711825
  have htrace : WordTrace (prefixWord ++ tailWord_4711825) baseStart_4711825 baseEnd_4711825 := by
    simpa [prefixWord, tailWord_4711825, baseEnd_4711825] using wordTrace_append hprefix tailTrace_4711825
  have hstable : (prefixWord ++ tailWord_4711825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711825).length < 2 ^ (prefixWord ++ tailWord_4711825).sum := by decide
  have hdescent : baseEnd_4711825 < baseStart_4711825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711836 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 2, 5]
def baseStart_4711836 : Nat := 118140960795 + 4711836 * 2 ^ 59
def prefixEnd_4711836 : Nat := 4983230072969 + 3 ^ 40 * 4711836 * 2
def baseEnd_4711836 : Nat := 806478877719444051226889

theorem tailTrace_4711836 : CollatzResearch.WordTrace tailWord_4711836 prefixEnd_4711836 806478877719444051226889 := by
  unfold tailWord_4711836
  simp only [CollatzResearch.WordTrace]
  refine ⟨85927388678915182183537681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114569851571886909578050241 85927388678915182183537681)
  ·
    refine ⟨64445541509186386637653261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85927388678915182183537681 64445541509186386637653261)
    ·
      refine ⟨24167078065944894989119973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64445541509186386637653261 24167078065944894989119973)
      ·
        refine ⟨4531327137364667810459995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24167078065944894989119973 4531327137364667810459995)
        ·
          refine ⟨6796990706047001715689993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4531327137364667810459995 6796990706047001715689993)
          ·
            refine ⟨5097743029535251286767495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6796990706047001715689993 5097743029535251286767495)
            ·
              refine ⟨7646614544302876930151243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5097743029535251286767495 7646614544302876930151243)
              ·
                refine ⟨11469921816454315395226865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7646614544302876930151243 11469921816454315395226865)
                ·
                  refine ⟨8602441362340736546420149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11469921816454315395226865 8602441362340736546420149)
                  ·
                    refine ⟨806478877719444051226889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8602441362340736546420149 806478877719444051226889)
                    ·
                      rfl

theorem cell23_4711836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_4711836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711836 prefixEnd_4711836 := by exact prefixLift 4711836
  have htrace : WordTrace (prefixWord ++ tailWord_4711836) baseStart_4711836 baseEnd_4711836 := by
    simpa [prefixWord, tailWord_4711836, baseEnd_4711836] using wordTrace_append hprefix tailTrace_4711836
  have hstable : (prefixWord ++ tailWord_4711836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711836).length < 2 ^ (prefixWord ++ tailWord_4711836).sum := by decide
  have hdescent : baseEnd_4711836 < baseStart_4711836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711839 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 4]
def baseStart_4711839 : Nat := 118140960795 + 4711839 * 2 ^ 59
def prefixEnd_4711839 : Nat := 4983230072969 + 3 ^ 40 * 4711839 * 2
def baseEnd_4711839 : Nat := 2419438173600295641943153

theorem tailTrace_4711839 : CollatzResearch.WordTrace tailWord_4711839 prefixEnd_4711839 2419438173600295641943153 := by
  unfold tailWord_4711839
  simp only [CollatzResearch.WordTrace]
  refine ⟨171854886776819495879434571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114569924517879663919623047 171854886776819495879434571)
  ·
    refine ⟨257782330165229243819151857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171854886776819495879434571 257782330165229243819151857)
    ·
      refine ⟨193336747623921932864363893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257782330165229243819151857 193336747623921932864363893)
      ·
        refine ⟨18125320089742681206034115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193336747623921932864363893 18125320089742681206034115)
        ·
          refine ⟨27187980134614021809051173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18125320089742681206034115 27187980134614021809051173)
          ·
            refine ⟨5097746275240129089197095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27187980134614021809051173 5097746275240129089197095)
            ·
              refine ⟨7646619412860193633795643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5097746275240129089197095 7646619412860193633795643)
              ·
                refine ⟨11469929119290290450693465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7646619412860193633795643 11469929119290290450693465)
                ·
                  refine ⟨8602446839467717838020099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11469929119290290450693465 8602446839467717838020099)
                  ·
                    refine ⟨12903670259201576757030149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8602446839467717838020099 12903670259201576757030149)
                    ·
                      refine ⟨2419438173600295641943153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12903670259201576757030149 2419438173600295641943153)
                      ·
                        rfl

theorem cell23_4711839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_4711839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711839 prefixEnd_4711839 := by exact prefixLift 4711839
  have htrace : WordTrace (prefixWord ++ tailWord_4711839) baseStart_4711839 baseEnd_4711839 := by
    simpa [prefixWord, tailWord_4711839, baseEnd_4711839] using wordTrace_append hprefix tailTrace_4711839
  have hstable : (prefixWord ++ tailWord_4711839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711839).length < 2 ^ (prefixWord ++ tailWord_4711839).sum := by decide
  have hdescent : baseEnd_4711839 < baseStart_4711839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711855 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 3]
def baseStart_4711855 : Nat := 118140960795 + 4711855 * 2 ^ 59
def prefixEnd_4711855 : Nat := 4983230072969 + 3 ^ 40 * 4711855 * 2
def baseEnd_4711855 : Nat := 2419446389290767579343079

theorem tailTrace_4711855 : CollatzResearch.WordTrace tailWord_4711855 prefixEnd_4711855 2419446389290767579343079 := by
  unfold tailWord_4711855
  simp only [CollatzResearch.WordTrace]
  refine ⟨171855470344761530612017019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114570313563174353741344679 171855470344761530612017019)
  ·
    refine ⟨257783205517142295918025529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171855470344761530612017019 257783205517142295918025529)
    ·
      refine ⟨193337404137856721938519147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257783205517142295918025529 193337404137856721938519147)
      ·
        refine ⟨290006106206785082907778721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193337404137856721938519147 290006106206785082907778721)
        ·
          refine ⟨217504579655088812180834041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290006106206785082907778721 217504579655088812180834041)
          ·
            refine ⟨163128434741316609135625531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217504579655088812180834041 163128434741316609135625531)
            ·
              refine ⟨244692652111974913703438297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163128434741316609135625531 244692652111974913703438297)
              ·
                refine ⟨183519489083981185277578723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244692652111974913703438297 183519489083981185277578723)
                ·
                  refine ⟨275279233625971777916368085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183519489083981185277578723 275279233625971777916368085)
                  ·
                    refine ⟨6451857038108713544914877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 275279233625971777916368085 6451857038108713544914877)
                    ·
                      refine ⟨2419446389290767579343079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6451857038108713544914877 2419446389290767579343079)
                      ·
                        rfl

theorem cell23_4711855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 3].length) (baseStart_4711855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711855 prefixEnd_4711855 := by exact prefixLift 4711855
  have htrace : WordTrace (prefixWord ++ tailWord_4711855) baseStart_4711855 baseEnd_4711855 := by
    simpa [prefixWord, tailWord_4711855, baseEnd_4711855] using wordTrace_append hprefix tailTrace_4711855
  have hstable : (prefixWord ++ tailWord_4711855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711855).length < 2 ^ (prefixWord ++ tailWord_4711855).sum := by decide
  have hdescent : baseEnd_4711855 < baseStart_4711855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711875 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 5, 5]
def baseStart_4711875 : Nat := 118140960795 + 4711875 * 2 ^ 59
def prefixEnd_4711875 : Nat := 4983230072969 + 3 ^ 40 * 4711875 * 2
def baseEnd_4711875 : Nat := 806485552967952500364329

theorem tailTrace_4711875 : CollatzResearch.WordTrace tailWord_4711875 prefixEnd_4711875 806485552967952500364329 := by
  unfold tailWord_4711875
  simp only [CollatzResearch.WordTrace]
  refine ⟨171856199804689074027745079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114570799869792716018496719 171856199804689074027745079)
  ·
    refine ⟨257784299707033611041617619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171856199804689074027745079 257784299707033611041617619)
    ·
      refine ⟨386676449560550416562426429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257784299707033611041617619 386676449560550416562426429)
      ·
        refine ⟨145003668585206406210909911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 386676449560550416562426429 145003668585206406210909911)
        ·
          refine ⟨217505502877809609316364867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145003668585206406210909911 217505502877809609316364867)
          ·
            refine ⟨326258254316714413974547301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217505502877809609316364867 326258254316714413974547301)
            ·
              refine ⟨61173422684383952620227619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 326258254316714413974547301 61173422684383952620227619)
              ·
                refine ⟨91760134026575928930341429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61173422684383952620227619 91760134026575928930341429)
                ·
                  refine ⟨8602512564991493337219509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91760134026575928930341429 8602512564991493337219509)
                  ·
                    refine ⟨806485552967952500364329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8602512564991493337219509 806485552967952500364329)
                    ·
                      rfl

theorem cell23_4711875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 5].length) (baseStart_4711875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711875 prefixEnd_4711875 := by exact prefixLift 4711875
  have htrace : WordTrace (prefixWord ++ tailWord_4711875) baseStart_4711875 baseEnd_4711875 := by
    simpa [prefixWord, tailWord_4711875, baseEnd_4711875] using wordTrace_append hprefix tailTrace_4711875
  have hstable : (prefixWord ++ tailWord_4711875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711875).length < 2 ^ (prefixWord ++ tailWord_4711875).sum := by decide
  have hdescent : baseEnd_4711875 < baseStart_4711875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711895 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_4711895 : Nat := 118140960795 + 4711895 * 2 ^ 59
def prefixEnd_4711895 : Nat := 4983230072969 + 3 ^ 40 * 4711895 * 2
def baseEnd_4711895 : Nat := 2419466928516947422842895

theorem tailTrace_4711895 : CollatzResearch.WordTrace tailWord_4711895 prefixEnd_4711895 2419466928516947422842895 := by
  unfold tailWord_4711895
  simp only [CollatzResearch.WordTrace]
  refine ⟨171856929264616617443473139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114571286176411078295648759 171856929264616617443473139)
  ·
    refine ⟨257785393896924926165209709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171856929264616617443473139 257785393896924926165209709)
    ·
      refine ⟨96669522711346847311953641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257785393896924926165209709 96669522711346847311953641)
      ·
        refine ⟨72502142033510135483965231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96669522711346847311953641 72502142033510135483965231)
        ·
          refine ⟨108753213050265203225947847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72502142033510135483965231 108753213050265203225947847)
          ·
            refine ⟨163129819575397804838921771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108753213050265203225947847 163129819575397804838921771)
            ·
              refine ⟨244694729363096707258382657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163129819575397804838921771 244694729363096707258382657)
              ·
                refine ⟨183521047022322530443786993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244694729363096707258382657 183521047022322530443786993)
                ·
                  refine ⟨137640785266741897832840245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183521047022322530443786993 137640785266741897832840245)
                  ·
                    refine ⟨12903823618757052921828773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 137640785266741897832840245 12903823618757052921828773)
                    ·
                      refine ⟨2419466928516947422842895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12903823618757052921828773 2419466928516947422842895)
                      ·
                        rfl

theorem cell23_4711895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_4711895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711895 prefixEnd_4711895 := by exact prefixLift 4711895
  have htrace : WordTrace (prefixWord ++ tailWord_4711895) baseStart_4711895 baseEnd_4711895 := by
    simpa [prefixWord, tailWord_4711895, baseEnd_4711895] using wordTrace_append hprefix tailTrace_4711895
  have hstable : (prefixWord ++ tailWord_4711895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711895).length < 2 ^ (prefixWord ++ tailWord_4711895).sum := by decide
  have hdescent : baseEnd_4711895 < baseStart_4711895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711909 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 1, 5]
def baseStart_4711909 : Nat := 118140960795 + 4711909 * 2 ^ 59
def prefixEnd_4711909 : Nat := 4983230072969 + 3 ^ 40 * 4711909 * 2
def baseEnd_4711909 : Nat := 806491372415370122689277

theorem tailTrace_4711909 : CollatzResearch.WordTrace tailWord_4711909 prefixEnd_4711909 806491372415370122689277 := by
  unfold tailWord_4711909
  simp only [CollatzResearch.WordTrace]
  refine ⟨171857439886565897834482781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114571626591043931889655187 171857439886565897834482781)
  ·
    refine ⟨64446539957462211687931043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171857439886565897834482781 64446539957462211687931043)
    ·
      refine ⟨96669809936193317531896565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64446539957462211687931043 96669809936193317531896565)
      ·
        refine ⟨9062794681518123518615303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96669809936193317531896565 9062794681518123518615303)
        ·
          refine ⟨13594192022277185277922955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9062794681518123518615303 13594192022277185277922955)
          ·
            refine ⟨20391288033415777916884433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13594192022277185277922955 20391288033415777916884433)
            ·
              refine ⟨15293466025061833437663325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20391288033415777916884433 15293466025061833437663325)
              ·
                refine ⟨5735049759398187539123747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15293466025061833437663325 5735049759398187539123747)
                ·
                  refine ⟨8602574639097281308685621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5735049759398187539123747 8602574639097281308685621)
                  ·
                    refine ⟨806491372415370122689277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8602574639097281308685621 806491372415370122689277)
                    ·
                      rfl

theorem cell23_4711909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_4711909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711909 prefixEnd_4711909 := by exact prefixLift 4711909
  have htrace : WordTrace (prefixWord ++ tailWord_4711909) baseStart_4711909 baseEnd_4711909 := by
    simpa [prefixWord, tailWord_4711909, baseEnd_4711909] using wordTrace_append hprefix tailTrace_4711909
  have hstable : (prefixWord ++ tailWord_4711909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711909).length < 2 ^ (prefixWord ++ tailWord_4711909).sum := by decide
  have hdescent : baseEnd_4711909 < baseStart_4711909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711932 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_4711932 : Nat := 118140960795 + 4711932 * 2 ^ 59
def prefixEnd_4711932 : Nat := 4983230072969 + 3 ^ 40 * 4711932 * 2
def baseEnd_4711932 : Nat := 2419485927301163778080225

theorem tailTrace_4711932 : CollatzResearch.WordTrace tailWord_4711932 prefixEnd_4711932 2419485927301163778080225 := by
  unfold tailWord_4711932
  simp only [CollatzResearch.WordTrace]
  refine ⟨85929139382741286381285025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114572185843655048508380033 85929139382741286381285025)
  ·
    refine ⟨64446854537055964785963769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85929139382741286381285025 64446854537055964785963769)
    ·
      refine ⟨48335140902791973589472827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64446854537055964785963769 48335140902791973589472827)
      ·
        refine ⟨72502711354187960384209241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48335140902791973589472827 72502711354187960384209241)
        ·
          refine ⟨54377033515640970288156931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72502711354187960384209241 54377033515640970288156931)
          ·
            refine ⟨81565550273461455432235397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54377033515640970288156931 81565550273461455432235397)
            ·
              refine ⟨15293540676274022893544137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81565550273461455432235397 15293540676274022893544137)
              ·
                refine ⟨11470155507205517170158103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15293540676274022893544137 11470155507205517170158103)
                ·
                  refine ⟨17205233260808275755237155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11470155507205517170158103 17205233260808275755237155)
                  ·
                    refine ⟨25807849891212413632855733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17205233260808275755237155 25807849891212413632855733)
                    ·
                      refine ⟨2419485927301163778080225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25807849891212413632855733 2419485927301163778080225)
                      ·
                        rfl

theorem cell23_4711932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_4711932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711932 prefixEnd_4711932 := by exact prefixLift 4711932
  have htrace : WordTrace (prefixWord ++ tailWord_4711932) baseStart_4711932 baseEnd_4711932 := by
    simpa [prefixWord, tailWord_4711932, baseEnd_4711932] using wordTrace_append hprefix tailTrace_4711932
  have hstable : (prefixWord ++ tailWord_4711932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711932).length < 2 ^ (prefixWord ++ tailWord_4711932).sum := by decide
  have hdescent : baseEnd_4711932 < baseStart_4711932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711946 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_4711946 : Nat := 118140960795 + 4711946 * 2 ^ 59
def prefixEnd_4711946 : Nat := 4983230072969 + 3 ^ 40 * 4711946 * 2
def baseEnd_4711946 : Nat := 2419493116030326723305161

theorem tailTrace_4711946 : CollatzResearch.WordTrace tailWord_4711946 prefixEnd_4711946 2419493116030326723305161 := by
  unfold tailWord_4711946
  simp only [CollatzResearch.WordTrace]
  refine ⟨42964697346857963288394923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114572526258287902102386461 42964697346857963288394923)
  ·
    refine ⟨64447046020286944932592385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42964697346857963288394923 64447046020286944932592385)
    ·
      refine ⟨48335284515215208699444289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64447046020286944932592385 48335284515215208699444289)
      ·
        refine ⟨36251463386411406524583217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48335284515215208699444289 36251463386411406524583217)
        ·
          refine ⟨27188597539808554893437413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36251463386411406524583217 27188597539808554893437413)
          ·
            refine ⟨5097862038714104042519515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27188597539808554893437413 5097862038714104042519515)
            ·
              refine ⟨7646793058071156063779273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5097862038714104042519515 7646793058071156063779273)
              ·
                refine ⟨5735094793553367047834455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7646793058071156063779273 5735094793553367047834455)
                ·
                  refine ⟨8602642190330050571751683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5735094793553367047834455 8602642190330050571751683)
                  ·
                    refine ⟨12903963285495075857627525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8602642190330050571751683 12903963285495075857627525)
                    ·
                      refine ⟨2419493116030326723305161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12903963285495075857627525 2419493116030326723305161)
                      ·
                        rfl

theorem cell23_4711946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_4711946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711946 prefixEnd_4711946 := by exact prefixLift 4711946
  have htrace : WordTrace (prefixWord ++ tailWord_4711946) baseStart_4711946 baseEnd_4711946 := by
    simpa [prefixWord, tailWord_4711946, baseEnd_4711946] using wordTrace_append hprefix tailTrace_4711946
  have hstable : (prefixWord ++ tailWord_4711946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711946).length < 2 ^ (prefixWord ++ tailWord_4711946).sum := by decide
  have hdescent : baseEnd_4711946 < baseStart_4711946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711956 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_4711956 : Nat := 118140960795 + 4711956 * 2 ^ 59
def prefixEnd_4711956 : Nat := 4983230072969 + 3 ^ 40 * 4711956 * 2
def baseEnd_4711956 : Nat := 806499416945623894726705

theorem tailTrace_4711956 : CollatzResearch.WordTrace tailWord_4711956 prefixEnd_4711956 806499416945623894726705 := by
  unfold tailWord_4711956
  simp only [CollatzResearch.WordTrace]
  refine ⟨85929577058697812430721861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114572769411597083240962481 85929577058697812430721861)
  ·
    refine ⟨16111795698505839830760349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85929577058697812430721861 16111795698505839830760349)
    ·
      refine ⟨6041923386939689936535131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16111795698505839830760349 6041923386939689936535131)
      ·
        refine ⟨9062885080409534904802697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6041923386939689936535131 9062885080409534904802697)
        ·
          refine ⟨6797163810307151178602023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9062885080409534904802697 6797163810307151178602023)
          ·
            refine ⟨10195745715460726767903035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6797163810307151178602023 10195745715460726767903035)
            ·
              refine ⟨15293618573191090151854553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10195745715460726767903035 15293618573191090151854553)
              ·
                refine ⟨11470213929893317613890915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15293618573191090151854553 11470213929893317613890915)
                ·
                  refine ⟨17205320894839976420836373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11470213929893317613890915 17205320894839976420836373)
                  ·
                    refine ⟨806499416945623894726705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17205320894839976420836373 806499416945623894726705)
                    ·
                      rfl

theorem cell23_4711956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_4711956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711956 prefixEnd_4711956 := by exact prefixLift 4711956
  have htrace : WordTrace (prefixWord ++ tailWord_4711956) baseStart_4711956 baseEnd_4711956 := by
    simpa [prefixWord, tailWord_4711956, baseEnd_4711956] using wordTrace_append hprefix tailTrace_4711956
  have hstable : (prefixWord ++ tailWord_4711956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711956).length < 2 ^ (prefixWord ++ tailWord_4711956).sum := by decide
  have hdescent : baseEnd_4711956 < baseStart_4711956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4711996 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_4711996 : Nat := 118140960795 + 4711996 * 2 ^ 59
def prefixEnd_4711996 : Nat := 4983230072969 + 3 ^ 40 * 4711996 * 2
def baseEnd_4711996 : Nat := 2419518790063051527679931

theorem tailTrace_4711996 : CollatzResearch.WordTrace tailWord_4711996 prefixEnd_4711996 2419518790063051527679931 := by
  unfold tailWord_4711996
  simp only [CollatzResearch.WordTrace]
  refine ⟨85930306518625355846449921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114573742024833807795266561 85930306518625355846449921)
  ·
    refine ⟨64447729888969016884837441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85930306518625355846449921 64447729888969016884837441)
    ·
      refine ⟨48335797416726762663628081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64447729888969016884837441 48335797416726762663628081)
      ·
        refine ⟨36251848062545071997721061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48335797416726762663628081 36251848062545071997721061)
        ·
          refine ⟨6797221511727200999572699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36251848062545071997721061 6797221511727200999572699)
          ·
            refine ⟨10195832267590801499359049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6797221511727200999572699 10195832267590801499359049)
            ·
              refine ⟨7646874200693101124519287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10195832267590801499359049 7646874200693101124519287)
              ·
                refine ⟨11470311301039651686778931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7646874200693101124519287 11470311301039651686778931)
                ·
                  refine ⟨17205466951559477530168397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11470311301039651686778931 17205466951559477530168397)
                  ·
                    refine ⟨6452050106834804073813149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17205466951559477530168397 6452050106834804073813149)
                    ·
                      refine ⟨2419518790063051527679931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6452050106834804073813149 2419518790063051527679931)
                      ·
                        rfl

theorem cell23_4711996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_4711996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4711996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4711996 prefixEnd_4711996 := by exact prefixLift 4711996
  have htrace : WordTrace (prefixWord ++ tailWord_4711996) baseStart_4711996 baseEnd_4711996 := by
    simpa [prefixWord, tailWord_4711996, baseEnd_4711996] using wordTrace_append hprefix tailTrace_4711996
  have hstable : (prefixWord ++ tailWord_4711996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4711996).length < 2 ^ (prefixWord ++ tailWord_4711996).sum := by decide
  have hdescent : baseEnd_4711996 < baseStart_4711996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4711996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712023 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 1, 3, 2]
def baseStart_4712023 : Nat := 118140960795 + 4712023 * 2 ^ 59
def prefixEnd_4712023 : Nat := 4983230072969 + 3 ^ 40 * 4712023 * 2
def baseEnd_4712023 : Nat := 2419532654040722922042307

theorem tailTrace_4712023 : CollatzResearch.WordTrace tailWord_4712023 prefixEnd_4712023 2419532654040722922042307 := by
  unfold tailWord_4712023
  simp only [CollatzResearch.WordTrace]
  refine ⟨171861597808152895304132723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114574398538768596869421815 171861597808152895304132723)
  ·
    refine ⟨257792396712229342956199085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171861597808152895304132723 257792396712229342956199085)
    ·
      refine ⟨96672148767086003608574657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257792396712229342956199085 96672148767086003608574657)
      ·
        refine ⟨72504111575314502706430993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96672148767086003608574657 72504111575314502706430993)
        ·
          refine ⟨54378083681485877029823245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72504111575314502706430993 54378083681485877029823245)
          ·
            refine ⟨20391781380557203886183717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54378083681485877029823245 20391781380557203886183717)
            ·
              refine ⟨3823459008854475728659447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20391781380557203886183717 3823459008854475728659447)
              ·
                refine ⟨5735188513281713592989171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3823459008854475728659447 5735188513281713592989171)
                ·
                  refine ⟨8602782769922570389483757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5735188513281713592989171 8602782769922570389483757)
                  ·
                    refine ⟨3226043538720963896056409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8602782769922570389483757 3226043538720963896056409)
                    ·
                      refine ⟨2419532654040722922042307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3226043538720963896056409 2419532654040722922042307)
                      ·
                        rfl

theorem cell23_4712023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_4712023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712023 prefixEnd_4712023 := by exact prefixLift 4712023
  have htrace : WordTrace (prefixWord ++ tailWord_4712023) baseStart_4712023 baseEnd_4712023 := by
    simpa [prefixWord, tailWord_4712023, baseEnd_4712023] using wordTrace_append hprefix tailTrace_4712023
  have hstable : (prefixWord ++ tailWord_4712023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712023).length < 2 ^ (prefixWord ++ tailWord_4712023).sum := by decide
  have hdescent : baseEnd_4712023 < baseStart_4712023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712053 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_4712053 : Nat := 118140960795 + 4712053 * 2 ^ 59
def prefixEnd_4712053 : Nat := 4983230072969 + 3 ^ 40 * 4712053 * 2
def baseEnd_4712053 : Nat := 2419548058460357804667169

theorem tailTrace_4712053 : CollatzResearch.WordTrace tailWord_4712053 prefixEnd_4712053 2419548058460357804667169 := by
  unfold tailWord_4712053
  simp only [CollatzResearch.WordTrace]
  refine ⟨171862691998044210427724813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114575127998696140285149875 171862691998044210427724813)
  ·
    refine ⟨64448509499266578910396805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171862691998044210427724813 64448509499266578910396805)
    ·
      refine ⟨12084095531112483545699401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64448509499266578910396805 12084095531112483545699401)
      ·
        refine ⟨9063071648334362659274551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12084095531112483545699401 9063071648334362659274551)
        ·
          refine ⟨13594607472501543988911827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9063071648334362659274551 13594607472501543988911827)
          ·
            refine ⟨20391911208752315983367741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13594607472501543988911827 20391911208752315983367741)
            ·
              refine ⟨7646966703282118493762903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20391911208752315983367741 7646966703282118493762903)
              ·
                refine ⟨11470450054923177740644355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7646966703282118493762903 11470450054923177740644355)
                ·
                  refine ⟨17205675082384766610966533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11470450054923177740644355 17205675082384766610966533)
                  ·
                    refine ⟨3226064077947143739556225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17205675082384766610966533 3226064077947143739556225)
                    ·
                      refine ⟨2419548058460357804667169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3226064077947143739556225 2419548058460357804667169)
                      ·
                        rfl

theorem cell23_4712053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_4712053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712053 prefixEnd_4712053 := by exact prefixLift 4712053
  have htrace : WordTrace (prefixWord ++ tailWord_4712053) baseStart_4712053 baseEnd_4712053 := by
    simpa [prefixWord, tailWord_4712053, baseEnd_4712053] using wordTrace_append hprefix tailTrace_4712053
  have hstable : (prefixWord ++ tailWord_4712053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712053).length < 2 ^ (prefixWord ++ tailWord_4712053).sum := by decide
  have hdescent : baseEnd_4712053 < baseStart_4712053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712104 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4712104 : Nat := 118140960795 + 4712104 * 2 ^ 59
def prefixEnd_4712104 : Nat := 4983230072969 + 3 ^ 40 * 4712104 * 2
def baseEnd_4712104 : Nat := 2419574245973737105129435

theorem tailTrace_4712104 : CollatzResearch.WordTrace tailWord_4712104 prefixEnd_4712104 2419574245973737105129435 := by
  unfold tailWord_4712104
  simp only [CollatzResearch.WordTrace]
  refine ⟨85932276060429723068915683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114576368080572964091887577 85932276060429723068915683)
  ·
    refine ⟨128898414090644584603373525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85932276060429723068915683 128898414090644584603373525)
    ·
      refine ⟨3021056580249482451641567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 128898414090644584603373525 3021056580249482451641567)
      ·
        refine ⟨4531584870374223677462351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3021056580249482451641567 4531584870374223677462351)
        ·
          refine ⟨6797377305561335516193527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4531584870374223677462351 6797377305561335516193527)
          ·
            refine ⟨10196065958342003274290291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6797377305561335516193527 10196065958342003274290291)
            ·
              refine ⟨15294098937513004911435437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10196065958342003274290291 15294098937513004911435437)
              ·
                refine ⟨5735287101567376841788289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15294098937513004911435437 5735287101567376841788289)
                ·
                  refine ⟨4301465326175532631341217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5735287101567376841788289 4301465326175532631341217)
                  ·
                    refine ⟨3226098994631649473505913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4301465326175532631341217 3226098994631649473505913)
                    ·
                      refine ⟨2419574245973737105129435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3226098994631649473505913 2419574245973737105129435)
                      ·
                        rfl

theorem cell23_4712104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4712104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712104 prefixEnd_4712104 := by exact prefixLift 4712104
  have htrace : WordTrace (prefixWord ++ tailWord_4712104) baseStart_4712104 baseEnd_4712104 := by
    simpa [prefixWord, tailWord_4712104, baseEnd_4712104] using wordTrace_append hprefix tailTrace_4712104
  have hstable : (prefixWord ++ tailWord_4712104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712104).length < 2 ^ (prefixWord ++ tailWord_4712104).sum := by decide
  have hdescent : baseEnd_4712104 < baseStart_4712104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712126 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_4712126 : Nat := 118140960795 + 4712126 * 2 ^ 59
def prefixEnd_4712126 : Nat := 4983230072969 + 3 ^ 40 * 4712126 * 2
def baseEnd_4712126 : Nat := 2419585542548136019054333

theorem tailTrace_4712126 : CollatzResearch.WordTrace tailWord_4712126 prefixEnd_4712126 2419585542548136019054333 := by
  unfold tailWord_4712126
  simp only [CollatzResearch.WordTrace]
  refine ⟨21483169315847467986891529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114576903017853162596754821 21483169315847467986891529)
  ·
    refine ⟨16112376986885600990168647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21483169315847467986891529 16112376986885600990168647)
    ·
      refine ⟨24168565480328401485252971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16112376986885600990168647 24168565480328401485252971)
      ·
        refine ⟨36252848220492602227879457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24168565480328401485252971 36252848220492602227879457)
        ·
          refine ⟨27189636165369451670909593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36252848220492602227879457 27189636165369451670909593)
          ·
            refine ⟨20392227124027088753182195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27189636165369451670909593 20392227124027088753182195)
            ·
              refine ⟨30588340686040633129773293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20392227124027088753182195 30588340686040633129773293)
              ·
                refine ⟨11470627757265237423664985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30588340686040633129773293 11470627757265237423664985)
                ·
                  refine ⟨8602970817948928067748739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11470627757265237423664985 8602970817948928067748739)
                  ·
                    refine ⟨12904456226923392101623109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8602970817948928067748739 12904456226923392101623109)
                    ·
                      refine ⟨2419585542548136019054333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12904456226923392101623109 2419585542548136019054333)
                      ·
                        rfl

theorem cell23_4712126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_4712126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712126 prefixEnd_4712126 := by exact prefixLift 4712126
  have htrace : WordTrace (prefixWord ++ tailWord_4712126) baseStart_4712126 baseEnd_4712126 := by
    simpa [prefixWord, tailWord_4712126, baseEnd_4712126] using wordTrace_append hprefix tailTrace_4712126
  have hstable : (prefixWord ++ tailWord_4712126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712126).length < 2 ^ (prefixWord ++ tailWord_4712126).sum := by decide
  have hdescent : baseEnd_4712126 < baseStart_4712126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712153 : List Nat := [1, 2, 1, 2, 3, 4, 1, 4, 1, 4]
def baseStart_4712153 : Nat := 118140960795 + 4712153 * 2 ^ 59
def prefixEnd_4712153 : Nat := 4983230072969 + 3 ^ 40 * 4712153 * 2
def baseEnd_4712153 : Nat := 806533135508602471138903

theorem tailTrace_4712153 : CollatzResearch.WordTrace tailWord_4712153 prefixEnd_4712153 806533135508602471138903 := by
  unfold tailWord_4712153
  simp only [CollatzResearch.WordTrace]
  refine ⟨171866339297681927506365113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114577559531787951670910075 171866339297681927506365113)
  ·
    refine ⟨128899754473261445629773835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171866339297681927506365113 128899754473261445629773835)
    ·
      refine ⟨193349631709892168444660753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128899754473261445629773835 193349631709892168444660753)
      ·
        refine ⟨145012223782419126333495565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193349631709892168444660753 145012223782419126333495565)
        ·
          refine ⟨54379583918407172375060837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145012223782419126333495565 54379583918407172375060837)
          ·
            refine ⟨10196171984701344820323907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54379583918407172375060837 10196171984701344820323907)
            ·
              refine ⟨15294257977052017230485861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10196171984701344820323907 15294257977052017230485861)
              ·
                refine ⟨2867673370697253230716099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15294257977052017230485861 2867673370697253230716099)
                ·
                  refine ⟨4301510056045879846074149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867673370697253230716099 4301510056045879846074149)
                  ·
                    refine ⟨806533135508602471138903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4301510056045879846074149 806533135508602471138903)
                    ·
                      rfl

theorem cell23_4712153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4, 1, 4].length) (baseStart_4712153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712153 prefixEnd_4712153 := by exact prefixLift 4712153
  have htrace : WordTrace (prefixWord ++ tailWord_4712153) baseStart_4712153 baseEnd_4712153 := by
    simpa [prefixWord, tailWord_4712153, baseEnd_4712153] using wordTrace_append hprefix tailTrace_4712153
  have hstable : (prefixWord ++ tailWord_4712153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712153).length < 2 ^ (prefixWord ++ tailWord_4712153).sum := by decide
  have hdescent : baseEnd_4712153 < baseStart_4712153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712179 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 3, 5]
def baseStart_4712179 : Nat := 118140960795 + 4712179 * 2 ^ 59
def prefixEnd_4712179 : Nat := 4983230072969 + 3 ^ 40 * 4712179 * 2
def baseEnd_4712179 : Nat := 806537585674274770563863

theorem tailTrace_4712179 : CollatzResearch.WordTrace tailWord_4712179 prefixEnd_4712179 806537585674274770563863 := by
  unfold tailWord_4712179
  simp only [CollatzResearch.WordTrace]
  refine ⟨171867287595587733946811591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114578191730391822631207727 171867287595587733946811591)
  ·
    refine ⟨257800931393381600920217387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171867287595587733946811591 257800931393381600920217387)
    ·
      refine ⟨386701397090072401380326081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257800931393381600920217387 386701397090072401380326081)
      ·
        refine ⟨290026047817554301035244561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386701397090072401380326081 290026047817554301035244561)
        ·
          refine ⟨217519535863165725776433421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290026047817554301035244561 217519535863165725776433421)
          ·
            refine ⟨81569825948687147166162533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217519535863165725776433421 81569825948687147166162533)
            ·
              refine ⟨15294342365378840093655475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81569825948687147166162533 15294342365378840093655475)
              ·
                refine ⟨22941513548068260140483213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15294342365378840093655475 22941513548068260140483213)
                ·
                  refine ⟨8603067580525597552681205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22941513548068260140483213 8603067580525597552681205)
                  ·
                    refine ⟨806537585674274770563863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8603067580525597552681205 806537585674274770563863)
                    ·
                      rfl

theorem cell23_4712179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 5].length) (baseStart_4712179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712179 prefixEnd_4712179 := by exact prefixLift 4712179
  have htrace : WordTrace (prefixWord ++ tailWord_4712179) baseStart_4712179 baseEnd_4712179 := by
    simpa [prefixWord, tailWord_4712179, baseEnd_4712179] using wordTrace_append hprefix tailTrace_4712179
  have hstable : (prefixWord ++ tailWord_4712179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712179).length < 2 ^ (prefixWord ++ tailWord_4712179).sum := by decide
  have hdescent : baseEnd_4712179 < baseStart_4712179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712180 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_4712180 : Nat := 118140960795 + 4712180 * 2 ^ 59
def prefixEnd_4712180 : Nat := 4983230072969 + 3 ^ 40 * 4712180 * 2
def baseEnd_4712180 : Nat := 2419613270503478807779085

theorem tailTrace_4712180 : CollatzResearch.WordTrace tailWord_4712180 prefixEnd_4712180 2419613270503478807779085 := by
  unfold tailWord_4712180
  simp only [CollatzResearch.WordTrace]
  refine ⟨85933662034292055558798997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114578216045722740745065329 85933662034292055558798997)
  ·
    refine ⟨4028140407857440104318703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 85933662034292055558798997 4028140407857440104318703)
    ·
      refine ⟨6042210611786160156478055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4028140407857440104318703 6042210611786160156478055)
      ·
        refine ⟨9063315917679240234717083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6042210611786160156478055 9063315917679240234717083)
        ·
          refine ⟨13594973876518860352075625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9063315917679240234717083 13594973876518860352075625)
          ·
            refine ⟨10196230407389145264056719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13594973876518860352075625 10196230407389145264056719)
            ·
              refine ⟨15294345611083717896085079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10196230407389145264056719 15294345611083717896085079)
              ·
                refine ⟨22941518416625576844127619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15294345611083717896085079 22941518416625576844127619)
                ·
                  refine ⟨34412277624938365266191429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22941518416625576844127619 34412277624938365266191429)
                  ·
                    refine ⟨6452302054675943487410893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34412277624938365266191429 6452302054675943487410893)
                    ·
                      refine ⟨2419613270503478807779085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6452302054675943487410893 2419613270503478807779085)
                      ·
                        rfl

theorem cell23_4712180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_4712180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712180 prefixEnd_4712180 := by exact prefixLift 4712180
  have htrace : WordTrace (prefixWord ++ tailWord_4712180) baseStart_4712180 baseEnd_4712180 := by
    simpa [prefixWord, tailWord_4712180, baseEnd_4712180] using wordTrace_append hprefix tailTrace_4712180
  have hstable : (prefixWord ++ tailWord_4712180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712180).length < 2 ^ (prefixWord ++ tailWord_4712180).sum := by decide
  have hdescent : baseEnd_4712180 < baseStart_4712180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712210 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_4712210 : Nat := 118140960795 + 4712210 * 2 ^ 59
def prefixEnd_4712210 : Nat := 4983230072969 + 3 ^ 40 * 4712210 * 2
def baseEnd_4712210 : Nat := 2419628674923113690403947

theorem tailTrace_4712210 : CollatzResearch.WordTrace tailWord_4712210 prefixEnd_4712210 2419628674923113690403947 := by
  unfold tailWord_4712210
  simp only [CollatzResearch.WordTrace]
  refine ⟨42967104564618856560297521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114578945505650284160793389 42967104564618856560297521)
  ·
    refine ⟨32225328423464142420223141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42967104564618856560297521 32225328423464142420223141)
    ·
      refine ⟨6042249079399526703791839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32225328423464142420223141 6042249079399526703791839)
      ·
        refine ⟨9063373619099290055687759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6042249079399526703791839 9063373619099290055687759)
        ·
          refine ⟨13595060428648935083531639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9063373619099290055687759 13595060428648935083531639)
          ·
            refine ⟨20392590642973402625297459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13595060428648935083531639 20392590642973402625297459)
            ·
              refine ⟨30588885964460103937946189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20392590642973402625297459 30588885964460103937946189)
              ·
                refine ⟨11470832236672538976729821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30588885964460103937946189 11470832236672538976729821)
                ·
                  refine ⟨4301562088752202116273683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11470832236672538976729821 4301562088752202116273683)
                  ·
                    refine ⟨6452343133128303174410525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4301562088752202116273683 6452343133128303174410525)
                    ·
                      refine ⟨2419628674923113690403947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6452343133128303174410525 2419628674923113690403947)
                      ·
                        rfl

theorem cell23_4712210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_4712210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712210 prefixEnd_4712210 := by exact prefixLift 4712210
  have htrace : WordTrace (prefixWord ++ tailWord_4712210) baseStart_4712210 baseEnd_4712210 := by
    simpa [prefixWord, tailWord_4712210, baseEnd_4712210] using wordTrace_append hprefix tailTrace_4712210
  have hstable : (prefixWord ++ tailWord_4712210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712210).length < 2 ^ (prefixWord ++ tailWord_4712210).sum := by decide
  have hdescent : baseEnd_4712210 < baseStart_4712210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712219 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 5]
def baseStart_4712219 : Nat := 118140960795 + 4712219 * 2 ^ 59
def prefixEnd_4712219 : Nat := 4983230072969 + 3 ^ 40 * 4712219 * 2
def baseEnd_4712219 : Nat := 2419633296249004155191405

theorem tailTrace_4712219 : CollatzResearch.WordTrace tailWord_4712219 prefixEnd_4712219 2419633296249004155191405 := by
  unfold tailWord_4712219
  simp only [CollatzResearch.WordTrace]
  refine ⟨171868746515442820778267711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114579164343628547185511807 171868746515442820778267711)
  ·
    refine ⟨257803119773164231167401567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171868746515442820778267711 257803119773164231167401567)
    ·
      refine ⟨386704679659746346751102351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257803119773164231167401567 386704679659746346751102351)
      ·
        refine ⟨580057019489619520126653527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386704679659746346751102351 580057019489619520126653527)
        ·
          refine ⟨870085529234429280189980291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580057019489619520126653527 870085529234429280189980291)
          ·
            refine ⟨1305128293851643920284970437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870085529234429280189980291 1305128293851643920284970437)
            ·
              refine ⟨244711555097183235053431957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1305128293851643920284970437 244711555097183235053431957)
              ·
                refine ⟨11470854145180464143129623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 244711555097183235053431957 11470854145180464143129623)
                ·
                  refine ⟨17206281217770696214694435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11470854145180464143129623 17206281217770696214694435)
                  ·
                    refine ⟨25809421826656044322041653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17206281217770696214694435 25809421826656044322041653)
                    ·
                      refine ⟨2419633296249004155191405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25809421826656044322041653 2419633296249004155191405)
                      ·
                        rfl

theorem cell23_4712219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 5].length) (baseStart_4712219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712219 prefixEnd_4712219 := by exact prefixLift 4712219
  have htrace : WordTrace (prefixWord ++ tailWord_4712219) baseStart_4712219 baseEnd_4712219 := by
    simpa [prefixWord, tailWord_4712219, baseEnd_4712219] using wordTrace_append hprefix tailTrace_4712219
  have hstable : (prefixWord ++ tailWord_4712219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712219).length < 2 ^ (prefixWord ++ tailWord_4712219).sum := by decide
  have hdescent : baseEnd_4712219 < baseStart_4712219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712244 : List Nat := [2, 5, 1, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_4712244 : Nat := 118140960795 + 4712244 * 2 ^ 59
def prefixEnd_4712244 : Nat := 4983230072969 + 3 ^ 40 * 4712244 * 2
def baseEnd_4712244 : Nat := 2419646133265366557378791

theorem tailTrace_4712244 : CollatzResearch.WordTrace tailWord_4712244 prefixEnd_4712244 2419646133265366557378791 := by
  unfold tailWord_4712244
  simp only [CollatzResearch.WordTrace]
  refine ⟨85934829170176125023963893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114579772226901500031951857 85934829170176125023963893)
  ·
    refine ⟨8056390234704011720996615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85934829170176125023963893 8056390234704011720996615)
    ·
      refine ⟨12084585352056017581494923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8056390234704011720996615 12084585352056017581494923)
      ·
        refine ⟨18126878028084026372242385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12084585352056017581494923 18126878028084026372242385)
        ·
          refine ⟨13595158521063019779181789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18126878028084026372242385 13595158521063019779181789)
          ·
            refine ⟨5098184445398632417193171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13595158521063019779181789 5098184445398632417193171)
            ·
              refine ⟨7647276668097948625789757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5098184445398632417193171 7647276668097948625789757)
              ·
                refine ⟨2867728750536730734671159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7647276668097948625789757 2867728750536730734671159)
                ·
                  refine ⟨4301593125805096102006739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867728750536730734671159 4301593125805096102006739)
                  ·
                    refine ⟨6452389688707644153010109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4301593125805096102006739 6452389688707644153010109)
                    ·
                      refine ⟨2419646133265366557378791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6452389688707644153010109 2419646133265366557378791)
                      ·
                        rfl

theorem cell23_4712244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_4712244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712244 prefixEnd_4712244 := by exact prefixLift 4712244
  have htrace : WordTrace (prefixWord ++ tailWord_4712244) baseStart_4712244 baseEnd_4712244 := by
    simpa [prefixWord, tailWord_4712244, baseEnd_4712244] using wordTrace_append hprefix tailTrace_4712244
  have hstable : (prefixWord ++ tailWord_4712244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712244).length < 2 ^ (prefixWord ++ tailWord_4712244).sum := by decide
  have hdescent : baseEnd_4712244 < baseStart_4712244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712253 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_4712253 : Nat := 118140960795 + 4712253 * 2 ^ 59
def prefixEnd_4712253 : Nat := 4983230072969 + 3 ^ 40 * 4712253 * 2
def baseEnd_4712253 : Nat := 2419650754591257022166249

theorem tailTrace_4712253 : CollatzResearch.WordTrace tailWord_4712253 prefixEnd_4712253 2419650754591257022166249 := by
  unfold tailWord_4712253
  simp only [CollatzResearch.WordTrace]
  refine ⟨171869986597319644585005413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114579991064879763056670275 171869986597319644585005413)
  ·
    refine ⟨32225622486997433359688515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171869986597319644585005413 32225622486997433359688515)
    ·
      refine ⟨48338433730496150039532773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32225622486997433359688515 48338433730496150039532773)
      ·
        refine ⟨9063456324468028132412395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48338433730496150039532773 9063456324468028132412395)
        ·
          refine ⟨13595184486702042198618593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9063456324468028132412395 13595184486702042198618593)
          ·
            refine ⟨10196388365026531648963945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13595184486702042198618593 10196388365026531648963945)
            ·
              refine ⟨7647291273769898736722959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10196388365026531648963945 7647291273769898736722959)
              ·
                refine ⟨11470936910654848105084439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7647291273769898736722959 11470936910654848105084439)
                ·
                  refine ⟨17206405365982272157626659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11470936910654848105084439 17206405365982272157626659)
                  ·
                    refine ⟨25809608048973408236439989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17206405365982272157626659 25809608048973408236439989)
                    ·
                      refine ⟨2419650754591257022166249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25809608048973408236439989 2419650754591257022166249)
                      ·
                        rfl

theorem cell23_4712253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_4712253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712253 prefixEnd_4712253 := by exact prefixLift 4712253
  have htrace : WordTrace (prefixWord ++ tailWord_4712253) baseStart_4712253 baseEnd_4712253 := by
    simpa [prefixWord, tailWord_4712253, baseEnd_4712253] using wordTrace_append hprefix tailTrace_4712253
  have hstable : (prefixWord ++ tailWord_4712253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712253).length < 2 ^ (prefixWord ++ tailWord_4712253).sum := by decide
  have hdescent : baseEnd_4712253 < baseStart_4712253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712299 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 4, 6]
def baseStart_4712299 : Nat := 118140960795 + 4712299 * 2 ^ 59
def prefixEnd_4712299 : Nat := 4983230072969 + 3 ^ 40 * 4712299 * 2
def baseEnd_4712299 : Nat := 806558124900454614063679

theorem tailTrace_4712299 : CollatzResearch.WordTrace tailWord_4712299 prefixEnd_4712299 806558124900454614063679 := by
  unfold tailWord_4712299
  simp only [CollatzResearch.WordTrace]
  refine ⟨171871664355152994441179951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114581109570101996294119967 171871664355152994441179951)
  ·
    refine ⟨257807496532729491661769927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171871664355152994441179951 257807496532729491661769927)
    ·
      refine ⟨386711244799094237492654891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257807496532729491661769927 386711244799094237492654891)
      ·
        refine ⟨580066867198641356238982337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386711244799094237492654891 580066867198641356238982337)
        ·
          refine ⟨435050150398981017179236753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 580066867198641356238982337 435050150398981017179236753)
          ·
            refine ⟨326287612799235762884427565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435050150398981017179236753 326287612799235762884427565)
            ·
              refine ⟨122357854799713411081660337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326287612799235762884427565 122357854799713411081660337)
              ·
                refine ⟨91768391099785058311245253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122357854799713411081660337 91768391099785058311245253)
                ·
                  refine ⟨17206573331209698433358485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91768391099785058311245253 17206573331209698433358485)
                  ·
                    refine ⟨806558124900454614063679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17206573331209698433358485 806558124900454614063679)
                    ·
                      rfl

theorem cell23_4712299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 6].length) (baseStart_4712299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712299 prefixEnd_4712299 := by exact prefixLift 4712299
  have htrace : WordTrace (prefixWord ++ tailWord_4712299) baseStart_4712299 baseEnd_4712299 := by
    simpa [prefixWord, tailWord_4712299, baseEnd_4712299] using wordTrace_append hprefix tailTrace_4712299
  have hstable : (prefixWord ++ tailWord_4712299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712299).length < 2 ^ (prefixWord ++ tailWord_4712299).sum := by decide
  have hdescent : baseEnd_4712299 < baseStart_4712299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712318 : List Nat := [4, 2, 3, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4712318 : Nat := 118140960795 + 4712318 * 2 ^ 59
def prefixEnd_4712318 : Nat := 4983230072969 + 3 ^ 40 * 4712318 * 2
def baseEnd_4712318 : Nat := 2419684130833799267853451

theorem tailTrace_4712318 : CollatzResearch.WordTrace tailWord_4712318 prefixEnd_4712318 2419684130833799267853451 := by
  unfold tailWord_4712318
  simp only [CollatzResearch.WordTrace]
  refine ⟨21484044667760520085765201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114581571561389440457414405 21484044667760520085765201)
  ·
    refine ⟨16113033500820390064323901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21484044667760520085765201 16113033500820390064323901)
    ·
      refine ⟨6042387562807646274121463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16113033500820390064323901 6042387562807646274121463)
      ·
        refine ⟨9063581344211469411182195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6042387562807646274121463 9063581344211469411182195)
        ·
          refine ⟨13595372016317204116773293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9063581344211469411182195 13595372016317204116773293)
          ·
            refine ⟨5098264506118951543789985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13595372016317204116773293 5098264506118951543789985)
            ·
              refine ⟨3823698379589213657842489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5098264506118951543789985 3823698379589213657842489)
              ·
                refine ⟨2867773784691910243381867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3823698379589213657842489 2867773784691910243381867)
                ·
                  refine ⟨4301660677037865365072801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867773784691910243381867 4301660677037865365072801)
                  ·
                    refine ⟨3226245507778399023804601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4301660677037865365072801 3226245507778399023804601)
                    ·
                      refine ⟨2419684130833799267853451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3226245507778399023804601 2419684130833799267853451)
                      ·
                        rfl

theorem cell23_4712318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4712318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712318 prefixEnd_4712318 := by exact prefixLift 4712318
  have htrace : WordTrace (prefixWord ++ tailWord_4712318) baseStart_4712318 baseEnd_4712318 := by
    simpa [prefixWord, tailWord_4712318, baseEnd_4712318] using wordTrace_append hprefix tailTrace_4712318
  have hstable : (prefixWord ++ tailWord_4712318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712318).length < 2 ^ (prefixWord ++ tailWord_4712318).sum := by decide
  have hdescent : baseEnd_4712318 < baseStart_4712318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712319 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_4712319 : Nat := 118140960795 + 4712319 * 2 ^ 59
def prefixEnd_4712319 : Nat := 4983230072969 + 3 ^ 40 * 4712319 * 2
def baseEnd_4712319 : Nat := 2419684644314453763940945

theorem tailTrace_4712319 : CollatzResearch.WordTrace tailWord_4712319 prefixEnd_4712319 2419684644314453763940945 := by
  unfold tailWord_4712319
  simp only [CollatzResearch.WordTrace]
  refine ⟨171872393815080537856908011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114581595876720358571272007 171872393815080537856908011)
  ·
    refine ⟨257808590722620806785362017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171872393815080537856908011 257808590722620806785362017)
    ·
      refine ⟨193356443041965605089021513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257808590722620806785362017 193356443041965605089021513)
      ·
        refine ⟨145017332281474203816766135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193356443041965605089021513 145017332281474203816766135)
        ·
          refine ⟨217525998422211305725149203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145017332281474203816766135 217525998422211305725149203)
          ·
            refine ⟨326288997633316958587723805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217525998422211305725149203 326288997633316958587723805)
            ·
              refine ⟨122358374112493859470396427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326288997633316958587723805 122358374112493859470396427)
              ·
                refine ⟨183537561168740789205594641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122358374112493859470396427 183537561168740789205594641)
                ·
                  refine ⟨137653170876555591904195981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183537561168740789205594641 137653170876555591904195981)
                  ·
                    refine ⟨51619939078708346964073493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 137653170876555591904195981 51619939078708346964073493)
                    ·
                      refine ⟨2419684644314453763940945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51619939078708346964073493 2419684644314453763940945)
                      ·
                        rfl

theorem cell23_4712319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_4712319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712319 prefixEnd_4712319 := by exact prefixLift 4712319
  have htrace : WordTrace (prefixWord ++ tailWord_4712319) baseStart_4712319 baseEnd_4712319 := by
    simpa [prefixWord, tailWord_4712319, baseEnd_4712319] using wordTrace_append hprefix tailTrace_4712319
  have hstable : (prefixWord ++ tailWord_4712319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712319).length < 2 ^ (prefixWord ++ tailWord_4712319).sum := by decide
  have hdescent : baseEnd_4712319 < baseStart_4712319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712339 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 7]
def baseStart_4712339 : Nat := 118140960795 + 4712339 * 2 ^ 59
def prefixEnd_4712339 : Nat := 4983230072969 + 3 ^ 40 * 4712339 * 2
def baseEnd_4712339 : Nat := 2419694913927543685690853

theorem tailTrace_4712339 : CollatzResearch.WordTrace tailWord_4712339 prefixEnd_4712339 2419694913927543685690853 := by
  unfold tailWord_4712339
  simp only [CollatzResearch.WordTrace]
  refine ⟨171873123275008081272636071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114582082183338720848424047 171873123275008081272636071)
  ·
    refine ⟨257809684912512121908954107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171873123275008081272636071 257809684912512121908954107)
    ·
      refine ⟨386714527368768182863431161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257809684912512121908954107 386714527368768182863431161)
      ·
        refine ⟨290035895526576137147573371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 386714527368768182863431161 290035895526576137147573371)
        ·
          refine ⟨435053843289864205721360057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290035895526576137147573371 435053843289864205721360057)
          ·
            refine ⟨326290382467398154291020043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435053843289864205721360057 326290382467398154291020043)
            ·
              refine ⟨489435573701097231436530065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326290382467398154291020043 489435573701097231436530065)
              ·
                refine ⟨367076680275822923577397549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 489435573701097231436530065 367076680275822923577397549)
                ·
                  refine ⟨137653755103433596341524081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 367076680275822923577397549 137653755103433596341524081)
                  ·
                    refine ⟨103240316327575197256143061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 137653755103433596341524081 103240316327575197256143061)
                    ·
                      refine ⟨2419694913927543685690853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103240316327575197256143061 2419694913927543685690853)
                      ·
                        rfl

theorem cell23_4712339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_4712339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712339 prefixEnd_4712339 := by exact prefixLift 4712339
  have htrace : WordTrace (prefixWord ++ tailWord_4712339) baseStart_4712339 baseEnd_4712339 := by
    simpa [prefixWord, tailWord_4712339, baseEnd_4712339] using wordTrace_append hprefix tailTrace_4712339
  have hstable : (prefixWord ++ tailWord_4712339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712339).length < 2 ^ (prefixWord ++ tailWord_4712339).sum := by decide
  have hdescent : baseEnd_4712339 < baseStart_4712339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712340 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_4712340 : Nat := 118140960795 + 4712340 * 2 ^ 59
def prefixEnd_4712340 : Nat := 4983230072969 + 3 ^ 40 * 4712340 * 2
def baseEnd_4712340 : Nat := 2419695427408198181778349

theorem tailTrace_4712340 : CollatzResearch.WordTrace tailWord_4712340 prefixEnd_4712340 2419695427408198181778349 := by
  unfold tailWord_4712340
  simp only [CollatzResearch.WordTrace]
  refine ⟨85936579874002229221711237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114582106498669638962281649 85936579874002229221711237)
  ·
    refine ⟨16113108726375417979070857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85936579874002229221711237 16113108726375417979070857)
    ·
      refine ⟨12084831544781563484303143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16113108726375417979070857 12084831544781563484303143)
      ·
        refine ⟨18127247317172345226454715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12084831544781563484303143 18127247317172345226454715)
        ·
          refine ⟨27190870975758517839682073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18127247317172345226454715 27190870975758517839682073)
          ·
            refine ⟨20393153231818888379761555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27190870975758517839682073 20393153231818888379761555)
            ·
              refine ⟨30589729847728332569642333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20393153231818888379761555 30589729847728332569642333)
              ·
                refine ⟨11471148692898124713615875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30589729847728332569642333 11471148692898124713615875)
                ·
                  refine ⟨17206723039347187070423813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11471148692898124713615875 17206723039347187070423813)
                  ·
                    refine ⟨3226260569877597575704465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17206723039347187070423813 3226260569877597575704465)
                    ·
                      refine ⟨2419695427408198181778349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3226260569877597575704465 2419695427408198181778349)
                      ·
                        rfl

theorem cell23_4712340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_4712340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712340 prefixEnd_4712340 := by exact prefixLift 4712340
  have htrace : WordTrace (prefixWord ++ tailWord_4712340) baseStart_4712340 baseEnd_4712340 := by
    simpa [prefixWord, tailWord_4712340, baseEnd_4712340] using wordTrace_append hprefix tailTrace_4712340
  have hstable : (prefixWord ++ tailWord_4712340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712340).length < 2 ^ (prefixWord ++ tailWord_4712340).sum := by decide
  have hdescent : baseEnd_4712340 < baseStart_4712340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712346 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 9]
def baseStart_4712346 : Nat := 118140960795 + 4712346 * 2 ^ 59
def prefixEnd_4712346 : Nat := 4983230072969 + 3 ^ 40 * 4712346 * 2
def baseEnd_4712346 : Nat := 268855389810236128700369

theorem tailTrace_4712346 : CollatzResearch.WordTrace tailWord_4712346 prefixEnd_4712346 268855389810236128700369 := by
  unfold tailWord_4712346
  simp only [CollatzResearch.WordTrace]
  refine ⟨42968344646495680367035223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 114582252390655147645427261 42968344646495680367035223)
  ·
    refine ⟨64452516969743520550552835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42968344646495680367035223 64452516969743520550552835)
    ·
      refine ⟨96678775454615280825829253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64452516969743520550552835 96678775454615280825829253)
      ·
        refine ⟨18127270397740365154842985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96678775454615280825829253 18127270397740365154842985)
        ·
          refine ⟨13595452798305273866132239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18127270397740365154842985 13595452798305273866132239)
          ·
            refine ⟨20393179197457910799198359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13595452798305273866132239 20393179197457910799198359)
            ·
              refine ⟨30589768796186866198797539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20393179197457910799198359 30589768796186866198797539)
              ·
                refine ⟨45884653194280299298196309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30589768796186866198797539 45884653194280299298196309)
                ·
                  refine ⟨268855389810236128700369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45884653194280299298196309 268855389810236128700369)
                  ·
                    rfl

theorem cell23_4712346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_4712346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712346 prefixEnd_4712346 := by exact prefixLift 4712346
  have htrace : WordTrace (prefixWord ++ tailWord_4712346) baseStart_4712346 baseEnd_4712346 := by
    simpa [prefixWord, tailWord_4712346, baseEnd_4712346] using wordTrace_append hprefix tailTrace_4712346
  have hstable : (prefixWord ++ tailWord_4712346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712346).length < 2 ^ (prefixWord ++ tailWord_4712346).sum := by decide
  have hdescent : baseEnd_4712346 < baseStart_4712346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712373 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_4712373 : Nat := 118140960795 + 4712373 * 2 ^ 59
def prefixEnd_4712373 : Nat := 4983230072969 + 3 ^ 40 * 4712373 * 2
def baseEnd_4712373 : Nat := 2419712372269796552665697

theorem tailTrace_4712373 : CollatzResearch.WordTrace tailWord_4712373 prefixEnd_4712373 2419712372269796552665697 := by
  unfold tailWord_4712373
  simp only [CollatzResearch.WordTrace]
  refine ⟨171874363356884905079373773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114582908904589936719582515 171874363356884905079373773)
  ·
    refine ⟨64452886258831839404765165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171874363356884905079373773 64452886258831839404765165)
    ·
      refine ⟨24169832347061939776786937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64452886258831839404765165 24169832347061939776786937)
      ·
        refine ⟨18127374260296454832590203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24169832347061939776786937 18127374260296454832590203)
        ·
          refine ⟨27191061390444682248885305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18127374260296454832590203 27191061390444682248885305)
          ·
            refine ⟨20393296042833511686663979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27191061390444682248885305 20393296042833511686663979)
            ·
              refine ⟨30589944064250267529995969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20393296042833511686663979 30589944064250267529995969)
              ·
                refine ⟨22942458048187700647496977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30589944064250267529995969 22942458048187700647496977)
                ·
                  refine ⟨17206843536140775485622733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22942458048187700647496977 17206843536140775485622733)
                  ·
                    refine ⟨6452566326052790807108525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17206843536140775485622733 6452566326052790807108525)
                    ·
                      refine ⟨2419712372269796552665697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6452566326052790807108525 2419712372269796552665697)
                      ·
                        rfl

theorem cell23_4712373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_4712373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712373 prefixEnd_4712373 := by exact prefixLift 4712373
  have htrace : WordTrace (prefixWord ++ tailWord_4712373) baseStart_4712373 baseEnd_4712373 := by
    simpa [prefixWord, tailWord_4712373, baseEnd_4712373] using wordTrace_append hprefix tailTrace_4712373
  have hstable : (prefixWord ++ tailWord_4712373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712373).length < 2 ^ (prefixWord ++ tailWord_4712373).sum := by decide
  have hdescent : baseEnd_4712373 < baseStart_4712373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712376 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 4, 5]
def baseStart_4712376 : Nat := 118140960795 + 4712376 * 2 ^ 59
def prefixEnd_4712376 : Nat := 4983230072969 + 3 ^ 40 * 4712376 * 2
def baseEnd_4712376 : Nat := 806571304237253346976061

theorem tailTrace_4712376 : CollatzResearch.WordTrace tailWord_4712376 prefixEnd_4712376 806571304237253346976061 := by
  unfold tailWord_4712376
  simp only [CollatzResearch.WordTrace]
  refine ⟨85937236387937018295866491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114582981850582691061155321 85937236387937018295866491)
  ·
    refine ⟨128905854581905527443799737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85937236387937018295866491 128905854581905527443799737)
    ·
      refine ⟨96679390936429145582849803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128905854581905527443799737 96679390936429145582849803)
      ·
        refine ⟨145019086404643718374274705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96679390936429145582849803 145019086404643718374274705)
        ·
          refine ⟨108764314803482788780706029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145019086404643718374274705 108764314803482788780706029)
          ·
            refine ⟨40786618051306045792764761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108764314803482788780706029 40786618051306045792764761)
            ·
              refine ⟨30589963538479534344573571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40786618051306045792764761 30589963538479534344573571)
              ·
                refine ⟨45884945307719301516860357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30589963538479534344573571 45884945307719301516860357)
                ·
                  refine ⟨8603427245197369034411317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45884945307719301516860357 8603427245197369034411317)
                  ·
                    refine ⟨806571304237253346976061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8603427245197369034411317 806571304237253346976061)
                    ·
                      rfl

theorem cell23_4712376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_4712376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712376 prefixEnd_4712376 := by exact prefixLift 4712376
  have htrace : WordTrace (prefixWord ++ tailWord_4712376) baseStart_4712376 baseEnd_4712376 := by
    simpa [prefixWord, tailWord_4712376, baseEnd_4712376] using wordTrace_append hprefix tailTrace_4712376
  have hstable : (prefixWord ++ tailWord_4712376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712376).length < 2 ^ (prefixWord ++ tailWord_4712376).sum := by decide
  have hdescent : baseEnd_4712376 < baseStart_4712376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712380 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 7]
def baseStart_4712380 : Nat := 118140960795 + 4712380 * 2 ^ 59
def prefixEnd_4712380 : Nat := 4983230072969 + 3 ^ 40 * 4712380 * 2
def baseEnd_4712380 : Nat := 268857329626042002808685

theorem tailTrace_4712380 : CollatzResearch.WordTrace tailWord_4712380 prefixEnd_4712380 268857329626042002808685 := by
  unfold tailWord_4712380
  simp only [CollatzResearch.WordTrace]
  refine ⟨85937309333929772637439297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114583079111906363516585729 85937309333929772637439297)
  ·
    refine ⟨64452982000447329478079473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85937309333929772637439297 64452982000447329478079473)
    ·
      refine ⟨48339736500335497108559605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64452982000447329478079473 48339736500335497108559605)
      ·
        refine ⟨4531850296906452853927463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48339736500335497108559605 4531850296906452853927463)
        ·
          refine ⟨6797775445359679280891195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4531850296906452853927463 6797775445359679280891195)
          ·
            refine ⟨10196663168039518921336793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6797775445359679280891195 10196663168039518921336793)
            ·
              refine ⟨7647497376029639191002595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10196663168039518921336793 7647497376029639191002595)
              ·
                refine ⟨11471246064044458786503893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7647497376029639191002595 11471246064044458786503893)
                ·
                  refine ⟨268857329626042002808685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11471246064044458786503893 268857329626042002808685)
                  ·
                    rfl

theorem cell23_4712380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_4712380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712380 prefixEnd_4712380 := by exact prefixLift 4712380
  have htrace : WordTrace (prefixWord ++ tailWord_4712380) baseStart_4712380 baseEnd_4712380 := by
    simpa [prefixWord, tailWord_4712380, baseEnd_4712380] using wordTrace_append hprefix tailTrace_4712380
  have hstable : (prefixWord ++ tailWord_4712380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712380).length < 2 ^ (prefixWord ++ tailWord_4712380).sum := by decide
  have hdescent : baseEnd_4712380 < baseStart_4712380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712430 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_4712430 : Nat := 118140960795 + 4712430 * 2 ^ 59
def prefixEnd_4712430 : Nat := 4983230072969 + 3 ^ 40 * 4712430 * 2
def baseEnd_4712430 : Nat := 2419741640667102829652935

theorem tailTrace_4712430 : CollatzResearch.WordTrace tailWord_4712430 prefixEnd_4712430 2419741640667102829652935 := by
  unfold tailWord_4712430
  simp only [CollatzResearch.WordTrace]
  refine ⟨21484555289709800476774843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114584294878452269209465829 21484555289709800476774843)
  ·
    refine ⟨32226832934564700715162265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21484555289709800476774843 32226832934564700715162265)
    ·
      refine ⟨24170124700923525536371699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32226832934564700715162265 24170124700923525536371699)
      ·
        refine ⟨36255187051385288304557549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24170124700923525536371699 36255187051385288304557549)
        ·
          refine ⟨13595695144269483114209081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36255187051385288304557549 13595695144269483114209081)
          ·
            refine ⟨10196771358202112335656811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13595695144269483114209081 10196771358202112335656811)
            ·
              refine ⟨15295157037303168503485217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10196771358202112335656811 15295157037303168503485217)
              ·
                refine ⟨11471367777977376377613913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15295157037303168503485217 11471367777977376377613913)
                ·
                  refine ⟨8603525833483032283210435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11471367777977376377613913 8603525833483032283210435)
                  ·
                    refine ⟨12905288750224548424815653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8603525833483032283210435 12905288750224548424815653)
                    ·
                      refine ⟨2419741640667102829652935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12905288750224548424815653 2419741640667102829652935)
                      ·
                        rfl

theorem cell23_4712430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_4712430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712430 prefixEnd_4712430 := by exact prefixLift 4712430
  have htrace : WordTrace (prefixWord ++ tailWord_4712430) baseStart_4712430 baseEnd_4712430 := by
    simpa [prefixWord, tailWord_4712430, baseEnd_4712430] using wordTrace_append hprefix tailTrace_4712430
  have hstable : (prefixWord ++ tailWord_4712430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712430).length < 2 ^ (prefixWord ++ tailWord_4712430).sum := by decide
  have hdescent : baseEnd_4712430 < baseStart_4712430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712440 : List Nat := [2, 1, 2, 1, 1, 3, 2, 6, 1, 4]
def baseStart_4712440 : Nat := 118140960795 + 4712440 * 2 ^ 59
def prefixEnd_4712440 : Nat := 4983230072969 + 3 ^ 40 * 4712440 * 2
def baseEnd_4712440 : Nat := 806582258491215930175963

theorem tailTrace_4712440 : CollatzResearch.WordTrace tailWord_4712440 prefixEnd_4712440 806582258491215930175963 := by
  unfold tailWord_4712440
  simp only [CollatzResearch.WordTrace]
  refine ⟨85938403523821087761031387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114584538031761450348041849 85938403523821087761031387)
  ·
    refine ⟨128907605285731631641547081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85938403523821087761031387 128907605285731631641547081)
    ·
      refine ⟨96680703964298723731160311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128907605285731631641547081 96680703964298723731160311)
      ·
        refine ⟨145021055946448085596740467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96680703964298723731160311 145021055946448085596740467)
        ·
          refine ⟨217531583919672128395110701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145021055946448085596740467 217531583919672128395110701)
          ·
            refine ⟨81574343969877048148166513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217531583919672128395110701 81574343969877048148166513)
            ·
              refine ⟨61180757977407786111124885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81574343969877048148166513 61180757977407786111124885)
              ·
                refine ⟨2867848030190989973958979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61180757977407786111124885 2867848030190989973958979)
                ·
                  refine ⟨4301772045286484960938469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2867848030190989973958979 4301772045286484960938469)
                  ·
                    refine ⟨806582258491215930175963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4301772045286484960938469 806582258491215930175963)
                    ·
                      rfl

theorem cell23_4712440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_4712440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712440 prefixEnd_4712440 := by exact prefixLift 4712440
  have htrace : WordTrace (prefixWord ++ tailWord_4712440) baseStart_4712440 baseEnd_4712440 := by
    simpa [prefixWord, tailWord_4712440, baseEnd_4712440] using wordTrace_append hprefix tailTrace_4712440
  have hstable : (prefixWord ++ tailWord_4712440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712440).length < 2 ^ (prefixWord ++ tailWord_4712440).sum := by decide
  have hdescent : baseEnd_4712440 < baseStart_4712440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712453 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 6]
def baseStart_4712453 : Nat := 118140960795 + 4712453 * 2 ^ 59
def prefixEnd_4712453 : Nat := 4983230072969 + 3 ^ 40 * 4712453 * 2
def baseEnd_4712453 : Nat := 268861494524684026629481

theorem tailTrace_4712453 : CollatzResearch.WordTrace tailWord_4712453 prefixEnd_4712453 268861494524684026629481 := by
  unfold tailWord_4712453
  simp only [CollatzResearch.WordTrace]
  refine ⟨171877281196595078742286013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114584854131063385828190675 171877281196595078742286013)
  ·
    refine ⟨64453980448723154528357255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171877281196595078742286013 64453980448723154528357255)
    ·
      refine ⟨96680970673084731792535883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64453980448723154528357255 96680970673084731792535883)
      ·
        refine ⟨145021456009627097688803825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96680970673084731792535883 145021456009627097688803825)
        ·
          refine ⟨108766092007220323266602869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145021456009627097688803825 108766092007220323266602869)
          ·
            refine ⟨10196821125676905306244019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 108766092007220323266602869 10196821125676905306244019)
            ·
              refine ⟨15295231688515357959366029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10196821125676905306244019 15295231688515357959366029)
              ·
                refine ⟨5735711883193259234762261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15295231688515357959366029 5735711883193259234762261)
                ·
                  refine ⟨268861494524684026629481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5735711883193259234762261 268861494524684026629481)
                  ·
                    rfl

theorem cell23_4712453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 6].length) (baseStart_4712453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712453 prefixEnd_4712453 := by exact prefixLift 4712453
  have htrace : WordTrace (prefixWord ++ tailWord_4712453) baseStart_4712453 baseEnd_4712453 := by
    simpa [prefixWord, tailWord_4712453, baseEnd_4712453] using wordTrace_append hprefix tailTrace_4712453
  have hstable : (prefixWord ++ tailWord_4712453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712453).length < 2 ^ (prefixWord ++ tailWord_4712453).sum := by decide
  have hdescent : baseEnd_4712453 < baseStart_4712453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712487 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 6]
def baseStart_4712487 : Nat := 118140960795 + 4712487 * 2 ^ 59
def prefixEnd_4712487 : Nat := 4983230072969 + 3 ^ 40 * 4712487 * 2
def baseEnd_4712487 : Nat := 268863434340489900737797

theorem tailTrace_4712487 : CollatzResearch.WordTrace tailWord_4712487 prefixEnd_4712487 268863434340489900737797 := by
  unfold tailWord_4712487
  simp only [CollatzResearch.WordTrace]
  refine ⟨171878521278471902549023715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114585680852314601699349143 171878521278471902549023715)
  ·
    refine ⟨257817781917707853823535573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171878521278471902549023715 257817781917707853823535573)
    ·
      refine ⟨6042604263696277823989115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 257817781917707853823535573 6042604263696277823989115)
      ·
        refine ⟨9063906395544416735983673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6042604263696277823989115 9063906395544416735983673)
        ·
          refine ⟨6797929796658312551987755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9063906395544416735983673 6797929796658312551987755)
          ·
            refine ⟨10196894694987468827981633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6797929796658312551987755 10196894694987468827981633)
            ·
              refine ⟨7647671021240601620986225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10196894694987468827981633 7647671021240601620986225)
              ·
                refine ⟨5735753265930451215739669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7647671021240601620986225 5735753265930451215739669)
                ·
                  refine ⟨268863434340489900737797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5735753265930451215739669 268863434340489900737797)
                  ·
                    rfl

theorem cell23_4712487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 6].length) (baseStart_4712487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712487 prefixEnd_4712487 := by exact prefixLift 4712487
  have htrace : WordTrace (prefixWord ++ tailWord_4712487) baseStart_4712487 baseEnd_4712487 := by
    simpa [prefixWord, tailWord_4712487, baseEnd_4712487] using wordTrace_append hprefix tailTrace_4712487
  have hstable : (prefixWord ++ tailWord_4712487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712487).length < 2 ^ (prefixWord ++ tailWord_4712487).sum := by decide
  have hdescent : baseEnd_4712487 < baseStart_4712487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712503 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_4712503 : Nat := 118140960795 + 4712503 * 2 ^ 59
def prefixEnd_4712503 : Nat := 4983230072969 + 3 ^ 40 * 4712503 * 2
def baseEnd_4712503 : Nat := 2419779124754881044040099

theorem tailTrace_4712503 : CollatzResearch.WordTrace tailWord_4712503 prefixEnd_4712503 2419779124754881044040099 := by
  unfold tailWord_4712503
  simp only [CollatzResearch.WordTrace]
  refine ⟨171879104846413937281606163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114586069897609291521070775 171879104846413937281606163)
  ·
    refine ⟨257818657269620905922409245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171879104846413937281606163 257818657269620905922409245)
    ·
      refine ⟨96681996476107839720903467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257818657269620905922409245 96681996476107839720903467)
      ·
        refine ⟨145022994714161759581355201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96681996476107839720903467 145022994714161759581355201)
        ·
          refine ⟨108767246035621319686016401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145022994714161759581355201 108767246035621319686016401)
          ·
            refine ⟨81575434526715989764512301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108767246035621319686016401 81575434526715989764512301)
            ·
              refine ⟨30590787947518496161692113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81575434526715989764512301 30590787947518496161692113)
              ·
                refine ⟨22943090960638872121269085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30590787947518496161692113 22943090960638872121269085)
                ·
                  refine ⟨8603659110239577045475907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22943090960638872121269085 8603659110239577045475907)
                  ·
                    refine ⟨12905488665359365568213861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8603659110239577045475907 12905488665359365568213861)
                    ·
                      refine ⟨2419779124754881044040099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12905488665359365568213861 2419779124754881044040099)
                      ·
                        rfl

theorem cell23_4712503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_4712503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712503 prefixEnd_4712503 := by exact prefixLift 4712503
  have htrace : WordTrace (prefixWord ++ tailWord_4712503) baseStart_4712503 baseEnd_4712503 := by
    simpa [prefixWord, tailWord_4712503, baseEnd_4712503] using wordTrace_append hprefix tailTrace_4712503
  have hstable : (prefixWord ++ tailWord_4712503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712503).length < 2 ^ (prefixWord ++ tailWord_4712503).sum := by decide
  have hdescent : baseEnd_4712503 < baseStart_4712503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712534 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_4712534 : Nat := 118140960795 + 4712534 * 2 ^ 59
def prefixEnd_4712534 : Nat := 4983230072969 + 3 ^ 40 * 4712534 * 2
def baseEnd_4712534 : Nat := 806598347551723474250819

theorem tailTrace_4712534 : CollatzResearch.WordTrace tailWord_4712534 prefixEnd_4712534 806598347551723474250819 := by
  unfold tailWord_4712534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742514719331351848499041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114586823672867753050656437 10742514719331351848499041)
  ·
    refine ⟨8056886039498513886374281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10742514719331351848499041 8056886039498513886374281)
    ·
      refine ⟨6042664529623885414780711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8056886039498513886374281 6042664529623885414780711)
      ·
        refine ⟨9063996794435828122171067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6042664529623885414780711 9063996794435828122171067)
        ·
          refine ⟨13595995191653742183256601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9063996794435828122171067 13595995191653742183256601)
          ·
            refine ⟨10196996393740306637442451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13595995191653742183256601 10196996393740306637442451)
            ·
              refine ⟨15295494590610459956163677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10196996393740306637442451 15295494590610459956163677)
              ·
                refine ⟨5735810471478922483561379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15295494590610459956163677 5735810471478922483561379)
                ·
                  refine ⟨8603715707218383725342069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5735810471478922483561379 8603715707218383725342069)
                  ·
                    refine ⟨806598347551723474250819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8603715707218383725342069 806598347551723474250819)
                    ·
                      rfl

theorem cell23_4712534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_4712534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712534 prefixEnd_4712534 := by exact prefixLift 4712534
  have htrace : WordTrace (prefixWord ++ tailWord_4712534) baseStart_4712534 baseEnd_4712534 := by
    simpa [prefixWord, tailWord_4712534, baseEnd_4712534] using wordTrace_append hprefix tailTrace_4712534
  have hstable : (prefixWord ++ tailWord_4712534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712534).length < 2 ^ (prefixWord ++ tailWord_4712534).sum := by decide
  have hdescent : baseEnd_4712534 < baseStart_4712534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712577 : List Nat := [1, 2, 4, 2, 3, 2, 2, 7]
def baseStart_4712577 : Nat := 118140960795 + 4712577 * 2 ^ 59
def prefixEnd_4712577 : Nat := 4983230072969 + 3 ^ 40 * 4712577 * 2
def baseEnd_4712577 : Nat := 89622856382344953870917

theorem tailTrace_4712577 : CollatzResearch.WordTrace tailWord_4712577 prefixEnd_4712577 89622856382344953870917 := by
  unfold tailWord_4712577
  simp only [CollatzResearch.WordTrace]
  refine ⟨171881803848145847919799985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114587869232097231946533323 171881803848145847919799985)
  ·
    refine ⟨128911352886109385939849989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171881803848145847919799985 128911352886109385939849989)
    ·
      refine ⟨24170878666145509863721873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 128911352886109385939849989 24170878666145509863721873)
      ·
        refine ⟨18128158999609132397791405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24170878666145509863721873 18128158999609132397791405)
        ·
          refine ⟨6798059624853424649171777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18128158999609132397791405 6798059624853424649171777)
          ·
            refine ⟨5098544718640068486878833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6798059624853424649171777 5098544718640068486878833)
            ·
              refine ⟨3823908538980051365159125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5098544718640068486878833 3823908538980051365159125)
              ·
                refine ⟨89622856382344953870917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3823908538980051365159125 89622856382344953870917)
                ·
                  rfl

theorem cell23_4712577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 7].length) (baseStart_4712577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712577 prefixEnd_4712577 := by exact prefixLift 4712577
  have htrace : WordTrace (prefixWord ++ tailWord_4712577) baseStart_4712577 baseEnd_4712577 := by
    simpa [prefixWord, tailWord_4712577, baseEnd_4712577] using wordTrace_append hprefix tailTrace_4712577
  have hstable : (prefixWord ++ tailWord_4712577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712577).length < 2 ^ (prefixWord ++ tailWord_4712577).sum := by decide
  have hdescent : baseEnd_4712577 < baseStart_4712577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712583 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_4712583 : Nat := 118140960795 + 4712583 * 2 ^ 59
def prefixEnd_4712583 : Nat := 4983230072969 + 3 ^ 40 * 4712583 * 2
def baseEnd_4712583 : Nat := 2419820203207240731039731

theorem tailTrace_4712583 : CollatzResearch.WordTrace tailWord_4712583 prefixEnd_4712583 2419820203207240731039731 := by
  unfold tailWord_4712583
  simp only [CollatzResearch.WordTrace]
  refine ⟨171882022686124110944518403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114588015124082740629678935 171882022686124110944518403)
  ·
    refine ⟨257823034029186166416777605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171882022686124110944518403 257823034029186166416777605)
    ·
      refine ⟨48341818880472406203145801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257823034029186166416777605 48341818880472406203145801)
      ·
        refine ⟨36256364160354304652359351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48341818880472406203145801 36256364160354304652359351)
        ·
          refine ⟨54384546240531456978539027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36256364160354304652359351 54384546240531456978539027)
          ·
            refine ⟨81576819360797185467808541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54384546240531456978539027 81576819360797185467808541)
            ·
              refine ⟨30591307260298944550428203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81576819360797185467808541 30591307260298944550428203)
              ·
                refine ⟨45886960890448416825642305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30591307260298944550428203 45886960890448416825642305)
                ·
                  refine ⟨34415220667836312619231729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45886960890448416825642305 34415220667836312619231729)
                  ·
                    refine ⟨25811415500877234464423797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34415220667836312619231729 25811415500877234464423797)
                    ·
                      refine ⟨2419820203207240731039731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25811415500877234464423797 2419820203207240731039731)
                      ·
                        rfl

theorem cell23_4712583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_4712583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712583 prefixEnd_4712583 := by exact prefixLift 4712583
  have htrace : WordTrace (prefixWord ++ tailWord_4712583) baseStart_4712583 baseEnd_4712583 := by
    simpa [prefixWord, tailWord_4712583, baseEnd_4712583] using wordTrace_append hprefix tailTrace_4712583
  have hstable : (prefixWord ++ tailWord_4712583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712583).length < 2 ^ (prefixWord ++ tailWord_4712583).sum := by decide
  have hdescent : baseEnd_4712583 < baseStart_4712583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712597 : List Nat := [1, 3, 2, 1, 1, 1, 3, 5, 1, 3, 2]
def baseStart_4712597 : Nat := 118140960795 + 4712597 * 2 ^ 59
def prefixEnd_4712597 : Nat := 4983230072969 + 3 ^ 40 * 4712597 * 2
def baseEnd_4712597 : Nat := 2419827391936403676264667

theorem tailTrace_4712597 : CollatzResearch.WordTrace tailWord_4712597 prefixEnd_4712597 2419827391936403676264667 := by
  unfold tailWord_4712597
  simp only [CollatzResearch.WordTrace]
  refine ⟨171882533308073391335528045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114588355538715594223685363 171882533308073391335528045)
  ·
    refine ⟨64455949990527521750823017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171882533308073391335528045 64455949990527521750823017)
    ·
      refine ⟨48341962492895641313117263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64455949990527521750823017 48341962492895641313117263)
      ·
        refine ⟨72512943739343461969675895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48341962492895641313117263 72512943739343461969675895)
        ·
          refine ⟨108769415609015192954513843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72512943739343461969675895 108769415609015192954513843)
          ·
            refine ⟨163154123413522789431770765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108769415609015192954513843 163154123413522789431770765)
            ·
              refine ⟨61182796280071046036914037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163154123413522789431770765 61182796280071046036914037)
              ·
                refine ⟨5735887151256660565960691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61182796280071046036914037 5735887151256660565960691)
                ·
                  refine ⟨8603830726884990848941037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5735887151256660565960691 8603830726884990848941037)
                  ·
                    refine ⟨3226436522581871568352889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8603830726884990848941037 3226436522581871568352889)
                    ·
                      refine ⟨2419827391936403676264667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3226436522581871568352889 2419827391936403676264667)
                      ·
                        rfl

theorem cell23_4712597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_4712597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712597 prefixEnd_4712597 := by exact prefixLift 4712597
  have htrace : WordTrace (prefixWord ++ tailWord_4712597) baseStart_4712597 baseEnd_4712597 := by
    simpa [prefixWord, tailWord_4712597, baseEnd_4712597] using wordTrace_append hprefix tailTrace_4712597
  have hstable : (prefixWord ++ tailWord_4712597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712597).length < 2 ^ (prefixWord ++ tailWord_4712597).sum := by decide
  have hdescent : baseEnd_4712597 < baseStart_4712597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712613 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_4712613 : Nat := 118140960795 + 4712613 * 2 ^ 59
def prefixEnd_4712613 : Nat := 4983230072969 + 3 ^ 40 * 4712613 * 2
def baseEnd_4712613 : Nat := 2419835607626875613664593

theorem tailTrace_4712613 : CollatzResearch.WordTrace tailWord_4712613 prefixEnd_4712613 2419835607626875613664593 := by
  unfold tailWord_4712613
  simp only [CollatzResearch.WordTrace]
  refine ⟨171883116876015426068110493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114588744584010284045406995 171883116876015426068110493)
  ·
    refine ⟨64456168828505784775541435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171883116876015426068110493 64456168828505784775541435)
    ·
      refine ⟨96684253242758677163312153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64456168828505784775541435 96684253242758677163312153)
      ·
        refine ⟨72513189932069007872484115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96684253242758677163312153 72513189932069007872484115)
        ·
          refine ⟨108769784898103511808726173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72513189932069007872484115 108769784898103511808726173)
          ·
            refine ⟨40788669336788816928272315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108769784898103511808726173 40788669336788816928272315)
            ·
              refine ⟨61183004005183225392408473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40788669336788816928272315 61183004005183225392408473)
              ·
                refine ⟨45887253003887419044306355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61183004005183225392408473 45887253003887419044306355)
                ·
                  refine ⟨68830879505831128566459533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45887253003887419044306355 68830879505831128566459533)
                  ·
                    refine ⟨25811579814686673212422325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68830879505831128566459533 25811579814686673212422325)
                    ·
                      refine ⟨2419835607626875613664593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25811579814686673212422325 2419835607626875613664593)
                      ·
                        rfl

theorem cell23_4712613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_4712613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712613 prefixEnd_4712613 := by exact prefixLift 4712613
  have htrace : WordTrace (prefixWord ++ tailWord_4712613) baseStart_4712613 baseEnd_4712613 := by
    simpa [prefixWord, tailWord_4712613, baseEnd_4712613] using wordTrace_append hprefix tailTrace_4712613
  have hstable : (prefixWord ++ tailWord_4712613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712613).length < 2 ^ (prefixWord ++ tailWord_4712613).sum := by decide
  have hdescent : baseEnd_4712613 < baseStart_4712613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712621 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_4712621 : Nat := 118140960795 + 4712621 * 2 ^ 59
def prefixEnd_4712621 : Nat := 4983230072969 + 3 ^ 40 * 4712621 * 2
def baseEnd_4712621 : Nat := 2419839715472111582364557

theorem tailTrace_4712621 : CollatzResearch.WordTrace tailWord_4712621 prefixEnd_4712621 2419839715472111582364557 := by
  unfold tailWord_4712621
  simp only [CollatzResearch.WordTrace]
  refine ⟨171883408659986443434401717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114588939106657628956267811 171883408659986443434401717)
  ·
    refine ⟨16114069561873729071975161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 171883408659986443434401717 16114069561873729071975161)
    ·
      refine ⟨12085552171405296803981371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16114069561873729071975161 12085552171405296803981371)
      ·
        refine ⟨18128328257107945205972057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12085552171405296803981371 18128328257107945205972057)
        ·
          refine ⟨13596246192830958904479043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18128328257107945205972057 13596246192830958904479043)
          ·
            refine ⟨20394369289246438356718565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13596246192830958904479043 20394369289246438356718565)
            ·
              refine ⟨3823944241733707191884731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20394369289246438356718565 3823944241733707191884731)
              ·
                refine ⟨5735916362600560787827097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3823944241733707191884731 5735916362600560787827097)
                ·
                  refine ⟨4301937271950420590870323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5735916362600560787827097 4301937271950420590870323)
                  ·
                    refine ⟨6452905907925630886305485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4301937271950420590870323 6452905907925630886305485)
                    ·
                      refine ⟨2419839715472111582364557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6452905907925630886305485 2419839715472111582364557)
                      ·
                        rfl

theorem cell23_4712621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_4712621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712621 prefixEnd_4712621 := by exact prefixLift 4712621
  have htrace : WordTrace (prefixWord ++ tailWord_4712621) baseStart_4712621 baseEnd_4712621 := by
    simpa [prefixWord, tailWord_4712621, baseEnd_4712621] using wordTrace_append hprefix tailTrace_4712621
  have hstable : (prefixWord ++ tailWord_4712621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712621).length < 2 ^ (prefixWord ++ tailWord_4712621).sum := by decide
  have hdescent : baseEnd_4712621 < baseStart_4712621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712623 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 4]
def baseStart_4712623 : Nat := 118140960795 + 4712623 * 2 ^ 59
def prefixEnd_4712623 : Nat := 4983230072969 + 3 ^ 40 * 4712623 * 2
def baseEnd_4712623 : Nat := 2419840742433420574539547

theorem tailTrace_4712623 : CollatzResearch.WordTrace tailWord_4712623 prefixEnd_4712623 2419840742433420574539547 := by
  unfold tailWord_4712623
  simp only [CollatzResearch.WordTrace]
  refine ⟨171883481605979197775974523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114588987737319465183983015 171883481605979197775974523)
  ·
    refine ⟨257825222408968796663961785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171883481605979197775974523 257825222408968796663961785)
    ·
      refine ⟨193368916806726597497971339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257825222408968796663961785 193368916806726597497971339)
      ·
        refine ⟨290053375210089896246957009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193368916806726597497971339 290053375210089896246957009)
        ·
          refine ⟨217540031407567422185217757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290053375210089896246957009 217540031407567422185217757)
          ·
            refine ⟨81577511777837783319456659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217540031407567422185217757 81577511777837783319456659)
            ·
              refine ⟨122366267666756674979184989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81577511777837783319456659 122366267666756674979184989)
              ·
                refine ⟨45887350375033753117194371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122366267666756674979184989 45887350375033753117194371)
                ·
                  refine ⟨68831025562550629675791557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45887350375033753117194371 68831025562550629675791557)
                  ·
                    refine ⟨12905817292978243064210917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68831025562550629675791557 12905817292978243064210917)
                    ·
                      refine ⟨2419840742433420574539547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12905817292978243064210917 2419840742433420574539547)
                      ·
                        rfl

theorem cell23_4712623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_4712623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712623 prefixEnd_4712623 := by exact prefixLift 4712623
  have htrace : WordTrace (prefixWord ++ tailWord_4712623) baseStart_4712623 baseEnd_4712623 := by
    simpa [prefixWord, tailWord_4712623, baseEnd_4712623] using wordTrace_append hprefix tailTrace_4712623
  have hstable : (prefixWord ++ tailWord_4712623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712623).length < 2 ^ (prefixWord ++ tailWord_4712623).sum := by decide
  have hdescent : baseEnd_4712623 < baseStart_4712623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712633 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 9]
def baseStart_4712633 : Nat := 118140960795 + 4712633 * 2 ^ 59
def prefixEnd_4712633 : Nat := 4983230072969 + 3 ^ 40 * 4712633 * 2
def baseEnd_4712633 : Nat := 268871764137773948379389

theorem tailTrace_4712633 : CollatzResearch.WordTrace tailWord_4712633 prefixEnd_4712633 268871764137773948379389 := by
  unfold tailWord_4712633
  simp only [CollatzResearch.WordTrace]
  refine ⟨171883846335942969483838553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114589230890628646322559035 171883846335942969483838553)
  ·
    refine ⟨128912884751957227112878915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171883846335942969483838553 128912884751957227112878915)
    ·
      refine ⟨193369327127935840669318373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128912884751957227112878915 193369327127935840669318373)
      ·
        refine ⟨36256748836487970125497195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193369327127935840669318373 36256748836487970125497195)
        ·
          refine ⟨54385123254731955188245793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36256748836487970125497195 54385123254731955188245793)
          ·
            refine ⟨40788842441048966391184345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54385123254731955188245793 40788842441048966391184345)
            ·
              refine ⟨30591631830786724793388259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40788842441048966391184345 30591631830786724793388259)
              ·
                refine ⟨45887447746180087190082389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30591631830786724793388259 45887447746180087190082389)
                ·
                  refine ⟨268871764137773948379389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45887447746180087190082389 268871764137773948379389)
                  ·
                    rfl

theorem cell23_4712633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 9].length) (baseStart_4712633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712633 prefixEnd_4712633 := by exact prefixLift 4712633
  have htrace : WordTrace (prefixWord ++ tailWord_4712633) baseStart_4712633 baseEnd_4712633 := by
    simpa [prefixWord, tailWord_4712633, baseEnd_4712633] using wordTrace_append hprefix tailTrace_4712633
  have hstable : (prefixWord ++ tailWord_4712633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712633).length < 2 ^ (prefixWord ++ tailWord_4712633).sum := by decide
  have hdescent : baseEnd_4712633 < baseStart_4712633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712644 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_4712644 : Nat := 118140960795 + 4712644 * 2 ^ 59
def prefixEnd_4712644 : Nat := 4983230072969 + 3 ^ 40 * 4712644 * 2
def baseEnd_4712644 : Nat := 2419851525527164992376951

theorem tailTrace_4712644 : CollatzResearch.WordTrace tailWord_4712644 prefixEnd_4712644 2419851525527164992376951 := by
  unfold tailWord_4712644
  simp only [CollatzResearch.WordTrace]
  refine ⟨85942123769451559181244493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114589498359268745574992657 85942123769451559181244493)
  ·
    refine ⟨32228296413544334692966685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85942123769451559181244493 32228296413544334692966685)
    ·
      refine ⟨12085611155079125509862507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32228296413544334692966685 12085611155079125509862507)
      ·
        refine ⟨18128416732618688264793761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12085611155079125509862507 18128416732618688264793761)
        ·
          refine ⟨13596312549464016198595321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18128416732618688264793761 13596312549464016198595321)
          ·
            refine ⟨10197234412098012148946491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13596312549464016198595321 10197234412098012148946491)
            ·
              refine ⟨15295851618147018223419737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10197234412098012148946491 15295851618147018223419737)
              ·
                refine ⟨11471888713610263667564803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15295851618147018223419737 11471888713610263667564803)
                ·
                  refine ⟨17207833070415395501347205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11471888713610263667564803 17207833070415395501347205)
                  ·
                    refine ⟨3226468700702886656502601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17207833070415395501347205 3226468700702886656502601)
                    ·
                      refine ⟨2419851525527164992376951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3226468700702886656502601 2419851525527164992376951)
                      ·
                        rfl

theorem cell23_4712644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_4712644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712644 prefixEnd_4712644 := by exact prefixLift 4712644
  have htrace : WordTrace (prefixWord ++ tailWord_4712644) baseStart_4712644 baseEnd_4712644 := by
    simpa [prefixWord, tailWord_4712644, baseEnd_4712644] using wordTrace_append hprefix tailTrace_4712644
  have hstable : (prefixWord ++ tailWord_4712644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712644).length < 2 ^ (prefixWord ++ tailWord_4712644).sum := by decide
  have hdescent : baseEnd_4712644 < baseStart_4712644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712663 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 3, 7]
def baseStart_4712663 : Nat := 118140960795 + 4712663 * 2 ^ 59
def prefixEnd_4712663 : Nat := 4983230072969 + 3 ^ 40 * 4712663 * 2
def baseEnd_4712663 : Nat := 806620427219866806013121

theorem tailTrace_4712663 : CollatzResearch.WordTrace tailWord_4712663 prefixEnd_4712663 806620427219866806013121 := by
  unfold tailWord_4712663
  simp only [CollatzResearch.WordTrace]
  refine ⟨171884940525834284607430643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114589960350556189738287095 171884940525834284607430643)
  ·
    refine ⟨257827410788751426911145965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171884940525834284607430643 257827410788751426911145965)
    ·
      refine ⟨96685279045781785091679737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257827410788751426911145965 96685279045781785091679737)
      ·
        refine ⟨72513959284336338818759803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96685279045781785091679737 72513959284336338818759803)
        ·
          refine ⟨108770938926504508228139705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72513959284336338818759803 108770938926504508228139705)
          ·
            refine ⟨81578204194878381171104779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108770938926504508228139705 81578204194878381171104779)
            ·
              refine ⟨122367306292317571756657169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81578204194878381171104779 122367306292317571756657169)
              ·
                refine ⟨91775479719238178817492877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122367306292317571756657169 91775479719238178817492877)
                ·
                  refine ⟨34415804894714317056559829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91775479719238178817492877 34415804894714317056559829)
                  ·
                    refine ⟨806620427219866806013121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34415804894714317056559829 806620427219866806013121)
                    ·
                      rfl

theorem cell23_4712663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_4712663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712663 prefixEnd_4712663 := by exact prefixLift 4712663
  have htrace : WordTrace (prefixWord ++ tailWord_4712663) baseStart_4712663 baseEnd_4712663 := by
    simpa [prefixWord, tailWord_4712663, baseEnd_4712663] using wordTrace_append hprefix tailTrace_4712663
  have hstable : (prefixWord ++ tailWord_4712663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712663).length < 2 ^ (prefixWord ++ tailWord_4712663).sum := by decide
  have hdescent : baseEnd_4712663 < baseStart_4712663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712677 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 2, 3, 3]
def baseStart_4712677 : Nat := 118140960795 + 4712677 * 2 ^ 59
def prefixEnd_4712677 : Nat := 4983230072969 + 3 ^ 40 * 4712677 * 2
def baseEnd_4712677 : Nat := 2419868470388763363264299

theorem tailTrace_4712677 : CollatzResearch.WordTrace tailWord_4712677 prefixEnd_4712677 2419868470388763363264299 := by
  unfold tailWord_4712677
  simp only [CollatzResearch.WordTrace]
  refine ⟨171885451147783564998440285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114590300765189043332293523 171885451147783564998440285)
  ·
    refine ⟨64457044180418836874415107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171885451147783564998440285 64457044180418836874415107)
    ·
      refine ⟨96685566270628255311622661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64457044180418836874415107 96685566270628255311622661)
      ·
        refine ⟨18128543675742797870929249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96685566270628255311622661 18128543675742797870929249)
        ·
          refine ⟨13596407756807098403196937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18128543675742797870929249 13596407756807098403196937)
          ·
            refine ⟨10197305817605323802397703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13596407756807098403196937 10197305817605323802397703)
            ·
              refine ⟨15295958726407985703596555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10197305817605323802397703 15295958726407985703596555)
              ·
                refine ⟨22943938089611978555394833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15295958726407985703596555 22943938089611978555394833)
                ·
                  refine ⟨17207953567208983916546125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22943938089611978555394833 17207953567208983916546125)
                  ·
                    refine ⟨6452982587703368968704797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17207953567208983916546125 6452982587703368968704797)
                    ·
                      refine ⟨2419868470388763363264299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6452982587703368968704797 2419868470388763363264299)
                      ·
                        rfl

theorem cell23_4712677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_4712677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712677 prefixEnd_4712677 := by exact prefixLift 4712677
  have htrace : WordTrace (prefixWord ++ tailWord_4712677) baseStart_4712677 baseEnd_4712677 := by
    simpa [prefixWord, tailWord_4712677, baseEnd_4712677] using wordTrace_append hprefix tailTrace_4712677
  have hstable : (prefixWord ++ tailWord_4712677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712677).length < 2 ^ (prefixWord ++ tailWord_4712677).sum := by decide
  have hdescent : baseEnd_4712677 < baseStart_4712677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712727 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 3, 4]
def baseStart_4712727 : Nat := 118140960795 + 4712727 * 2 ^ 59
def prefixEnd_4712727 : Nat := 4983230072969 + 3 ^ 40 * 4712727 * 2
def baseEnd_4712727 : Nat := 806631381473829389213023

theorem tailTrace_4712727 : CollatzResearch.WordTrace tailWord_4712727 prefixEnd_4712727 806631381473829389213023 := by
  unfold tailWord_4712727
  simp only [CollatzResearch.WordTrace]
  refine ⟨171887274797602423537760435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114591516531734949025173623 171887274797602423537760435)
  ·
    refine ⟨257830912196403635306640653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171887274797602423537760435 257830912196403635306640653)
    ·
      refine ⟨96686592073651363239990245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257830912196403635306640653 96686592073651363239990245)
      ·
        refine ⟨18128736013809630607498171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96686592073651363239990245 18128736013809630607498171)
        ·
          refine ⟨27193104020714445911247257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18128736013809630607498171 27193104020714445911247257)
          ·
            refine ⟨20394828015535834433435443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27193104020714445911247257 20394828015535834433435443)
            ·
              refine ⟨30592242023303751650153165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20394828015535834433435443 30592242023303751650153165)
              ·
                refine ⟨11472090758738906868807437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30592242023303751650153165 11472090758738906868807437)
                ·
                  refine ⟨4302034034527090075802789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11472090758738906868807437 4302034034527090075802789)
                  ·
                    refine ⟨806631381473829389213023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4302034034527090075802789 806631381473829389213023)
                    ·
                      rfl

theorem cell23_4712727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_4712727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712727 prefixEnd_4712727 := by exact prefixLift 4712727
  have htrace : WordTrace (prefixWord ++ tailWord_4712727) baseStart_4712727 baseEnd_4712727 := by
    simpa [prefixWord, tailWord_4712727, baseEnd_4712727] using wordTrace_append hprefix tailTrace_4712727
  have hstable : (prefixWord ++ tailWord_4712727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712727).length < 2 ^ (prefixWord ++ tailWord_4712727).sum := by decide
  have hdescent : baseEnd_4712727 < baseStart_4712727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712734 : List Nat := [4, 3, 2, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_4712734 : Nat := 118140960795 + 4712734 * 2 ^ 59
def prefixEnd_4712734 : Nat := 4983230072969 + 3 ^ 40 * 4712734 * 2
def baseEnd_4712734 : Nat := 2419897738786069640251537

theorem tailTrace_4712734 : CollatzResearch.WordTrace tailWord_4712734 prefixEnd_4712734 2419897738786069640251537 := by
  unfold tailWord_4712734
  simp only [CollatzResearch.WordTrace]
  refine ⟨21485941263572132966658157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 114591686739051375822176837 21485941263572132966658157)
  ·
    refine ⟨8057227973839549862496809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21485941263572132966658157 8057227973839549862496809)
    ·
      refine ⟨6042920980379662396872607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8057227973839549862496809 6042920980379662396872607)
      ·
        refine ⟨9064381470569493595308911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6042920980379662396872607 9064381470569493595308911)
        ·
          refine ⟨13596572205854240392963367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9064381470569493595308911 13596572205854240392963367)
          ·
            refine ⟨20394858308781360589445051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13596572205854240392963367 20394858308781360589445051)
            ·
              refine ⟨30592287463172040884167577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20394858308781360589445051 30592287463172040884167577)
              ·
                refine ⟨22944215597379030663125683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30592287463172040884167577 22944215597379030663125683)
                ·
                  refine ⟨34416323396068545994688525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22944215597379030663125683 34416323396068545994688525)
                  ·
                    refine ⟨12906121273525704748008197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34416323396068545994688525 12906121273525704748008197)
                    ·
                      refine ⟨2419897738786069640251537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12906121273525704748008197 2419897738786069640251537)
                      ·
                        rfl

theorem cell23_4712734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_4712734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712734 prefixEnd_4712734 := by exact prefixLift 4712734
  have htrace : WordTrace (prefixWord ++ tailWord_4712734) baseStart_4712734 baseEnd_4712734 := by
    simpa [prefixWord, tailWord_4712734, baseEnd_4712734] using wordTrace_append hprefix tailTrace_4712734
  have hstable : (prefixWord ++ tailWord_4712734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712734).length < 2 ^ (prefixWord ++ tailWord_4712734).sum := by decide
  have hdescent : baseEnd_4712734 < baseStart_4712734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712761 : List Nat := [1, 2, 1, 6, 1, 1, 3, 3, 1, 4]
def baseStart_4712761 : Nat := 118140960795 + 4712761 * 2 ^ 59
def prefixEnd_4712761 : Nat := 4983230072969 + 3 ^ 40 * 4712761 * 2
def baseEnd_4712761 : Nat := 806637200921247011537971

theorem tailTrace_4712761 : CollatzResearch.WordTrace tailWord_4712761 prefixEnd_4712761 806637200921247011537971 := by
  unfold tailWord_4712761
  simp only [CollatzResearch.WordTrace]
  refine ⟨171888514879479247344498137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114592343252986164896332091 171888514879479247344498137)
  ·
    refine ⟨128916386159609435508373603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171888514879479247344498137 128916386159609435508373603)
    ·
      refine ⟨193374579239414153262560405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128916386159609435508373603 193374579239414153262560405)
      ·
        refine ⟨9064433401847538434182519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 193374579239414153262560405 9064433401847538434182519)
        ·
          refine ⟨13596650102771307651273779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9064433401847538434182519 13596650102771307651273779)
          ·
            refine ⟨20394975154156961476910669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13596650102771307651273779 20394975154156961476910669)
            ·
              refine ⟨7648115682808860553841501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20394975154156961476910669 7648115682808860553841501)
              ·
                refine ⟨2868043381053322707690563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7648115682808860553841501 2868043381053322707690563)
                ·
                  refine ⟨4302065071579984061535845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868043381053322707690563 4302065071579984061535845)
                  ·
                    refine ⟨806637200921247011537971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4302065071579984061535845 806637200921247011537971)
                    ·
                      rfl

theorem cell23_4712761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 3, 1, 4].length) (baseStart_4712761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712761 prefixEnd_4712761 := by exact prefixLift 4712761
  have htrace : WordTrace (prefixWord ++ tailWord_4712761) baseStart_4712761 baseEnd_4712761 := by
    simpa [prefixWord, tailWord_4712761, baseEnd_4712761] using wordTrace_append hprefix tailTrace_4712761
  have hstable : (prefixWord ++ tailWord_4712761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712761).length < 2 ^ (prefixWord ++ tailWord_4712761).sum := by decide
  have hdescent : baseEnd_4712761 < baseStart_4712761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712784 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 3, 1, 3]
def baseStart_4712784 : Nat := 118140960795 + 4712784 * 2 ^ 59
def prefixEnd_4712784 : Nat := 4983230072969 + 3 ^ 40 * 4712784 * 2
def baseEnd_4712784 : Nat := 2419923412818794444626307

theorem tailTrace_4712784 : CollatzResearch.WordTrace tailWord_4712784 prefixEnd_4712784 2419923412818794444626307 := by
  unfold tailWord_4712784
  simp only [CollatzResearch.WordTrace]
  refine ⟨85944676879197961136292703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114592902505597281515056937 85944676879197961136292703)
  ·
    refine ⟨128917015318796941704439055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85944676879197961136292703 128917015318796941704439055)
    ·
      refine ⟨193375522978195412556658583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128917015318796941704439055 193375522978195412556658583)
      ·
        refine ⟨290063284467293118834987875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193375522978195412556658583 290063284467293118834987875)
        ·
          refine ⟨435094926700939678252481813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290063284467293118834987875 435094926700939678252481813)
          ·
            refine ⟨20395074689106547418085085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 435094926700939678252481813 20395074689106547418085085)
            ·
              refine ⟨7648153008414955281781907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20395074689106547418085085 7648153008414955281781907)
              ·
                refine ⟨11472229512622432922672861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7648153008414955281781907 11472229512622432922672861)
                ·
                  refine ⟨4302086067233412346002323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11472229512622432922672861 4302086067233412346002323)
                  ·
                    refine ⟨6453129100850118519003485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4302086067233412346002323 6453129100850118519003485)
                    ·
                      refine ⟨2419923412818794444626307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6453129100850118519003485 2419923412818794444626307)
                      ·
                        rfl

theorem cell23_4712784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 3, 1, 3].length) (baseStart_4712784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712784 prefixEnd_4712784 := by exact prefixLift 4712784
  have htrace : WordTrace (prefixWord ++ tailWord_4712784) baseStart_4712784 baseEnd_4712784 := by
    simpa [prefixWord, tailWord_4712784, baseEnd_4712784] using wordTrace_append hprefix tailTrace_4712784
  have hstable : (prefixWord ++ tailWord_4712784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712784).length < 2 ^ (prefixWord ++ tailWord_4712784).sum := by decide
  have hdescent : baseEnd_4712784 < baseStart_4712784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712821 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 1, 5]
def baseStart_4712821 : Nat := 118140960795 + 4712821 * 2 ^ 59
def prefixEnd_4712821 : Nat := 4983230072969 + 3 ^ 40 * 4712821 * 2
def baseEnd_4712821 : Nat := 806647470534336933287879

theorem tailTrace_4712821 : CollatzResearch.WordTrace tailWord_4712821 prefixEnd_4712821 806647470534336933287879 := by
  unfold tailWord_4712821
  simp only [CollatzResearch.WordTrace]
  refine ⟨171890703259261877591682317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114593802172841251727788211 171890703259261877591682317)
  ·
    refine ⟨64459013722223204096880869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171890703259261877591682317 64459013722223204096880869)
    ·
      refine ⟨12086065072916850768165163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64459013722223204096880869 12086065072916850768165163)
      ·
        refine ⟨18129097609375276152247745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12086065072916850768165163 18129097609375276152247745)
        ·
          refine ⟨13596823207031457114185809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18129097609375276152247745 13596823207031457114185809)
          ·
            refine ⟨10197617405273592835639357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13596823207031457114185809 10197617405273592835639357)
            ·
              refine ⟨3824106526977597313364759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10197617405273592835639357 3824106526977597313364759)
              ·
                refine ⟨5736159790466395970047139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3824106526977597313364759 5736159790466395970047139)
                ·
                  refine ⟨8604239685699593955070709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5736159790466395970047139 8604239685699593955070709)
                  ·
                    refine ⟨806647470534336933287879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8604239685699593955070709 806647470534336933287879)
                    ·
                      rfl

theorem cell23_4712821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_4712821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712821 prefixEnd_4712821 := by exact prefixLift 4712821
  have htrace : WordTrace (prefixWord ++ tailWord_4712821) baseStart_4712821 baseEnd_4712821 := by
    simpa [prefixWord, tailWord_4712821, baseEnd_4712821] using wordTrace_append hprefix tailTrace_4712821
  have hstable : (prefixWord ++ tailWord_4712821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712821).length < 2 ^ (prefixWord ++ tailWord_4712821).sum := by decide
  have hdescent : baseEnd_4712821 < baseStart_4712821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712827 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 5]
def baseStart_4712827 : Nat := 118140960795 + 4712827 * 2 ^ 59
def prefixEnd_4712827 : Nat := 4983230072969 + 3 ^ 40 * 4712827 * 2
def baseEnd_4712827 : Nat := 2419945492486937776388609

theorem tailTrace_4712827 : CollatzResearch.WordTrace tailWord_4712827 prefixEnd_4712827 2419945492486937776388609 := by
  unfold tailWord_4712827
  simp only [CollatzResearch.WordTrace]
  refine ⟨171890922097240140616400735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114593948064826760410933823 171890922097240140616400735)
  ·
    refine ⟨257836383145860210924601103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171890922097240140616400735 257836383145860210924601103)
    ·
      refine ⟨386754574718790316386901655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257836383145860210924601103 386754574718790316386901655)
      ·
        refine ⟨580131862078185474580352483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386754574718790316386901655 580131862078185474580352483)
        ·
          refine ⟨870197793117278211870528725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580131862078185474580352483 870197793117278211870528725)
          ·
            refine ⟨20395260776186208090715517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 870197793117278211870528725 20395260776186208090715517)
            ·
              refine ⟨7648222791069828034018319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20395260776186208090715517 7648222791069828034018319)
              ·
                refine ⟨11472334186604742051027479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7648222791069828034018319 11472334186604742051027479)
                ·
                  refine ⟨17208501279907113076541219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11472334186604742051027479 17208501279907113076541219)
                  ·
                    refine ⟨25812751919860669614811829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17208501279907113076541219 25812751919860669614811829)
                    ·
                      refine ⟨2419945492486937776388609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25812751919860669614811829 2419945492486937776388609)
                      ·
                        rfl

theorem cell23_4712827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 5].length) (baseStart_4712827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712827 prefixEnd_4712827 := by exact prefixLift 4712827
  have htrace : WordTrace (prefixWord ++ tailWord_4712827) baseStart_4712827 baseEnd_4712827 := by
    simpa [prefixWord, tailWord_4712827, baseEnd_4712827] using wordTrace_append hprefix tailTrace_4712827
  have hstable : (prefixWord ++ tailWord_4712827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712827).length < 2 ^ (prefixWord ++ tailWord_4712827).sum := by decide
  have hdescent : baseEnd_4712827 < baseStart_4712827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712835 : List Nat := [1, 1, 1, 3, 6, 2, 2, 2, 1, 1, 3]
def baseStart_4712835 : Nat := 118140960795 + 4712835 * 2 ^ 59
def prefixEnd_4712835 : Nat := 4983230072969 + 3 ^ 40 * 4712835 * 2
def baseEnd_4712835 : Nat := 2419949600332173745088573

theorem tailTrace_4712835 : CollatzResearch.WordTrace tailWord_4712835 prefixEnd_4712835 2419949600332173745088573 := by
  unfold tailWord_4712835
  simp only [CollatzResearch.WordTrace]
  refine ⟨171891213881211157982691959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114594142587474105321794639 171891213881211157982691959)
  ·
    refine ⟨257836820821816736974037939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171891213881211157982691959 257836820821816736974037939)
    ·
      refine ⟨386755231232725105461056909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257836820821816736974037939 386755231232725105461056909)
      ·
        refine ⟨145033211712271914547896341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 386755231232725105461056909 145033211712271914547896341)
        ·
          refine ⟨6798431799012745994432641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145033211712271914547896341 6798431799012745994432641)
          ·
            refine ⟨5098823849259559495824481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6798431799012745994432641 5098823849259559495824481)
            ·
              refine ⟨3824117886944669621868361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5098823849259559495824481 3824117886944669621868361)
              ·
                refine ⟨2868088415208502216401271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3824117886944669621868361 2868088415208502216401271)
                ·
                  refine ⟨4302132622812753324601907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2868088415208502216401271 4302132622812753324601907)
                  ·
                    refine ⟨6453198934219129986902861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4302132622812753324601907 6453198934219129986902861)
                    ·
                      refine ⟨2419949600332173745088573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6453198934219129986902861 2419949600332173745088573)
                      ·
                        rfl

theorem cell23_4712835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 2, 1, 1, 3].length) (baseStart_4712835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712835 prefixEnd_4712835 := by exact prefixLift 4712835
  have htrace : WordTrace (prefixWord ++ tailWord_4712835) baseStart_4712835 baseEnd_4712835 := by
    simpa [prefixWord, tailWord_4712835, baseEnd_4712835] using wordTrace_append hprefix tailTrace_4712835
  have hstable : (prefixWord ++ tailWord_4712835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712835).length < 2 ^ (prefixWord ++ tailWord_4712835).sum := by decide
  have hdescent : baseEnd_4712835 < baseStart_4712835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712908 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 1, 3, 3]
def baseStart_4712908 : Nat := 118140960795 + 4712908 * 2 ^ 59
def prefixEnd_4712908 : Nat := 4983230072969 + 3 ^ 40 * 4712908 * 2
def baseEnd_4712908 : Nat := 2419987084419951959475737

theorem tailTrace_4712908 : CollatzResearch.WordTrace tailWord_4712908 prefixEnd_4712908 2419987084419951959475737 := by
  unfold tailWord_4712908
  simp only [CollatzResearch.WordTrace]
  refine ⟨85946938204973345725049689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114595917606631127633399585 85946938204973345725049689)
  ·
    refine ⟨64460203653730009293787267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85946938204973345725049689 64460203653730009293787267)
    ·
      refine ⟨96690305480595013940680901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64460203653730009293787267 96690305480595013940680901)
      ·
        refine ⟨18129432277611565113877669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96690305480595013940680901 18129432277611565113877669)
        ·
          refine ⟨3399268552052168458852063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18129432277611565113877669 3399268552052168458852063)
          ·
            refine ⟨5098902828078252688278095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3399268552052168458852063 5098902828078252688278095)
            ·
              refine ⟨7648354242117379032417143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5098902828078252688278095 7648354242117379032417143)
              ·
                refine ⟨11472531363176068548625715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7648354242117379032417143 11472531363176068548625715)
                ·
                  refine ⟨17208797044764102822938573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11472531363176068548625715 17208797044764102822938573)
                  ·
                    refine ⟨6453298891786538558601965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17208797044764102822938573 6453298891786538558601965)
                    ·
                      refine ⟨2419987084419951959475737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6453298891786538558601965 2419987084419951959475737)
                      ·
                        rfl

theorem cell23_4712908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_4712908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712908 prefixEnd_4712908 := by exact prefixLift 4712908
  have htrace : WordTrace (prefixWord ++ tailWord_4712908) baseStart_4712908 baseEnd_4712908 := by
    simpa [prefixWord, tailWord_4712908, baseEnd_4712908] using wordTrace_append hprefix tailTrace_4712908
  have hstable : (prefixWord ++ tailWord_4712908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712908).length < 2 ^ (prefixWord ++ tailWord_4712908).sum := by decide
  have hdescent : baseEnd_4712908 < baseStart_4712908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4712984 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 2, 5]
def baseStart_4712984 : Nat := 118140960795 + 4712984 * 2 ^ 59
def prefixEnd_4712984 : Nat := 4983230072969 + 3 ^ 40 * 4712984 * 2
def baseEnd_4712984 : Nat := 806675369649897887375129

theorem tailTrace_4712984 : CollatzResearch.WordTrace tailWord_4712984 prefixEnd_4712984 806675369649897887375129 := by
  unfold tailWord_4712984
  simp only [CollatzResearch.WordTrace]
  refine ⟨85948324178835678214933003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114597765571780904286577337 85948324178835678214933003)
  ·
    refine ⟨128922486268253517322399505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85948324178835678214933003 128922486268253517322399505)
    ·
      refine ⟨96691864701190137991799629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128922486268253517322399505 96691864701190137991799629)
      ·
        refine ⟨36259449262946301746924861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96691864701190137991799629 36259449262946301746924861)
        ·
          refine ⟨13597293473604863155096823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36259449262946301746924861 13597293473604863155096823)
          ·
            refine ⟨20395940210407294732645235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13597293473604863155096823 20395940210407294732645235)
            ·
              refine ⟨30593910315610942098967853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20395940210407294732645235 30593910315610942098967853)
              ·
                refine ⟨11472716368354103287112945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30593910315610942098967853 11472716368354103287112945)
                ·
                  refine ⟨8604537276265577465334709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11472716368354103287112945 8604537276265577465334709)
                  ·
                    refine ⟨806675369649897887375129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8604537276265577465334709 806675369649897887375129)
                    ·
                      rfl

theorem cell23_4712984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_4712984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4712984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4712984 prefixEnd_4712984 := by exact prefixLift 4712984
  have htrace : WordTrace (prefixWord ++ tailWord_4712984) baseStart_4712984 baseEnd_4712984 := by
    simpa [prefixWord, tailWord_4712984, baseEnd_4712984] using wordTrace_append hprefix tailTrace_4712984
  have hstable : (prefixWord ++ tailWord_4712984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4712984).length < 2 ^ (prefixWord ++ tailWord_4712984).sum := by decide
  have hdescent : baseEnd_4712984 < baseStart_4712984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4712984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713004 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 3, 6, 2]
def baseStart_4713004 : Nat := 118140960795 + 4713004 * 2 ^ 59
def prefixEnd_4713004 : Nat := 4983230072969 + 3 ^ 40 * 4713004 * 2
def baseEnd_4713004 : Nat := 2420036378562783583875295

theorem tailTrace_4713004 : CollatzResearch.WordTrace tailWord_4713004 prefixEnd_4713004 2420036378562783583875295 := by
  unfold tailWord_4713004
  simp only [CollatzResearch.WordTrace]
  refine ⟨85948688908799449922797033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114598251878399266563729377 85948688908799449922797033)
  ·
    refine ⟨64461516681599587442097775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85948688908799449922797033 64461516681599587442097775)
    ·
      refine ⟨96692275022399381163146663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64461516681599587442097775 96692275022399381163146663)
      ·
        refine ⟨145038412533599071744719995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96692275022399381163146663 145038412533599071744719995)
        ·
          refine ⟨217557618800398607617079993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145038412533599071744719995 217557618800398607617079993)
          ·
            refine ⟨163168214100298955712809995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217557618800398607617079993 163168214100298955712809995)
            ·
              refine ⟨244752321150448433569214993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163168214100298955712809995 244752321150448433569214993)
              ·
                refine ⟨183564240862836325176911245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244752321150448433569214993 183564240862836325176911245)
                ·
                  refine ⟨68836590323563621941341717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183564240862836325176911245 68836590323563621941341717)
                  ·
                    refine ⟨3226715171417044778500393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68836590323563621941341717 3226715171417044778500393)
                    ·
                      refine ⟨2420036378562783583875295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3226715171417044778500393 2420036378562783583875295)
                      ·
                        rfl

theorem cell23_4713004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 6, 2].length) (baseStart_4713004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713004 prefixEnd_4713004 := by exact prefixLift 4713004
  have htrace : WordTrace (prefixWord ++ tailWord_4713004) baseStart_4713004 baseEnd_4713004 := by
    simpa [prefixWord, tailWord_4713004, baseEnd_4713004] using wordTrace_append hprefix tailTrace_4713004
  have hstable : (prefixWord ++ tailWord_4713004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713004).length < 2 ^ (prefixWord ++ tailWord_4713004).sum := by decide
  have hdescent : baseEnd_4713004 < baseStart_4713004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713021 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 1, 6, 2]
def baseStart_4713021 : Nat := 118140960795 + 4713021 * 2 ^ 59
def prefixEnd_4713021 : Nat := 4983230072969 + 3 ^ 40 * 4713021 * 2
def baseEnd_4713021 : Nat := 2420045107733910017362717

theorem tailTrace_4713021 : CollatzResearch.WordTrace tailWord_4713021 prefixEnd_4713021 2420045107733910017362717 := by
  unfold tailWord_4713021
  simp only [CollatzResearch.WordTrace]
  refine ⟨171897997858537311748962917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114598665239024874499308611 171897997858537311748962917)
  ·
    refine ⟨32230874598475745952930547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 171897997858537311748962917 32230874598475745952930547)
    ·
      refine ⟨48346311897713618929395821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32230874598475745952930547 48346311897713618929395821)
      ·
        refine ⟨18129866961642607098523433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48346311897713618929395821 18129866961642607098523433)
        ·
          refine ⟨13597400221231955323892575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18129866961642607098523433 13597400221231955323892575)
          ·
            refine ⟨20396100331847932985838863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13597400221231955323892575 20396100331847932985838863)
            ·
              refine ⟨30594150497771899478758295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20396100331847932985838863 30594150497771899478758295)
              ·
                refine ⟨45891225746657849218137443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30594150497771899478758295 45891225746657849218137443)
                ·
                  refine ⟨68836838619986773827206165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45891225746657849218137443 68836838619986773827206165)
                  ·
                    refine ⟨3226726810311880023150289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68836838619986773827206165 3226726810311880023150289)
                    ·
                      refine ⟨2420045107733910017362717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3226726810311880023150289 2420045107733910017362717)
                      ·
                        rfl

theorem cell23_4713021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_4713021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713021 prefixEnd_4713021 := by exact prefixLift 4713021
  have htrace : WordTrace (prefixWord ++ tailWord_4713021) baseStart_4713021 baseEnd_4713021 := by
    simpa [prefixWord, tailWord_4713021, baseEnd_4713021] using wordTrace_append hprefix tailTrace_4713021
  have hstable : (prefixWord ++ tailWord_4713021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713021).length < 2 ^ (prefixWord ++ tailWord_4713021).sum := by decide
  have hdescent : baseEnd_4713021 < baseStart_4713021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713024 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 3]
def baseStart_4713024 : Nat := 118140960795 + 4713024 * 2 ^ 59
def prefixEnd_4713024 : Nat := 4983230072969 + 3 ^ 40 * 4713024 * 2
def baseEnd_4713024 : Nat := 2420046648175873505625203

theorem tailTrace_4713024 : CollatzResearch.WordTrace tailWord_4713024 prefixEnd_4713024 2420046648175873505625203 := by
  unfold tailWord_4713024
  simp only [CollatzResearch.WordTrace]
  refine ⟨85949053638763221630661063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114598738185017628840881417 85949053638763221630661063)
  ·
    refine ⟨128923580458144832445991595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85949053638763221630661063 128923580458144832445991595)
    ·
      refine ⟨193385370687217248668987393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128923580458144832445991595 193385370687217248668987393)
      ·
        refine ⟨145039028015412936501740545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193385370687217248668987393 145039028015412936501740545)
        ·
          refine ⟨108779271011559702376305409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145039028015412936501740545 108779271011559702376305409)
          ·
            refine ⟨81584453258669776782229057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108779271011559702376305409 81584453258669776782229057)
            ·
              refine ⟨61188339944002332586671793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81584453258669776782229057 61188339944002332586671793)
              ·
                refine ⟨45891254958001749440003845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61188339944002332586671793 45891254958001749440003845)
                ·
                  refine ⟨8604610304625328020000721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45891254958001749440003845 8604610304625328020000721)
                  ·
                    refine ⟨6453457728468996015000541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8604610304625328020000721 6453457728468996015000541)
                    ·
                      refine ⟨2420046648175873505625203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6453457728468996015000541 2420046648175873505625203)
                      ·
                        rfl

theorem cell23_4713024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 3].length) (baseStart_4713024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713024 prefixEnd_4713024 := by exact prefixLift 4713024
  have htrace : WordTrace (prefixWord ++ tailWord_4713024) baseStart_4713024 baseEnd_4713024 := by
    simpa [prefixWord, tailWord_4713024, baseEnd_4713024] using wordTrace_append hprefix tailTrace_4713024
  have hstable : (prefixWord ++ tailWord_4713024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713024).length < 2 ^ (prefixWord ++ tailWord_4713024).sum := by decide
  have hdescent : baseEnd_4713024 < baseStart_4713024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713031 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 3, 4]
def baseStart_4713031 : Nat := 118140960795 + 4713031 * 2 ^ 59
def prefixEnd_4713031 : Nat := 4983230072969 + 3 ^ 40 * 4713031 * 2
def baseEnd_4713031 : Nat := 806683414180151659412557

theorem tailTrace_4713031 : CollatzResearch.WordTrace tailWord_4713031 prefixEnd_4713031 806683414180151659412557 := by
  unfold tailWord_4713031
  simp only [CollatzResearch.WordTrace]
  refine ⟨171898362588501083456826947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114598908392334055637884631 171898362588501083456826947)
  ·
    refine ⟨257847543882751625185240421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171898362588501083456826947 257847543882751625185240421)
    ·
      refine ⟨48346414478015929722232579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 257847543882751625185240421 48346414478015929722232579)
      ·
        refine ⟨72519621717023894583348869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48346414478015929722232579 72519621717023894583348869)
        ·
          refine ⟨13597429071941980234377913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72519621717023894583348869 13597429071941980234377913)
          ·
            refine ⟨10198071803956485175783435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13597429071941980234377913 10198071803956485175783435)
            ·
              refine ⟨15297107705934727763675153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10198071803956485175783435 15297107705934727763675153)
              ·
                refine ⟨11472830779451045822756365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15297107705934727763675153 11472830779451045822756365)
                ·
                  refine ⟨4302311542294142183533637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11472830779451045822756365 4302311542294142183533637)
                  ·
                    refine ⟨806683414180151659412557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4302311542294142183533637 806683414180151659412557)
                    ·
                      rfl

theorem cell23_4713031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_4713031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713031 prefixEnd_4713031 := by exact prefixLift 4713031
  have htrace : WordTrace (prefixWord ++ tailWord_4713031) baseStart_4713031 baseEnd_4713031 := by
    simpa [prefixWord, tailWord_4713031, baseEnd_4713031] using wordTrace_append hprefix tailTrace_4713031
  have hstable : (prefixWord ++ tailWord_4713031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713031).length < 2 ^ (prefixWord ++ tailWord_4713031).sum := by decide
  have hdescent : baseEnd_4713031 < baseStart_4713031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713041 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 2, 2, 3]
def baseStart_4713041 : Nat := 118140960795 + 4713041 * 2 ^ 59
def prefixEnd_4713041 : Nat := 4983230072969 + 3 ^ 40 * 4713041 * 2
def baseEnd_4713041 : Nat := 2420055377346999939112625

theorem tailTrace_4713041 : CollatzResearch.WordTrace tailWord_4713041 prefixEnd_4713041 2420055377346999939112625 := by
  unfold tailWord_4713041
  simp only [CollatzResearch.WordTrace]
  refine ⟨171898727318464855164690977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114599151545643236776460651 171898727318464855164690977)
  ·
    refine ⟨128924045488848641373518233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171898727318464855164690977 128924045488848641373518233)
    ·
      refine ⟨96693034116636481030138675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 128924045488848641373518233 96693034116636481030138675)
      ·
        refine ⟨145039551174954721545208013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96693034116636481030138675 145039551174954721545208013)
        ·
          refine ⟨54389831690608020579453005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145039551174954721545208013 54389831690608020579453005)
          ·
            refine ⟨20396186883978007717294877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54389831690608020579453005 20396186883978007717294877)
            ·
              refine ⟨7648570081491752893985579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20396186883978007717294877 7648570081491752893985579)
              ·
                refine ⟨11472855122237629340978369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7648570081491752893985579 11472855122237629340978369)
                ·
                  refine ⟨8604641341678222005733777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11472855122237629340978369 8604641341678222005733777)
                  ·
                    refine ⟨6453481006258666504300333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8604641341678222005733777 6453481006258666504300333)
                    ·
                      refine ⟨2420055377346999939112625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6453481006258666504300333 2420055377346999939112625)
                      ·
                        rfl

theorem cell23_4713041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_4713041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713041 prefixEnd_4713041 := by exact prefixLift 4713041
  have htrace : WordTrace (prefixWord ++ tailWord_4713041) baseStart_4713041 baseEnd_4713041 := by
    simpa [prefixWord, tailWord_4713041, baseEnd_4713041] using wordTrace_append hprefix tailTrace_4713041
  have hstable : (prefixWord ++ tailWord_4713041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713041).length < 2 ^ (prefixWord ++ tailWord_4713041).sum := by decide
  have hdescent : baseEnd_4713041 < baseStart_4713041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713067 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 7]
def baseStart_4713067 : Nat := 118140960795 + 4713067 * 2 ^ 59
def prefixEnd_4713067 : Nat := 4983230072969 + 3 ^ 40 * 4713067 * 2
def baseEnd_4713067 : Nat := 2420068727844016837387505

theorem tailTrace_4713067 : CollatzResearch.WordTrace tailWord_4713067 prefixEnd_4713067 2420068727844016837387505 := by
  unfold tailWord_4713067
  simp only [CollatzResearch.WordTrace]
  refine ⟨171899675616370661605137455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114599783744247107736758303 171899675616370661605137455)
  ·
    refine ⟨257849513424555992407706183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171899675616370661605137455 257849513424555992407706183)
    ·
      refine ⟨386774270136833988611559275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257849513424555992407706183 386774270136833988611559275)
      ·
        refine ⟨580161405205250982917338913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 386774270136833988611559275 580161405205250982917338913)
        ·
          refine ⟨435121053903938237188004185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 580161405205250982917338913 435121053903938237188004185)
          ·
            refine ⟨326340790427953677891003139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 435121053903938237188004185 326340790427953677891003139)
            ·
              refine ⟨489511185641930516836504709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326340790427953677891003139 489511185641930516836504709)
              ·
                refine ⟨91783347307861971906844633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 489511185641930516836504709 91783347307861971906844633)
                ·
                  refine ⟨68837510480896478930133475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91783347307861971906844633 68837510480896478930133475)
                  ·
                    refine ⟨103256265721344718395200213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68837510480896478930133475 103256265721344718395200213)
                    ·
                      refine ⟨2420068727844016837387505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 103256265721344718395200213 2420068727844016837387505)
                      ·
                        rfl

theorem cell23_4713067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_4713067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713067 prefixEnd_4713067 := by exact prefixLift 4713067
  have htrace : WordTrace (prefixWord ++ tailWord_4713067) baseStart_4713067 baseEnd_4713067 := by
    simpa [prefixWord, tailWord_4713067, baseEnd_4713067] using wordTrace_append hprefix tailTrace_4713067
  have hstable : (prefixWord ++ tailWord_4713067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713067).length < 2 ^ (prefixWord ++ tailWord_4713067).sum := by decide
  have hdescent : baseEnd_4713067 < baseStart_4713067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713071 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 3, 1, 3]
def baseStart_4713071 : Nat := 118140960795 + 4713071 * 2 ^ 59
def prefixEnd_4713071 : Nat := 4983230072969 + 3 ^ 40 * 4713071 * 2
def baseEnd_4713071 : Nat := 2420070781766634821737487

theorem tailTrace_4713071 : CollatzResearch.WordTrace tailWord_4713071 prefixEnd_4713071 2420070781766634821737487 := by
  unfold tailWord_4713071
  simp only [CollatzResearch.WordTrace]
  refine ⟨171899821508356170288283067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114599881005570780192188711 171899821508356170288283067)
  ·
    refine ⟨257849732262534255432424601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171899821508356170288283067 257849732262534255432424601)
    ·
      refine ⟨193387299196900691574318451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257849732262534255432424601 193387299196900691574318451)
      ·
        refine ⟨290080948795351037361477677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193387299196900691574318451 290080948795351037361477677)
        ·
          refine ⟨108780355798256639010554129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290080948795351037361477677 108780355798256639010554129)
          ·
            refine ⟨81585266848692479257915597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108780355798256639010554129 81585266848692479257915597)
            ·
              refine ⟨30594475068259679721718349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81585266848692479257915597 30594475068259679721718349)
              ·
                refine ⟨11472928150597379895644381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30594475068259679721718349 11472928150597379895644381)
                ·
                  refine ⟨4302348056474017460866643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11472928150597379895644381 4302348056474017460866643)
                  ·
                    refine ⟨6453522084711026191299965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4302348056474017460866643 6453522084711026191299965)
                    ·
                      refine ⟨2420070781766634821737487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6453522084711026191299965 2420070781766634821737487)
                      ·
                        rfl

theorem cell23_4713071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 1, 3].length) (baseStart_4713071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713071 prefixEnd_4713071 := by exact prefixLift 4713071
  have htrace : WordTrace (prefixWord ++ tailWord_4713071) baseStart_4713071 baseEnd_4713071 := by
    simpa [prefixWord, tailWord_4713071, baseEnd_4713071] using wordTrace_append hprefix tailTrace_4713071
  have hstable : (prefixWord ++ tailWord_4713071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713071).length < 2 ^ (prefixWord ++ tailWord_4713071).sum := by decide
  have hdescent : baseEnd_4713071 < baseStart_4713071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713081 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 1, 5, 2]
def baseStart_4713081 : Nat := 118140960795 + 4713081 * 2 ^ 59
def prefixEnd_4713081 : Nat := 4983230072969 + 3 ^ 40 * 4713081 * 2
def baseEnd_4713081 : Nat := 2420075916573179782612441

theorem tailTrace_4713081 : CollatzResearch.WordTrace tailWord_4713081 prefixEnd_4713081 2420075916573179782612441 := by
  unfold tailWord_4713081
  simp only [CollatzResearch.WordTrace]
  refine ⟨171900186238319941996147097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114600124158879961330764731 171900186238319941996147097)
  ·
    refine ⟨128925139678739956497110323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171900186238319941996147097 128925139678739956497110323)
    ·
      refine ⟨193387709518109934745665485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128925139678739956497110323 193387709518109934745665485)
      ·
        refine ⟨72520391069291225529624557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193387709518109934745665485 72520391069291225529624557)
        ·
          refine ⟨27195146650984209573609209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72520391069291225529624557 27195146650984209573609209)
          ·
            refine ⟨20396359988238157180206907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27195146650984209573609209 20396359988238157180206907)
            ·
              refine ⟨30594539982357235770310361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20396359988238157180206907 30594539982357235770310361)
              ·
                refine ⟨22945904986767926827732771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30594539982357235770310361 22945904986767926827732771)
                ·
                  refine ⟨34418857480151890241599157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22945904986767926827732771 34418857480151890241599157)
                  ·
                    refine ⟨3226767888764239710149921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34418857480151890241599157 3226767888764239710149921)
                    ·
                      refine ⟨2420075916573179782612441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3226767888764239710149921 2420075916573179782612441)
                      ·
                        rfl

theorem cell23_4713081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_4713081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713081 prefixEnd_4713081 := by exact prefixLift 4713081
  have htrace : WordTrace (prefixWord ++ tailWord_4713081) baseStart_4713081 baseEnd_4713081 := by
    simpa [prefixWord, tailWord_4713081, baseEnd_4713081] using wordTrace_append hprefix tailTrace_4713081
  have hstable : (prefixWord ++ tailWord_4713081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713081).length < 2 ^ (prefixWord ++ tailWord_4713081).sum := by decide
  have hdescent : baseEnd_4713081 < baseStart_4713081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713108 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_4713108 : Nat := 118140960795 + 4713108 * 2 ^ 59
def prefixEnd_4713108 : Nat := 4983230072969 + 3 ^ 40 * 4713108 * 2
def baseEnd_4713108 : Nat := 806696593516950392324939

theorem tailTrace_4713108 : CollatzResearch.WordTrace tailWord_4713108 prefixEnd_4713108 806696593516950392324939 := by
  unfold tailWord_4713108
  simp only [CollatzResearch.WordTrace]
  refine ⟨85950585504611062803689989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114600780672814750404919985 85950585504611062803689989)
  ·
    refine ⟨16115734782114574275691873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85950585504611062803689989 16115734782114574275691873)
    ·
      refine ⟨12086801086585930706768905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16115734782114574275691873 12086801086585930706768905)
      ·
        refine ⟨9065100814939448030076679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12086801086585930706768905 9065100814939448030076679)
        ·
          refine ⟨13597651222409172045115019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9065100814939448030076679 13597651222409172045115019)
          ·
            refine ⟨20396476833613758067672529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13597651222409172045115019 20396476833613758067672529)
            ·
              refine ⟨15297357625210318550754397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20396476833613758067672529 15297357625210318550754397)
              ·
                refine ⟨5736509109453869456532899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15297357625210318550754397 5736509109453869456532899)
                ·
                  refine ⟨8604763664180804184799349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5736509109453869456532899 8604763664180804184799349)
                  ·
                    refine ⟨806696593516950392324939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8604763664180804184799349 806696593516950392324939)
                    ·
                      rfl

theorem cell23_4713108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_4713108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713108 prefixEnd_4713108 := by exact prefixLift 4713108
  have htrace : WordTrace (prefixWord ++ tailWord_4713108) baseStart_4713108 baseEnd_4713108 := by
    simpa [prefixWord, tailWord_4713108, baseEnd_4713108] using wordTrace_append hprefix tailTrace_4713108
  have hstable : (prefixWord ++ tailWord_4713108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713108).length < 2 ^ (prefixWord ++ tailWord_4713108).sum := by decide
  have hdescent : baseEnd_4713108 < baseStart_4713108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713111 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 4]
def baseStart_4713111 : Nat := 118140960795 + 4713111 * 2 ^ 59
def prefixEnd_4713111 : Nat := 4983230072969 + 3 ^ 40 * 4713111 * 2
def baseEnd_4713111 : Nat := 2420091320992814665237303

theorem tailTrace_4713111 : CollatzResearch.WordTrace tailWord_4713111 prefixEnd_4713111 2420091320992814665237303 := by
  unfold tailWord_4713111
  simp only [CollatzResearch.WordTrace]
  refine ⟨171901280428211257119739187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114600853618807504746492791 171901280428211257119739187)
  ·
    refine ⟨257851920642316885679608781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171901280428211257119739187 257851920642316885679608781)
    ·
      refine ⟨96694470240868832129853293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 257851920642316885679608781 96694470240868832129853293)
      ·
        refine ⟨36260426340325812048694985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96694470240868832129853293 36260426340325812048694985)
        ·
          refine ⟨27195319755244359036521239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36260426340325812048694985 27195319755244359036521239)
          ·
            refine ⟨40792979632866538554781859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27195319755244359036521239 40792979632866538554781859)
            ·
              refine ⟨61189469449299807832172789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40792979632866538554781859 61189469449299807832172789)
              ·
                refine ⟨5736512760871856984266199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61189469449299807832172789 5736512760871856984266199)
                ·
                  refine ⟨8604769141307785476399299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5736512760871856984266199 8604769141307785476399299)
                  ·
                    refine ⟨12907153711961678214598949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8604769141307785476399299 12907153711961678214598949)
                    ·
                      refine ⟨2420091320992814665237303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12907153711961678214598949 2420091320992814665237303)
                      ·
                        rfl

theorem cell23_4713111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_4713111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713111 prefixEnd_4713111 := by exact prefixLift 4713111
  have htrace : WordTrace (prefixWord ++ tailWord_4713111) baseStart_4713111 baseEnd_4713111 := by
    simpa [prefixWord, tailWord_4713111, baseEnd_4713111] using wordTrace_append hprefix tailTrace_4713111
  have hstable : (prefixWord ++ tailWord_4713111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713111).length < 2 ^ (prefixWord ++ tailWord_4713111).sum := by decide
  have hdescent : baseEnd_4713111 < baseStart_4713111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713124 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_4713124 : Nat := 118140960795 + 4713124 * 2 ^ 59
def prefixEnd_4713124 : Nat := 4983230072969 + 3 ^ 40 * 4713124 * 2
def baseEnd_4713124 : Nat := 2420097996241323114374743

theorem tailTrace_4713124 : CollatzResearch.WordTrace tailWord_4713124 prefixEnd_4713124 2420097996241323114374743 := by
  unfold tailWord_4713124
  simp only [CollatzResearch.WordTrace]
  refine ⟨85950877288582080169981213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114601169718109440226641617 85950877288582080169981213)
  ·
    refine ⟨32231578983218280063742955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85950877288582080169981213 32231578983218280063742955)
    ·
      refine ⟨48347368474827420095614433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32231578983218280063742955 48347368474827420095614433)
      ·
        refine ⟨36260526356120565071710825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48347368474827420095614433 36260526356120565071710825)
        ·
          refine ⟨27195394767090423803783119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36260526356120565071710825 27195394767090423803783119)
          ·
            refine ⟨40793092150635635705674679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27195394767090423803783119 40793092150635635705674679)
            ·
              refine ⟨61189638225953453558512019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40793092150635635705674679 61189638225953453558512019)
              ·
                refine ⟨91784457338930180337768029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61189638225953453558512019 91784457338930180337768029)
                ·
                  refine ⟨34419171502098817626663011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91784457338930180337768029 34419171502098817626663011)
                  ·
                    refine ⟨51628757253148226439994517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34419171502098817626663011 51628757253148226439994517)
                    ·
                      refine ⟨2420097996241323114374743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51628757253148226439994517 2420097996241323114374743)
                      ·
                        rfl

theorem cell23_4713124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_4713124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713124 prefixEnd_4713124 := by exact prefixLift 4713124
  have htrace : WordTrace (prefixWord ++ tailWord_4713124) baseStart_4713124 baseEnd_4713124 := by
    simpa [prefixWord, tailWord_4713124, baseEnd_4713124] using wordTrace_append hprefix tailTrace_4713124
  have hstable : (prefixWord ++ tailWord_4713124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713124).length < 2 ^ (prefixWord ++ tailWord_4713124).sum := by decide
  have hdescent : baseEnd_4713124 < baseStart_4713124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713141 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4713141 : Nat := 118140960795 + 4713141 * 2 ^ 59
def prefixEnd_4713141 : Nat := 4983230072969 + 3 ^ 40 * 4713141 * 2
def baseEnd_4713141 : Nat := 2420106725412449547862165

theorem tailTrace_4713141 : CollatzResearch.WordTrace tailWord_4713141 prefixEnd_4713141 2420106725412449547862165 := by
  unfold tailWord_4713141
  simp only [CollatzResearch.WordTrace]
  refine ⟨171902374618102572243331277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 114601583078735048162220851 171902374618102572243331277)
  ·
    refine ⟨64463390481788464591249229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 171902374618102572243331277 64463390481788464591249229)
    ·
      refine ⟨24173771430670674221718461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64463390481788464591249229 24173771430670674221718461)
      ·
        refine ⟨9065164286501502833144423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24173771430670674221718461 9065164286501502833144423)
        ·
          refine ⟨13597746429752254249716635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9065164286501502833144423 13597746429752254249716635)
          ·
            refine ⟨20396619644628381374574953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13597746429752254249716635 20396619644628381374574953)
            ·
              refine ⟨15297464733471286030931215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20396619644628381374574953 15297464733471286030931215)
              ·
                refine ⟨22946197100206929046396823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15297464733471286030931215 22946197100206929046396823)
                ·
                  refine ⟨34419295650310393569595235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22946197100206929046396823 34419295650310393569595235)
                  ·
                    refine ⟨51628943475465590354392853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34419295650310393569595235 51628943475465590354392853)
                    ·
                      refine ⟨2420106725412449547862165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 51628943475465590354392853 2420106725412449547862165)
                      ·
                        rfl

theorem cell23_4713141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4713141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713141 prefixEnd_4713141 := by exact prefixLift 4713141
  have htrace : WordTrace (prefixWord ++ tailWord_4713141) baseStart_4713141 baseEnd_4713141 := by
    simpa [prefixWord, tailWord_4713141, baseEnd_4713141] using wordTrace_append hprefix tailTrace_4713141
  have hstable : (prefixWord ++ tailWord_4713141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713141).length < 2 ^ (prefixWord ++ tailWord_4713141).sum := by decide
  have hdescent : baseEnd_4713141 < baseStart_4713141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713142 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_4713142 : Nat := 118140960795 + 4713142 * 2 ^ 59
def prefixEnd_4713142 : Nat := 4983230072969 + 3 ^ 40 * 4713142 * 2
def baseEnd_4713142 : Nat := 806702412964368014649887

theorem tailTrace_4713142 : CollatzResearch.WordTrace tailWord_4713142 prefixEnd_4713142 806702412964368014649887 := by
  unfold tailWord_4713142
  simp only [CollatzResearch.WordTrace]
  refine ⟨10743900693193684338382355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 114601607394065966276078453 10743900693193684338382355)
  ·
    refine ⟨16115851039790526507573533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10743900693193684338382355 16115851039790526507573533)
    ·
      refine ⟨6043444139921447440340075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16115851039790526507573533 6043444139921447440340075)
      ·
        refine ⟨9065166209882171160510113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6043444139921447440340075 9065166209882171160510113)
        ·
          refine ⟨6798874657411628370382585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9065166209882171160510113 6798874657411628370382585)
          ·
            refine ⟨5099155993058721277786939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6798874657411628370382585 5099155993058721277786939)
            ·
              refine ⟨7648733989588081916680409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5099155993058721277786939 7648733989588081916680409)
              ·
                refine ⟨5736550492191061437510307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7648733989588081916680409 5736550492191061437510307)
                ·
                  refine ⟨8604825738286592156265461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5736550492191061437510307 8604825738286592156265461)
                  ·
                    refine ⟨806702412964368014649887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8604825738286592156265461 806702412964368014649887)
                    ·
                      rfl

theorem cell23_4713142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_4713142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713142 prefixEnd_4713142 := by exact prefixLift 4713142
  have htrace : WordTrace (prefixWord ++ tailWord_4713142) baseStart_4713142 baseEnd_4713142 := by
    simpa [prefixWord, tailWord_4713142, baseEnd_4713142] using wordTrace_append hprefix tailTrace_4713142
  have hstable : (prefixWord ++ tailWord_4713142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713142).length < 2 ^ (prefixWord ++ tailWord_4713142).sum := by decide
  have hdescent : baseEnd_4713142 < baseStart_4713142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713188 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 3, 3, 2]
def baseStart_4713188 : Nat := 118140960795 + 4713188 * 2 ^ 59
def prefixEnd_4713188 : Nat := 4983230072969 + 3 ^ 40 * 4713188 * 2
def baseEnd_4713188 : Nat := 2420130859003210863974449

theorem tailTrace_4713188 : CollatzResearch.WordTrace tailWord_4713188 prefixEnd_4713188 2420130859003210863974449 := by
  unfold tailWord_4713188
  simp only [CollatzResearch.WordTrace]
  refine ⟨85952044424466149635146109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114602725899288199513528145 85952044424466149635146109)
  ·
    refine ⟨32232016659174806113179791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85952044424466149635146109 32232016659174806113179791)
    ·
      refine ⟨48348024988762209169769687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32232016659174806113179791 48348024988762209169769687)
      ·
        refine ⟨72522037483143313754654531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48348024988762209169769687 72522037483143313754654531)
        ·
          refine ⟨108783056224714970631981797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72522037483143313754654531 108783056224714970631981797)
          ·
            refine ⟨20396823042134056993496587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 108783056224714970631981797 20396823042134056993496587)
            ·
              refine ⟨30595234563201085490244881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20396823042134056993496587 30595234563201085490244881)
              ·
                refine ⟨22946425922400814117683661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30595234563201085490244881 22946425922400814117683661)
                ·
                  refine ⟨8604909720900305294131373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22946425922400814117683661 8604909720900305294131373)
                  ·
                    refine ⟨3226841145337614485299265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8604909720900305294131373 3226841145337614485299265)
                    ·
                      refine ⟨2420130859003210863974449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3226841145337614485299265 2420130859003210863974449)
                      ·
                        rfl

theorem cell23_4713188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 3, 3, 2].length) (baseStart_4713188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713188 prefixEnd_4713188 := by exact prefixLift 4713188
  have htrace : WordTrace (prefixWord ++ tailWord_4713188) baseStart_4713188 baseEnd_4713188 := by
    simpa [prefixWord, tailWord_4713188, baseEnd_4713188] using wordTrace_append hprefix tailTrace_4713188
  have hstable : (prefixWord ++ tailWord_4713188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713188).length < 2 ^ (prefixWord ++ tailWord_4713188).sum := by decide
  have hdescent : baseEnd_4713188 < baseStart_4713188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4713252 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 1, 4, 2]
def baseStart_4713252 : Nat := 118140960795 + 4713252 * 2 ^ 59
def prefixEnd_4713252 : Nat := 4983230072969 + 3 ^ 40 * 4713252 * 2
def baseEnd_4713252 : Nat := 2420163721765098613574155

theorem tailTrace_4713252 : CollatzResearch.WordTrace tailWord_4713252 prefixEnd_4713252 2420163721765098613574155 := by
  unfold tailWord_4713252
  simp only [CollatzResearch.WordTrace]
  refine ⟨85953211560350219100311005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 114604282080466958800414673 85953211560350219100311005)
  ·
    refine ⟨32232454335131332162616627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85953211560350219100311005 32232454335131332162616627)
    ·
      refine ⟨48348681502696998243924941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32232454335131332162616627 48348681502696998243924941)
      ·
        refine ⟨18130755563511374341471853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48348681502696998243924941 18130755563511374341471853)
        ·
          refine ⟨6799033336316765378051945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18130755563511374341471853 6799033336316765378051945)
          ·
            refine ⟨5099275002237574033538959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6799033336316765378051945 5099275002237574033538959)
            ·
              refine ⟨7648912503356361050308439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5099275002237574033538959 7648912503356361050308439)
              ·
                refine ⟨11473368755034541575462659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7648912503356361050308439 11473368755034541575462659)
                ·
                  refine ⟨17210053132551812363193989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11473368755034541575462659 17210053132551812363193989)
                  ·
                    refine ⟨3226884962353464818098873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17210053132551812363193989 3226884962353464818098873)
                    ·
                      refine ⟨2420163721765098613574155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3226884962353464818098873 2420163721765098613574155)
                      ·
                        rfl

theorem cell23_4713252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_4713252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4713252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4713252 prefixEnd_4713252 := by exact prefixLift 4713252
  have htrace : WordTrace (prefixWord ++ tailWord_4713252) baseStart_4713252 baseEnd_4713252 := by
    simpa [prefixWord, tailWord_4713252, baseEnd_4713252] using wordTrace_append hprefix tailTrace_4713252
  have hstable : (prefixWord ++ tailWord_4713252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4713252).length < 2 ^ (prefixWord ++ tailWord_4713252).sum := by decide
  have hdescent : baseEnd_4713252 < baseStart_4713252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4713252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
